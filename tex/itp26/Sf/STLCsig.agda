{-# OPTIONS --rewriting --local-confluence-check #-}
module STLCsig where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)
open import Agda.Builtin.Equality.Rewrite
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate funext : ∀ {a b} → Extensionality a b
variable l m n k : ℕ

data Tm : ℕ → Set where
  `_  : Fin n → Tm n
  ƛ_  : Tm (suc n) → Tm n
  _·_ : Tm n → Tm n → Tm n
infixr 5 ƛ_
infixl 6 _·_

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n
idᴿ : Ren n n
idᴿ x = x
wkᴿ : Ren n (suc n)
wkᴿ x = suc x
_↑ᴿ : Ren m n → Ren (suc m) (suc n)
(ρ ↑ᴿ) zero = zero
(ρ ↑ᴿ) (suc x) = suc (ρ x)

Sub : ℕ → ℕ → Set
Sub m n = Fin m → Tm n

opaque
  -- model operators, OPAQUE (clauses hidden at the pragma); Sub stays transparent
  _⟨_⟩ : Tm m → Ren m n → Tm n
  (` x)     ⟨ ρ ⟩ = ` (ρ x)
  (ƛ e)     ⟨ ρ ⟩ = ƛ (e ⟨ ρ ↑ᴿ ⟩)
  (e₁ · e₂) ⟨ ρ ⟩ = (e₁ ⟨ ρ ⟩) · (e₂ ⟨ ρ ⟩)
  id : Sub n n
  id = `_
  wk : Sub n (suc n)
  wk x = ` (suc x)
  _∙_ : Tm n → Sub m n → Sub (suc m) n
  (e ∙ σ) zero    = e
  (e ∙ σ) (suc x) = σ x
  liftˢ : Sub m n → Sub (suc m) (suc n)
  (liftˢ σ) zero    = ` zero
  (liftˢ σ) (suc x) = (σ x) ⟨ wkᴿ ⟩
  _[_] : Tm m → Sub m n → Tm n
  (` x)     [ σ ] = σ x
  (ƛ e)     [ σ ] = ƛ (e [ liftˢ σ ])
  (e₁ · e₂) [ σ ] = (e₁ [ σ ]) · (e₂ [ σ ])
  _⨟_ : Sub m k → Sub k n → Sub m n
  (σ ⨟ τ) x = (σ x) [ τ ]
  ⌜_⌝ : Ren m n → Sub m n
  ⌜ ρ ⌝ x = ` (ρ x)
  infixl 6 _⨟_
  infixr 7 _∙_
  infixl 8 _[_]
  variable e e₁ e₂ : Tm n
  variable σ τ υ : Sub m n
  variable ρ : Ren m n

  -- helper lemmas (opaque)
  ⟨⟩⟨⟩ : (e : Tm m)(ρ₁ : Ren m k)(ρ₂ : Ren k n) → (e ⟨ ρ₁ ⟩) ⟨ ρ₂ ⟩ ≡ e ⟨ (λ x → ρ₂ (ρ₁ x)) ⟩
  ⟨⟩⟨⟩ (` x) ρ₁ ρ₂ = refl
  ⟨⟩⟨⟩ (ƛ e) ρ₁ ρ₂ = cong ƛ_ (trans (⟨⟩⟨⟩ e (ρ₁ ↑ᴿ) (ρ₂ ↑ᴿ)) (cong (λ r → e ⟨ r ⟩) (funext λ { zero → refl ; (suc x) → refl })))
  ⟨⟩⟨⟩ (e₁ · e₂) ρ₁ ρ₂ = cong₂ _·_ (⟨⟩⟨⟩ e₁ ρ₁ ρ₂) (⟨⟩⟨⟩ e₂ ρ₁ ρ₂)
  []⟨⟩ : (e : Tm m)(ρ : Ren m k)(σ : Sub k n) → (e ⟨ ρ ⟩) [ σ ] ≡ e [ (λ x → σ (ρ x)) ]
  []⟨⟩ (` x) ρ σ = refl
  []⟨⟩ (ƛ e) ρ σ = cong ƛ_ (trans ([]⟨⟩ e (ρ ↑ᴿ) (liftˢ σ)) (cong (λ s → e [ s ]) (funext λ { zero → refl ; (suc x) → refl })))
  []⟨⟩ (e₁ · e₂) ρ σ = cong₂ _·_ ([]⟨⟩ e₁ ρ σ) ([]⟨⟩ e₂ ρ σ)
  ⟨⟩[] : (e : Tm m)(σ : Sub m k)(ρ : Ren k n) → (e [ σ ]) ⟨ ρ ⟩ ≡ e [ (λ x → (σ x) ⟨ ρ ⟩) ]
  ⟨⟩[] (` x) σ ρ = refl
  ⟨⟩[] (ƛ e) σ ρ = cong ƛ_ (trans (⟨⟩[] e (liftˢ σ) (ρ ↑ᴿ)) (cong (λ s → e [ s ]) (funext λ { zero → refl ; (suc x) → trans (⟨⟩⟨⟩ (σ x) wkᴿ (ρ ↑ᴿ)) (sym (⟨⟩⟨⟩ (σ x) ρ wkᴿ)) })))
  ⟨⟩[] (e₁ · e₂) σ ρ = cong₂ _·_ (⟨⟩[] e₁ σ ρ) (⟨⟩[] e₂ σ ρ)
  liftˢ⨟ : (σ : Sub m k)(τ : Sub k n) → (λ x → ((liftˢ σ) x) [ liftˢ τ ]) ≡ liftˢ (σ ⨟ τ)
  liftˢ⨟ σ τ = funext λ { zero → refl ; (suc x) → trans ([]⟨⟩ (σ x) wkᴿ (liftˢ τ)) (sym (⟨⟩[] (σ x) τ wkᴿ)) }
  Clos-pf : (e : Tm m)(σ : Sub m k)(τ : Sub k n) → (e [ σ ]) [ τ ] ≡ e [ σ ⨟ τ ]
  Clos-pf (` x) σ τ = refl
  Clos-pf (ƛ e) σ τ = cong ƛ_ (trans (Clos-pf e (liftˢ σ) (liftˢ τ)) (cong (λ s → e [ s ]) (liftˢ⨟ σ τ)))
  Clos-pf (e₁ · e₂) σ τ = cong₂ _·_ (Clos-pf e₁ σ τ) (Clos-pf e₂ σ τ)
  IdSubst-pf : (e : Tm n) → e [ id ] ≡ e
  IdSubst-pf (` x) = refl
  IdSubst-pf (ƛ e) = cong ƛ_ (trans (cong (λ s → e [ s ]) (funext λ { zero → refl ; (suc x) → refl })) (IdSubst-pf e))
  IdSubst-pf (e₁ · e₂) = cong₂ _·_ (IdSubst-pf e₁) (IdSubst-pf e₂)
  coincidence-pf : (e : Tm m)(ρ : Ren m n) → e ⟨ ρ ⟩ ≡ e [ ⌜ ρ ⌝ ]
  coincidence-pf (` x) ρ = refl
  coincidence-pf (ƛ e) ρ = cong ƛ_ (trans (coincidence-pf e (ρ ↑ᴿ)) (cong (λ s → e [ s ]) (funext λ { zero → refl ; (suc x) → refl })))
  coincidence-pf (e₁ · e₂) ρ = cong₂ _·_ (coincidence-pf e₁ ρ) (coincidence-pf e₂ ρ)

  -- σ-laws (proofs are opaque)
  Clos      : (e [ σ ]) [ τ ] ≡ e [ σ ⨟ τ ]
  Clos {e = e} {σ = σ} {τ = τ} = Clos-pf e σ τ
  IdSubst   : e [ id ] ≡ e
  IdSubst {e = e} = IdSubst-pf e
  VarCons-z : (` zero) [ e ∙ σ ] ≡ e
  VarCons-z = refl
  su-elim   : ∀ {x : Fin n} → (` (suc x)) ≡ (` x) [ wk ]
  su-elim = refl
  IdL       : id ⨟ σ ≡ σ
  IdL = refl
  IdR       : σ ⨟ id ≡ σ
  IdR {σ = σ} = funext λ x → IdSubst-pf (σ x)
  ShiftCons : wk ⨟ (e ∙ σ) ≡ σ
  ShiftCons = funext λ x → refl
  Map       : (e ∙ σ) ⨟ τ ≡ (e [ τ ]) ∙ (σ ⨟ τ)
  Map = funext λ { zero → refl ; (suc x) → refl }
  Ass       : (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
  Ass {σ = σ} {τ = τ} {υ = υ} = funext λ x → Clos-pf (σ x) τ υ
  IdCons    : (` zero {n}) ∙ wk ≡ id
  IdCons = funext λ { zero → refl ; (suc x) → refl }
  SCons     : ((` zero) [ σ ]) ∙ (wk ⨟ σ) ≡ σ
  SCons = funext λ { zero → refl ; (suc x) → refl }
  Inst-·    : (e₁ · e₂) [ σ ] ≡ (e₁ [ σ ]) · (e₂ [ σ ])
  Inst-· = refl
  Inst-ƛ    : (ƛ e) [ σ ] ≡ ƛ (e [ (` zero) ∙ (σ ⨟ wk) ])
  Inst-ƛ {e = e} {σ = σ} = cong ƛ_ (cong (λ s → e [ s ]) (funext λ { zero → refl ; (suc x) → coincidence-pf (σ x) wkᴿ }))
  coincidence : e ⟨ ρ ⟩ ≡ e [ ⌜ ρ ⌝ ]
  coincidence {e = e} {ρ = ρ} = coincidence-pf e ρ
  embed-id : ⌜ idᴿ {n} ⌝ ≡ id
  embed-id = funext λ x → refl
  embed-wk : ⌜ wkᴿ {n} ⌝ ≡ wk
  embed-wk = funext λ x → refl
  embed-↑  : ⌜ ρ ↑ᴿ ⌝ ≡ (` zero) ∙ (⌜ ρ ⌝ ⨟ wk)
  embed-↑ {ρ = ρ} = funext λ { zero → refl ; (suc x) → refl }
  var-ren : ∀ {x} → (` x) ⟨ ρ ⟩ ≡ ` (ρ x)
  var-ren = refl
{-# REWRITE Clos IdSubst VarCons-z IdL IdR ShiftCons Map Ass IdCons SCons
            Inst-· Inst-ƛ coincidence embed-id embed-wk embed-↑ su-elim #-}
