{-# OPTIONS --rewriting --local-confluence-check #-}
-- Renaming kept TRANSPARENT (a computing Fin-traversal); substitution alone is symbolic.
module STLCone where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
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
_∘_ : Ren m k → Ren k n → Ren m n
(ρ₁ ∘ ρ₂) x = ρ₂ (ρ₁ x)

-- TRANSPARENT term renaming — it COMPUTES (this is the whole point)
_⟨_⟩ : Tm m → Ren m n → Tm n
(` x)     ⟨ ρ ⟩ = ` (ρ x)
(ƛ e)     ⟨ ρ ⟩ = ƛ (e ⟨ ρ ↑ᴿ ⟩)
(e₁ · e₂) ⟨ ρ ⟩ = (e₁ ⟨ ρ ⟩) · (e₂ ⟨ ρ ⟩)
infixl 8 _⟨_⟩

↑ᴿ-∘ : (ρ₁ : Ren m k)(ρ₂ : Ren k n)(x : Fin (suc m)) → ((ρ₁ ∘ ρ₂) ↑ᴿ) x ≡ ((ρ₁ ↑ᴿ) ∘ (ρ₂ ↑ᴿ)) x
↑ᴿ-∘ ρ₁ ρ₂ zero = refl
↑ᴿ-∘ ρ₁ ρ₂ (suc x) = refl
ren-∘ : (e : Tm m)(ρ₁ : Ren m k)(ρ₂ : Ren k n) → (e ⟨ ρ₁ ⟩) ⟨ ρ₂ ⟩ ≡ e ⟨ ρ₁ ∘ ρ₂ ⟩
ren-∘ (` x) ρ₁ ρ₂ = refl
ren-∘ (ƛ e) ρ₁ ρ₂ = cong ƛ_ (trans (ren-∘ e (ρ₁ ↑ᴿ) (ρ₂ ↑ᴿ)) (cong (e ⟨_⟩) (funext (λ x → sym (↑ᴿ-∘ ρ₁ ρ₂ x)))))
ren-∘ (e₁ · e₂) ρ₁ ρ₂ = cong₂ _·_ (ren-∘ e₁ ρ₁ ρ₂) (ren-∘ e₂ ρ₁ ρ₂)

Sub : ℕ → ℕ → Set
Sub m n = Fin m → Tm n


-- ===== typing relation (OUTSIDE the block: exposed; constructors aren't confluence-checked) =====
data Type : Set where
  ι   : Type
  _⇒_ : Type → Type → Type
infixr 5 _⇒_
variable A B C : Type
data Ctx : ℕ → Set where
  ∅    : Ctx 0
  _,,_ : ∀ {n} → Ctx n → Type → Ctx (suc n)
infixl 6 _,,_
variable Γ Δ : Ctx n
data _∋_∶_ : ∀ {n} → Ctx n → Fin n → Type → Set where
  here  : ∀ {n}{Γ : Ctx n}{A}      → (Γ ,, A) ∋ zero ∶ A
  there : ∀ {n}{Γ : Ctx n}{A B}{x} → Γ ∋ x ∶ A → (Γ ,, B) ∋ (suc x) ∶ A
infix 4 _∋_∶_
data _⊢_∶_ : ∀ {n} → Ctx n → Tm n → Type → Set where
  ⊢v : ∀ {n}{Γ : Ctx n}{x}{A}        → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  ⊢ƛ : ∀ {n}{Γ : Ctx n}{e}{A B}      → (Γ ,, A) ⊢ e ∶ B → Γ ⊢ (ƛ e) ∶ (A ⇒ B)
  ⊢· : ∀ {n}{Γ : Ctx n}{e₁ e₂}{A B}  → Γ ⊢ e₁ ∶ (A ⇒ B) → Γ ⊢ e₂ ∶ A → Γ ⊢ (e₁ · e₂) ∶ B
infix 4 _⊢_∶_

opaque
  liftˢ : Sub m n → Sub (suc m) (suc n)
  (liftˢ σ) zero    = ` zero
  (liftˢ σ) (suc x) = (σ x) ⟨ wkᴿ ⟩
  _[_] : Tm m → Sub m n → Tm n
  (` x)     [ σ ] = σ x
  (ƛ e)     [ σ ] = ƛ (e [ liftˢ σ ])
  (e₁ · e₂) [ σ ] = (e₁ [ σ ]) · (e₂ [ σ ])
  id : Sub n n
  id = `_
  wk : Sub n (suc n)
  wk x = ` (suc x)
  _∙_ : Tm n → Sub m n → Sub (suc m) n
  (e ∙ σ) zero    = e
  (e ∙ σ) (suc x) = σ x
  _⨟_ : Sub m k → Sub k n → Sub m n
  (σ ⨟ τ) x = (σ x) [ τ ]
  infixl 6 _⨟_
  infixr 7 _∙_
  infixl 8 _[_]
  variable e e₁ e₂ : Tm n
  variable σ τ υ : Sub m n
  variable ρ : Ren m n

  -- kit lemmas
  sub-ren : (e : Tm m)(ρ : Ren m k)(σ : Sub k n) → (e ⟨ ρ ⟩) [ σ ] ≡ e [ (λ x → σ (ρ x)) ]
  sub-ren (` x) ρ σ = refl
  sub-ren (ƛ e) ρ σ = cong ƛ_ (trans (sub-ren e (ρ ↑ᴿ) (liftˢ σ)) (cong (λ s → e [ s ]) (funext λ { zero → refl ; (suc x) → refl })))
  sub-ren (e₁ · e₂) ρ σ = cong₂ _·_ (sub-ren e₁ ρ σ) (sub-ren e₂ ρ σ)
  ren-sub : (e : Tm m)(σ : Sub m k)(ρ : Ren k n) → (e [ σ ]) ⟨ ρ ⟩ ≡ e [ (λ x → (σ x) ⟨ ρ ⟩) ]
  ren-sub (` x) σ ρ = refl
  ren-sub (ƛ e) σ ρ = cong ƛ_ (trans (ren-sub e (liftˢ σ) (ρ ↑ᴿ)) (cong (λ s → e [ s ]) (funext λ { zero → refl ; (suc x) → trans (ren-∘ (σ x) wkᴿ (ρ ↑ᴿ)) (sym (ren-∘ (σ x) ρ wkᴿ)) })))
  ren-sub (e₁ · e₂) σ ρ = cong₂ _·_ (ren-sub e₁ σ ρ) (ren-sub e₂ σ ρ)
  liftˢ⨟ : (σ : Sub m k)(τ : Sub k n) → (λ x → ((liftˢ σ) x) [ liftˢ τ ]) ≡ liftˢ (σ ⨟ τ)
  liftˢ⨟ σ τ = funext λ { zero → refl ; (suc x) → trans (sub-ren (σ x) wkᴿ (liftˢ τ)) (sym (ren-sub (σ x) τ wkᴿ)) }
  Clos-pf : (e : Tm m)(σ : Sub m k)(τ : Sub k n) → (e [ σ ]) [ τ ] ≡ e [ σ ⨟ τ ]
  Clos-pf (` x) σ τ = refl
  Clos-pf (ƛ e) σ τ = cong ƛ_ (trans (Clos-pf e (liftˢ σ) (liftˢ τ)) (cong (λ s → e [ s ]) (liftˢ⨟ σ τ)))
  Clos-pf (e₁ · e₂) σ τ = cong₂ _·_ (Clos-pf e₁ σ τ) (Clos-pf e₂ σ τ)
  IdSubst-pf : (e : Tm n) → e [ id ] ≡ e
  IdSubst-pf (` x) = refl
  IdSubst-pf (ƛ e) = cong ƛ_ (trans (cong (λ s → e [ s ]) (funext λ { zero → refl ; (suc x) → refl })) (IdSubst-pf e))
  IdSubst-pf (e₁ · e₂) = cong₂ _·_ (IdSubst-pf e₁) (IdSubst-pf e₂)
  ren-is-sub : (e : Tm m)(ρ : Ren m n) → e ⟨ ρ ⟩ ≡ e [ (λ x → ` (ρ x)) ]
  ren-is-sub (` x) ρ = refl
  ren-is-sub (ƛ e) ρ = cong ƛ_ (trans (cong (e ⟨_⟩) refl) (trans (ren-is-sub e (ρ ↑ᴿ)) (cong (λ s → e [ s ]) (funext λ { zero → refl ; (suc x) → refl }))))
  ren-is-sub (e₁ · e₂) ρ = cong₂ _·_ (ren-is-sub e₁ ρ) (ren-is-sub e₂ ρ)

  Clos      : (e [ σ ]) [ τ ] ≡ e [ σ ⨟ τ ]
  Clos {e = e} {σ = σ} {τ = τ} = Clos-pf e σ τ
  IdSubst   : e [ id ] ≡ e
  IdSubst {e = e} = IdSubst-pf e
  VarCons-z : (` zero) [ e ∙ σ ] ≡ e
  VarCons-z = refl
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
  Inst-ƛ {e = e} {σ = σ} = cong ƛ_ (cong (λ s → e [ s ]) (funext λ { zero → refl ; (suc x) → ren-is-sub (σ x) wkᴿ }))
  -- the kit bridge, exposed as a lemma (NOT a rewrite): renaming-weakening = subst-weakening
  ⟨wk⟩≡[wk] : (e : Tm n) → e ⟨ wkᴿ ⟩ ≡ e [ wk ]
  ⟨wk⟩≡[wk] e = ren-is-sub e wkᴿ
  lift-suc : ∀ {x : Fin m} → (` (suc x)) [ (` zero) ∙ (σ ⨟ wk) ] ≡ (` x) [ σ ⨟ wk ]
  lift-suc = refl

  -- ===== preservation, INSIDE the block (operators transparent here → proofs COMPUTE, subst-free) =====
  _∶_⇒ᴿ_ : ∀ {m n} → Ren m n → Ctx m → Ctx n → Set
  _∶_⇒ᴿ_ ρ Γ Δ = ∀ {x}{A} → Γ ∋ x ∶ A → Δ ∋ (ρ x) ∶ A
  ↑ᴿ-pres : ∀ {m n}{A}{Γ : Ctx m}{Δ : Ctx n}{ρ : Ren m n} → ρ ∶ Γ ⇒ᴿ Δ → (ρ ↑ᴿ) ∶ (Γ ,, A) ⇒ᴿ (Δ ,, A)
  ↑ᴿ-pres ⊢ρ here      = here
  ↑ᴿ-pres ⊢ρ (there i) = there (⊢ρ i)
  wk-mor : ∀ {n}{B}{Δ : Ctx n} → wkᴿ ∶ Δ ⇒ᴿ (Δ ,, B)
  wk-mor i = there i
  ren-pres : ∀ {m n}{Γ : Ctx m}{Δ : Ctx n}{ρ : Ren m n}{e}{A} → ρ ∶ Γ ⇒ᴿ Δ → Γ ⊢ e ∶ A → Δ ⊢ (e ⟨ ρ ⟩) ∶ A
  ren-pres ⊢ρ (⊢v i)     = ⊢v (⊢ρ i)
  ren-pres ⊢ρ (⊢ƛ ⊢e)    = ⊢ƛ (ren-pres (↑ᴿ-pres ⊢ρ) ⊢e)
  ren-pres ⊢ρ (⊢· ⊢a ⊢b) = ⊢· (ren-pres ⊢ρ ⊢a) (ren-pres ⊢ρ ⊢b)
  _∶_⇒ˢ_ : ∀ {m n} → Sub m n → Ctx m → Ctx n → Set
  _∶_⇒ˢ_ σ Γ Δ = ∀ {x}{A} → Γ ∋ x ∶ A → Δ ⊢ ((` x) [ σ ]) ∶ A
  ↑ˢ-pres : ∀ {m n}{A}{Γ : Ctx m}{Δ : Ctx n}{σ : Sub m n} → σ ∶ Γ ⇒ˢ Δ → (liftˢ σ) ∶ (Γ ,, A) ⇒ˢ (Δ ,, A)
  ↑ˢ-pres ⊢σ here      = ⊢v here
  ↑ˢ-pres ⊢σ (there i) = ren-pres wk-mor (⊢σ i)
  sub-pres : ∀ {m n}{Γ : Ctx m}{Δ : Ctx n}{σ : Sub m n}{e}{A} → σ ∶ Γ ⇒ˢ Δ → Γ ⊢ e ∶ A → Δ ⊢ (e [ σ ]) ∶ A
  sub-pres ⊢σ (⊢v i)     = ⊢σ i
  sub-pres ⊢σ (⊢ƛ ⊢e)    = ⊢ƛ (sub-pres (↑ˢ-pres ⊢σ) ⊢e)
  sub-pres ⊢σ (⊢· ⊢a ⊢b) = ⊢· (sub-pres ⊢σ ⊢a) (sub-pres ⊢σ ⊢b)
  -- the β-substitution morphism (u ∙ id); inside the block so the lookups COMPUTE
  β-mor : ∀ {n}{Γ : Ctx n}{u}{A} → Γ ⊢ u ∶ A → (u ∙ id) ∶ (Γ ,, A) ⇒ˢ Γ
  β-mor ⊢u here      = ⊢u
  β-mor ⊢u (there j) = ⊢v j

{-# REWRITE Clos IdSubst VarCons-z IdL IdR ShiftCons Map Ass IdCons SCons Inst-· Inst-ƛ #-}

-- ===== reduction and subject reduction =====
data _⟶_ : ∀ {n} → Tm n → Tm n → Set where
  β   : ∀ {n}{e : Tm (suc n)}{u : Tm n} → ((ƛ e) · u) ⟶ (e [ u ∙ id ])
  ξƛ  : ∀ {n}{e e' : Tm (suc n)}        → e ⟶ e' → (ƛ e) ⟶ (ƛ e')
  ξ·ₗ : ∀ {n}{e₁ e₁' e₂ : Tm n}         → e₁ ⟶ e₁' → (e₁ · e₂) ⟶ (e₁' · e₂)
  ξ·ᵣ : ∀ {n}{e₁ e₂ e₂' : Tm n}         → e₂ ⟶ e₂' → (e₁ · e₂) ⟶ (e₁ · e₂')
infix 3 _⟶_

-- SUBJECT REDUCTION: typing is preserved by reduction
preserve : ∀ {n}{Γ : Ctx n}{e e′}{A} → Γ ⊢ e ∶ A → e ⟶ e′ → Γ ⊢ e′ ∶ A
preserve (⊢· (⊢ƛ ⊢e) ⊢u) β        = sub-pres (β-mor ⊢u) ⊢e
preserve (⊢ƛ ⊢e)         (ξƛ  r)  = ⊢ƛ (preserve ⊢e r)
preserve (⊢· ⊢a ⊢b)      (ξ·ₗ r)  = ⊢· (preserve ⊢a r) ⊢b
preserve (⊢· ⊢a ⊢b)      (ξ·ᵣ r)  = ⊢· ⊢a (preserve ⊢b r)
