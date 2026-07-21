{-# OPTIONS --rewriting --local-confluence-check #-}
-- STLC over the genuinely-confluent σ-calculus, in ONE module:
--   * the σ-rewrite set passes --local-confluence-check at 0 (NO --double-check);
--   * renaming-preserves-typing (ren-pres) and substitution-preserves-typing (sub-pres),
--     with sub-pres using ren-pres for weakening.
-- Only `funext` is postulated.  The proofs are definitional EXCEPT two propositional
-- steps (var-ren, lift-suc): variable-renaming and suc-lookup CANNOT be rewrites without
-- breaking confluence (VarCons-s/Var-wk do — verified), so they are the price of confluence.
-- `subst` (not `rewrite`) is used for those two, which also avoids an Agda
-- confluence-checker __IMPOSSIBLE__ crash triggered by `rewrite` under --local-confluence-check.
module STLC where
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
-- transparent renaming primitives (they compute on indices in the proofs)
idᴿ : Ren n n
idᴿ x = x
wkᴿ : Ren n (suc n)
wkᴿ x = suc x
_↑ᴿ : Ren m n → Ren (suc m) (suc n)
(ρ ↑ᴿ) zero = zero
(ρ ↑ᴿ) (suc x) = suc (ρ x)

module M where
  ren : Tm m → Ren m n → Tm n
  ren (` x) ρ = ` (ρ x)
  ren (ƛ e) ρ = ƛ (ren e (ρ ↑ᴿ))
  ren (e₁ · e₂) ρ = ren e₁ ρ · ren e₂ ρ
  Sub : ℕ → ℕ → Set
  Sub m n = Fin m → Tm n
  id : Sub n n
  id = `_
  wk : Sub n (suc n)
  wk x = ` (suc x)
  _∙_ : Tm n → Sub m n → Sub (suc m) n
  (e ∙ σ) zero = e
  (e ∙ σ) (suc x) = σ x
  _↑ˢ : Sub m n → Sub (suc m) (suc n)
  (σ ↑ˢ) zero = ` zero
  (σ ↑ˢ) (suc x) = ren (σ x) suc
  sub : Tm m → Sub m n → Tm n
  sub (` x) σ = σ x
  sub (ƛ e) σ = ƛ (sub e (σ ↑ˢ))
  sub (e₁ · e₂) σ = sub e₁ σ · sub e₂ σ
  _⨟_ : Sub m k → Sub k n → Sub m n
  (σ ⨟ τ) x = sub (σ x) τ
  ⟨_⟩ : Ren m n → Sub m n
  ⟨ ρ ⟩ x = ` (ρ x)
  ren-ren : (e : Tm m)(ρ₁ : Ren m k)(ρ₂ : Ren k n) → ren (ren e ρ₁) ρ₂ ≡ ren e (λ x → ρ₂ (ρ₁ x))
  ren-ren (` x) ρ₁ ρ₂ = refl
  ren-ren (ƛ e) ρ₁ ρ₂ = cong ƛ_ (trans (ren-ren e (ρ₁ ↑ᴿ) (ρ₂ ↑ᴿ)) (cong (ren e) (funext λ { zero → refl ; (suc x) → refl })))
  ren-ren (e₁ · e₂) ρ₁ ρ₂ = cong₂ _·_ (ren-ren e₁ ρ₁ ρ₂) (ren-ren e₂ ρ₁ ρ₂)
  sub-ren : (e : Tm m)(ρ : Ren m k)(σ : Sub k n) → sub (ren e ρ) σ ≡ sub e (λ x → σ (ρ x))
  sub-ren (` x) ρ σ = refl
  sub-ren (ƛ e) ρ σ = cong ƛ_ (trans (sub-ren e (ρ ↑ᴿ) (σ ↑ˢ)) (cong (sub e) (funext λ { zero → refl ; (suc x) → refl })))
  sub-ren (e₁ · e₂) ρ σ = cong₂ _·_ (sub-ren e₁ ρ σ) (sub-ren e₂ ρ σ)
  ren-sub : (e : Tm m)(σ : Sub m k)(ρ : Ren k n) → ren (sub e σ) ρ ≡ sub e (λ x → ren (σ x) ρ)
  ren-sub (` x) σ ρ = refl
  ren-sub (ƛ e) σ ρ = cong ƛ_ (trans (ren-sub e (σ ↑ˢ) (ρ ↑ᴿ)) (cong (sub e) (funext λ { zero → refl ; (suc x) → trans (ren-ren (σ x) suc (ρ ↑ᴿ)) (sym (ren-ren (σ x) ρ suc)) })))
  ren-sub (e₁ · e₂) σ ρ = cong₂ _·_ (ren-sub e₁ σ ρ) (ren-sub e₂ σ ρ)
  ⨟∘↑ˢ : (σ : Sub m k)(τ : Sub k n) → (λ x → sub ((σ ↑ˢ) x) (τ ↑ˢ)) ≡ ((λ x → sub (σ x) τ) ↑ˢ)
  ⨟∘↑ˢ σ τ = funext λ { zero → refl ; (suc x) → trans (sub-ren (σ x) suc (τ ↑ˢ)) (sym (ren-sub (σ x) τ suc)) }
  compositionality : (e : Tm m)(σ : Sub m k)(τ : Sub k n) → sub (sub e σ) τ ≡ sub e (σ ⨟ τ)
  compositionality (` x) σ τ = refl
  compositionality (ƛ e) σ τ = cong ƛ_ (trans (compositionality e (σ ↑ˢ) (τ ↑ˢ)) (cong (sub e) (⨟∘↑ˢ σ τ)))
  compositionality (e₁ · e₂) σ τ = cong₂ _·_ (compositionality e₁ σ τ) (compositionality e₂ σ τ)
  sub-id : (e : Tm n) → sub e id ≡ e
  sub-id (` x) = refl
  sub-id (ƛ e) = cong ƛ_ (trans (cong (sub e) (funext λ { zero → refl ; (suc x) → refl })) (sub-id e))
  sub-id (e₁ · e₂) = cong₂ _·_ (sub-id e₁) (sub-id e₂)
  ren-is-sub : (e : Tm m)(ρ : Ren m n) → ren e ρ ≡ sub e (λ x → ` (ρ x))
  ren-is-sub (` x) ρ = refl
  ren-is-sub (ƛ e) ρ = cong ƛ_ (trans (ren-is-sub e (ρ ↑ᴿ)) (cong (sub e) (funext λ { zero → refl ; (suc x) → refl })))
  ren-is-sub (e₁ · e₂) ρ = cong₂ _·_ (ren-is-sub e₁ ρ) (ren-is-sub e₂ ρ)

opaque
  Sub : ℕ → ℕ → Set
  Sub = M.Sub
  _[_] : Tm m → Sub m n → Tm n
  e [ σ ] = M.sub e σ
  _⨟_ : Sub m k → Sub k n → Sub m n
  σ ⨟ τ = σ M.⨟ τ
  id : Sub n n
  id = M.id
  wk : Sub n (suc n)
  wk = M.wk
  _∙_ : Tm n → Sub m n → Sub (suc m) n
  e ∙ σ = e M.∙ σ
  infixl 6 _⨟_
  infixr 7 _∙_
  infixl 8 _[_]
  variable e e₁ e₂ : Tm n
  variable σ τ υ : Sub m n
  variable ρ : Ren m n
  Clos      : (e [ σ ]) [ τ ] ≡ e [ σ ⨟ τ ]
  Clos {e = e} {σ = σ} {τ = τ} = M.compositionality e σ τ
  IdSubst   : e [ id ] ≡ e
  IdSubst {e = e} = M.sub-id e
  VarCons-z : (` zero) [ e ∙ σ ] ≡ e
  VarCons-z = refl
  VarCons-s : ∀ {x} → (` (suc x)) [ e ∙ σ ] ≡ (` x) [ σ ]
  VarCons-s = refl
  Var-wk    : ∀ {x : Fin n} → (` x) [ wk ] ≡ ` (suc x)
  Var-wk = refl
  IdL       : id ⨟ σ ≡ σ
  IdL = refl
  IdR       : σ ⨟ id ≡ σ
  IdR {σ = σ} = funext λ x → M.sub-id (σ x)
  ShiftCons : wk ⨟ (e ∙ σ) ≡ σ
  ShiftCons = funext λ x → refl
  Map       : (e ∙ σ) ⨟ τ ≡ (e [ τ ]) ∙ (σ ⨟ τ)
  Map = funext λ { zero → refl ; (suc x) → refl }
  Ass       : (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
  Ass {σ = σ} {τ = τ} {υ = υ} = funext λ x → M.compositionality (σ x) τ υ
  IdCons    : (` zero {n}) ∙ wk ≡ id
  IdCons = funext λ { zero → refl ; (suc x) → refl }
  SCons     : ((` zero) [ σ ]) ∙ (wk ⨟ σ) ≡ σ
  SCons = funext λ { zero → refl ; (suc x) → refl }
  Inst-·    : (e₁ · e₂) [ σ ] ≡ (e₁ [ σ ]) · (e₂ [ σ ])
  Inst-· = refl
  Inst-ƛ    : (ƛ e) [ σ ] ≡ ƛ (e [ (` zero) ∙ (σ ⨟ wk) ])
  Inst-ƛ {e = e} {σ = σ} = cong ƛ_ (cong (M.sub e) (funext λ { zero → refl ; (suc x) → M.ren-is-sub (σ x) suc }))
  _⟨_⟩ : Tm m → Ren m n → Tm n
  e ⟨ ρ ⟩ = M.ren e ρ
  ⌜_⌝ : Ren m n → Sub m n
  ⌜ ρ ⌝ = M.⟨ ρ ⟩
  coincidence : e ⟨ ρ ⟩ ≡ e [ ⌜ ρ ⌝ ]
  coincidence {e = e} {ρ = ρ} = M.ren-is-sub e ρ
  embed-id : ⌜ idᴿ {n} ⌝ ≡ id
  embed-id = funext λ x → refl
  embed-wk : ⌜ wkᴿ {n} ⌝ ≡ wk
  embed-wk = funext λ x → refl
  embed-↑  : ⌜ ρ ↑ᴿ ⌝ ≡ (` zero) ∙ (⌜ ρ ⌝ ⨟ wk)
  embed-↑ {ρ = ρ} = funext λ { zero → refl ; (suc x) → M.ren-is-sub (` (ρ x)) suc }
  -- the one irreducible fact: variable renaming for a GENERAL ρ (⌜ρ⌝ is opaque)
  var-ren : ∀ {x} → (` x) ⟨ ρ ⟩ ≡ ` (ρ x)
  var-ren = refl
  lift-suc : ∀ {y} → (` (suc y)) [ (` zero) ∙ (σ ⨟ wk) ] ≡ ((` y) [ σ ]) ⟨ wkᴿ ⟩
  lift-suc {σ = σ} {y = y} = sym (M.ren-is-sub (σ y) suc)
{-# REWRITE Clos IdSubst VarCons-z IdL IdR ShiftCons Map Ass IdCons SCons
            Inst-· Inst-ƛ coincidence embed-id embed-wk embed-↑ #-}


-- ============ simple types, contexts, typing ============
data Type : Set where
  ι   : Type
  _⇒_ : Type → Type → Type
infixr 5 _⇒_
variable A B C : Type

Ctx : ℕ → Set
Ctx n = Fin n → Type
_,,_ : Type → Ctx n → Ctx (suc n)
(A ,, Γ) zero = A
(A ,, Γ) (suc x) = Γ x
infixr 6 _,,_
variable Γ Δ : Ctx n

data _⊢_∶_ {n} (Γ : Ctx n) : Tm n → Type → Set where
  ⊢` : ∀ {x} → Γ ⊢ (` x) ∶ Γ x
  ⊢ƛ : ∀ {e} → (A ,, Γ) ⊢ e ∶ B → Γ ⊢ (ƛ e) ∶ (A ⇒ B)
  ⊢· : ∀ {e₁ e₂} → Γ ⊢ e₁ ∶ (A ⇒ B) → Γ ⊢ e₂ ∶ A → Γ ⊢ (e₁ · e₂) ∶ B
infix 4 _⊢_∶_

_∶_⇒ᴿ_ : Ren m n → Ctx m → Ctx n → Set
_∶_⇒ᴿ_ {m} ρ Γ Δ = ∀ (x : Fin m) → Γ x ≡ Δ (ρ x)

↑ᴿ-pres : ρ ∶ Γ ⇒ᴿ Δ → (ρ ↑ᴿ) ∶ (A ,, Γ) ⇒ᴿ (A ,, Δ)
↑ᴿ-pres ⊢ρ zero    = refl
↑ᴿ-pres ⊢ρ (suc x) = ⊢ρ x

wk-pres : ∀ (A : Type) {Δ : Ctx n} → wkᴿ ∶ Δ ⇒ᴿ (A ,, Δ)
wk-pres A x = refl

-- renaming preserves typing.  ƛ/· cases are DEFINITIONAL (the σ-rewrites + embed-↑
-- make (ƛ e)⟨ρ⟩ ≡ ƛ (e⟨ρ↑ᴿ⟩) hold by refl).  Only the variable case needs a step,
-- because (` x)⟨ρ⟩ cannot reduce for a general ρ (⌜ρ⌝ is opaque) — the price of confluence.
ren-pres : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {ρ : Ren m n} {e : Tm m} {A}
         → ρ ∶ Γ ⇒ᴿ Δ → Γ ⊢ e ∶ A → Δ ⊢ (e ⟨ ρ ⟩) ∶ A
ren-pres {Γ = Γ} {Δ = Δ} {ρ = ρ} ⊢ρ (⊢` {x = x}) =
  subst (λ t → Δ ⊢ t ∶ Γ x) (sym (var-ren {ρ = ρ} {x = x}))
        (subst (λ B → Δ ⊢ (` (ρ x)) ∶ B) (sym (⊢ρ x)) (⊢` {x = ρ x}))
ren-pres {ρ = ρ} ⊢ρ (⊢ƛ ⊢e)      = ⊢ƛ (ren-pres {ρ = ρ ↑ᴿ} (↑ᴿ-pres {ρ = ρ} ⊢ρ) ⊢e)
ren-pres {ρ = ρ} ⊢ρ (⊢· ⊢e₁ ⊢e₂) = ⊢· (ren-pres {ρ = ρ} ⊢ρ ⊢e₁) (ren-pres {ρ = ρ} ⊢ρ ⊢e₂)

_↑ˢ : Sub m n → Sub (suc m) (suc n)
σ ↑ˢ = (` zero) ∙ (σ ⨟ wk)

_∶_⇒ˢ_ : Sub m n → Ctx m → Ctx n → Set
_∶_⇒ˢ_ {m} σ Γ Δ = ∀ (x : Fin m) → Δ ⊢ ((` x) [ σ ]) ∶ Γ x

-- substitution lift preserves the morphism.  zero case definitional (VarCons-z);
-- suc case uses ren-pres (weakening) + lift-suc (suc-lookup also can't reduce: VarCons-s
-- is not a rewrite, again the price of confluence).
↑ˢ-pres : ∀ {m n} {A : Type} {Γ : Ctx m} {Δ : Ctx n} {σ : Sub m n}
        → σ ∶ Γ ⇒ˢ Δ → (σ ↑ˢ) ∶ (A ,, Γ) ⇒ˢ (A ,, Δ)
↑ˢ-pres ⊢σ zero = ⊢`
↑ˢ-pres {A = A} {Γ = Γ} {Δ = Δ} {σ = σ} ⊢σ (suc y) =
  subst (λ t → (A ,, Δ) ⊢ t ∶ Γ y) (sym (lift-suc {σ = σ} {y = y})) (ren-pres {ρ = wkᴿ} (wk-pres A) (⊢σ y))

sub-pres : σ ∶ Γ ⇒ˢ Δ → Γ ⊢ e ∶ A → Δ ⊢ (e [ σ ]) ∶ A
sub-pres ⊢σ (⊢` {x = x}) = ⊢σ x
sub-pres ⊢σ (⊢ƛ ⊢e)      = ⊢ƛ (sub-pres (↑ˢ-pres ⊢σ) ⊢e)
sub-pres ⊢σ (⊢· ⊢e₁ ⊢e₂) = ⊢· (sub-pres ⊢σ ⊢e₁) (sub-pres ⊢σ ⊢e₂)
