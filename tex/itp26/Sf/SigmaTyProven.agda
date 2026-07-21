-- Genuinely PROVEN σ-laws for System F types: substitutions are real functions,
-- _[_] is DEFINED by structural recursion (renamings-first solves the ∀-lift
-- termination), and the σ-laws are THEOREMS (no postulates except funext).
module SigmaTyProven where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate funext : ∀ {a b} → Extensionality a b

variable l m n k : ℕ

data Ty (n : ℕ) : Set where
  `_  : Fin n → Ty n
  _⇒_ : Ty n → Ty n → Ty n
  ∀'_ : Ty (suc n) → Ty n

------------------------------------------------------------------------
-- Renamings (Fin → Fin): structural, terminate trivially
Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

_↑ᴿ : Ren m n → Ren (suc m) (suc n)
(ρ ↑ᴿ) zero    = zero
(ρ ↑ᴿ) (suc x) = suc (ρ x)

ren : Ty m → Ren m n → Ty n
ren (` x)   ρ = ` (ρ x)
ren (A ⇒ B) ρ = ren A ρ ⇒ ren B ρ
ren (∀' A)  ρ = ∀' (ren A (ρ ↑ᴿ))

------------------------------------------------------------------------
-- Substitutions (Fin → Ty): the lift uses RENAMING for weakening (key!)
Sub : ℕ → ℕ → Set
Sub m n = Fin m → Ty n

_↑ˢ : Sub m n → Sub (suc m) (suc n)
(σ ↑ˢ) zero    = ` zero
(σ ↑ˢ) (suc x) = ren (σ x) suc      -- weaken by the renaming `suc`, not by sub-composition

sub : Ty m → Sub m n → Ty n
sub (` x)   σ = σ x
sub (A ⇒ B) σ = sub A σ ⇒ sub B σ
sub (∀' A)  σ = ∀' (sub A (σ ↑ˢ))

idˢ : Sub n n
idˢ = `_

_⨟_ : Sub m k → Sub k n → Sub m n
(σ ⨟ τ) x = sub (σ x) τ

------------------------------------------------------------------------
-- Fusion lemmas (the Autosubst lemmas), all by structural induction + funext
↑ᴿ∘↑ᴿ : (ρ₁ : Ren m k)(ρ₂ : Ren k n) → (λ x → (ρ₂ ↑ᴿ) ((ρ₁ ↑ᴿ) x)) ≡ ((λ x → ρ₂ (ρ₁ x)) ↑ᴿ)
↑ᴿ∘↑ᴿ ρ₁ ρ₂ = funext λ { zero → refl ; (suc x) → refl }

ren-ren : (A : Ty m)(ρ₁ : Ren m k)(ρ₂ : Ren k n) → ren (ren A ρ₁) ρ₂ ≡ ren A (λ x → ρ₂ (ρ₁ x))
ren-ren (` x)   ρ₁ ρ₂ = refl
ren-ren (A ⇒ B) ρ₁ ρ₂ = cong₂ _⇒_ (ren-ren A ρ₁ ρ₂) (ren-ren B ρ₁ ρ₂)
ren-ren (∀' A)  ρ₁ ρ₂ = cong ∀'_ (trans (ren-ren A (ρ₁ ↑ᴿ) (ρ₂ ↑ᴿ)) (cong (ren A) (↑ᴿ∘↑ᴿ ρ₁ ρ₂)))

↑ˢ∘↑ᴿ : (σ : Sub k n)(ρ : Ren m k) → (λ x → (σ ↑ˢ) ((ρ ↑ᴿ) x)) ≡ ((λ x → σ (ρ x)) ↑ˢ)
↑ˢ∘↑ᴿ σ ρ = funext λ { zero → refl ; (suc x) → refl }

sub-ren : (A : Ty m)(ρ : Ren m k)(σ : Sub k n) → sub (ren A ρ) σ ≡ sub A (λ x → σ (ρ x))
sub-ren (` x)   ρ σ = refl
sub-ren (A ⇒ B) ρ σ = cong₂ _⇒_ (sub-ren A ρ σ) (sub-ren B ρ σ)
sub-ren (∀' A)  ρ σ = cong ∀'_ (trans (sub-ren A (ρ ↑ᴿ) (σ ↑ˢ)) (cong (sub A) (↑ˢ∘↑ᴿ σ ρ)))

ren∘↑ˢ : (σ : Sub m k)(ρ : Ren k n) → (λ x → ren ((σ ↑ˢ) x) (ρ ↑ᴿ)) ≡ ((λ x → ren (σ x) ρ) ↑ˢ)
ren∘↑ˢ σ ρ = funext λ { zero → refl
                      ; (suc x) → trans (ren-ren (σ x) suc (ρ ↑ᴿ)) (sym (ren-ren (σ x) ρ suc)) }

ren-sub : (A : Ty m)(σ : Sub m k)(ρ : Ren k n) → ren (sub A σ) ρ ≡ sub A (λ x → ren (σ x) ρ)
ren-sub (` x)   σ ρ = refl
ren-sub (A ⇒ B) σ ρ = cong₂ _⇒_ (ren-sub A σ ρ) (ren-sub B σ ρ)
ren-sub (∀' A)  σ ρ = cong ∀'_ (trans (ren-sub A (σ ↑ˢ) (ρ ↑ᴿ)) (cong (sub A) (ren∘↑ˢ σ ρ)))

⨟∘↑ˢ : (σ : Sub m k)(τ : Sub k n) → (λ x → sub ((σ ↑ˢ) x) (τ ↑ˢ)) ≡ ((λ x → sub (σ x) τ) ↑ˢ)
⨟∘↑ˢ σ τ = funext λ { zero → refl
                    ; (suc x) → trans (sub-ren (σ x) suc (τ ↑ˢ)) (sym (ren-sub (σ x) τ suc)) }

------------------------------------------------------------------------
-- THE σ-LAWS, as THEOREMS (no postulates beyond funext)

-- compositionality / closure  (Clos):  the headline law
compositionality : (A : Ty m)(σ : Sub m k)(τ : Sub k n) → sub (sub A σ) τ ≡ sub A (σ ⨟ τ)
compositionality (` x)   σ τ = refl
compositionality (A ⇒ B) σ τ = cong₂ _⇒_ (compositionality A σ τ) (compositionality B σ τ)
compositionality (∀' A)  σ τ = cong ∀'_ (trans (compositionality A (σ ↑ˢ) (τ ↑ˢ)) (cong (sub A) (⨟∘↑ˢ σ τ)))

idˢ↑ˢ : (λ x → (idˢ {n} ↑ˢ) x) ≡ idˢ {suc n}
idˢ↑ˢ = funext λ { zero → refl ; (suc x) → refl }

sub-id : (A : Ty n) → sub A idˢ ≡ A
sub-id (` x)   = refl
sub-id (A ⇒ B) = cong₂ _⇒_ (sub-id A) (sub-id B)
sub-id (∀' A)  = cong ∀'_ (trans (cong (sub A) idˢ↑ˢ) (sub-id A))

comp-idₗ : (σ : Sub m n) → idˢ ⨟ σ ≡ σ
comp-idₗ σ = refl                                   -- definitional!

comp-idᵣ : (σ : Sub m n) → σ ⨟ idˢ ≡ σ
comp-idᵣ σ = funext λ x → sub-id (σ x)

assoc : (σ : Sub l m)(τ : Sub m k)(υ : Sub k n) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
assoc σ τ υ = funext λ x → compositionality (σ x) τ υ

-- cons & the η / surjective-pairing law
_∙_ : Ty n → Sub m n → Sub (suc m) n
(A ∙ σ) zero    = A
(A ∙ σ) (suc x) = σ x
wkˢ : Sub n (suc n)
wkˢ x = ` (suc x)

η-law : (σ : Sub (suc m) n) → ((σ zero) ∙ (wkˢ ⨟ σ)) ≡ σ
η-law σ = funext λ { zero → refl ; (suc x) → refl }

-- the critical-pair WITNESS that was non-confluent — here it's just a theorem:
witness : (σ : Sub (suc m) k)(τ : Sub k n) → ((σ zero) ∙ (wkˢ ⨟ σ)) ⨟ τ ≡ σ ⨟ τ
witness σ τ = funext λ { zero → refl ; (suc x) → refl }
