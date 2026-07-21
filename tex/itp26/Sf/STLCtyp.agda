{-# OPTIONS --rewriting --local-confluence-check #-}
module STLCtyp where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import STLCsig

_↑ˢ : ∀ {m n} → Sub m n → Sub (suc m) (suc n)
σ ↑ˢ = (` zero) ∙ (σ ⨟ wk)

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

-- pure de Bruijn membership; the variable TERM is read off via ⌊_⌋ (a neutral head)
data _∋_ : ∀ {n} → Ctx n → Type → Set where
  here  : ∀ {n}{Γ : Ctx n}{A}   → (Γ ,, A) ∋ A
  there : ∀ {n}{Γ : Ctx n}{A B} → Γ ∋ A → (Γ ,, B) ∋ A

infix 4 _∋_
⌊_⌋ : ∀ {n}{Γ : Ctx n}{A} → Γ ∋ A → Tm n
⌊ here ⌋    = ` zero
⌊ there i ⌋ = ⌊ i ⌋ [ wk ]

data _⊢_∶_ : ∀ {n} → Ctx n → Tm n → Type → Set where
  ⊢v : ∀ {n}{Γ : Ctx n}{A}        → (i : Γ ∋ A) → Γ ⊢ ⌊ i ⌋ ∶ A
  ⊢ƛ : ∀ {n}{Γ : Ctx n}{e}{A B}   → (Γ ,, A) ⊢ e ∶ B → Γ ⊢ (ƛ e) ∶ (A ⇒ B)
  ⊢· : ∀ {n}{Γ : Ctx n}{e₁ e₂}{A B} → Γ ⊢ e₁ ∶ (A ⇒ B) → Γ ⊢ e₂ ∶ A → Γ ⊢ (e₁ · e₂) ∶ B
infix 4 _⊢_∶_

lemma : ∀ {x} → ⌊ ρ x ⌋ ≡ ⌊ x ⌋ ⟨ ρ ⟩
lemma = ?
-- renaming as a STRUCTURAL membership map + a ⌊_⌋/⟨⟩ coherence (terminating)
record _∶_⇒ᴿ_ {m n} (ρ : Ren m n) (Γ : Ctx m) (Δ : Ctx n) : Set where
  field
    mapᴿ : ∀ {A} → Γ ∋ A → Δ ∋ A
    cohᴿ : ∀ {A} (i : Γ ∋ A) → ⌊ mapᴿ i ⌋ ≡ ⌊ i ⌋ ⟨ ρ ⟩
open _∶_⇒ᴿ_

wk-mor : ∀ {n}{B}{Δ : Ctx n} → wkᴿ ∶ Δ ⇒ᴿ (Δ ,, B)
mapᴿ wk-mor i     = there i
cohᴿ wk-mor i     = refl   -- ⌊ there i ⌋ = ⌊ i ⌋[wk] = ⌊ i ⌋⟨wkᴿ⟩ (coincidence+embed-wk)

↑ᴿ-pres : ∀ {m n}{A}{Γ : Ctx m}{Δ : Ctx n}{ρ : Ren m n} → ρ ∶ Γ ⇒ᴿ Δ → (ρ ↑ᴿ) ∶ (Γ ,, A) ⇒ᴿ (Δ ,, A)
mapᴿ (↑ᴿ-pres ⊢ρ) here      = here
mapᴿ (↑ᴿ-pres ⊢ρ) (there i) = there (mapᴿ ⊢ρ i)
cohᴿ (↑ᴿ-pres ⊢ρ) here      = refl
cohᴿ (↑ᴿ-pres ⊢ρ) (there i) = cong (_[ wk ]) (cohᴿ ⊢ρ i)

ren-pres : ∀ {m n}{Γ : Ctx m}{Δ : Ctx n}{ρ : Ren m n}{e}{A} → ρ ∶ Γ ⇒ᴿ Δ → Γ ⊢ e ∶ A → Δ ⊢ (e ⟨ ρ ⟩) ∶ A
ren-pres ⊢ρ (⊢v i)     = subst (λ t → _ ⊢ t ∶ _) (cohᴿ ⊢ρ i) (⊢v (mapᴿ ⊢ρ i))
ren-pres ⊢ρ (⊢ƛ ⊢e)    = ⊢ƛ (ren-pres (↑ᴿ-pres ⊢ρ) ⊢e)
ren-pres ⊢ρ (⊢· ⊢a ⊢b) = ⊢· (ren-pres ⊢ρ ⊢a) (ren-pres ⊢ρ ⊢b)

-- substitution preserves typing
_∶_⇒ˢ_ : ∀ {m n} → Sub m n → Ctx m → Ctx n → Set
_∶_⇒ˢ_ σ Γ Δ = ∀ {A} → (i : Γ ∋ A) → Δ ⊢ (⌊ i ⌋ [ σ ]) ∶ A

↑ˢ-pres : ∀ {m n}{A}{Γ : Ctx m}{Δ : Ctx n}{σ : Sub m n} → σ ∶ Γ ⇒ˢ Δ → (σ ↑ˢ) ∶ (Γ ,, A) ⇒ˢ (Δ ,, A)
↑ˢ-pres ⊢σ here      = ⊢v here
↑ˢ-pres ⊢σ (there i) = ren-pres wk-mor (⊢σ i)
sub-pres : ∀ {m n}{Γ : Ctx m}{Δ : Ctx n}{σ : Sub m n}{e}{A} → σ ∶ Γ ⇒ˢ Δ → Γ ⊢ e ∶ A → Δ ⊢ (e [ σ ]) ∶ A
sub-pres ⊢σ (⊢v i)     = ⊢σ i
sub-pres {σ = σ} ⊢σ (⊢ƛ ⊢e) = ⊢ƛ (sub-pres {σ = σ ↑ˢ} (↑ˢ-pres {σ = σ} ⊢σ) ⊢e)
sub-pres ⊢σ (⊢· ⊢a ⊢b) = ⊢· (sub-pres ⊢σ ⊢a) (sub-pres ⊢σ ⊢b)
