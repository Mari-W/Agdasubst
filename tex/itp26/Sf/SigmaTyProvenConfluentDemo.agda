{-# OPTIONS --rewriting --local-confluence-check #-}
module SigmaTyProvenConfluentDemo where
open import SigmaTyProvenConfluent
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- the renaming laws you need (renaming preserves typing etc.) hold BY REFL,
-- derived through the confluent substitution layer:
module _ {l m k n : ℕ} (A B : Ty m) (ρ : Ren m k) (ρ′ : Ren k n) (σ : Sub k n) where
  ren-comp : (A ⟨ ρ ⟩) ⟨ ρ′ ⟩ ≡ A ⟨ ρ ∘ ρ′ ⟩            -- renaming compositionality
  ren-comp = refl
  ren-idn  : A ⟨ idᴿ ⟩ ≡ A                                -- renaming identity
  ren-idn  = refl
  ren-arr  : (A ⇒ B) ⟨ ρ ⟩ ≡ (A ⟨ ρ ⟩) ⇒ (B ⟨ ρ ⟩)       -- traversal (⇒)
  ren-arr  = refl
  ren-sub  : (A ⟨ ρ ⟩) [ σ ] ≡ A [ ⌜ ρ ⌝ ⨟ σ ]           -- renaming-then-substitution
  ren-sub  = refl

module _ {m n : ℕ} (A : Ty (suc m)) (ρ : Ren m n) where
  ren-all  : (∀' A) ⟨ ρ ⟩ ≡ ∀' (A ⟨ zero ∙ᴿ (ρ ∘ wkᴿ) ⟩)  -- traversal (∀, lift)
  ren-all  = refl
