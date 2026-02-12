-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemFSub.Inversion where

open import Agdasubst.Examples.SystemFSub.Definitions.Syntax 
open import Agdasubst.Examples.SystemFSub.Definitions.Typing 
open import Agdasubst.Examples.SystemFSub.Definitions.Semantics
open import Agdasubst.Examples.SystemFSub.Substitution
open import Agdasubst.Examples.SystemFSub.Injectivity
-- open import Agdasubst.Examples.SystemFSub.SubstitutionPreservesTyping

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using () renaming (_∋_ to _by_)

Valid : Ctx S → Set
Valid {S} Γ =
  ∀ (x : S ∋ cstr) {t₁ t₂} →
  Γ ∋ x ∶ (t₁ ∶⊑ t₂) →
  ∃[ y ] t₁ ≡ ` y

∶⊑-wk : ∀ {t₁ t₂ : (s ∷ S) ⊢ type} (t : S ⊢ cind) →
  (t₁ ∶⊑ t₂) ≡ (((s ∷ S) ⊢ cind) by (t &/⋯ wk)) →
  Σ[ t₁′ ∈ S ⊢ type ] Σ[ t₂′ ∈ S ⊢ type ] t₁ ≡ t₁′ &/⋯ wk × t₂ ≡ t₂′ &/⋯ wk
∶⊑-wk (t₁′ ∶⊑ t₂′) refl = t₁′ , t₂′ , refl , refl 

data Valid-Type {S} : S ⊢ s → Set where
  instance Valid-type : ∀ {t : S ⊢ type} → Valid-Type t
  instance Valid-kind : ∀ {k : S ⊢ kind} → Valid-Type k
  instance Valid-cstr : ∀ {α : S ∋ type} {t : S ⊢ type} → Valid-Type ((` α) ∶⊑ t)

_∷ⱽ_ : ∀ {Γ : Ctx S} →
  (t : S ∶⊢ s) →
  Valid Γ →
  {{_ : Valid-Type t}} →
  Valid (t ∷ₜ Γ) 
(_ ∷ⱽ ⊢Γ) {{Valid-cstr}} zero ∋x = suc _ , sym (proj₁ (∶⊑-injective ∋x))   
_∷ⱽ_  {Γ = Γ} _ ⊢Γ       (suc x) ∋x 
  with t₁ , t₂ , refl , refl ← ∶⊑-wk (lookup Γ x) (sym ∋x)
  with x′ , refl ← ⊢Γ x (⋯-injective wk-injective (lookup Γ x) (t₁ ∶⊑ t₂) ∋x)
  = suc x′ , refl

invert-λ : {Γ : Ctx S} →
  Γ ⊢ λx e ∶ t →
  ∃[ t₁ ] ∃[ t₂ ]
    Γ ⊢ (t₁ ⇒ t₂) ⊑ t ×
    (t₁ ∷ₜ Γ) ⊢ e ∶ (t₂ &/⋯ wk)
invert-λ (⊢λ ⊢e) = _ , _ , ⊑-refl , ⊢e
invert-λ (⊢⊑ ⊢e t₃⊑t) with invert-λ ⊢e
... | t₁ , t₂ , [t₁⇒t₂]⊑t₃ , ⊢e = _ , _ , ⊑-trans [t₁⇒t₂]⊑t₃ t₃⊑t , ⊢e

invert-Λ : {Γ : Ctx S} →
  Γ ⊢ Λα e ∶ t →
  ∃[ t₁ ] ∃[ t₂ ]
    (Γ ⊢ (∀[α⊑ t₁ ] t₂) ⊑ t) ×
    ((((` zero) ∶⊑ (t₁ &/⋯ wk)) ∷ₜ (★ ∷ₜ Γ)) ⊢ (e &/⋯ wk {s = cstr}) ∶ (t₂ &/⋯ wk))
invert-Λ (⊢Λ ⊢e) = _ , _ , ⊑-refl , ⊢e
invert-Λ (⊢⊑ ⊢e t₃⊑t) with invert-Λ ⊢e
... | t₁ , t₂ , [t₁⇒t₂]⊑t₃ , ⊢e = _ , _ , ⊑-trans [t₁⇒t₂]⊑t₃ t₃⊑t , ⊢e

-- This is the key for getting the inversion lemmas to work:
-- By requiring `Valid Γ` we know that a subtype of a type variable
-- has to be also a type variable, so it cannot be a ∀- or ⇒-type.
invert-⊑` : ∀ {Γ : Ctx S} {α : S ∋ type} →
  Valid Γ →
  Γ ⊢ t ⊑ (` α) →
  ∃[ β ] t ≡ ` β
invert-⊑` ⊢Γ ⊑-refl-var = _ , refl
invert-⊑` ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr t₁⊑t₂) st₂)
 with invert-⊑` ⊢Γ st₂
... | β₁ , refl
 with invert-⊑` ⊢Γ t₁⊑t₂
... | β₂ , refl
 with invert-⊑` ⊢Γ st₁
... | β₃ , refl
 = β₃ , refl
invert-⊑` ⊢Γ (⊑-` {c = ` c} st₁ (⊢` ∋c) st₂)
 with ⊢Γ c ∋c
... | y , refl
 with invert-⊑` ⊢Γ st₁
... | β₂ , refl
 = β₂ , refl

invert-⊑⇒′ : {Γ : Ctx S} →
  Valid Γ →
  Γ ⊢ t ⊑ (t₁′ ⇒ t₂′) →
  (∃[ t₁ ] ∃[ t₂ ] t ≡ t₁ ⇒ t₂ × Γ ⊢ t₁′ ⊑ t₁ × Γ ⊢ t₂ ⊑ t₂′) ⊎ (∃[ α ] t ≡ ` α)
invert-⊑⇒′ ⊢Γ (⊑-` {c = ` c} st₁ (⊢` ∋c) st₂) with ⊢Γ c ∋c
invert-⊑⇒′ ⊢Γ (⊑-` {c = ` c} st₁ (⊢` ∋c) st₂) | α , refl = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑⇒′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) with invert-⊑⇒′ ⊢Γ st₃
invert-⊑⇒′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₂ (α , refl) with invert-⊑` ⊢Γ st₂
invert-⊑⇒′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₂ (α , refl) | β , refl = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑⇒′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , t₁′⊑t₁ , t₂⊑t₂′) with invert-⊑⇒′ ⊢Γ st₂
invert-⊑⇒′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , t₁′⊑t₁ , t₂⊑t₂′) | inj₂ (α , refl) = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑⇒′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , t₁′⊑t₁ , t₂⊑t₂′) | inj₁ (t₁x , t₂x , refl , t₁⊑t₁x , t₂x⊑t₂) with invert-⊑⇒′ ⊢Γ st₁
invert-⊑⇒′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , t₁′⊑t₁ , t₂⊑t₂′) | inj₁ (t₁x , t₂x , refl , t₁⊑t₁x , t₂x⊑t₂) | inj₂ (α , refl) = inj₂ (α , refl)
invert-⊑⇒′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , t₁′⊑t₁ , t₂⊑t₂′) | inj₁ (t₁x , t₂x , refl , t₁⊑t₁x , t₂x⊑t₂) | inj₁ (t₁y , t₂y , refl , t₁x⊑t₁y , t₂y⊑t₂x) = inj₁ (_ , _ , refl , ⊑-trans t₁′⊑t₁ (⊑-trans t₁⊑t₁x t₁x⊑t₁y) , ⊑-trans t₂y⊑t₂x (⊑-trans t₂x⊑t₂ t₂⊑t₂′))
invert-⊑⇒′ ⊢Γ (⊑-⇒ st₁ st₂) = inj₁ (_ , _ , refl , st₁ , st₂) 

invert-⊑⇒ : {Γ : Ctx S} →
  Valid Γ →
  Γ ⊢ (t₁ ⇒ t₂) ⊑ (t₁′ ⇒ t₂′) →
  Γ ⊢ t₁′ ⊑ t₁ × Γ ⊢ t₂ ⊑ t₂′
invert-⊑⇒ ⊢Γ st with invert-⊑⇒′ ⊢Γ st
... | inj₁ (_ , _ , refl , st₁ , st₂) = st₁ , st₂

invert-⊑∀′ : {Γ : Ctx S} {t₁′ : S ⊢ type} {t₂′ : (type ∷ S) ⊢ type} →
  Valid Γ →
  Γ ⊢ t ⊑ (∀[α⊑ t₁′ ] t₂′) →
  (∃[ t₁ ] ∃[ t₂ ] t ≡ (∀[α⊑ t₁ ] t₂) × t₁ ≡ t₁′ × (★ ∷ₜ Γ) ⊢ t₂ ⊑ t₂′) ⊎ (∃[ α ] t ≡ ` α)
invert-⊑∀′ ⊢Γ (⊑-` {c = ` c} st₁ (⊢` ∋c) st₂) with ⊢Γ c ∋c
invert-⊑∀′ ⊢Γ (⊑-` {c = ` c} st₁ (⊢` ∋c) st₂) | α , refl = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑∀′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) with invert-⊑∀′ ⊢Γ st₃
invert-⊑∀′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₂ (α , refl) with invert-⊑` ⊢Γ st₂
invert-⊑∀′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₂ (α , refl) | β , refl = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑∀′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , refl , t₂⊑t₂′) with invert-⊑∀′ ⊢Γ st₂
invert-⊑∀′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , refl , t₂⊑t₂′) | inj₂ (α , refl) = inj₂ (invert-⊑` ⊢Γ st₁)
invert-⊑∀′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , refl , t₂⊑t₂′) | inj₁ (t₁x , t₂x , refl , refl , t₂x⊑t₂) with invert-⊑∀′ ⊢Γ st₁
invert-⊑∀′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , refl , t₂⊑t₂′) | inj₁ (t₁x , t₂x , refl , refl , t₂x⊑t₂) | inj₂ (α , refl) = inj₂ (α , refl)
invert-⊑∀′ ⊢Γ (⊑-` {c = sat} st₁ (⊢cstr st₂) st₃) | inj₁ (t₁ , t₂ , refl , refl , t₂⊑t₂′) | inj₁ (t₁x , t₂x , refl , refl , t₂x⊑t₂) | inj₁ (t₁y , t₂y , refl , refl , t₂y⊑t₂x) = inj₁ (_ , _ , refl , refl , ⊑-trans t₂y⊑t₂x (⊑-trans t₂x⊑t₂ t₂⊑t₂′))
invert-⊑∀′ ⊢Γ (⊑-∀ st) = inj₁ (_ , _ , refl , refl , st)

invert-⊑∀ : {Γ : Ctx S} {t₁ t₁′ : S ⊢ type} {t₂ t₂′ : (type ∷ S) ⊢ type} →
  Valid Γ →
  Γ ⊢ (∀[α⊑ t₁ ] t₂) ⊑ (∀[α⊑ t₁′ ] t₂′) →
  t₁ ≡ t₁′ × (★ ∷ₜ Γ) ⊢ t₂ ⊑ t₂′
invert-⊑∀ ⊢Γ st with invert-⊑∀′ ⊢Γ st
... | inj₁ (_ , _ , refl , refl , st) = refl , st
