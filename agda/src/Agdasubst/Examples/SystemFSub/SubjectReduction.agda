-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemFSub.SubjectReduction where

open import Agdasubst.Examples.SystemFSub.Definitions.Syntax
open import Agdasubst.Examples.SystemFSub.Definitions.Typing
open import Agdasubst.Examples.SystemFSub.Definitions.Semantics
open import Agdasubst.Examples.SystemFSub.Substitution
open import Agdasubst.Examples.SystemFSub.SubstitutionPreservesTyping
open import Agdasubst.Examples.SystemFSub.Injectivity
open import Agdasubst.Examples.SystemFSub.Inversion

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

ren-pres-↪ : {e e′ : S ⊢ s′} (ρ : S →ᴿ S′) →
  e ↪ e′ →
  (e ⋯ ρ) ↪ (e′ ⋯ ρ)
ren-pres-↪ {e = e} {e′ = e′} ρ e↪e′ 
  with #e ← e ⋯ ρ in eq-e | #he′ ← e′ ⋯ ρ in eq-e′ 
  with e↪e′ | eq-e | eq-e′
... | β-λ        | refl | refl = β-λ
... | β-Λ        | refl | refl = β-Λ
... | ξ-λ e↪e′′  | refl | refl = ξ-λ (ren-pres-↪ (ρ ↑ _) e↪e′′)
... | ξ-Λ e↪e′′  | refl | refl = ξ-Λ (ren-pres-↪ (ρ ↑ _) e↪e′′)
... | ξ-·₁ e↪e′′ | refl | refl = ξ-·₁ (ren-pres-↪ ρ e↪e′′)
... | ξ-·₂ e↪e′′ | refl | refl = ξ-·₂ (ren-pres-↪ ρ e↪e′′)
... | ξ-•₁ e↪e′′ | refl | refl = ξ-•₁ (ren-pres-↪ ρ e↪e′′)

subject-reduction : 
  Valid Γ →
  Γ ⊢ e ∶ t →
  e ↪ e′ →
  Γ ⊢ e′ ∶ t
subject-reduction ⊢Γ (⊢· {e₂ = e₂} ⊢e₁ ⊢e₂)          β-λ         
  with _ , _ , t₁′⇒t₂′⊑t₁⇒t₂ , ⊢e ← invert-λ ⊢e₁
  with t₁′⊑t₁ , t₂′⊑t₂ ← invert-⊑⇒ ⊢Γ t₁′⇒t₂′⊑t₁⇒t₂
  = ⊢⊑ (_⊢⋯ˢ_ {σ = ⦅ e₂ ⦆ˢ} ⊢e ⊢⦅ ⊢⊑ ⊢e₂ t₁′⊑t₁ ⦆ˢ) t₂′⊑t₂  
subject-reduction ⊢Γ (⊢• {t = t} {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ t₁⊑t ⊢e) (β-Λ {e₁ = e₁}) 
  with _ , t₁′ , ∀[α⊑t₁′]t₂′⊑∀[α⊑t₁]t₂ , ⊢e ← invert-Λ ⊢e 
  with refl , t₂′⊑t₂ ← invert-⊑∀ ⊢Γ ∀[α⊑t₁′]t₂′⊑∀[α⊑t₁]t₂
  = ⊢⊑ (_⊢⋯ˢ_ {σ = ⦅ sat ⦆ˢ} (_⊢⋯ˢ_ {e = weaken {s′ = cstr} e₁} {t = weaken {s′ = cstr} t₁′} {σ = ⦅ t₂ ⦆ˢ ↑ cstr} ⊢e (_⊢↑_ {ϕ = ⦅ t₂ ⦆ˢ} ⊢⦅ ⊢t₂ ⦆ˢ ((` zero) ∶⊑ weaken t))) ⊢⦅ ⊢cstr t₁⊑t ⦆ˢ) (_⊑⋯_ {ϕ = ⦅ t₂ ⦆ˢ} t₂′⊑t₂ ⊢⦅ ⊢t₂ ⦆ˢ)
subject-reduction ⊢Γ (⊢λ ⊢e)               (ξ-λ e↪e')  = ⊢λ (subject-reduction (_ ∷ⱽ ⊢Γ) ⊢e e↪e')
subject-reduction ⊢Γ (⊢Λ ⊢e)               (ξ-Λ e↪e')  = ⊢Λ (subject-reduction (_ ∷ⱽ (★ ∷ⱽ ⊢Γ)) ⊢e (ren-pres-↪ wk e↪e'))
subject-reduction ⊢Γ (⊢· ⊢e₁ ⊢e₂)          (ξ-·₁ e↪e') = ⊢· (subject-reduction ⊢Γ ⊢e₁ e↪e') ⊢e₂
subject-reduction ⊢Γ (⊢· ⊢e₁ ⊢e₂)          (ξ-·₂ e↪e') = ⊢· ⊢e₁ (subject-reduction ⊢Γ ⊢e₂ e↪e')
subject-reduction ⊢Γ (⊢• ⊢t₁ ⊢t₂ t₂⊑t ⊢e)  (ξ-•₁ e↪e') = ⊢• ⊢t₁ ⊢t₂ t₂⊑t (subject-reduction ⊢Γ ⊢e e↪e')
subject-reduction ⊢Γ (⊢⊑ ⊢e t⊑t')          e↪e'        = ⊢⊑ (subject-reduction ⊢Γ  ⊢e e↪e') t⊑t' 