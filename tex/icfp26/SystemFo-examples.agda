{-# OPTIONS --rewriting --local-confluence-check #-}
module SystemFo-examples where
open import Agda.Builtin.Equality.Rewrite public

-- standard eq reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)

open import SystemFo

{-# REWRITE β≡* #-}

ℕᵏ : Kind
ℕᵏ = (∗ ⇒ ∗) ⇒ (∗ ⇒ ∗)

zeroᵏ : Type ∅ ℕᵏ
zeroᵏ = λα (λα (` Z))

succᵏ : Type ∅ (ℕᵏ ⇒ ℕᵏ)
succᵏ = λα (λα (λα ((` S Z) $ (((` S (S Z)) $ (` S Z)) $ (` Z)))))

oneᵏ : Type ∅ ℕᵏ
oneᵏ = λα (λα ((` S Z) $ (` Z)))

_ : succᵏ $ zeroᵏ ≡ oneᵏ
_ = begin
      (succᵏ $ zeroᵏ)
    ≡⟨ refl ⟩
      (λα (λα (λα ((` S Z) $ (((` S (S Z)) $ (` S Z)) $ (` Z))))) $ zeroᵏ)
    ≡⟨ refl ⟩
      ((λα (λα ((` S Z) $ (((` S (S Z)) $ (` S Z)) $ (` Z))))) [ zeroᵏ ]*)
    ≡⟨ refl ⟩
      ( (λα (λα ((` S Z) $ (((` S (S Z)) $ (` S Z)) $ (` Z))))) ⋯ˢ ( zeroᵏ ∙ ⟨ id ⟩) )
    ≡⟨ refl ⟩
      ( (λα (λα ((` S Z) $ (((` S (S Z)) $ (` S Z)) $ (` Z)))  ⋯ˢ (↑ˢ ( zeroᵏ ∙ ⟨ id ⟩)) )) )
    ≡⟨ refl ⟩
      λα (λα ((` S Z) $ (` Z)))
    ∎

twoᵏ : Type ∅ ℕᵏ
twoᵏ = succᵏ $ (succᵏ $ zeroᵏ)

_ : twoᵏ ≡ λα (λα ((` S Z) $ ((` S Z) $ (` Z))))
_ = begin
      twoᵏ
    ≡⟨ refl ⟩
      succᵏ $ (succᵏ $ zeroᵏ)
    ≡⟨ refl ⟩
      λα (λα ((` S Z) $ ((` S Z) $ (` Z))))
    ∎

-- this gets *real* slow

addᵏ : Type ∅ (ℕᵏ ⇒ (ℕᵏ ⇒ ℕᵏ))
addᵏ = λα (λα (λα (λα (((` S (S (S Z))) $ (` S Z)) $ (((` S (S Z)) $ (` S Z)) $ (` Z))))))

_ : twoᵏ ≡ (addᵏ $ oneᵏ) $ oneᵏ
_ = refl
