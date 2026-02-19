{-# OPTIONS --rewriting --local-confluence-check #-}
module SystemFo-examples where
open import Agda.Builtin.Equality.Rewrite public

-- standard eq reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning

-- open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)

open import SystemFo

{-# REWRITE β≡* #-}

-- readability
∀β ∀κ : Type (Φ ,* J) ∗ → Type Φ ∗
∀β = ∀α
∀κ = ∀α

λβ λγ : Type (Φ ,* J) K → Type Φ (J ⇒ K)
λβ = λα
λγ = λα

λf λg λz λy : Expr (Γ , T₁) T₂ → Expr Γ (T₁ ⇒ T₂)
λf = λx
λg = λx
λz = λx
λy = λx

`α : Type (Φ ,* K) K
`α = ` Z
`β : Type ((Φ ,* K) ,* J) K
`β = ` (S Z)
`κ `γ : Type (((Φ ,* K) ,* I) ,* J) K
`κ = ` (S (S Z))
`γ = `κ

Λκ Λβ : Expr (Γ ,*) T → Expr Γ (∀α T)
Λκ = Λα
Λβ = Λα

`x : Expr (Γ , T) T
`x = ` Z
`y `g : Expr ((Γ , T) , T₁) T
`y = ` (S Z)
`g = ` (S Z)
`z `f : Expr (((Γ , T) , T₂) , T₁) T
`z = ` (S (S Z))
`f = `z

-- abstracting over a type constructor

--! FOPrelude
arrow-app : (κ : Set → Set → Set) (β α : Set) → (app : κ β α → β → α) → κ β α → β → α
arrow-app = λ κ β α → λ app f x → app f x

Funᵏ : Kind
Funᵏ = ∗ ⇒ (∗ ⇒ ∗)

--! FOTyApp
ty-app : Type Φ ∗
ty-app = ∀κ (∀β (∀α ((((`κ $ `β) $ `α) ⇒ (`β ⇒ `α))
                   ⇒ (((`κ $ `β) $ `α) ⇒ (`β ⇒ `α)))))

--! FOAbstApp
abst-app : Expr Γ ty-app
abst-app = Λκ (Λβ (Λα (λf (λy (λx ((`f · `y) · `x))))))

--! FOInstApp
inst-app : Expr Γ (∀α (ty-app ⇒ (`α ⇒ `α)))
inst-app = Λα (λg (λx ((((((`g • (λβ (λα (`β ⇒ `α)))) • `α) • `α)
                                    · (λy (λx (`y · `x))))
                                    · (λx `x))
                                    · `x)))

--! FOUseApp
use-app : Expr ∅ (∀α (`α ⇒ `α))
use-app = Λα (λx (((inst-app • `α) · abst-app) · `x))

-- type level Church numerals

--! CNKind
ℕᵏ : Kind
ℕᵏ = (∗ ⇒ ∗) ⇒ (∗ ⇒ ∗)

--! CNZeroSucc {
zeroᵏ : Type ∅ ℕᵏ
zeroᵏ = λβ (λα `α)

succᵏ : Type ∅ (ℕᵏ ⇒ ℕᵏ)
succᵏ = λγ (λβ (λα (`β $ ((`γ $ `β) $ `α))))
--! }

--! CNTwoProof {
twoᵏ : Type ∅ ℕᵏ
twoᵏ = succᵏ $ (succᵏ $ zeroᵏ)

_ : twoᵏ ≡ λβ (λα (`β $ (`β $ `α)))
_ = refl
--! }

-- this gets *real* slow

--! CNAddition {
oneᵏ : Type ∅ ℕᵏ
oneᵏ = λβ (λα (`β $ `α))

addᵏ : Type ∅ (ℕᵏ ⇒ (ℕᵏ ⇒ ℕᵏ))
addᵏ = λα (λα (λα (λα (((` S (S (S Z))) $ (` S Z)) $ (((` S (S Z)) $ (` S Z)) $ (` Z))))))

_ : twoᵏ ≡ (addᵏ $ oneᵏ) $ oneᵏ
_ = refl
--! }

--! CNOneProof {
_ : succᵏ $ zeroᵏ ≡ oneᵏ
_ = refl
--! }
