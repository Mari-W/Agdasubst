{-# OPTIONS --rewriting --local-confluence-check #-}
module SystemFo-examples where
open import Agda.Builtin.Equality.Rewrite public

-- standard eq reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning

open import SystemFo

--! FORewrite
{-# REWRITE β≡* #-}


-- abstracting over a type constructor

module example-in-agda where
  --! FOPrelude {
  ty : Set₁
  ty = (κ : Set → Set → Set) (β α : Set) (app : κ β α → β → α) (f : κ β α) (x : β) → α

  abst : ty
  abst = λ κ β α → λ app f x → app f x

  inst : ∀ α → ty → α → α
  inst = λ α g x → g (λ β α → (β → α)) α α (λ f x → f x) (λ z → z) x

  use : ∀ α → α → α
  use = λ α x → inst α abst x
  --! }

Funᵏ : Kind
Funᵏ = ∗ ⇒ (∗ ⇒ ∗)

--! FOTyApp
ty-enc : Type Φ ∗
ty-enc = ∀κ (∀β (∀α ((((`κ $ `β) $ `α) ⇒ (`β ⇒ `α))
                   ⇒ (((`κ $ `β) $ `α) ⇒ (`β ⇒ `α)))))

--! FOAbstApp
abst-enc : Expr Γ ty-enc
abst-enc = Λκ (Λβ (Λα (λf (λy (λx ((`f · `y) · `x))))))

--! FOInstApp
inst-enc : Expr Γ (∀α (ty-enc ⇒ (`α ⇒ `α)))
inst-enc = Λα (λg (λx ((((((`g  • (λβ (λα (`β ⇒ `α)))) • `α) • `α)
                                · (λy (λx (`y · `x))))
                                · (λx `x))
                                · `x)))

--! FOUseApp
use-enc : Expr ∅ (∀α (`α ⇒ `α))
use-enc = Λα (λx (((inst-enc • `α) · abst-enc) · `x))

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
