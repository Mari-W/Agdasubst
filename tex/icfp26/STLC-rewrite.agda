{-# OPTIONS --rewriting #-}
module STLC-rewrite where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import STLC

postulate
  _·_ : Expr Γ (T ⇒ U) → Expr Γ T → Expr Γ U
  β≡ : ∀ {Γ T U} {e₁ : Expr (Γ ▷ T) U} {e₂ : Expr Γ T} → lam e₁ · e₂ ≡ e₁ [ e₂ ]
  rf-· : ∀ {x : Γ ∋ (T ⇒ U)} {e : Expr Γ T} → var x · e ≡ app (var x) e
  ·[] : (e₁ · e₂) [ e ] ≡ (e₁ [ e ]) · (e₂ [ e ])
  app[] : (app e₁ e₂) [ e ] ≡ app (e₁ [ e ]) (e₂ [ e ])
  con[] : con [ e ] ≡ con
  var[] : var here [ e ] ≡ e

{-# REWRITE app[] con[] var[] #-}

e₀ : Expr ∅ (𝟙 ⇒ 𝟙)
e₀ = lam con

_ : app (var here) con [ e₀ ] ≡ app (lam con) con
_ = refl

{-# REWRITE ·[] β≡ #-}

_ : lam (var here · con) · e₀ ≡ con
_ = refl
