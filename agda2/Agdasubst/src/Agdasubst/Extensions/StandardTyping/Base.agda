-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances --no-fast-reduce #-}
module Agdasubst.Extensions.StandardTyping.Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (drop)
open import Data.Product using (∃-syntax; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Agdasubst.Common
open import Agdasubst.Lib
open import Agdasubst.Extensions.Common

module _ {{library : Library}} where 
  open Library library
  open CommonWithSort Sort
  open Meta
  open KitsWithSort Sort
 
  opaque
    unfolding lib 

    wk-cancels-⦅⦆ :
      ∀ {{K : Kit k}} (q : S ∋/⊢[ K ] s) →
      (wkᴿ {s = s} ; ⦅ q ⦆) ~ id
    wk-cancels-⦅⦆ {{K}} q sx x = `/id-injective (
        `/id {{K}} (x & (wkᴿ ; ⦅ q ⦆))  ≡⟨⟩
        `/id {{K}} (id/` (suc x) &/⋯ ⦅ q ⦆)   ≡⟨ &/⋯-& {{Cᴿ {{K}}}} (suc x) ⦅ q ⦆ ⟩
        `/id {{K}} (id/` x)                  ≡⟨⟩
        `/id {{K}} (x & id)                  ∎)

    wk-cancels-⦅⦆-⋯ :
      ∀ {{K : Kit k}} (t : S ⊢ s′) (q : S ∋/⊢[ K ] s) →
      t ⋯ wkᴿ {s = s} ⋯ ⦅ q ⦆ ≡ t
    wk-cancels-⦅⦆-⋯ t q =
      t ⋯ wkᴿ ⋯ ⦅ q ⦆   ≡⟨ ⋯-compositionality t wkᴿ ⦅ q ⦆ ⟩
      t ⋯ (wkᴿ ; ⦅ q ⦆) ≡⟨ cong (t ⋯_) (~-ext (wk-cancels-⦅⦆ q)) ⟩
      t ⋯ id             ≡⟨ ⋯-id t ⟩
      t                  ∎

    dist-↑-⦅⦆ :
      ∀  {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K : Kit k}}
         {{C₁ : ComposeKit K₁ K₂ K}} {{C₂ : ComposeKit K₂ K K}}
         (q : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
      (⦅ q ⦆ ; ϕ) ~ ((ϕ ↑ᴷ s) ; ⦅ (q &/⋯ ϕ) ⦆)
    dist-↑-⦅⦆ {s = s} {{K₁}} {{K₂}} {{K}} {{C₁}} {{C₂}} q ϕ sx x@zero = `/id-injective (
        `/id {{K}} (x & (⦅ q ⦆ ; ϕ))                     ≡⟨⟩
        `/id {{K}} (q &/⋯ ϕ)                            ≡⟨⟩
        `/id {{K}} (zero & ⦅ (q &/⋯ ϕ) ⦆)                ≡⟨ sym (&/⋯-& {{C₂}} zero ⦅ (q &/⋯ ϕ) ⦆) ⟩
        `/id {{K}} (id/` {{K₂}} zero &/⋯ ⦅ (q &/⋯ ϕ) ⦆) ≡⟨⟩
        `/id {{K}} (x & ((ϕ ↑ᴷ s) ; ⦅ (q &/⋯ ϕ) ⦆))      ∎)
    dist-↑-⦅⦆ {s = s} {{K₁}} {{K₂}} {{K}} {{C₁}} {{C₂}} q ϕ sx x@(suc y) = `/id-injective ( 
        `/id (x & (⦅ q ⦆ ; ϕ))                     ≡⟨⟩
        `/id (id/` {{K₁}} y &/⋯ ϕ)                 ≡⟨ &/⋯-& {{C₁}} y ϕ ⟩
        `/id (y & ϕ)                                ≡⟨ sym (wk-cancels-⦅⦆-⋯ (`/id (y & ϕ)) (q &/⋯ ϕ)) ⟩
        `/id (y & ϕ) ⋯ wkᴿ {s = s} ⋯ ⦅ (q &/⋯ ϕ) ⦆ ≡⟨ cong (_⋯ ⦅ q &/⋯ ϕ ⦆) (wk-`/id s (y & ϕ)) ⟩
        `/id (K-wk s (y & ϕ)) ⋯ ⦅ (q &/⋯ ϕ) ⦆       ≡⟨ &/⋯-⋯ (K-wk s (y & ϕ)) ⦅ (q &/⋯ ϕ) ⦆ ⟩
        `/id (K-wk s (y & ϕ) &/⋯ ⦅ (q &/⋯ ϕ) ⦆)     ≡⟨⟩
        `/id (x & ((ϕ ↑ᴷ s) ; ⦅ (q &/⋯ ϕ) ⦆))      ∎)

    dist-↑-⦅⦆-⋯ :
      ∀  {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K : Kit k}} 
         {{C₁ : ComposeKit K₁ K₂ K}} {{C₂ : ComposeKit K₂ K K}}
         (t : (s ∷ S₁) ⊢ s′) (q : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
      t ⋯ ⦅ q ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ᴷ s) ⋯ ⦅ (q &/⋯ ϕ) ⦆
    dist-↑-⦅⦆-⋯ t q ϕ =
      t ⋯ ⦅ q ⦆ ⋯ ϕ                  ≡⟨ ⋯-compositionality t ⦅ q ⦆ ϕ ⟩
      t ⋯ (⦅ q ⦆ ; ϕ)                ≡⟨ cong (t ⋯_) (~-ext (dist-↑-⦅⦆ q ϕ)) ⟩
      t ⋯ ((ϕ ↑ᴷ _) ; ⦅ (q &/⋯ ϕ) ⦆) ≡⟨ sym (⋯-compositionality t (ϕ ↑ᴷ _) ⦅ q &/⋯ ϕ ⦆ ) ⟩
      t ⋯ (ϕ ↑ᴷ _) ⋯ ⦅ (q &/⋯ ϕ) ⦆   ∎

  record Types : Set₁ where
    constructor mkTypes
    field
      ↑ᵗ : Sort → Sort

    _∶⊢_ : ∀ Scope → Sort → Set
    S ∶⊢ s = S ⊢ (↑ᵗ s)

    depth : S ∋ s → ℕ
    depth zero     = zero
    depth (suc x)  = suc (depth x)

    -- We need to drop one extra using `suc`, because otherwise the types in a
    -- context are allowed to use themselves.
    drop-∈ : S ∋ s → Scope → Scope
    drop-∈ e xs = drop (suc (depth e)) xs

    Ctx : Scope → Set
    Ctx S = ∀ s → (x : S ∋ s) → drop-∈ x S ∶⊢ s

    []ₜ : Ctx []
    []ₜ _ ()

    _∷ₜ_ : S ∶⊢ s → Ctx S → Ctx (s ∷ S)
    (t ∷ₜ Γ) _ zero     = t
    (t ∷ₜ Γ) _ (suc x)  = Γ _ x

    wk-drop-∈ : (x : S ∋ s) → drop-∈ x S ⊢ s′ → S ⊢ s′
    wk-drop-∈ zero     t = t &/⋯ wkᴿ
    wk-drop-∈ (suc x)  t = wk-drop-∈ x t &/⋯ wkᴿ

    wk-telescope : Ctx S → S ∋ s → S ∶⊢ s
    wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

    infix   4  _∋_∶_
    _∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
    Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

    module TypesMeta where
      variable
        Γ : Ctx S 

    record Typing : Set₁ where 
      constructor mkTyping
      infix   4  _⊢_∶_
      field
        _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set

        ⊢` : ∀ {Γ : Ctx S} {x : S ∋ s} {t} →
            Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t

      record TypingKit (K : Kit k) : Set₁ where
        private instance _ = K
        infix   4  _∋/⊢_∶_  _∋*/⊢*_∶_
        infixl  6  _∋↑/⊢↑_
        field
          _∋/⊢_∶_      : Ctx S → S ∋/⊢ᴷ s → S ∶⊢ s → Set
          id/⊢`        : ∀ {t : S ∶⊢ s} {Γ : Ctx S} →
                         Γ ∋ x ∶ t → Γ ∋/⊢ (id/` x) ∶ t
          ⊢`/id        : ∀ {e : S ∋/⊢ᴷ s} {t : S ∶⊢ s} {Γ : Ctx S} →
                         Γ ∋/⊢ e ∶ t → Γ ⊢ `/id e ∶ t
          ∋wk/⊢wk      : ∀ (Γ : Ctx S) (t′ : S ∶⊢ s) (e : S ∋/⊢ᴷ s′)
                           (t : S ∶⊢ s′) →
                         Γ ∋/⊢ e ∶ t →
                         (t′ ∷ₜ Γ) ∋/⊢ K-wk _ e ∶ t &/⋯ wkᴿ 

        _∋*/⊢*_∶_ : Ctx S₂ → S₁ –[ K ]→ S₂ → Ctx S₁ → Set
        _∋*/⊢*_∶_ {S₂} {S₁} Γ₂ ϕ Γ₁ =
          ∀ {s₁} (x : S₁ ∋ s₁) (t : S₁ ∶⊢ s₁) →
          Γ₁ ∋ x ∶ t → 
          Γ₂ ∋/⊢ (x &/⋯ ϕ) ∶ (t &/⋯ ϕ)

        opaque 
          unfolding lib
          _∋↑/⊢↑_ : 
            {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ϕ : S₁ –[ K ]→ S₂} →
            Γ₂             ∋*/⊢* ϕ       ∶ Γ₁ →
            (t : S₁ ∶⊢ s) →
            ((t &/⋯ ϕ) ∷ₜ Γ₂) ∋*/⊢* (ϕ ↑ᴷ s) ∶ (t ∷ₜ Γ₁) 
          _∋↑/⊢↑_ {S₁} {S₂} {s} {Γ₁} {Γ₂} {ϕ} ⊢ϕ t {sx} x@zero _ refl =
            subst (  ((t ⋯ ϕ) ∷ₜ Γ₂) ∋/⊢ (zero & (ϕ ↑ᴷ s)) ∶_ )
                  (  t ⋯ ϕ ⋯ wkᴿ {s = s}                       ≡⟨ ⋯-↑ᴷ-wk {{C₁ = K ;ᶜ Kᴿ}} t ϕ s ⟩
                     t ⋯ wkᴿ {s = s} ⋯ (ϕ ↑ᴷ s)                ≡⟨⟩
                     wk-telescope (t ∷ₜ Γ₁) zero ⋯ (ϕ ↑ᴷ s)    ∎)
                  (  id/⊢` {x = zero} {Γ = (t ⋯ ϕ) ∷ₜ Γ₂} refl )
          _∋↑/⊢↑_ {S₁} {S₂} {s} {Γ₁} {Γ₂} {ϕ} ⊢ϕ t {sx} x@(suc y) _ refl =  
            subst (((t &/⋯ ϕ) ∷ₜ Γ₂) ∋/⊢ (suc y & (ϕ ↑ᴷ s)) ∶_)
                  (wk-telescope Γ₁ y ⋯ ϕ ⋯ wkᴿ {s = s}          ≡⟨ ⋯-↑ᴷ-wk {{C₁ = K ;ᶜ Kᴿ}} _ ϕ s ⟩
                   wk-telescope Γ₁ y ⋯ wkᴿ {s = s} ⋯ (ϕ ↑ᴷ s)   ≡⟨⟩
                   wk-telescope (t ∷ₜ Γ₁) (suc y) ⋯ (ϕ ↑ᴷ s)    ∎)
                  (∋wk/⊢wk _ _ _ _ (⊢ϕ y _ refl))

          ⊢⦅_⦆ : ∀ {s S} {Γ : Ctx S} {t : S ∋/⊢ᴷ s} {T : S ∶⊢ s}
            → Γ ∋/⊢ t ∶ T 
            → Γ ∋*/⊢* ⦅ t ⦆ ∶ (T ∷ₜ Γ)
          ⊢⦅_⦆ {s} {S} {Γ} {t} {T} ⊢x/t x@zero _ refl =
            subst (Γ ∋/⊢ t ∶_)
                  (T               ≡⟨ sym (wk-cancels-⦅⦆-⋯ T t) ⟩
                   T ⋯ wkᴿ ⋯ ⦅ t ⦆  ≡⟨⟩
                   wk-telescope (T ∷ₜ Γ) zero ⋯ ⦅ t ⦆  ∎)
                  ⊢x/t
          ⊢⦅_⦆ {s} {S} {Γ} {t} {T} ⊢x/t x@(suc y) _ refl =
            subst (Γ ∋/⊢ id/` y ∶_)
                  (wk-telescope Γ y              ≡⟨ sym (wk-cancels-⦅⦆-⋯ _ t) ⟩
                   wk-telescope Γ y ⋯ wkᴿ ⋯ ⦅ t ⦆ ≡⟨⟩
                   wk-telescope (T ∷ₜ Γ) (suc y) ⋯ ⦅ t ⦆  ∎)
                  (id/⊢` refl)

      open TypingKit {{ ...}} public

      infixl  5  _∋*/⊢*[_]_∶_
      _∋*/⊢*[_]_∶_ :
        ∀ {K : Kit k} {S₁ S₂} 
        → Ctx S₂ → TypingKit K → S₁ –[ K ]→ S₂ → Ctx S₁ → Set
      Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ = Γ₂ ∋*/⊢* ϕ ∶ Γ₁ where instance _ = TK

      record TypingTraversal : Set₁ where
        constructor mkTTraversal
        field
          _⊢⋯_ :
            ∀  {{K : Kit k}} {{TK : TypingKit K}}
               {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} 
               {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
            Γ₁ ⊢ e ∶ t →
            Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
            Γ₂ ⊢ e &/⋯ ϕ ∶ t &/⋯ ϕ

        opaque
          unfolding lib 
          
          TKᵣ-id/⊢` : {Γ : Ctx S} {t : S ∶⊢ s} → Γ ∋ x ∶ t → Γ ∋ id/` x ∶ t
          TKᵣ-id/⊢` = λ ⊢x → ⊢x

          TKᵣ-⊢`/id : {t : S ∶⊢ s} {Γ : Ctx S} {e : S ∋/⊢ᴷ s} → Γ ∋ e ∶ t → Γ ⊢ `/id e ∶ t
          TKᵣ-⊢`/id = ⊢`

          TKᵣ-∋wk/⊢wk : (Γ : Ctx S) (t′ : S ∶⊢ s)
                (e : S ∋/⊢ᴷ s′) (t : S ∶⊢ s′) →
                Γ ∋ e ∶ t →
                (t′ ∷ₜ Γ) ∋ K-wk _ e ∶ t &/⋯ wkᴿ
          TKᵣ-∋wk/⊢wk _ _ _ _ refl = refl

        instance
          TKᵣ : TypingKit Kᴿ
          TKᵣ = record
            { _∋/⊢_∶_     = _∋_∶_
            ; id/⊢`       = λ {Γ = Γ} → TKᵣ-id/⊢` {Γ = Γ}
            ; ⊢`/id       = TKᵣ-⊢`/id 
            ; ∋wk/⊢wk     = TKᵣ-∋wk/⊢wk }

        opaque
          unfolding lib  
          TKₛ-∋wk/⊢wk : (Γ : Ctx S) (t′ : S ∶⊢ s) (e : S ⊢ s′) (t : S ∶⊢ s′) → 
            Γ ⊢ e ∶ t → (t′ ∷ₜ Γ) ⊢ K-wk _ e ∶ t  &/⋯ wkᴿ
          TKₛ-∋wk/⊢wk = λ Γ t′ e t ⊢e → ⊢e ⊢⋯ ∋wk/⊢wk Γ t′ 

          TKₛ-id/⊢` : {Γ : Ctx S} {t : S ∶⊢ s} → Γ ∋ x ∶ t → Γ ⊢ id/` x ∶ t
          TKₛ-id/⊢` = ⊢`

          TKₛ-⊢`/id : {t : S ∶⊢ s} {Γ : Ctx S} {e : S ⊢ s} → Γ ⊢ e ∶ t → Γ ⊢ `/id e ∶ t
          TKₛ-⊢`/id = λ ⊢x → ⊢x

        instance 
          TKₛ : TypingKit Kˢ
          TKₛ = record
            { _∋/⊢_∶_     = _⊢_∶_
            ; id/⊢`       = TKₛ-id/⊢`
            ; ⊢`/id       = TKₛ-⊢`/id
            ; ∋wk/⊢wk     = TKₛ-∋wk/⊢wk } 

        open TypingKit TKᵣ public using () renaming
          (∋wk/⊢wk to ⊢wk; _∋*/⊢*_∶_ to _∋*_∶_; ⊢⦅_⦆ to ⊢⦅_⦆ᵣ)
        open TypingKit TKₛ public using () renaming
          (∋wk/⊢wk to ∋wk; _∋*/⊢*_∶_ to _⊢*_∶_; ⊢⦅_⦆ to ⊢⦅_⦆ₛ)

        _⊢⋯ᵣ_ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
                  {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ρ : S₁ →ᴿ S₂} →
                Γ₁ ⊢ e ∶ t →
                Γ₂ ∋* ρ ∶ Γ₁ →
                Γ₂ ⊢ e &/⋯ ρ ∶ t &/⋯ ρ
        _⊢⋯ᵣ_ = _⊢⋯_

        _⊢⋯ₛ_ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
                  {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {σ : S₁ →ˢ S₂} →
                Γ₁ ⊢ e ∶ t →
                Γ₂ ⊢* σ ∶ Γ₁ →
                Γ₂ ⊢ e &/⋯ σ ∶ t &/⋯ σ
        _⊢⋯ₛ_ = _⊢⋯_ 