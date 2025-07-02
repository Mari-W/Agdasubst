-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting #-}
module Extensions.StandardTyping.Base where

open import Extensions.Common
module _ {{lib : WithLib}} where 
  open WithLib lib

  open import Data.Nat using (ℕ; zero; suc)
  open import Data.List using (drop)
  open import Data.Product using (∃-syntax; proj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
  open ≡-Reasoning

  opaque
    unfolding all_kit_and_compose_definitions 

    wk-cancels-⦅⦆ :
      ∀ {{K : Kit k}} (x/t : S ∋/⊢[ K ] s) →
      (wkᵣ {s = s} ; ⦅ x/t ⦆) ~ id
    wk-cancels-⦅⦆ {{K }} x/t sx x = `/id-injective (
        `/id {{K }} (x & (wkᵣ ; ⦅ x/t ⦆))  ≡⟨⟩
        `/id {{K }} (id/` (suc x) &/⋯ ⦅ x/t ⦆) ≡⟨ &/⋯-& {{Cᵣ {{K }} }} (suc x) ⦅ x/t ⦆ ⟩
        `/id {{K }} (id/` x)                  ≡⟨⟩
        `/id {{K }} (x & id)                  ∎)
 
    wk-cancels-⦅⦆-⋯ :
      ∀ {{K : Kit k }} (t : S ⊢ s′) (x/t : S ∋/⊢[ K ] s) →
      t ⋯ wkᵣ {s = s} ⋯ ⦅ x/t ⦆ ≡ t
    wk-cancels-⦅⦆-⋯ t x/t =
      t ⋯ wkᵣ ⋯ ⦅ x/t ⦆   ≡⟨ ⋯-fusion t wkᵣ ⦅ x/t ⦆ ⟩
      t ⋯ (wkᵣ ; ⦅ x/t ⦆) ≡⟨ cong (t ⋯_) (~-ext (wk-cancels-⦅⦆ x/t)) ⟩
      t ⋯ id             ≡⟨ ⋯-id t ⟩
      t                  ∎

    dist-↑-⦅⦆ :
      ∀  {{K₁ : Kit k₁ }} {{K₂ : Kit k₂}} {{K : Kit k}}
         {{C₁ : ComposeKit K₁ K₂ K}} {{C₂ : ComposeKit K₂ K K}}
         (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
      (⦅ x/t ⦆ ; ϕ) ~ ((ϕ ↑ₖ s) ; ⦅ (x/t &/⋯ ϕ) ⦆)
    dist-↑-⦅⦆ {s = s} {{K₁ }} {{K₂ }} {{K }} {{C₁ }} {{C₂ }} x/t ϕ sx x@zero = `/id-injective (
        `/id {{K }} (x & (⦅ x/t ⦆ ; ϕ))                     ≡⟨⟩
        `/id {{K }} (x/t &/⋯ ϕ)                            ≡⟨⟩
        `/id {{K }} (zero & ⦅ (x/t &/⋯ ϕ) ⦆)                ≡⟨ sym (&/⋯-& {{C₂ }} zero ⦅ (x/t &/⋯ ϕ) ⦆) ⟩
        `/id {{K }} (id/` {{K₂ }} zero &/⋯ ⦅ (x/t &/⋯ ϕ) ⦆) ≡⟨⟩
        `/id {{K }} (x & ((ϕ ↑ₖ s) ; ⦅ (x/t &/⋯ ϕ) ⦆))      ∎)
    dist-↑-⦅⦆ {s = s} {{K₁ }} {{K₂ }} {{K }} {{C₁ }} {{C₂ }} x/t ϕ sx x@(suc y) = `/id-injective ( 
        `/id (x & (⦅ x/t ⦆ ; ϕ))                     ≡⟨⟩
        `/id (id/` {{K₁ }} y &/⋯ ϕ)                 ≡⟨ &/⋯-& {{C₁ }} y ϕ ⟩
        `/id (y & ϕ)                                ≡⟨ sym (wk-cancels-⦅⦆-⋯ (`/id (y & ϕ)) (x/t &/⋯ ϕ)) ⟩
        `/id (y & ϕ) ⋯ wkᵣ {s = s} ⋯ ⦅ (x/t &/⋯ ϕ) ⦆ ≡⟨ cong (_⋯ ⦅ x/t &/⋯ ϕ ⦆) (wk-`/id s (y & ϕ)) ⟩
        `/id (wk′ s (y & ϕ)) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆       ≡⟨ sym (&/⋯-⋯ (wk′ s (y & ϕ)) ⦅ (x/t &/⋯ ϕ) ⦆) ⟩
        `/id (wk′ s (y & ϕ) &/⋯ ⦅ (x/t &/⋯ ϕ) ⦆)     ≡⟨⟩
        `/id (x & ((ϕ ↑ₖ s) ; ⦅ (x/t &/⋯ ϕ) ⦆))      ∎)

    dist-↑-⦅⦆-⋯ :
      ∀  {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K : Kit k}} 
         {{C₁ : ComposeKit K₁ K₂ K }} {{C₂ : ComposeKit K₂ K K}}
         (t : (s ∷ S₁) ⊢ s′) (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
      t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ₖ s) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆
    dist-↑-⦅⦆-⋯ t x/t ϕ =
      t ⋯ ⦅ x/t ⦆ ⋯ ϕ                  ≡⟨ ⋯-fusion t ⦅ x/t ⦆ ϕ ⟩
      t ⋯ (⦅ x/t ⦆ ; ϕ)                ≡⟨ cong (t ⋯_) (~-ext (dist-↑-⦅⦆ x/t ϕ)) ⟩
      t ⋯ ((ϕ ↑ₖ _) ; ⦅ (x/t &/⋯ ϕ) ⦆) ≡⟨ sym (⋯-fusion t (ϕ ↑ₖ _) ⦅ x/t &/⋯ ϕ ⦆ ) ⟩
      t ⋯ (ϕ ↑ₖ _) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆   ∎

  record Types : Set₁ where
    field
      ↑ᵗ : ∀ {st} → Sort st → ∃[ st′ ] Sort st′

    _∶⊢_ : ∀ {t} → List (Sort Bind) → Sort t → Set
    S ∶⊢ s = S ⊢ proj₂ (↑ᵗ s)

    depth : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → xs ∋ x → ℕ
    depth zero     = zero
    depth (suc x)  = suc (depth x)

    -- We need to drop one extra using `suc`, because otherwise the types in a
    -- context are allowed to use themselves.
    drop-∈ :  ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} →
      xs ∋ x → List A → List A
    drop-∈ e xs = drop (suc (depth e)) xs

    Ctx : List (Sort Bind) → Set
    Ctx S = ∀ s → (x : S ∋ s) → drop-∈ x S ∶⊢ s

    []ₜ : Ctx []
    []ₜ _ ()

    _∷ₜ_ : S ∶⊢ s → Ctx S → Ctx (s ∷ S)
    (t ∷ₜ Γ) _ zero     = t
    (t ∷ₜ Γ) _ (suc x)  = Γ _ x

    wk-drop-∈ : (x : S ∋ s) → drop-∈ x S ⊢ s′ → S ⊢ s′
    wk-drop-∈ zero     t = t ⋯ wkᵣ
    wk-drop-∈ (suc x)  t = wk-drop-∈ x t ⋯ wkᵣ

    wk-telescope : Ctx S → S ∋ s → S ∶⊢ s
    wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

    infix   4  _∋_∶_
    _∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
    Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

    record Typing : Set₁ where 
      infix   4  _⊢_∶_
      field
        _⊢_∶_ : ∀ {s : Sort m} → Ctx S → S ⊢ s → S ∶⊢ s → Set

        ⊢` : ∀ {Γ : Ctx S} {x : S ∋ s} {t} →
            Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t

      record TypingKit (K : Kit k) : Set₁ where
        private instance _ = K
        infix   4  _∋/⊢_∶_  _∋*/⊢*_∶_
        infixl  6  _∋↑/⊢↑_
        field
          _∋/⊢_∶_      : Ctx S → S ∋/⊢ s → S ∶⊢ s → Set
          id/⊢`        : ∀ {t : S ∶⊢ s} {Γ : Ctx S} →
                         Γ ∋ x ∶ t → Γ ∋/⊢ id/` x ∶ t
          ⊢`/id        : ∀ {e : S ∋/⊢ s} {t : S ∶⊢ s} {Γ : Ctx S} →
                         Γ ∋/⊢ e ∶ t → Γ ⊢ `/id e ∶ t
          ∋wk/⊢wk      : ∀ (Γ : Ctx S) (t′ : S ∶⊢ s) (e : S ∋/⊢ s′)
                           (t : S ∶⊢ s′) →
                         Γ ∋/⊢ e ∶ t →
                         (t′ ∷ₜ Γ) ∋/⊢ wk′ _ e ∶ (t ⋯ wkᵣ) 

        _∋*/⊢*_∶_ : Ctx S₂ → S₁ –[ K ]→ S₂ → Ctx S₁ → Set
        _∋*/⊢*_∶_ {S₂} {S₁} Γ₂ ϕ Γ₁ =
          ∀ {s₁} (x : S₁ ∋ s₁) (t : S₁ ∶⊢ s₁) →
          Γ₁ ∋ x ∶ t →
          Γ₂ ∋/⊢ (x & ϕ) ∶ (t ⋯ ϕ)

        opaque 
          unfolding all_kit_and_compose_definitions
          _∋↑/⊢↑_ : 
            {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ϕ : S₁ –[ K ]→ S₂} →
            Γ₂             ∋*/⊢* ϕ       ∶ Γ₁ →
            (t : S₁ ∶⊢ s) →
            ((t ⋯ ϕ) ∷ₜ Γ₂) ∋*/⊢* (ϕ ↑ₖ s) ∶ (t ∷ₜ Γ₁) 
          _∋↑/⊢↑_ {S₁} {S₂} {s} {Γ₁} {Γ₂} {ϕ} ⊢ϕ t {sx} x@zero _ refl =
            subst (  ((t ⋯ ϕ) ∷ₜ Γ₂) ∋/⊢ (zero & (ϕ ↑ₖ s)) ∶_ )
                  (  t ⋯ ϕ ⋯ wkᵣ {s = s}                       ≡⟨ ⋯-↑ₖ-wk {{C₁ = C–⊔ }} t ϕ s ⟩
                     t ⋯ wkᵣ {s = s} ⋯ (ϕ ↑ₖ s)                ≡⟨⟩
                     wk-telescope (t ∷ₜ Γ₁) zero ⋯ (ϕ ↑ₖ s)    ∎)
                  (  id/⊢` {x = zero} {Γ = (t ⋯ ϕ) ∷ₜ Γ₂} refl )
          _∋↑/⊢↑_ {S₁} {S₂} {s} {Γ₁} {Γ₂} {ϕ} ⊢ϕ t {sx} x@(suc y) _ refl =
            subst (((t ⋯ ϕ) ∷ₜ Γ₂) ∋/⊢ (suc y & (ϕ ↑ₖ s)) ∶_)
                  (wk-telescope Γ₁ y ⋯ ϕ ⋯ wkᵣ {s = s}          ≡⟨ ⋯-↑ₖ-wk {{C₁ = C–⊔ }} _ ϕ s ⟩
                   wk-telescope Γ₁ y ⋯ wkᵣ {s = s} ⋯ (ϕ ↑ₖ s)   ≡⟨⟩
                   wk-telescope (t ∷ₜ Γ₁) (suc y) ⋯ (ϕ ↑ₖ s)    ∎)
                  (∋wk/⊢wk _ _ _ _ (⊢ϕ y _ refl))

          ⊢⦅_⦆ : ∀ {s S} {Γ : Ctx S} {t : S ∋/⊢ s} {T : S ∶⊢ s}
            → Γ ∋/⊢ t ∶ T 
            → Γ ∋*/⊢* ⦅ t ⦆ ∶ (T ∷ₜ Γ)
          ⊢⦅_⦆ {s} {S} {Γ} {t} {T} ⊢x/t x@zero _ refl =
            subst (Γ ∋/⊢ t ∶_)
                  (T               ≡⟨ sym (wk-cancels-⦅⦆-⋯ T t) ⟩
                   T ⋯ wkᵣ ⋯ ⦅ t ⦆  ≡⟨⟩
                   wk-telescope (T ∷ₜ Γ) zero ⋯ ⦅ t ⦆  ∎)
                  ⊢x/t
          ⊢⦅_⦆ {s} {S} {Γ} {t} {T} ⊢x/t x@(suc y) _ refl =
            subst (Γ ∋/⊢ id/` y ∶_)
                  (wk-telescope Γ y              ≡⟨ sym (wk-cancels-⦅⦆-⋯ _ t) ⟩
                   wk-telescope Γ y ⋯ wkᵣ ⋯ ⦅ t ⦆ ≡⟨⟩
                   wk-telescope (T ∷ₜ Γ) (suc y) ⋯ ⦅ t ⦆  ∎)
                  (id/⊢` refl)

      open TypingKit {{... }} public

      infixl  5  _∋*/⊢*[_]_∶_
      _∋*/⊢*[_]_∶_ :
        ∀ {K : Kit k} {S₁ S₂}
        → Ctx S₂ → TypingKit K → S₁ –[ K ]→ S₂ → Ctx S₁ → Set
      Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ = Γ₂ ∋*/⊢* ϕ ∶ Γ₁ where instance _ = TK

      record TypingTraversal : Set₁ where
        field
          _⊢⋯_ :
            ∀  {{K : Kit k }} {{TK : TypingKit K}}
               {{C₁ : ComposeKit K Kᵣ K}}
               {{C₂ : ComposeKit K K K}}
               {{C₃ : ComposeKit K Kₛ Kₛ}}
               {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
               {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
            Γ₁ ⊢ e ∶ t →
            Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
            Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ

        instance
          TKᵣ : TypingKit Kᵣ
          TKᵣ = record
            { _∋/⊢_∶_     = _∋_∶_
            ; id/⊢`       = λ ⊢x → ⊢x
            ; ⊢`/id       = ⊢`
            ; ∋wk/⊢wk     = λ { Γ t′ x t refl → refl } }

        opaque
          unfolding all_kit_and_compose_definitions
          TKₛ-∋wk/⊢wk : {S : Scope} {s s′ : Sort Bind} (Γ : Ctx S) (t′ : S ∶⊢ s) (e : S ⊢ s′) (t : S ∶⊢ s′) → 
            Γ ⊢ e ∶ t → (t′ ∷ₜ Γ) ⊢ Kit.wk′ Kₛ s e ∶ t ⋯ wkᵣ
          TKₛ-∋wk/⊢wk = λ Γ t′ e t ⊢e → ⊢e ⊢⋯ ∋wk/⊢wk Γ t′ 

        instance 
          TKₛ : TypingKit Kₛ
          TKₛ = record
            { _∋/⊢_∶_     = _⊢_∶_
            ; id/⊢`       = ⊢`
            ; ⊢`/id       = λ ⊢x → ⊢x
            ; ∋wk/⊢wk     = TKₛ-∋wk/⊢wk } 

        open TypingKit TKᵣ public using () renaming
          (∋wk/⊢wk to ⊢wk; _∋*/⊢*_∶_ to _∋*_∶_; ⊢⦅_⦆ to ⊢⦅_⦆ᵣ)
        open TypingKit TKₛ public using () renaming
          (∋wk/⊢wk to ∋wk; _∋*/⊢*_∶_ to _⊢*_∶_; ⊢⦅_⦆ to ⊢⦅_⦆ₛ)

        _⊢⋯ᵣ_ : ∀ {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
                  {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ρ : S₁ →ᵣ S₂} →
                Γ₁ ⊢ e ∶ t →
                Γ₂ ∋* ρ ∶ Γ₁ →
                Γ₂ ⊢ e ⋯ ρ ∶ t ⋯ ρ
        _⊢⋯ᵣ_ = _⊢⋯_

        _⊢⋯ₛ_ : ∀ {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
                  {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {σ : S₁ →ₛ S₂} →
                Γ₁ ⊢ e ∶ t →
                Γ₂ ⊢* σ ∶ Γ₁ →
                Γ₂ ⊢ e ⋯ σ ∶ t ⋯ σ
        _⊢⋯ₛ_ = _⊢⋯_ 