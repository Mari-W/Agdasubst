-- Author: Hannes Saffrich
-- Modified: Marius Weidner
module Kits where

open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; module ≡-Reasoning)
open ≡-Reasoning

open import DeBruijn
open import Sorts

module KitsWithSort (Sort : SORT) where
    open SortsWithSort Sort 
    open SortsMeta
  
    record Syntax : Set₁ where
      field
        _⊢_  : SCOPED
        `_   : S ∋ s → S ⊢ s

        `-injective : ` x₁ ≡ ` x₂ → x₁ ≡ x₂

      record Kit (_∋/⊢_ : SCOPED_BINDABLE) : Set where

        field
          id/`            : S ∋ s → S ∋/⊢ s
          `/id            : S ∋/⊢ s → S ⊢ s
          wk′             : ∀ s′ → S ∋/⊢ s → (s′ ∷ S) ∋/⊢ s

          `/`-is-`        : ∀ (x : S ∋ s) → `/id (id/` x) ≡ ` x
          id/`-injective  : id/` x₁ ≡ id/` x₂ → x₁ ≡ x₂
          `/id-injective  : ∀ {x/t₁ x/t₂ : S ∋/⊢ s} →
                              `/id x/t₁ ≡ `/id x/t₂ → x/t₁ ≡ x/t₂
          wk-id/`         : ∀ s′ (x : S ∋ s) →
                              wk′ s′ (id/` x) ≡ id/` (suc x)  

        opaque 
          import Data.Unit using (⊤; tt)
          all_kit_definitions : Data.Unit.⊤
          all_kit_definitions = Data.Unit.tt

          _→ₖ_ : Scope → Scope → Set
          S₁ →ₖ S₂ = ∀ s → S₁ ∋ s → S₂ ∋/⊢ s

          infixl 8 _&ₖ_
          _&ₖ_ : S₁ ∋ s → S₁ →ₖ S₂ → S₂ ∋/⊢ s
          x &ₖ ϕ = ϕ _ x 

          private
            wkmₖ : ∀ s → S₁ →ₖ S₂ → S₁ →ₖ (s ∷ S₂)
            wkmₖ s ϕ _ x = wk′ s (ϕ _ x)

          _∷ₖ_ : S₂ ∋/⊢ s → S₁ →ₖ S₂ → (s ∷ S₁) →ₖ S₂
          (x/t ∷ₖ ϕ) _ zero     = x/t
          (x/t ∷ₖ ϕ) _ (suc x)  = ϕ _ x

          _↑ₖ_ : S₁ →ₖ S₂ → ∀ s → (s ∷ S₁) →ₖ (s ∷ S₂)
          ϕ ↑ₖ s = id/` zero ∷ₖ wkmₖ s ϕ

          idₖ : S →ₖ S
          idₖ s x = id/` x

          ⦅_⦆ₖ : S ∋/⊢ s → (s ∷ S) →ₖ S
          ⦅ x/t ⦆ₖ = x/t ∷ₖ idₖ

          wkₖ : ∀ s → S →ₖ (s ∷ S)
          wkₖ s = wkmₖ s idₖ
        
        _↑ₖ*_ : S₁ →ₖ S₂ → ∀ S → (S ++ S₁) →ₖ (S ++ S₂)
        ϕ ↑ₖ* []       = ϕ
        ϕ ↑ₖ* (s ∷ S)  = (ϕ ↑ₖ* S) ↑ₖ s

        _~_ : (ϕ₁ ϕ₂ : S₁ →ₖ S₂) → Set
        _~_ {S₁} ϕ₁ ϕ₂ = ∀ s (x : S₁ ∋ s) → x &ₖ ϕ₁ ≡ x &ₖ ϕ₂ 

        postulate
          ~-ext : ∀ {ϕ₁ ϕ₂ : S₁ →ₖ S₂} → ϕ₁ ~ ϕ₂ → ϕ₁ ≡ ϕ₂

        opaque 
          unfolding all_kit_definitions

          id↑~id : (idₖ {S} ↑ₖ s) ~ idₖ {s ∷ S}
          id↑~id s zero    = refl
          id↑~id s (suc x) =
            (idₖ ↑ₖ _) s (suc x) ≡⟨⟩
            wk′ _ (id/` x)        ≡⟨ wk-id/` _ x ⟩
            id/` (suc x)         ≡⟨⟩
            idₖ s (suc x)         ∎

          id↑*~id : ∀ S → (idₖ ↑ₖ* S) ~ idₖ {S ++ S′}
          id↑*~id []      sx x = refl
          id↑*~id (s ∷ S) sx x =
            ((idₖ ↑ₖ* S) ↑ₖ s) sx x ≡⟨ cong (λ ■ → (■ ↑ₖ s) sx x) (~-ext (id↑*~id S)) ⟩
            (idₖ ↑ₖ s) sx x        ≡⟨ id↑~id sx x ⟩
            idₖ sx x              ∎


      _∋/⊢[_]_ : Scope → Kit _∋/⊢_ → BindSort → Set
      _∋/⊢[_]_ {_∋/⊢_} S K s = S ∋/⊢ s

      _–[_]→_ : Scope → Kit _∋/⊢_ → Scope → Set
      S₁ –[ K ]→ S₂ = Kit._→ₖ_ K S₁ S₂

      open Kit ⦃ … ⦄ public

      record Traversal : Set₁ where
        infixl   5  _⋯_

        field
          _⋯_    : ∀ {{K : Kit _∋/⊢_}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
          ⋯-var  : ∀ {{K : Kit _∋/⊢_}} → (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) →
                     (` x) ⋯ ϕ ≡ `/id {{K}} (x &ₖ ϕ)
          ⋯-id   : ∀ {{K : Kit _∋/⊢_}} → (t : S ⊢ s) →
                     t ⋯ idₖ {{K}} ≡ t
        instance
          Kᵣ : Kit _∋_
          Kᵣ = record
            { id/`            = λ x → x
            ; `/id            = `_
            ; wk′             = λ s′ x → suc x
            ; `/`-is-`        = λ x → refl
            ; id/`-injective  = λ eq → eq 
            ; `/id-injective  = `-injective 
            ; wk-id/`         = λ s′ x → refl 
            }

        opaque
          unfolding all_kit_definitions
          private 
            Kₛ-wk-id/` : {S : Scope} {s : BindSort} (s′ : BindSort) (x : S ∋ s) →
                        (` x) ⋯ Kit.wkₖ Kᵣ s′ ≡ (` suc x)
            Kₛ-wk-id/` = λ s′ x → ⋯-var x (wkₖ s′)

        instance
          Kₛ : Kit _⊢_
          Kₛ = record
            { id/`            = `_
            ; `/id            = λ t → t
            ; wk′             = λ s′ t → t ⋯ (wkₖ {{Kᵣ}} s′)
            ; `/`-is-`        = λ x → refl
            ; id/`-injective  = `-injective
            ; `/id-injective  = λ eq → eq 
            ; wk-id/`         = Kₛ-wk-id/`
            }

        open Kit Kᵣ public using () renaming 
          (_→ₖ_ to _→ᵣ_; _&ₖ_ to _&ᵣ_; _∷ₖ_ to _∷ᵣ_; _↑ₖ_ to _↑ᵣ_; 
           _↑ₖ*_ to _↑ᵣ*_; idₖ to idᵣ; ⦅_⦆ₖ to ⦅_⦆ᵣ; wkₖ to wkᵣ)
        open Kit Kₛ public using () renaming 
          (_→ₖ_ to _→ₛ_; _&ₖ_ to _&ₛ_; _∷ₖ_ to _∷ₛ_; _↑ₖ_ to _↑ₛ_; 
           _↑ₖ*_ to _↑ₛ*_; idₖ to idₛ; ⦅_⦆ₖ to ⦅_⦆ₛ; wkₖ to wkₛ)

        module KitsMeta where
          variable 
            T T₁ T₂ T₃ T₄ T′ T₁′ T₂′ T₃′ T₄′ : S ⊢ s
            ρ ρ₁ ρ₂ ρ₃ ρ₄ ρ′ ρ₁′ ρ₂′ ρ₃′ ρ₄′ : S₁ →ᵣ S₂
            σ σ₁ σ₂ σ₃ σ₄ σ′ σ₁′ σ₂′ σ₃′ σ₄′ : S₁ →ₛ S₂

        _⋯ᵣ_ : S₁ ⊢ s → S₁ →ᵣ S₂ → S₂ ⊢ s
        t ⋯ᵣ ρ = t ⋯ ρ

        wk : S ⊢ s → (s′ ∷ S) ⊢ s
        wk T = T ⋯ᵣ wkᵣ _

        _⋯ₛ_ : S₁ ⊢ s → S₁ →ₛ S₂ → S₂ ⊢ s
        t ⋯ₛ σ = t ⋯ σ

        _[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
        T [ T′ ] = T ⋯ₛ (T′ ∷ₛ idₛ) 

        record WkKit (K : Kit _∋/⊢_): Set₁ where
          private instance _ = K
          field
            wk-`/id  : ∀ s (x/t : S ∋/⊢ s′) → `/id x/t ⋯ᵣ wkᵣ s ≡ `/id (wk′ s x/t)

        opaque
          unfolding all_kit_definitions
          wk-`/id-Wᵣ : (s : BindSort) (x : S ∋ s′) → ((` x) ⋯ᵣ wkᵣ s) ≡ (` suc x)
          wk-`/id-Wᵣ = λ _ x/t → ⋯-var x/t (wkᵣ _)
       
        instance
          Wᵣ : WkKit Kᵣ
          Wᵣ = record { wk-`/id = wk-`/id-Wᵣ }

          Wₛ : WkKit Kₛ
          Wₛ = record { wk-`/id = λ s x/t → refl }

        open WkKit ⦃ … ⦄ public

        record ComposeKit (K₁ : Kit _∋/⊢₁_) (K₂ : Kit _∋/⊢₂_) (K₁⊔K₂ : Kit _∋/⊢_) : Set where

          private instance _ = K₁; _ = K₂; _ = K₁⊔K₂

          infixl 8 _&/⋯_
          field
            _&/⋯_     : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₁⊔K₂ ] s
            
            &/⋯-⋯     : (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                         `/id (x/t &/⋯ ϕ) ≡ `/id x/t ⋯ ϕ
            &/⋯-wk-↑  : (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                         wk′ s′ (x/t &/⋯ ϕ) ≡ wk′ s′ x/t &/⋯ (ϕ ↑ₖ s′)
      
          opaque
            unfolding all_kit_definitions

            import Data.Unit using (⊤; tt)
            all_kit_and_compose_definitions : Data.Unit.⊤
            all_kit_and_compose_definitions = Data.Unit.tt

            _⨟ₖₖ_ : S₁ –[ K₁ ]→ S₂ → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₁⊔K₂ ]→ S₃
            (ϕ₁ ⨟ₖₖ ϕ₂) _ x = (x &ₖ ϕ₁) &/⋯ ϕ₂ 

          opaque
            unfolding all_kit_and_compose_definitions

            &/⋯-& : ∀ (x : S₁ ∋ s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                    `/id (id/` ⦃ K₁ ⦄ x &/⋯ ϕ) ≡ `/id (x &ₖ ϕ)
            &/⋯-& x ϕ = 
              `/id (id/` x &/⋯ ϕ)       ≡⟨ &/⋯-⋯ (id/` x) ϕ ⟩
              `/id ⦃ K₁ ⦄ (id/` x) ⋯ ϕ  ≡⟨ cong (_⋯ ϕ) (`/`-is-` ⦃ K₁ ⦄ x) ⟩
              ` x ⋯ ϕ                   ≡⟨ ⋯-var ⦃ K₂ ⦄ x ϕ ⟩
              `/id ⦃ K₂ ⦄  (x &ₖ ϕ)      ∎

            dist-↑-⨟  : ∀ s (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                       ((ϕ₁ ⨟ₖₖ ϕ₂) ↑ₖ s) ~ ((ϕ₁ ↑ₖ s) ⨟ₖₖ (ϕ₂ ↑ₖ s))
            dist-↑-⨟ s ϕ₁ ϕ₂ s₁ x@zero = `/id-injective (   
              `/id ⦃ K₁⊔K₂ ⦄ (x &ₖ ((ϕ₁ ⨟ₖₖ ϕ₂) ↑ₖ s))         ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (id/` zero)                      ≡⟨ `/`-is-` ⦃ K₁⊔K₂ ⦄ zero ⟩
              ` zero                                           ≡⟨ sym (`/`-is-` ⦃ K₂ ⦄ zero) ⟩
              `/id ⦃ K₂ ⦄ (id/` zero)                         ≡⟨⟩
              `/id ⦃ K₂ ⦄ (zero &ₖ (ϕ₂ ↑ₖ s))                 ≡⟨ sym (&/⋯-& (id/` zero) (ϕ₂ ↑ₖ s)) ⟩
              `/id ⦃ K₁⊔K₂ ⦄ (id/` zero &/⋯ (ϕ₂ ↑ₖ s))        ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (x &ₖ (ϕ₁ ↑ₖ s) &/⋯ (ϕ₂ ↑ₖ s))   ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (x &ₖ ((ϕ₁ ↑ₖ s) ⨟ₖₖ (ϕ₂ ↑ₖ s)))  ∎
              )
            dist-↑-⨟ s ϕ₁ ϕ₂ s₁ x@(suc y) = `/id-injective (
              `/id ⦃ K₁⊔K₂ ⦄ (x &ₖ ((ϕ₁ ⨟ₖₖ ϕ₂) ↑ₖ s))         ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (wk′ _ (y &ₖ (ϕ₁ ⨟ₖₖ ϕ₂)))        ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (wk′ _ (y &ₖ ϕ₁ &/⋯ ϕ₂))          ≡⟨ cong `/id (&/⋯-wk-↑ (y &ₖ ϕ₁) ϕ₂) ⟩
              `/id ⦃ K₁⊔K₂ ⦄ (wk′ _ (y &ₖ ϕ₁) &/⋯ (ϕ₂ ↑ₖ s))   ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (x &ₖ (ϕ₁ ↑ₖ s) &/⋯ (ϕ₂ ↑ₖ s))   ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (x &ₖ ((ϕ₁ ↑ₖ s) ⨟ₖₖ (ϕ₂ ↑ₖ s)))  ∎
              )

            dist-↑*-⨟  : ∀ S (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                         ((ϕ₁ ⨟ₖₖ ϕ₂) ↑ₖ* S) ~ ((ϕ₁ ↑ₖ* S) ⨟ₖₖ (ϕ₂ ↑ₖ* S))
            dist-↑*-⨟ []      ϕ₁ ϕ₂ sx x = refl
            dist-↑*-⨟ (s ∷ S) ϕ₁ ϕ₂ sx x =
              ((ϕ₁ ⨟ₖₖ ϕ₂) ↑ₖ* (s ∷ S)) sx x                 ≡⟨⟩
              (((ϕ₁ ⨟ₖₖ ϕ₂) ↑ₖ* S) ↑ₖ s) sx x                ≡⟨ cong (λ ■ → (■ ↑ₖ s) sx x) (~-ext (dist-↑*-⨟ S ϕ₁ ϕ₂)) ⟩
              (((ϕ₁ ↑ₖ* S) ⨟ₖₖ (ϕ₂ ↑ₖ* S)) ↑ₖ s) sx x        ≡⟨ dist-↑-⨟ s (ϕ₁ ↑ₖ* S) (ϕ₂ ↑ₖ* S) sx x ⟩
              (((ϕ₁ ↑ₖ* S) ↑ₖ s) ⨟ₖₖ ((ϕ₂ ↑ₖ* S) ↑ₖ s)) sx x ≡⟨⟩
              ((ϕ₁ ↑ₖ* (s ∷ S)) ⨟ₖₖ (ϕ₂ ↑ₖ* (s ∷ S))) sx x ∎

        _⨟[_]_  : ∀ {K₁ : Kit _∋/⊢₁_} {K₂ : Kit _∋/⊢₂_} {K₁⊔K₂ : Kit _∋/⊢_} →
                  S₁ –[ K₁ ]→ S₂ → ComposeKit K₁ K₂ K₁⊔K₂ →
                  S₂ –[ K₂ ]→ S₃ → S₁ –[ K₁⊔K₂ ]→ S₃
        ϕ₁ ⨟[ C ] ϕ₂ = ϕ₁ ⨟ₖₖ ϕ₂ where open ComposeKit C

        open ComposeKit ⦃ … ⦄ public

        record ComposeTraversal : Set₁ where
          field
            ⋯-fusion : ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
                       ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
                       (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
                       (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ⨟ₖₖ ϕ₂)
          
          opaque
            unfolding all_kit_and_compose_definitions
          
            ↑-wk  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄
                    ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit Kᵣ K K ⦄ 
                    (ϕ : S₁ –[ K ]→ S₂) s → 
                    (ϕ ⨟ₖₖ wkₖ s) ~ (wkₖ s ⨟ₖₖ (ϕ ↑ₖ s))
            ↑-wk {S₁} {S₂} ϕ s sx x = `/id-injective (
              `/id ((ϕ ⨟ₖₖ wkᵣ s) sx x)         ≡⟨⟩
              `/id (x &ₖ ϕ &/⋯ wkᵣ s)           ≡⟨ &/⋯-⋯ (x &ₖ ϕ) (wkᵣ s) ⟩
              `/id (`/id (x &ₖ ϕ) ⋯ wkᵣ s)      ≡⟨ wk-`/id s (x &ₖ ϕ) ⟩
              `/id (suc x &ₖ (ϕ ↑ₖ s))          ≡⟨ sym (&/⋯-& (suc x) (ϕ ↑ₖ s)) ⟩
              `/id (suc x &/⋯ (ϕ ↑ₖ s))         ≡⟨⟩
              `/id (x &ₖ wkᵣ s &/⋯ (ϕ ↑ₖ s))    ≡⟨⟩
              `/id ((wkᵣ s ⨟ₖₖ (ϕ ↑ₖ s)) sx x)  ∎)
            
            ⋯-↑-wk  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄
                      ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit Kᵣ K K ⦄ 
                      (t : S₁ ⊢ s) (ϕ : S₁ –[ K ]→ S₂) s′ → 
                      t ⋯ ϕ ⋯ wkᵣ s′ ≡ t ⋯ wkᵣ s′ ⋯ (ϕ ↑ₖ s′)
            ⋯-↑-wk t ϕ s =
              t ⋯ ϕ ⋯ wkᵣ s           ≡⟨ ⋯-fusion t ϕ (wkᵣ s) ⟩
              t ⋯ (ϕ ⨟ₖₖ wkᵣ s)        ≡⟨ cong (t ⋯_) (~-ext (↑-wk ϕ s)) ⟩
              t ⋯ (wkᵣ s ⨟ₖₖ (ϕ ↑ₖ s))  ≡⟨ sym (⋯-fusion t (wkᵣ s) (ϕ ↑ₖ s)) ⟩
              t ⋯ wkᵣ s ⋯ (ϕ ↑ₖ s)     ∎

            Cᵣ-&/⋯-wk-↑  : ⦃ K₂ : Kit _∋/⊢_ ⦄ (x/t : S₁ ∋/⊢[ Kᵣ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                           Kit.wk′ K₂ s′ ((K₂ Kit.&ₖ x/t) ϕ) ≡ (K₂ Kit.&ₖ suc x/t) (ϕ ↑ₖ s′)
            Cᵣ-&/⋯-wk-↑ _ _ = refl

          instance
            Cᵣ : ⦃ K₂ : Kit _∋/⊢_ ⦄ → ComposeKit Kᵣ K₂ K₂
            Cᵣ = record
                { _&/⋯_     = _&ₖ_
                ; &/⋯-⋯     = λ x ϕ → sym (⋯-var x ϕ)
                ; &/⋯-wk-↑  = Cᵣ-&/⋯-wk-↑ }
                  
            Cₛ  : ⦃ K₂ : Kit _∋/⊢_ ⦄ ⦃ W₂ : WkKit K₂ ⦄
                  ⦃ C : ComposeKit K₂ Kᵣ K₂ ⦄ → ComposeKit Kₛ K₂ Kₛ
            Cₛ ⦃ C = C ⦄ = record
                { _&/⋯_     = _⋯_
                ; &/⋯-⋯     = λ t ϕ → refl
                ; &/⋯-wk-↑  = λ t ϕ → ⋯-↑-wk t ϕ _ }
          
          _⨟ᵣᵣ_ : S₁ →ᵣ S₂ → S₂ →ᵣ S₃ → S₁ →ᵣ S₃
          _⨟ᵣᵣ_ = _⨟ₖₖ_ 

          _⨟ᵣₛ_ : S₁ →ᵣ S₂ → S₂ →ₛ S₃ → S₁ →ₛ S₃
          _⨟ᵣₛ_ = _⨟ₖₖ_ 

          _⨟ₛᵣ_ : S₁ →ₛ S₂ → S₂ →ᵣ S₃ → S₁ →ₛ S₃
          _⨟ₛᵣ_ = _⨟ₖₖ_

          _⨟ₛₛ_ : S₁ →ₛ S₂ → S₂ →ₛ S₃ → S₁ →ₛ S₃
          _⨟ₛₛ_ = _⨟ₖₖ_
          
          opaque
            unfolding all_kit_and_compose_definitions
          
            wk-cancels-⦅⦆  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (x/t : S ∋/⊢[ K ] s) →
                            (wkᵣ s ⨟[ Cᵣ ] ⦅ x/t ⦆ₖ) ~ idₖ
            wk-cancels-⦅⦆ ⦃ K ⦄ x/t sx x = `/id-injective (
              `/id ⦃ K ⦄ (x &ₖ (wkᵣ _ ⨟[ Cᵣ ] ⦅ x/t ⦆ₖ))  ≡⟨⟩
              `/id ⦃ K ⦄ (id/` (suc x) &/⋯ ⦅ x/t ⦆ₖ)         ≡⟨ &/⋯-& ⦃ Cᵣ ⦃ K ⦄ ⦄ (suc x) ⦅ x/t ⦆ₖ ⟩
              `/id ⦃ K ⦄ (id/` x)                           ≡⟨⟩
              `/id ⦃ K ⦄ (x &ₖ idₖ)                           ∎)
            
            wk-cancels-⦅⦆-⋯  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s′) (x/t : S ∋/⊢[ K ] s) →
                              t ⋯ wkᵣ s ⋯ ⦅ x/t ⦆ₖ ≡ t
            wk-cancels-⦅⦆-⋯ t x/t =
              t ⋯ wkᵣ _ ⋯ ⦅ x/t ⦆ₖ     ≡⟨ ⋯-fusion t (wkᵣ _) ⦅ x/t ⦆ₖ ⟩
              t ⋯ (wkᵣ _ ⨟ₖₖ ⦅ x/t ⦆ₖ)  ≡⟨ cong (t ⋯_) (~-ext (wk-cancels-⦅⦆ x/t)) ⟩
              t ⋯ idₖ                      ≡⟨ ⋯-id t ⟩
              t                           ∎
            
            dist-↑-⦅⦆ :
              ∀  ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
                 ⦃ W₂ : WkKit K₂ ⦄
                 ⦃ C₁ : ComposeKit K₁ K₂ K ⦄ ⦃ C₂ : ComposeKit K₂ K K ⦄
                 (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                 (⦅ x/t ⦆ₖ ⨟[ C₁ ] ϕ) ~ ((ϕ ↑ₖ s) ⨟[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆ₖ)
            dist-↑-⦅⦆ {s = s} ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ x/t ϕ sx x@zero = `/id-injective (
              `/id ⦃ K ⦄ (x &ₖ (⦅ x/t ⦆ₖ ⨟[ C₁ ] ϕ))                ≡⟨⟩
              `/id ⦃ K ⦄ (x/t &/⋯ ϕ)                              ≡⟨⟩
              `/id ⦃ K ⦄ (zero &ₖ ⦅ (x/t &/⋯ ϕ) ⦆ₖ)                 ≡⟨ sym (&/⋯-& ⦃ C₂ ⦄ zero ⦅ (x/t &/⋯ ϕ) ⦆ₖ) ⟩
              `/id ⦃ K ⦄ (id/` ⦃ K₂ ⦄ zero &/⋯ ⦅ (x/t &/⋯ ϕ) ⦆ₖ)   ≡⟨⟩
              `/id ⦃ K ⦄ (x &ₖ ((ϕ ↑ₖ s) ⨟[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆ₖ))  ∎)
            dist-↑-⦅⦆ {s = s} ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ x/t ϕ sx x@(suc y) = `/id-injective (
              `/id (x &ₖ (⦅ x/t ⦆ₖ ⨟[ C₁ ] ϕ))                ≡⟨⟩
              `/id (id/` ⦃ K₁ ⦄ y &/⋯ ϕ)                    ≡⟨ &/⋯-& ⦃ C₁ ⦄ y ϕ ⟩
              `/id (y &ₖ ϕ)                                  ≡⟨ sym (wk-cancels-⦅⦆-⋯ (`/id (y &ₖ ϕ)) (x/t &/⋯ ϕ)) ⟩
              `/id (y &ₖ ϕ) ⋯ wkᵣ s ⋯ ⦅ (x/t &/⋯ ϕ) ⦆ₖ    ≡⟨ cong (_⋯ ⦅ x/t &/⋯ ϕ ⦆ₖ) (wk-`/id s (y &ₖ ϕ)) ⟩
              `/id (wk′ s (y &ₖ ϕ)) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆ₖ         ≡⟨ sym (&/⋯-⋯ (wk′ s (y &ₖ ϕ)) ⦅ (x/t &/⋯ ϕ) ⦆ₖ) ⟩
              `/id (wk′ s (y &ₖ ϕ) &/⋯ ⦅ (x/t &/⋯ ϕ) ⦆ₖ)       ≡⟨⟩
              `/id (x &ₖ ((ϕ ↑ₖ s) ⨟[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆ₖ))  ∎)
            
            dist-↑-⦅⦆-⋯ :
              ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
                ⦃ W₁ : WkKit K₁ ⦄ ⦃ W₂ : WkKit K₂ ⦄
                ⦃ C₁ : ComposeKit K₁ K₂ K ⦄ ⦃ C₂ : ComposeKit K₂ K K ⦄
                (t : (s ∷ S₁) ⊢ s′) (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                t ⋯ ⦅ x/t ⦆ₖ ⋯ ϕ ≡ t ⋯ (ϕ ↑ₖ s) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆ₖ
            dist-↑-⦅⦆-⋯ t x/t ϕ =
              t ⋯ ⦅ x/t ⦆ₖ ⋯ ϕ                   ≡⟨ ⋯-fusion t ⦅ x/t ⦆ₖ ϕ ⟩
              t ⋯ (⦅ x/t ⦆ₖ ⨟ₖₖ ϕ)                ≡⟨ cong (t ⋯_) (~-ext (dist-↑-⦅⦆ x/t ϕ)) ⟩
              t ⋯ ((ϕ ↑ₖ _) ⨟ₖₖ ⦅ (x/t &/⋯ ϕ) ⦆ₖ)  ≡⟨ sym (⋯-fusion t (ϕ ↑ₖ _) ⦅ x/t &/⋯ ϕ ⦆ₖ ) ⟩
              t ⋯ (ϕ ↑ₖ _) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆ₖ     ∎
