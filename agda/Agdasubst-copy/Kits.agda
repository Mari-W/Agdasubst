-- Author: Hannes Saffrich
-- Modified: Marius Weidner
module Kits where

open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃-syntax; proj₁; proj₂)

open import DeBruijn
open import Sorts

data KitTag : Set where
  Ren Sub : KitTag

module KitsWithSort (Sort : SORT) where
    open SortsWithSort Sort 
    open SortsMeta
  
    record Syntax : Set₁ where
      constructor mkSyntax
      field
        _⊢_  : SCOPED
        `_   : S ∋ s → S ⊢ s

        `-injective : ` x₁ ≡ ` x₂ → x₁ ≡ x₂

      f : KitTag → SCOPED_BINDABLE
      f Ren = _∋_
      f Sub = _⊢_

      -- Ax : (tag : KitTag) → (_∋/⊢_ ≡ f tag) → 
      --      (id/` : ∀ {S} {s} → S ∋ s → S ∋/⊢ s)
      --      (`/id : ∀ {S} {s} → S ∋/⊢ s → S ⊢ s)
      --      (wk′ : ∀ {S} {s} s′ → S ∋/⊢ s → (s′ ∷ S) ∋/⊢ s)
      --      → Set 
      record Kit (_∋/⊢_ : SCOPED_BINDABLE) : Set₁ 


      record Kit _∋/⊢_ where
        constructor mkKit
        pattern
        field
          tag             : KitTag
          tag-axiom       : _∋/⊢_ ≡ f tag

          id/`            : ∀ {S} {s} → S ∋ s → S ∋/⊢ s
          `/id            : S ∋/⊢ s → S ⊢ s
          wk′             : ∀ s′ → S ∋/⊢ s → (s′ ∷ S) ∋/⊢ s

          `/`-is-`        : ∀ (x : S ∋ s) → `/id (id/` x) ≡ ` x
          id/`-injective  : id/` x₁ ≡ id/` x₂ → x₁ ≡ x₂
          `/id-injective  : ∀ {x/t₁ x/t₂ : S ∋/⊢ s} →
                              `/id x/t₁ ≡ `/id x/t₂ → x/t₁ ≡ x/t₂
          wk-id/`         : ∀ s′ (x : S ∋ s) →
                              wk′ s′ (id/` x) ≡ id/` (suc x)  

          -- ax              : Ax tag tag-axiom id/` `/id wk′

        opaque 
          import Data.Unit using (⊤; tt)
          all_kit_definitions : Data.Unit.⊤
          all_kit_definitions = Data.Unit.tt

          _→ₖ_ : Scope → Scope → Set
          S₁ →ₖ S₂ = ∀ s → S₁ ∋ s → S₂ ∋/⊢ s

          infixl 8 _&_
          _&_ : S₁ ∋ s → S₁ →ₖ S₂ → S₂ ∋/⊢ s
          x & ϕ = ϕ _ x 

          private
            wkmₖ : ∀ s → S₁ →ₖ S₂ → S₁ →ₖ (s ∷ S₂)
            wkmₖ s ϕ _ x = wk′ s (ϕ _ x)

          _∙_ : S₂ ∋/⊢ s → S₁ →ₖ S₂ → (s ∷ S₁) →ₖ S₂
          (x/t ∙ ϕ) _ zero     = x/t
          (x/t ∙ ϕ) _ (suc x)  = ϕ _ x

          _↑_ : S₁ →ₖ S₂ → ∀ s → (s ∷ S₁) →ₖ (s ∷ S₂)
          ϕ ↑ s = id/` zero ∙ wkmₖ s ϕ

          id : S →ₖ S
          id s x = id/` x 
 
          wk : ∀ {s} → S →ₖ (s ∷ S)
          wk = wkmₖ _ id
        
        ⦅_⦆ : S ∋/⊢ s → (s ∷ S) →ₖ S
        ⦅ x/t ⦆ = x/t ∙ id

        _↑*_ : S₁ →ₖ S₂ → ∀ S → (S ++ S₁) →ₖ (S ++ S₂)
        ϕ ↑* []       = ϕ
        ϕ ↑* (s ∷ S)  = (ϕ ↑* S) ↑ s

        _~_ : (ϕ₁ ϕ₂ : S₁ →ₖ S₂) → Set
        _~_ {S₁} ϕ₁ ϕ₂ = ∀ s (x : S₁ ∋ s) → x & ϕ₁ ≡ x & ϕ₂ 

        postulate
          ~-ext : ∀ {ϕ₁ ϕ₂ : S₁ →ₖ S₂} → ϕ₁ ~ ϕ₂ → ϕ₁ ≡ ϕ₂

        opaque 
          unfolding all_kit_definitions

          id↑~id : (id {S} ↑ s) ~ id {s ∷ S}
          id↑~id s zero    = refl
          id↑~id s (suc x) =
            (id ↑ _) s (suc x) ≡⟨⟩
            wk′ _ (id/` x)        ≡⟨ wk-id/` _ x ⟩
            id/` (suc x)         ≡⟨⟩
            id s (suc x)         ∎

          id↑*~id : ∀ S → (id ↑* S) ~ id {S ++ S′}
          id↑*~id []      sx x = refl
          id↑*~id (s ∷ S) sx x =
            ((id ↑* S) ↑ s) sx x ≡⟨ cong (λ ■ → (■ ↑ s) sx x) (~-ext (id↑*~id S)) ⟩
            (id ↑ s) sx x        ≡⟨ id↑~id sx x ⟩
            id sx x              ∎

      

      -- Ax Ren refl id/` `/id wk′ = 
      --   (λ {S} {s} → id/` {S} {s}) ≡ (λ x → x) ×
      --   (λ {S} {s} → `/id {S} {s}) ≡ `_ ×
      --   (λ {S} {s} → wk′ {S} {s}) ≡ λ s′ x → suc x
      -- Ax Sub refl id/` `/id wk′ = 
      --   (λ {S} {s} → id/` {S} {s}) ≡ `_ ×
      --   (λ {S} {s} → `/id {S} {s}) ≡ (λ x → x) × 
      --   Σ[ _⋯_ ∈ (∀ {S₁ : Scope} {m : Mode} {s : Sort m} {S₂ : Scope} → S₁ ⊢ s → (∀ s → S₁ ∋ s → S₂ ∋ s) → S₂ ⊢ s) ]
      --     Σ[ wkᵣ ∈ ({S : List (Sort Bind)} {s : Sort Bind} (s₁ : Sort Bind) → S ∋ s₁ → (s ∷ S) ∋ s₁) ] 
      --     (λ {S} {s} → wk′ {S} {s}) ≡ λ s′ t → t ⋯ wkᵣ



      _∋/⊢[_]_ : Scope → Kit _∋/⊢_ → BindSort → Set
      _∋/⊢[_]_ {_∋/⊢_} S K s = S ∋/⊢ s

      _–[_]→_ : Scope → Kit _∋/⊢_ → Scope → Set
      S₁ –[ K ]→ S₂ = Kit._→ₖ_ K S₁ S₂

      open Kit ⦃ … ⦄ public hiding (wk)

      record Traversal : Set₁ where
        infixl   5  _⋯_

        field  
          _⋯_    : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
          ⋯-var  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) →
                     (` x) ⋯ ϕ ≡ `/id ⦃ K ⦄ (x & ϕ)
          ⋯-id   : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → (t : S ⊢ s) →
                     t ⋯ id ⦃ K ⦄ ≡ t

        instance
          Kᵣ : Kit _∋_
          Kᵣ = record
            { tag             = Ren
            ; tag-axiom       = refl
            ; id/`            = λ x → x
            ; `/id            = `_
            ; wk′             = λ s′ x → suc x
            ; `/`-is-`        = λ x → refl
            ; id/`-injective  = λ eq → eq 
            ; `/id-injective  = `-injective 
            ; wk-id/`         = λ s′ x → refl 
            -- ; ax              = refl , refl , refl
            } 
        
        postulate
          unique-Kᵣ-instance : (K : Kit _∋_) → K ≡ Kᵣ 
        -- unique-Kᵣ-instance (mkKit Ren refl id/`₁ `/id₁ wk′₁ `/`-is-`₁ id/`-injective₁ `/id-injective₁ wk-id/`₁ (refl , refl , refl)) = {!   !}
        -- unique-Kᵣ-instance (mkKit Sub eq id/`₁ `/id₁ wk′₁ `/`-is-`₁ id/`-injective₁ `/id-injective₁ wk-id/`₁ ax₁) = {!   !}
      

        open Kit Kᵣ public using () renaming 
          (_→ₖ_ to _→ᵣ_; _&_ to _&ᵣ_; _∙_ to _∙ᵣ_; _↑_ to _↑ᵣ_; id to idᵣ; wk to wkᵣ)

        _⋯ᵣ_ : S₁ ⊢ s → S₁ →ᵣ S₂ → S₂ ⊢ s
        t ⋯ᵣ ρ = t ⋯ ρ

        weaken : S ⊢ s → (s′ ∷ S) ⊢ s
        weaken T = _⋯_ ⦃ Kᵣ ⦄ T wkᵣ

        opaque
          unfolding all_kit_definitions
          private 
            Kₛ-wk-id/` : {S : Scope} {s : BindSort} (s′ : BindSort) (x : S ∋ s) →
                        (` x) ⋯ wkᵣ {s = s′} ≡ (` suc x)
            Kₛ-wk-id/` = λ s′ x → ⋯-var x wkᵣ

            -- axₛ : Ax Sub refl `_ (λ t → t) (λ s′ t → t ⋯ wkᵣ)
            -- axₛ = refl , refl , _⋯ᵣ_ , wkᵣ , refl

        instance
          Kₛ : Kit _⊢_
          Kₛ = record
            { tag             = Sub
            ; tag-axiom       = refl
            ; id/`            = `_
            ; `/id            = λ t → t
            ; wk′             = λ s′ t → t ⋯ wkᵣ
            ; `/`-is-`        = λ x → refl
            ; id/`-injective  = `-injective
            ; `/id-injective  = λ eq → eq 
            ; wk-id/`         = Kₛ-wk-id/`
            -- ; ax              = axₛ
            }

        postulate
          unique-Kₛ-instance : (K : Kit _⊢_) → K ≡ Kₛ
        -- unique-Kₛ-instance (mkKit Sub refl id/`₁ `/id₁ wk′₁ `/`-is-`₁ id/`-injective₁ `/id-injective₁ wk-id/`₁ (refl , refl , _ , _ , refl)) = {!   !}
        -- unique-Kₛ-instance (mkKit Ren eq id/`₁ `/id₁ wk′₁ `/`-is-`₁ id/`-injective₁ `/id-injective₁ wk-id/`₁ ax₁) = {!   !}
      

        open Kit Kₛ public using () renaming 
          (_→ₖ_ to _→ₛ_; _&_ to _&ₛ_; _∙_ to _∙ₛ_; _↑_ to _↑ₛ_; id to idₛ)

        module KitsMeta where
          variable 
            T T₁ T₂ T₃ T₄ T′ T₁′ T₂′ T₃′ T₄′ : S ⊢ s
            ρ ρ₁ ρ₂ ρ₃ ρ₄ ρ′ ρ₁′ ρ₂′ ρ₃′ ρ₄′ : S₁ →ᵣ S₂
            σ σ₁ σ₂ σ₃ σ₄ σ′ σ₁′ σ₂′ σ₃′ σ₄′ : S₁ →ₛ S₂

        _⋯ₛ_ : S₁ ⊢ s → S₁ →ₛ S₂ → S₂ ⊢ s
        t ⋯ₛ σ = t ⋯ σ

        _[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
        T [ T′ ] = T ⋯ (T′ ∙ id) 

        record WkKit (K : Kit _∋/⊢_): Set₁ where
          private instance _ = K
          field
            wk-`/id  : ∀ s (x/t : S ∋/⊢ s′) → `/id x/t ⋯ᵣ wkᵣ ≡ `/id (wk′ s x/t)

        opaque
          unfolding all_kit_definitions
          wk-`/id-Wᵣ : (s : BindSort) (x : S ∋ s′) → ((` x) ⋯ᵣ (wkᵣ {s = s})) ≡ (` suc x)
          wk-`/id-Wᵣ = λ _ x/t → ⋯-var x/t wkᵣ 
       
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
                         wk′ s′ (x/t &/⋯ ϕ) ≡ wk′ s′ x/t &/⋯ (ϕ ↑ s′)
      
          opaque
            unfolding all_kit_definitions

            import Data.Unit using (⊤; tt)
            all_kit_and_compose_definitions : Data.Unit.⊤
            all_kit_and_compose_definitions = Data.Unit.tt

            _⨟_ : S₁ –[ K₁ ]→ S₂ → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₁⊔K₂ ]→ S₃
            (ϕ₁ ⨟ ϕ₂) _ x = (x & ϕ₁) &/⋯ ϕ₂ 

          opaque
            unfolding all_kit_and_compose_definitions

            &/⋯-& : ∀ (x : S₁ ∋ s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                    `/id (id/` ⦃ K₁ ⦄ x &/⋯ ϕ) ≡ `/id (x & ϕ)
            &/⋯-& x ϕ = 
              `/id (id/` x &/⋯ ϕ)       ≡⟨ &/⋯-⋯ (id/` x) ϕ ⟩
              `/id ⦃ K₁ ⦄ (id/` x) ⋯ ϕ  ≡⟨ cong (_⋯ ϕ) (`/`-is-` ⦃ K₁ ⦄ x) ⟩
              ` x ⋯ ϕ                   ≡⟨ ⋯-var ⦃ K₂ ⦄ x ϕ ⟩
              `/id ⦃ K₂ ⦄  (x & ϕ)      ∎

            dist-↑-⨟  : ∀ s (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                       ((ϕ₁ ⨟ ϕ₂) ↑ s) ~ ((ϕ₁ ↑ s) ⨟ (ϕ₂ ↑ s))
            dist-↑-⨟ s ϕ₁ ϕ₂ s₁ x@zero = `/id-injective (   
              `/id ⦃ K₁⊔K₂ ⦄ (x & ((ϕ₁ ⨟ ϕ₂) ↑ s))         ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (id/` zero)                      ≡⟨ `/`-is-` ⦃ K₁⊔K₂ ⦄ zero ⟩
              ` zero                                           ≡⟨ sym (`/`-is-` ⦃ K₂ ⦄ zero) ⟩
              `/id ⦃ K₂ ⦄ (id/` zero)                         ≡⟨⟩
              `/id ⦃ K₂ ⦄ (zero & (ϕ₂ ↑ s))                 ≡⟨ sym (&/⋯-& (id/` zero) (ϕ₂ ↑ s)) ⟩
              `/id ⦃ K₁⊔K₂ ⦄ (id/` zero &/⋯ (ϕ₂ ↑ s))        ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (x & (ϕ₁ ↑ s) &/⋯ (ϕ₂ ↑ s))   ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (x & ((ϕ₁ ↑ s) ⨟ (ϕ₂ ↑ s)))  ∎
              )
            dist-↑-⨟ s ϕ₁ ϕ₂ s₁ x@(suc y) = `/id-injective (
              `/id ⦃ K₁⊔K₂ ⦄ (x & ((ϕ₁ ⨟ ϕ₂) ↑ s))         ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (wk′ _ (y & (ϕ₁ ⨟ ϕ₂)))        ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (wk′ _ (y & ϕ₁ &/⋯ ϕ₂))          ≡⟨ cong `/id (&/⋯-wk-↑ (y & ϕ₁) ϕ₂) ⟩
              `/id ⦃ K₁⊔K₂ ⦄ (wk′ _ (y & ϕ₁) &/⋯ (ϕ₂ ↑ s))   ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (x & (ϕ₁ ↑ s) &/⋯ (ϕ₂ ↑ s))   ≡⟨⟩
              `/id ⦃ K₁⊔K₂ ⦄ (x & ((ϕ₁ ↑ s) ⨟ (ϕ₂ ↑ s)))  ∎
              )

            dist-↑*-⨟  : ∀ S (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                         ((ϕ₁ ⨟ ϕ₂) ↑* S) ~ ((ϕ₁ ↑* S) ⨟ (ϕ₂ ↑* S))
            dist-↑*-⨟ []      ϕ₁ ϕ₂ sx x = refl
            dist-↑*-⨟ (s ∷ S) ϕ₁ ϕ₂ sx x =
              ((ϕ₁ ⨟ ϕ₂) ↑* (s ∷ S)) sx x                 ≡⟨⟩
              (((ϕ₁ ⨟ ϕ₂) ↑* S) ↑ s) sx x                ≡⟨ cong (λ ■ → (■ ↑ s) sx x) (~-ext (dist-↑*-⨟ S ϕ₁ ϕ₂)) ⟩
              (((ϕ₁ ↑* S) ⨟ (ϕ₂ ↑* S)) ↑ s) sx x        ≡⟨ dist-↑-⨟ s (ϕ₁ ↑* S) (ϕ₂ ↑* S) sx x ⟩
              (((ϕ₁ ↑* S) ↑ s) ⨟ ((ϕ₂ ↑* S) ↑ s)) sx x ≡⟨⟩
              ((ϕ₁ ↑* (s ∷ S)) ⨟ (ϕ₂ ↑* (s ∷ S))) sx x ∎
        
        _⨟[_]_  : ∀ {K₁ : Kit _∋/⊢₁_} {K₂ : Kit _∋/⊢₂_} {K₁⊔K₂ : Kit _∋/⊢_} →
                  S₁ –[ K₁ ]→ S₂ → ComposeKit K₁ K₂ K₁⊔K₂ →
                  S₂ –[ K₂ ]→ S₃ → S₁ –[ K₁⊔K₂ ]→ S₃
        ϕ₁ ⨟[ C ] ϕ₂ = ϕ₁ ⨟ ϕ₂ where open ComposeKit C

        open ComposeKit ⦃ … ⦄ public

        record ComposeTraversal : Set₁ where
          field
            ⋯-fusion : ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
                       ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
                       (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
                       (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ⨟ ϕ₂)
          
          opaque
            unfolding all_kit_and_compose_definitions
          
            ↑-wk  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄
                    ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit Kᵣ K K ⦄ 
                    (ϕ : S₁ –[ K ]→ S₂) s → 
                    (ϕ ⨟ wkᵣ) ~ (wkᵣ ⨟ (ϕ ↑ s))
            ↑-wk {S₁} {S₂} ϕ s sx x = `/id-injective (
              `/id ((ϕ ⨟ wkᵣ) sx x)         ≡⟨⟩
              `/id (x & ϕ &/⋯ wkᵣ)           ≡⟨ &/⋯-⋯ (x & ϕ) (wkᵣ) ⟩
              `/id (`/id (x & ϕ) ⋯ wkᵣ)      ≡⟨ wk-`/id s (x & ϕ) ⟩
              `/id (suc x & (ϕ ↑ s))          ≡⟨ sym (&/⋯-& (suc x) (ϕ ↑ s)) ⟩
              `/id (suc x &/⋯ (ϕ ↑ s))         ≡⟨⟩
              `/id (x & wkᵣ &/⋯ (ϕ ↑ s))    ≡⟨⟩
              `/id ((wkᵣ ⨟ (ϕ ↑ s)) sx x)  ∎)
            
            ⋯-↑-wk  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄
                      ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit Kᵣ K K ⦄ 
                      (t : S₁ ⊢ s) (ϕ : S₁ –[ K ]→ S₂) s′ → 
                      t ⋯ ϕ ⋯ wkᵣ ≡ t ⋯ wkᵣ  ⋯ (ϕ ↑ s′)
            ⋯-↑-wk t ϕ s =
              t ⋯ ϕ ⋯ wkᵣ           ≡⟨ ⋯-fusion t ϕ (wkᵣ) ⟩
              t ⋯ (ϕ ⨟ wkᵣ)        ≡⟨ cong (t ⋯_) (~-ext (↑-wk ϕ s)) ⟩
              t ⋯ (wkᵣ ⨟ (ϕ ↑ s))  ≡⟨ sym (⋯-fusion t (wkᵣ) (ϕ ↑ s)) ⟩
              t ⋯ wkᵣ ⋯ (ϕ ↑ s)     ∎

            Cᵣ-&/⋯-wk-↑  : ⦃ K₂ : Kit _∋/⊢_ ⦄ (x/t : S₁ ∋/⊢[ Kᵣ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                           Kit.wk′ K₂ s′ ((K₂ Kit.& x/t) ϕ) ≡ (K₂ Kit.& suc x/t) (ϕ ↑ s′)
            Cᵣ-&/⋯-wk-↑ _ _ = refl

          instance
            Cᵣ : ⦃ K₂ : Kit _∋/⊢_ ⦄ → ComposeKit Kᵣ K₂ K₂
            Cᵣ = record
                { _&/⋯_     = _&_
                ; &/⋯-⋯     = λ x ϕ → sym (⋯-var x ϕ)
                ; &/⋯-wk-↑  = Cᵣ-&/⋯-wk-↑ }
                  
            Cₛ  : ⦃ K₂ : Kit _∋/⊢_ ⦄ ⦃ W₂ : WkKit K₂ ⦄
                  ⦃ C : ComposeKit K₂ Kᵣ K₂ ⦄ → ComposeKit Kₛ K₂ Kₛ
            Cₛ ⦃ C = C ⦄ = record
                { _&/⋯_     = _⋯_
                ; &/⋯-⋯     = λ t ϕ → refl
                ; &/⋯-wk-↑  = λ t ϕ → ⋯-↑-wk t ϕ _ }
          
          open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃-syntax; proj₁; proj₂)
          open import Data.Bool 

          Cᵣᵣ : ComposeKit Kᵣ Kᵣ Kᵣ
          Cᵣᵣ = Cᵣ
          Cᵣₛ : ComposeKit Kᵣ Kₛ Kₛ
          Cᵣₛ = Cᵣ
          Cₛᵣ : ComposeKit Kₛ Kᵣ Kₛ
          Cₛᵣ = Cₛ
          Cₛₛ : ComposeKit Kₛ Kₛ Kₛ
          Cₛₛ = Cₛ

          composeKit : (K₁ : Kit _∋/⊢₁_) (K₂ : Kit _∋/⊢₂_) → ∃[ _∋/⊢_ ] Σ[ K₁⊔K₂ ∈ Kit _∋/⊢_ ] ComposeKit K₁ K₂ K₁⊔K₂
          composeKit K₁@(mkKit Ren refl _ _ _ _ _ _ _) K₂@(mkKit Ren refl _ _ _ _ _ _ _) 
            rewrite unique-Kᵣ-instance K₁ | unique-Kᵣ-instance K₂ = _ , _ , Cᵣᵣ
          composeKit K₁@(mkKit Ren refl _ _ _ _ _ _ _) K₂@(mkKit Sub refl _ _ _ _ _ _ _) 
            rewrite unique-Kᵣ-instance K₁ | unique-Kₛ-instance K₂ = _ , _ , Cᵣₛ
          composeKit K₁@(mkKit Sub refl _ _ _ _ _ _ _) K₂@(mkKit Ren refl i_ _ _ _ _ _ _) 
            rewrite unique-Kₛ-instance K₁ | unique-Kᵣ-instance K₂ = _ , _ , Cₛᵣ
          composeKit K₁@(mkKit Sub refl _ _ _ _ _ _ _) K₂@(mkKit Sub refl _ _ _ _ _ _ _) 
            rewrite unique-Kₛ-instance K₁ | unique-Kₛ-instance K₂ = _ , _ , Cₛₛ

          opaque
            unfolding all_kit_and_compose_definitions
          
            wk-cancels-⦅⦆  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (x/t : S ∋/⊢[ K ] s) →
                            (wkᵣ ⨟[ Cᵣ ] ⦅ x/t ⦆) ~ id
            wk-cancels-⦅⦆ ⦃ K ⦄ x/t sx x = `/id-injective (
              `/id ⦃ K ⦄ (x & (wkᵣ ⨟[ Cᵣ ] ⦅ x/t ⦆))  ≡⟨⟩
              `/id ⦃ K ⦄ (id/` (suc x) &/⋯ ⦅ x/t ⦆)         ≡⟨ &/⋯-& ⦃ Cᵣ ⦃ K ⦄ ⦄ (suc x) ⦅ x/t ⦆ ⟩
              `/id ⦃ K ⦄ (id/` x)                           ≡⟨⟩
              `/id ⦃ K ⦄ (x & id)                           ∎)
            
            wk-cancels-⦅⦆-⋯  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s′) (x/t : S ∋/⊢[ K ] s) →
                              t ⋯ wkᵣ ⋯ ⦅ x/t ⦆ ≡ t
            wk-cancels-⦅⦆-⋯ t x/t =
              t ⋯ wkᵣ ⋯ ⦅ x/t ⦆     ≡⟨ ⋯-fusion t (wkᵣ) ⦅ x/t ⦆ ⟩
              t ⋯ (wkᵣ ⨟ ⦅ x/t ⦆)  ≡⟨ cong (t ⋯_) (~-ext (wk-cancels-⦅⦆ x/t)) ⟩
              t ⋯ id                      ≡⟨ ⋯-id t ⟩
              t                           ∎
            
            dist-↑-⦅⦆ :
              ∀  ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
                 ⦃ W₂ : WkKit K₂ ⦄
                 ⦃ C₁ : ComposeKit K₁ K₂ K ⦄ ⦃ C₂ : ComposeKit K₂ K K ⦄
                 (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                 (⦅ x/t ⦆ ⨟[ C₁ ] ϕ) ~ ((ϕ ↑ s) ⨟[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆)
            dist-↑-⦅⦆ {s = s} ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ x/t ϕ sx x@zero = `/id-injective (
              `/id ⦃ K ⦄ (x & (⦅ x/t ⦆ ⨟[ C₁ ] ϕ))                ≡⟨⟩
              `/id ⦃ K ⦄ (x/t &/⋯ ϕ)                              ≡⟨⟩
              `/id ⦃ K ⦄ (zero & ⦅ (x/t &/⋯ ϕ) ⦆)                 ≡⟨ sym (&/⋯-& ⦃ C₂ ⦄ zero ⦅ (x/t &/⋯ ϕ) ⦆) ⟩
              `/id ⦃ K ⦄ (id/` ⦃ K₂ ⦄ zero &/⋯ ⦅ (x/t &/⋯ ϕ) ⦆)   ≡⟨⟩
              `/id ⦃ K ⦄ (x & ((ϕ ↑ s) ⨟[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆))  ∎)
            dist-↑-⦅⦆ {s = s} ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ x/t ϕ sx x@(suc y) = `/id-injective (
              `/id (x & (⦅ x/t ⦆ ⨟[ C₁ ] ϕ))                ≡⟨⟩
              `/id (id/` ⦃ K₁ ⦄ y &/⋯ ϕ)                    ≡⟨ &/⋯-& ⦃ C₁ ⦄ y ϕ ⟩
              `/id (y & ϕ)                                  ≡⟨ sym (wk-cancels-⦅⦆-⋯ (`/id (y & ϕ)) (x/t &/⋯ ϕ)) ⟩
              `/id (y & ϕ) ⋯ wkᵣ ⋯ ⦅ (x/t &/⋯ ϕ) ⦆    ≡⟨ cong (_⋯ ⦅ x/t &/⋯ ϕ ⦆) (wk-`/id s (y & ϕ)) ⟩
              `/id (wk′ s (y & ϕ)) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆         ≡⟨ sym (&/⋯-⋯ (wk′ s (y & ϕ)) ⦅ (x/t &/⋯ ϕ) ⦆) ⟩
              `/id (wk′ s (y & ϕ) &/⋯ ⦅ (x/t &/⋯ ϕ) ⦆)       ≡⟨⟩
              `/id (x & ((ϕ ↑ s) ⨟[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆))  ∎)
            
            dist-↑-⦅⦆-⋯ :
              ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
                ⦃ W₁ : WkKit K₁ ⦄ ⦃ W₂ : WkKit K₂ ⦄
                ⦃ C₁ : ComposeKit K₁ K₂ K ⦄ ⦃ C₂ : ComposeKit K₂ K K ⦄
                (t : (s ∷ S₁) ⊢ s′) (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ s) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆
            dist-↑-⦅⦆-⋯ t x/t ϕ =
              t ⋯ ⦅ x/t ⦆ ⋯ ϕ                   ≡⟨ ⋯-fusion t ⦅ x/t ⦆ ϕ ⟩
              t ⋯ (⦅ x/t ⦆ ⨟ ϕ)                ≡⟨ cong (t ⋯_) (~-ext (dist-↑-⦅⦆ x/t ϕ)) ⟩
              t ⋯ ((ϕ ↑ _) ⨟ ⦅ (x/t &/⋯ ϕ) ⦆)  ≡⟨ sym (⋯-fusion t (ϕ ↑ _) ⦅ x/t &/⋯ ϕ ⦆ ) ⟩
              t ⋯ (ϕ ↑ _) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆     ∎
