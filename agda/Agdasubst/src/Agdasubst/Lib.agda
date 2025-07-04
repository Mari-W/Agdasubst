-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --experimental-lazy-instances #-}
module Agdasubst.Lib where

open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim) 

open import Agdasubst.Common

module KitsWithSort (Sort : SORT) where
    open CommonWithSort Sort  
    open SortsMeta 
  
    record Syntax : Set₁ where
      constructor mkSyntax
      field 
        _⊢_  : SCOPED
        `_   : S ∋ s → S ⊢ s

        `-injective : ` x₁ ≡ ` x₂ → x₁ ≡ x₂ 

      unwrap : Tag → SCOPED_BINDABLE
      unwrap Ren = _∋_
      unwrap Sub = _⊢_ 

      -- prevents users from outside the library to construct more Kit and ComposeKit instances
      -- thus: the unique–Kᵣ, unique–Kₛ, unique–Cᵣ and unique–Cₛ postulates 
      -- cannot do any harm outside this file 
      private data Lock : Set where
        unlock : Lock 

      record Kit (k : Tag) : Set₁ where
        _∋/⊢_ = unwrap k
        field
          id/`            : ∀ {S} {s} → S ∋ s → S ∋/⊢ s
          `/id            : S ∋/⊢ s → S ⊢ s
          wk′             : ∀ s′ → S ∋/⊢ s → (s′ ∷ S) ∋/⊢ s

          `/`-is-`        : ∀ (x : S ∋ s) → `/id (id/` x) ≡ ` x
          id/`-injective  : id/` x₁ ≡ id/` x₂ → x₁ ≡ x₂
          `/id-injective  : ∀ {x/t₁ x/t₂ : S ∋/⊢ s} →
                              `/id x/t₁ ≡ `/id x/t₂ → x/t₁ ≡ x/t₂
          wk-id/`         : ∀ s′ (x : S ∋ s) →
                              wk′ s′ (id/` x) ≡ id/` (suc x)  
          lock            : Lock

        opaque 
          import Data.Unit using (⊤; tt)
          all_kit_definitions : Data.Unit.⊤
          all_kit_definitions = Data.Unit.tt

          _→ₖ_ : Scope → Scope → Set
          S₁ →ₖ S₂ = ∀ s → S₁ ∋ s → S₂ ∋/⊢ s

          infixl 8 _&_
          _&_ : S₁ ∋ s → S₁ →ₖ S₂ → S₂ ∋/⊢ s
          x & ϕ = ϕ _ x 

          wkmₖ : ∀ s → S₁ →ₖ S₂ → S₁ →ₖ (s ∷ S₂)
          wkmₖ s ϕ _ x = wk′ s (ϕ _ x)

          _∙_ : S₂ ∋/⊢ s → S₁ →ₖ S₂ → (s ∷ S₁) →ₖ S₂
          (x/t ∙ ϕ) _ zero     = x/t
          (x/t ∙ ϕ) _ (suc x)  = ϕ _ x
 
          id : S →ₖ S
          id s x = id/` x 

          wk : ∀ {s} → S →ₖ (s ∷ S)
          wk = wkmₖ _ id
        
        ⦅_⦆ : S ∋/⊢ s → (s ∷ S) →ₖ S
        ⦅ x/t ⦆ = x/t ∙ id

        _↑ₖ_ : S₁ →ₖ S₂ → ∀ s → (s ∷ S₁) →ₖ (s ∷ S₂)
        ϕ ↑ₖ s = id/` zero ∙ wkmₖ s ϕ

        _↑ₖ⋆_ : S₁ →ₖ S₂ → ∀ S → (S ++ S₁) →ₖ (S ++ S₂)
        ϕ ↑ₖ⋆ []       = ϕ
        ϕ ↑ₖ⋆ (s ∷ S)  = (ϕ ↑ₖ⋆ S) ↑ₖ s 

        _~_ : (ϕ₁ ϕ₂ : S₁ →ₖ S₂) → Set
        _~_ {S₁} ϕ₁ ϕ₂ = ∀ s (x : S₁ ∋ s) → x & ϕ₁ ≡ x & ϕ₂ 

        postulate 
          ~-ext : ∀ {ϕ₁ ϕ₂ : S₁ →ₖ S₂} → ϕ₁ ~ ϕ₂ → ϕ₁ ≡ ϕ₂ 

        opaque 
          unfolding all_kit_definitions

          id↑ₖ~id : (id {S} ↑ₖ s) ~ id {s ∷ S}
          id↑ₖ~id s zero    = refl
          id↑ₖ~id s (suc x) =
            (id ↑ₖ _) s (suc x) ≡⟨⟩
            wk′ _ (id/` x)        ≡⟨ wk-id/` _ x ⟩
            id/` (suc x)         ≡⟨⟩
            id s (suc x)         ∎
          
          id↑≡id :  _∙_ {S₁ = S} (id/` zero) (wkmₖ s id) ≡ id
          id↑≡id = ~-ext id↑ₖ~id

          id↑ₖ⋆~id : ∀ S → (id ↑ₖ⋆ S) ~ id {S ++ S′}
          id↑ₖ⋆~id []      sx x = refl
          id↑ₖ⋆~id (s ∷ S) sx x =
            ((id ↑ₖ⋆ S) ↑ₖ s) sx x ≡⟨ cong (λ ■ → (■ ↑ₖ s) sx x) (~-ext (id↑ₖ⋆~id S)) ⟩
            (id ↑ₖ s) sx x        ≡⟨ id↑ₖ~id sx x ⟩
            id sx x              ∎
          
          id↑⋆≡id : ∀ S → (id ↑ₖ⋆ S) ≡ id {S ++ S′}
          id↑⋆≡id S = ~-ext (id↑ₖ⋆~id S)

          ⋯-id-` : `/id (x & id) ≡ ` x
          ⋯-id-` {x = x} = `/`-is-`  x

      _∋/⊢[_]_ : Scope → Kit k → BindSort → Set
      _∋/⊢[_]_ S K s = Kit._∋/⊢_ K S s
 
      _–[_]→_ : Scope → Kit k → Scope → Set
      S₁ –[ K ]→ S₂ = Kit._→ₖ_ K S₁ S₂
      
      open Kit {{...}} public  
      
      opaque
        unfolding all_kit_definitions

        id-def : {{K : Kit k}} (x : S ∋ s) → x & (id {{K}}) ≡ id/` x
        id-def _ = refl

        ∙-def₁ : {{K : Kit k}} (x/t : S₂ ∋/⊢ s) (ϕ : S₁ –[ K ]→ S₂) → zero & (x/t ∙ ϕ) ≡ x/t
        ∙-def₁ _ _ = refl

        ∙-def₂ : {{K : Kit k}} (x/t : S₂ ∋/⊢ s) (x′ : S₁ ∋ s′) (ϕ : S₁ –[ K ]→ S₂) → suc x′ & (x/t ∙ ϕ) ≡ x′ & ϕ
        ∙-def₂ _ _ _ = refl

        wk-def : {{K : Kit k}} (x : S ∋ s) → x & (wk {s = s′}) ≡ id/` (suc x)
        wk-def = wk-id/` _

      -- opaque
      --   unfolding all_kit_definitions
      --   ⋯id-x : ?

      record Traversal : Set₁ where
        constructor mkTraversal
        infixl   5  _⋯_
        field  
          _⋯_    : ∀ {{K : Kit k}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
          ⋯-id   : ∀ {{K : Kit k}} → (t : S ⊢ s) →
                     t ⋯ id {{K}} ≡ t
          ⋯-var  : ∀ {{K : Kit k}} → (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) →
                     (` x) ⋯ ϕ ≡ `/id {{K}} (x & ϕ)
        instance
          Kᵣ : Kit Ren
          Kᵣ = record
            { id/`            = λ x → x
            ; `/id            = `_
            ; wk′             = λ s′ x → suc x
            ; `/`-is-`        = λ x → refl
            ; id/`-injective  = λ eq → eq 
            ; `/id-injective  = `-injective  
            ; wk-id/`         = λ s′ x → refl 
            ; lock            = unlock
            } 
        
        postulate
          unique–Kᵣ : (K : Kit Ren) → Kᵣ ≡ K
      
        open Kit Kᵣ public using () renaming 
          (_→ₖ_ to _→ᵣ_; _&_ to _&ᵣ_; _∙_ to _∙ᵣ_; id to idᵣ; wk to wkᵣ; _↑ₖ_ to _↑ᵣ_; _↑ₖ⋆_ to _↑ᵣ⋆_)

        _⋯ᵣ_ : S₁ ⊢ s → S₁ →ᵣ S₂ → S₂ ⊢ s
        t ⋯ᵣ ρ = t ⋯ ρ

        weaken : S ⊢ s → (s′ ∷ S) ⊢ s
        weaken T = T ⋯ wkᵣ

        opaque
          unfolding all_kit_definitions
          private 
            Kₛ-wk-id/` : {S : Scope} {s : BindSort} (s′ : BindSort) (x : S ∋ s) →
                        (` x) ⋯ wkᵣ {s = s′} ≡ (` suc x)
            Kₛ-wk-id/` = λ s′ x → ⋯-var x wkᵣ

        instance
          Kₛ : Kit Sub
          Kₛ = record
            { id/`            = `_
            ; `/id            = λ t → t
            ; wk′             = λ s′ t → t ⋯ wkᵣ
            ; `/`-is-`        = λ x → refl
            ; id/`-injective  = `-injective
            ; `/id-injective  = λ eq → eq 
            ; wk-id/`         = Kₛ-wk-id/`
            ; lock            = unlock
            }

        postulate
          unique–Kₛ : (K : Kit Sub) → Kₛ ≡ K

        f : (k : Tag) → Kit k   
        f Ren = Kᵣ
        f Sub = Kₛ

        unique : (K : Kit k) → K ≡ f k 
        unique {Ren} K = sym (unique–Kᵣ K)
        unique {Sub} K = sym (unique–Kₛ K)

        open Kit Kₛ public using () renaming 
          (_→ₖ_ to _→ₛ_; _&_ to _&ₛ_; _∙_ to _∙ₛ_; id to idₛ; _↑ₖ_ to _↑ₛ_; _↑ₖ⋆_ to _↑ₛ⋆_)

        _⋯ₛ_ : S₁ ⊢ s → S₁ →ₛ S₂ → S₂ ⊢ s
        t ⋯ₛ σ = t ⋯ σ 

        _[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
        T [ T′ ] = T ⋯ (T′ ∙ id) 

        
        _⊔′_ : Tag → Tag → Tag
        Ren ⊔′ Ren = Ren
        Ren ⊔′ Sub = Sub
        Sub ⊔′ Ren = Sub
        Sub ⊔′ Sub = Sub

        ⊔′-law₀ : ∀ k → k ⊔′ k ≡ k 
        ⊔′-law₀ Ren = refl
        ⊔′-law₀ Sub = refl 

        ⊔′-law₁ : ∀ k → k ⊔′ Ren ≡ k 
        ⊔′-law₁ Ren = refl 
        ⊔′-law₁ Sub = refl 

        ⊔′-law₂ : ∀ k → Ren ⊔′ k ≡ k
        ⊔′-law₂ Ren = refl 
        ⊔′-law₂ Sub = refl 

        ⊔′-law₃ : ∀ k → k ⊔′ Sub ≡ Sub
        ⊔′-law₃ Ren = refl 
        ⊔′-law₃ Sub = refl  

        ⊔′-law₄ : ∀ k → Sub ⊔′ k ≡ Sub
        ⊔′-law₄ Ren = refl 
        ⊔′-law₄ Sub = refl  

        ⊔′-law₅ : ∀ k₁ k₂ k₃ →  (k₁ ⊔′ k₂) ⊔′ k₃ ≡ k₁ ⊔′ (k₂ ⊔′ k₃)
        ⊔′-law₅ Ren Ren Ren = refl
        ⊔′-law₅ Ren Ren Sub = refl
        ⊔′-law₅ Ren Sub Ren = refl
        ⊔′-law₅ Ren Sub Sub = refl
        ⊔′-law₅ Sub Ren Ren = refl
        ⊔′-law₅ Sub Ren Sub = refl
        ⊔′-law₅ Sub Sub Ren = refl
        ⊔′-law₅ Sub Sub Sub = refl
        
        {-# REWRITE ⊔′-law₀ ⊔′-law₁ ⊔′-law₂ ⊔′-law₃ ⊔′-law₄ ⊔′-law₅ #-}

        _⊔_ : (K₁ : Kit k₁) (K₂ : Kit k₂) → Kit (k₁ ⊔′ k₂)
        _⊔_ {Ren} {Ren} K₁ K₂ = Kᵣ
        _⊔_ {Ren} {Sub} K₁ K₂ = Kₛ
        _⊔_ {Sub} {Ren} K₁ K₂ = Kₛ
        _⊔_ {Sub} {Sub} K₁ K₂ = Kₛ

        ⊔-law₀ : {{K : Kit k}} → (K ⊔ K) ≡ K
        ⊔-law₀ {Ren} {{K}} = unique–Kᵣ K
        ⊔-law₀ {Sub} {{K}} = unique–Kₛ K
           
        ⊔-law₁ : {{K : Kit k}} → K ⊔ Kᵣ ≡ K 
        ⊔-law₁ {Ren} {{K}} = unique–Kᵣ K 
        ⊔-law₁ {Sub} {{K}} = unique–Kₛ K 

        ⊔-law₂ : {{K : Kit k}} → Kᵣ ⊔ K ≡ K  
        ⊔-law₂ {Ren} {{K}} = unique–Kᵣ K
        ⊔-law₂ {Sub} {{K}} = unique–Kₛ K

        ⊔-law₃ : {{K : Kit k}} → K ⊔ Kₛ ≡ Kₛ
        ⊔-law₃ {Ren} = refl
        ⊔-law₃ {Sub} = refl

        ⊔-law₄ : {{K : Kit k}} → Kₛ ⊔ K ≡ Kₛ
        ⊔-law₄ {Ren} = refl
        ⊔-law₄ {Sub} = refl

        ⊔-law₅ : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} → 
          (K₁ ⊔ K₂) ⊔ K₃ ≡ K₁ ⊔ (K₂ ⊔ K₃)
        ⊔-law₅ {Ren} {Ren} {Ren} = refl
        ⊔-law₅ {Ren} {Ren} {Sub} = refl 
        ⊔-law₅ {Ren} {Sub} {Ren} = refl
        ⊔-law₅ {Ren} {Sub} {Sub} = refl
        ⊔-law₅ {Sub} {Ren} {Ren} = refl
        ⊔-law₅ {Sub} {Ren} {Sub} = refl
        ⊔-law₅ {Sub} {Sub} {Ren} = refl 
        ⊔-law₅ {Sub} {Sub} {Sub} = refl
 
        {-# REWRITE ⊔-law₀ ⊔-law₁ ⊔-law₂ ⊔-law₃ ⊔-law₄ ⊔-law₅ #-}

        module KitsMeta where
          variable 
            T T₁ T₂ T₃ T₄ T′ T₁′ T₂′ T₃′ T₄′ : S ⊢ s
            ρ ρ₁ ρ₂ ρ₃ ρ₄ ρ′ ρ₁′ ρ₂′ ρ₃′ ρ₄′ : S₁ →ᵣ S₂
            σ σ₁ σ₂ σ₃ σ₄ σ′ σ₁′ σ₂′ σ₃′ σ₄′ : S₁ →ₛ S₂

        record WkKit (K : Kit k): Set₁ where 
          private instance _ = K
          field
            wk-`/id  : ∀ s (x/t : Kit._∋/⊢_ K S s′) → `/id x/t ⋯ᵣ wkᵣ ≡ `/id (wk′ s x/t)

        open WkKit {{...}} public

        opaque
          unfolding all_kit_definitions
          wk-`/id-Wᵣ : (s : BindSort) (x : S ∋ s′) → ((` x) ⋯ᵣ (wkᵣ {s = s})) ≡ (` suc x)
          wk-`/id-Wᵣ = λ _ x/t → ⋯-var x/t wkᵣ 
        
        Wᵣ : WkKit Kᵣ
        Wᵣ = record { wk-`/id = wk-`/id-Wᵣ }

        Wₛ : WkKit Kₛ
        Wₛ = record { wk-`/id = λ s x/t → refl } 
        
        instance
          wkKit : {{K : Kit k}} → WkKit K
          wkKit {Ren} {{K}} = subst WkKit (unique–Kᵣ K) Wᵣ 
          wkKit {Sub} {{K}} = subst WkKit (unique–Kₛ K) Wₛ 

        record ComposeKit (K₁ : Kit k₁) (K₂ : Kit k₂) (K₃ : Kit k₃) : Set₁ where

          private instance _ = K₁; _ = K₂; _ = K₃

          infixl 8 _&/⋯′_
          field
            _&/⋯′_    : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₃ ] s 
           
            &/⋯-⋯     : (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                        `/id x/t ⋯ ϕ ≡ `/id (x/t &/⋯′ ϕ)
            &/⋯-wk-↑ₖ : (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                       wk′ s′ (x/t &/⋯′ ϕ) ≡ wk′ s′ x/t &/⋯′ (ϕ ↑ₖ s′) 
            lock      : Lock

          opaque
            unfolding all_kit_definitions
 
            import Data.Unit 
            all_kit_and_compose_definitions : Data.Unit.⊤
            all_kit_and_compose_definitions = Data.Unit.tt 

            infixl 8 _&/⋯_
            _&/⋯_ : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₃ ] s 
            _&/⋯_ = _&/⋯′_
            
            _;_ : S₁ –[ K₁ ]→ S₂ → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₃ ]→ S₃
            (ϕ₁ ; ϕ₂) _ x = (x & ϕ₁) &/⋯ ϕ₂ 
 
          opaque
            unfolding all_kit_and_compose_definitions
  
            &/⋯-& : ∀ (x : S₁ ∋ s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                    `/id (id/` {{K₁}} x &/⋯ ϕ) ≡ `/id (x & ϕ)
            &/⋯-& x ϕ = 
              `/id (id/` x &/⋯ ϕ)       ≡⟨ sym (&/⋯-⋯ (id/` x) ϕ) ⟩
              `/id {{K₁}} (id/` x) ⋯ ϕ  ≡⟨ cong (_⋯ ϕ) (`/`-is-` {{K₁}} x) ⟩
              ` x ⋯ ϕ                   ≡⟨ ⋯-var {{K₂}} x ϕ ⟩
              `/id {{K₂}}  (x & ϕ)      ∎

            dist-↑ₖ-;  : ∀ s (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                      ((ϕ₁ ; ϕ₂) ↑ₖ s) ~ ((ϕ₁ ↑ₖ s) ; (ϕ₂ ↑ₖ s))
            dist-↑ₖ-; s ϕ₁ ϕ₂ s₁ x@zero = `/id-injective (   
              `/id (x & ((ϕ₁ ; ϕ₂) ↑ₖ s)) ≡⟨⟩
              `/id {{K₃}} (id/` zero)     ≡⟨ `/`-is-` {{K₃}} zero ⟩
              ` zero                                        ≡⟨ sym (`/`-is-` {{K₂}} zero) ⟩
              `/id {{K₂}} (id/` zero)                       ≡⟨⟩
              `/id {{K₂}} (zero & (ϕ₂ ↑ₖ s))                 ≡⟨ sym (&/⋯-& (id/` zero) (ϕ₂ ↑ₖ s)) ⟩
              `/id (id/` zero &/⋯ (ϕ₂ ↑ₖ s))     ≡⟨⟩
              `/id (x & (ϕ₁ ↑ₖ s) &/⋯ (ϕ₂ ↑ₖ s))  ≡⟨⟩
              `/id (x & ((ϕ₁ ↑ₖ s) ; (ϕ₂ ↑ₖ s)))  ∎
              )
            dist-↑ₖ-; s ϕ₁ ϕ₂ s₁ x@(suc y) = `/id-injective (
              `/id (x & ((ϕ₁ ; ϕ₂) ↑ₖ s)) ≡⟨⟩
              `/id (wk′ _ ( y & (ϕ₁ ; ϕ₂))) ≡⟨⟩
              `/id (wk′ _ (y & ϕ₁ &/⋯ ϕ₂)) ≡⟨ cong (`/id) (&/⋯-wk-↑ₖ (y & ϕ₁) ϕ₂) ⟩
              `/id (wk′ _ (y & ϕ₁) &/⋯ (ϕ₂ ↑ₖ s)) ≡⟨⟩
              `/id (x & (ϕ₁ ↑ₖ s) &/⋯ (ϕ₂ ↑ₖ s))   ≡⟨⟩
              `/id (x & ((ϕ₁ ↑ₖ s) ; (ϕ₂ ↑ₖ s)))  ∎
              )
            
            dist–↑–; : ∀ s (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                       ((ϕ₁ ↑ₖ s) ; (ϕ₂ ↑ₖ s)) ≡ ((ϕ₁ ; ϕ₂) ↑ₖ s)
            dist–↑–; s ϕ₁ ϕ₂ = sym (~-ext (dist-↑ₖ-; s ϕ₁ ϕ₂))

            dist-↑ₖ⋆-;  : ∀ S (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                        ((ϕ₁ ; ϕ₂) ↑ₖ⋆ S) ~ ((ϕ₁ ↑ₖ⋆ S) ; (ϕ₂ ↑ₖ⋆ S))
            dist-↑ₖ⋆-; []      ϕ₁ ϕ₂ sx x = refl
            dist-↑ₖ⋆-; (s ∷ S) ϕ₁ ϕ₂ sx x =
              ((ϕ₁ ; ϕ₂) ↑ₖ⋆ (s ∷ S)) sx x ≡⟨⟩
              (((ϕ₁ ; ϕ₂) ↑ₖ⋆ S) ↑ₖ s) sx x ≡⟨ cong (λ ■ → ( ■ ↑ₖ  s) sx x) (~-ext (dist-↑ₖ⋆-; S ϕ₁ ϕ₂)) ⟩
              (((ϕ₁ ↑ₖ⋆ S) ; (ϕ₂ ↑ₖ⋆ S)) ↑ₖ s) sx x ≡⟨ dist-↑ₖ-; s (ϕ₁ ↑ₖ⋆ S) (ϕ₂ ↑ₖ⋆ S) sx x ⟩
              (((ϕ₁ ↑ₖ⋆ S) ↑ₖ s) ; ((ϕ₂ ↑ₖ⋆ S) ↑ₖ s)) sx x ≡⟨⟩
              ((ϕ₁ ↑ₖ⋆ (s ∷ S)) ; (ϕ₂ ↑ₖ⋆ (s ∷ S))) sx x ∎
            
            dist–↑⋆–;  : ∀ S (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                         ((ϕ₁ ↑ₖ⋆ S) ; (ϕ₂ ↑ₖ⋆ S)) ≡ ((ϕ₁ ; ϕ₂) ↑ₖ⋆ S)
            dist–↑⋆–; S ϕ₁ ϕ₂ = sym (~-ext (dist-↑ₖ⋆-; S ϕ₁ ϕ₂))
        
        open ComposeKit {{...}} public

        opaque
          unfolding all_kit_and_compose_definitions

          ⋯-fusion-` : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}} 
                {x : S₁ ∋ s} {ϕ₁ : S₁ –[ K₁ ]→ S₂} {ϕ₂ : S₂ –[ K₂ ]→ S₃} →
                 (`/id {{K₁}} (x & ϕ₁)) ⋯ ϕ₂ ≡ `/id {{K₃}} (x & (ϕ₁ ; ϕ₂))
          ⋯-fusion-` {x = x} {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} = &/⋯-⋯ (ϕ₁ _ x) ϕ₂ -- &/⋯-⋯ (ϕ₁ _ x) ϕ₂
        
        _;[_]_  : ∀ {K₁ : Kit k₁} {K₂ : Kit k₂} {K₃ : Kit k₃} →
                  S₁ –[ K₁ ]→ S₂ → ComposeKit K₁ K₂ K₃ →
                  S₂ –[ K₂ ]→ S₃ → S₁ –[ K₃ ]→ S₃
        ϕ₁ ;[ C ] ϕ₂ = let instance _ = C in ϕ₁ ; ϕ₂  
  
        record Compose : Set₁ where
          constructor mkCompose 
          field
            ⋯-fusion′ : ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}}
                       (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
                       (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
          
          opaque
            unfolding all_kit_and_compose_definitions 
          
            ↑ₖ-wk  : ∀ {{K : Kit k}}
                    {{C₁ : ComposeKit K Kᵣ K}} {{C₂ : ComposeKit Kᵣ K K}} 
                    (ϕ : S₁ –[ K ]→ S₂) s → 
                    (ϕ ; wkᵣ) ~ (wkᵣ ; (ϕ ↑ₖ s))
            ↑ₖ-wk {S₁} {S₂} {{K}} ϕ s sx x =  `/id-injective {{K ⊔ Kᵣ}} (
              `/id {{K ⊔ Kᵣ}} ((ϕ ; wkᵣ) sx x)         ≡⟨⟩
              `/id {{K ⊔ Kᵣ}} (x & ϕ &/⋯ wkᵣ)           ≡⟨ sym (&/⋯-⋯ (x & ϕ) (wkᵣ)) ⟩
              `/id (`/id (x & ϕ) ⋯ wkᵣ)                 ≡⟨ wk-`/id s (x & ϕ) ⟩
              `/id (suc x & (ϕ ↑ₖ s))                   ≡⟨ sym (&/⋯-& (suc x) (ϕ ↑ₖ s)) ⟩
              `/id {{K ⊔ Kᵣ}} (suc x &/⋯ (ϕ ↑ₖ s))      ≡⟨⟩
              `/id {{K ⊔ Kᵣ}} (x & wkᵣ &/⋯ (ϕ ↑ₖ s))    ≡⟨⟩
              `/id {{K ⊔ Kᵣ}} ((wkᵣ ; (ϕ ↑ₖ s)) sx x)  ∎) 
            
            ⋯-↑ₖ-wk  : ∀ {{K : Kit k}} {{C₁ : ComposeKit K Kᵣ K}} {{C₂ : ComposeKit Kᵣ K K}} 
                      (t : S₁ ⊢ s) (ϕ : S₁ –[ K ]→ S₂) s′ → 
                      t ⋯ ϕ ⋯ wkᵣ ≡ t ⋯ wkᵣ ⋯ (ϕ ↑ₖ s′)
            ⋯-↑ₖ-wk t ϕ s =
              t ⋯ ϕ ⋯ wkᵣ            ≡⟨ ⋯-fusion′ t ϕ (wkᵣ) ⟩
              t ⋯ (ϕ ; wkᵣ)         ≡⟨ cong (t ⋯_) (~-ext (↑ₖ-wk ϕ s)) ⟩
              t ⋯ (wkᵣ ; (ϕ ↑ₖ s))  ≡⟨ sym (⋯-fusion′ t (wkᵣ) (ϕ ↑ₖ s)) ⟩  
              t ⋯ wkᵣ ⋯ (ϕ ↑ₖ s)     ∎

            Cᵣ-&/⋯-wk-↑ₖ  : {{K₂ : Kit k}} (x : S₁ ∋ s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                           Kit.wk′ K₂ s′ ((K₂ Kit.& x) ϕ) ≡ (K₂ Kit.& suc x) (ϕ ↑ₖ s′)
            Cᵣ-&/⋯-wk-↑ₖ _ _ = refl

          -- allows ComposeKit Kᵣ K  K
          ---and    ComposeKit Kᵣ Kᵣ Kᵣ
          -- and    ComposeKit Kᵣ Kₛ Kₛ
          Cᵣ : {{K : Kit k}} → ComposeKit Kᵣ K K
          Cᵣ = record
                  { _&/⋯′_    = _&_
                  ; &/⋯-⋯     = λ x ϕ → ⋯-var x ϕ
                  ; &/⋯-wk-↑ₖ = Cᵣ-&/⋯-wk-↑ₖ 
                  ; lock      = unlock }

          postulate
            unique–Cᵣ : {{ K : Kit k }} (C : ComposeKit Kᵣ K K) → C ≡ Cᵣ

          -- allows ComposeKit Kₛ K  Kₛ
          -- and    ComposeKit Kₛ Kᵣ Kₛ 
          -- and    ComposeKit Kₛ Kₛ Kₛ
          Cₛ : {{K : Kit k}} {{C : ComposeKit K Kᵣ K}} → ComposeKit Kₛ K Kₛ
          Cₛ  = record
                  { _&/⋯′_    = _⋯_
                  ; &/⋯-⋯     = λ t ϕ → refl
                  ; &/⋯-wk-↑ₖ = λ t ϕ → let instance _ = Cᵣ in ⋯-↑ₖ-wk t ϕ _ 
                  ; lock      = unlock } 

          postulate
            unique–Cₛ : {{K : Kit k}} {{C₁ : ComposeKit K Kᵣ K}} → (C : ComposeKit Kₛ K Kₛ) → C ≡ Cₛ 

          instance 
            opaque 
              -- additionally allows ComposeKit K K K 
              C–⊔ : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} → ComposeKit K₁ K₂ (K₁ ⊔ K₂) 
              {-# INCOHERENT C–⊔ #-} 
              C–⊔ {Ren} {Ren} {{K₁}} {{K₂}} = subst₂ (λ K₁′ K₂′ → ComposeKit K₁′ K₂′ Kᵣ) (unique–Kᵣ K₁) (unique–Kᵣ K₂) (Cᵣ {{K = Kᵣ}})
              C–⊔ {Ren} {Sub} {{K₁}} {{K₂}} = subst₂ (λ K₁′ K₂′ → ComposeKit K₁′ K₂′ Kₛ) (unique–Kᵣ K₁) (unique–Kₛ K₂) (Cᵣ {{K = Kₛ}})
              C–⊔ {Sub} {Ren} {{K₁}} {{K₂}} = subst₂ (λ K₁′ K₂′ → ComposeKit K₁′ K₂′ Kₛ) (unique–Kₛ K₁) (unique–Kᵣ K₂) (Cₛ {{K = Kᵣ}} {{C = Cᵣ {{K = Kᵣ}}}})
              C–⊔ {Sub} {Sub} {{K₁}} {{K₂}} = subst₂ (λ K₁′ K₂′ → ComposeKit K₁′ K₂′ Kₛ) (unique–Kₛ K₁) (unique–Kₛ K₂) (Cₛ {{K = Kₛ}} {{C = Cₛ {{K = Kᵣ}} {{C = Cᵣ}}}}) 

          postulate
            -- disallows Kₛ K  Kᵣ
            -- and       K  Kₛ Kᵣ
            -- and       Kₛ Kᵣ Kᵣ
            -- and       Kₛ Kₛ Kᵣ
            -- and       Kᵣ Kₛ Kᵣ
            -- and       Kₛ Kₛ Kᵣ
            -- and       Kᵣ Kᵣ Kₛ
            impossible–Cᵣ  : {{K : Kit k}} → ¬ ComposeKit Kₛ K Kᵣ
            impossible–Cᵣ′ : {{K : Kit k}} → ¬ ComposeKit K Kₛ Kᵣ
            impossible–Cₛ  : ¬ ComposeKit Kᵣ Kᵣ Kₛ  

          C–⊔-law₀ : {{K : Kit k}} → C–⊔ {{Kᵣ}} {{K}} ≡ Cᵣ
          C–⊔-law₀ = unique–Cᵣ _

          C–⊔-law₁ : {{K : Kit k}} → C–⊔ {{Kₛ}} {{K}} ≡ Cₛ {{C = C–⊔ {{K}} {{Kᵣ}}}}
          C–⊔-law₁ = unique–Cₛ _
          
          {-# REWRITE C–⊔-law₀ C–⊔-law₁ #-}   

          opaque
            unfolding all_kit_and_compose_definitions 
            def-&/⋯Cₛ : {{K : Kit k}} {{C : ComposeKit K Kᵣ K}} 
              (t : S₁ ⊢ s) (ϕ : S₁ –[ K ]→ S₂) → _&/⋯_ {{Cₛ}} t ϕ ≡ t ⋯ ϕ
            def-&/⋯Cₛ _ _ = refl

            def-&/⋯Cᵣ : {{K : Kit k}} 
              (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) → _&/⋯_ {{Cᵣ}} x ϕ ≡ x & ϕ 
            def-&/⋯Cᵣ _ _ = refl
            
            &/⋯-law₁ :  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₂}} 
                (x/t : Kit._∋/⊢_ K₂ S₂ s) (ϕ : S₁ –[ K₂ ]→ S₂) → 
                (id/` {{K₁}} zero) &/⋯ (x/t ∙ ϕ) ≡ x/t 
            &/⋯-law₁ {Ren} {{K₁}} {{K₂}} {{C}} x/t ϕ 
              rewrite unique K₁ | unique–Cᵣ C = refl
            &/⋯-law₁ {Sub} {Ren} {{K₁}} {{K₂}} {{C}} x/t ϕ 
              rewrite unique K₁ | unique K₂ = ⊥-elim (impossible–Cᵣ {{Kᵣ}} C)
            &/⋯-law₁ {Sub} {Sub} {{K₁}} {{K₂}} {{C}} x/t ϕ 
              rewrite unique K₁ | unique K₂ | unique–Cₛ {{Kₛ}} {{Cₛ}} C = ⋯-var {{Kₛ}} _ _

            -- TODO: fix this to be rewritable, currently not a valid rewrite pattern on the lhs
            -- note: i.e. probably it suffices to make suc a defined function symbol instead of pattern
            -- &/⋯-law₂ :  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₂}} 
            --     (x/t : Kit._∋/⊢_ K₂ S₂ s) (ϕ : S₁ –[ K₂ ]→ S₂) (x : S₁ ∋ s) → 
            --     (id/` {{K₁}} (suc x)) &/⋯ (x/t ∙ ϕ) ≡ (id/` {{K₁}} x) &/⋯ ϕ 

          opaque
            unfolding all_kit_and_compose_definitions

            
            wkm-def : ∀ {{K : Kit k}} (ϕ : S₁ –[ K ]→ S₂) s → wkmₖ s ϕ ≡ ϕ ; wkᵣ
            wkm-def {Ren} {{K}} ϕ s rewrite unique K = refl 
            wkm-def {Sub} {{K}} ϕ s rewrite unique K = refl  

            ;-def : ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}} s 
                    (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (x : S₁ ∋ s) →  
                x & (ϕ₁ ; ϕ₂) ≡ (x & ϕ₁) &/⋯ ϕ₂   
            ;-def _ _ _ _ = refl
            
            interact : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₂}} 
                       (x/t : Kit._∋/⊢_ K₂ S₂ s) (ϕ : S₁ –[ K₂ ]→ S₂) → wk ; (x/t ∙ ϕ) ≡ ϕ 
            interact {Ren} {k₂} {{K₁}} {{K₂}} {{C}} x/t ϕ 
              rewrite unique K₁ | unique–Cᵣ C = refl
            interact {Sub} {Ren} {{K₁}} {{K₂}} {{C}} x/t ϕ 
              rewrite unique K₁ | unique K₂ = ⊥-elim (impossible–Cᵣ {{K = Kᵣ}} C)
            interact {Sub} {Sub} {{K₁}} {{K₂}} {{C}} x/t ϕ 
              rewrite unique K₁ | unique K₂ | unique–Cₛ {{Kₛ}} {{Cₛ}} C = ~-ext {{Kₛ}} λ s x → 
                _ ≡⟨ ⋯-fusion′ {{Kᵣ}} {{Kₛ}} {{Kₛ}} {{Cᵣ {{Kₛ}}}} _ _ _ ⟩ _ ≡⟨ ⋯-var {{Kₛ}} _ _ ⟩ _ ∎
 
            η-id : {{K : Kit k}} → _∙_ {s = s} {S₁ = S} (id/` {{K}} zero) wk ≡ id 
            η-id {Ren} {{K}} rewrite unique K = ~-ext {{K}} λ { _ zero → refl ; _ (suc x) → refl }
            η-id {Sub} {{K}} rewrite unique K = ~-ext {{K}} λ { _ zero → refl ; _ (suc x) → ⋯-var _ _ } 
          
            η-law : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₂}} 
                    (ϕ : (s ∷ S₁) –[ K₂ ]→ S₂) → (zero & ϕ) ∙ (wk ; ϕ) ≡ ϕ
            η-law {Ren} {k₂} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique K₁ | unique–Cᵣ C 
              = ~-ext λ { _ zero → refl  ; _ (suc x) → refl }
            η-law {Sub} {Ren} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique K₁ | unique K₂ = ⊥-elim (impossible–Cᵣ {{K = Kᵣ}} C)
            η-law {Sub} {Sub} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique K₁ | unique K₂ | unique–Cₛ {{K = Kₛ}} {{C₁ = Cₛ}} C 
              = ~-ext {{Kₛ}} λ { _ zero → refl  ; _ (suc x) → _ ≡⟨ ⋯-fusion′ {{Kᵣ}} {{Kₛ}} {{Kₛ}} {{Cᵣ {{Kₛ}}}} _ _ _ ⟩ _ ≡⟨ ⋯-var {{Kₛ}} _ _ ⟩ _ ∎ } 
        
            distributivity : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}} 
                             (x/t : Kit._∋/⊢_ K₁ S₂ s)  (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
                             (x/t ∙ ϕ₁) ; ϕ₂ ≡ let instance _ = (K₁ ⊔ K₂) in (x/t &/⋯ ϕ₂) ∙ (ϕ₁ ; ϕ₂)
            distributivity _ _ _ = ~-ext λ { _ zero → refl ; _ (suc x) → refl } 

            left-id : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₂}} 
                      (ϕ : S₁ –[ K₂ ]→ S₂) → id {{K₁}} ; ϕ ≡ ϕ 
            left-id {Ren} {k₂} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique K₁ | unique–Cᵣ C 
              = refl
            left-id {Sub} {Ren} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique K₁ | unique K₂ = ⊥-elim (impossible–Cᵣ {{Kᵣ}} C)
            left-id {Sub} {Sub} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique K₁ | unique K₂ | unique–Cₛ {{Kₛ}} {{Cₛ}} C 
              = ~-ext {{Kₛ}} λ _ x → ⋯-var {{Kₛ}} _ _  

            right-id : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₁}} (ϕ : S₁ –[ K₁ ]→ S₂) → ϕ ; id {{K₂}} ≡ ϕ
            right-id {Ren} {Ren} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique K₁ | unique K₂ | unique–Cᵣ {{Kᵣ}} C 
              = refl
            right-id {Ren} {Sub} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique K₁ | unique K₂ = ⊥-elim (impossible–Cᵣ′ {{Kᵣ}} C)
            right-id {Sub} {Ren} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique K₁ | unique K₂ | unique–Cₛ {{Kᵣ}} {{Cᵣ {{K = Kᵣ}}}} C 
              = ~-ext {{Kₛ}} λ _ x → ⋯-id {{Kᵣ}} _
            right-id {Sub} {Sub} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique K₁ | unique K₂ | unique–Cₛ {{Kₛ}} {{Cₛ}} C 
              = ~-ext {{Kₛ}} λ _ x → ⋯-id {{Kₛ}} _


            -- the idiomatic way to transform a sub/ren into a sub is to compose id on the right. 
            -- if its applied on the left, we transform it.   
            norm-id : {{K : Kit k}} (ϕ : S₁ –[ K ]→ S₂) → id {{Kₛ}} ; ϕ ≡ (ϕ ; id {{Kₛ}}) 
            norm-id {Ren} {{K}} ϕ rewrite unique K = ~-ext {{Kₛ}} λ _ x → ⋯-var {{Kᵣ}} _ _
            norm-id {Sub} {{K}} ϕ rewrite unique K = ~-ext {{Kₛ}} λ _ x → 
              _ ≡⟨ ⋯-var {{Kₛ}} _ _ ⟩ _ ≡⟨ sym (⋯-id {{Kₛ}} _) ⟩ _ ∎

            -- needs rewrite on ++ for lists, do we want this?
            -- ↑ₖ⋆↑ₖ⋆ : {{K : Kit k}} (ϕ : S₁ –[ K ]→ S₂) → ((ϕ ↑ₖ⋆ S) ↑ₖ⋆ S′) ≡ {!  ϕ ↑ₖ⋆ (S′ ++ S)  !}  

            associativityᵣᵣᵣ : (ϕ₁ : S₁ –[ Kᵣ ]→ S₂) (ϕ₂ : S₂ –[ Kᵣ ]→ S₃) (ϕ₃ : S₃ –[ Kᵣ ]→ S₄) →   
                        (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityᵣᵣᵣ _ _ _ = refl      

            associativityᵣᵣₛ : (ϕ₁ : S₁ –[ Kᵣ ]→ S₂) (ϕ₂ : S₂ –[ Kᵣ ]→ S₃) (ϕ₃ : S₃ –[ Kₛ ]→ S₄) →   
                        (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityᵣᵣₛ _ _ _ = refl

            associativityᵣᵣₖ : {{K₃ : Kit k₃}} 
                        (ϕ₁ : S₁ –[ Kᵣ ]→ S₂) (ϕ₂ : S₂ –[ Kᵣ ]→ S₃) (ϕ₃ : S₃ –[ K₃ ]→ S₄) →   
                        (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityᵣᵣₖ _ _ _ = refl
                        
            associativityᵣₛᵣ : (ϕ₁ : S₁ –[ Kᵣ ]→ S₂) (ϕ₂ : S₂ –[ Kₛ ]→ S₃) (ϕ₃ : S₃ –[ Kᵣ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityᵣₛᵣ _ _ _ = refl

            associativityᵣₛₛ : (ϕ₁ : S₁ –[ Kᵣ ]→ S₂) (ϕ₂ : S₂ –[ Kₛ ]→ S₃) (ϕ₃ : S₃ –[ Kₛ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityᵣₛₛ _ _ _ = refl
            
            associativityᵣₛₖ : {{K₃ : Kit k₃}}
                      (ϕ₁ : S₁ –[ Kᵣ ]→ S₂) (ϕ₂ : S₂ –[ Kₛ ]→ S₃) (ϕ₃ : S₃ –[ K₃ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityᵣₛₖ _ _ _ = refl

            associativityᵣₖᵣ : {{K₂ : Kit k₂}}
                      (ϕ₁ : S₁ –[ Kᵣ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ Kᵣ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityᵣₖᵣ _ _ _ = refl

            associativityᵣₖₛ : {{K₂ : Kit k₂}}
                      (ϕ₁ : S₁ –[ Kᵣ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ Kₛ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityᵣₖₛ _ _ _ = refl

            associativityᵣₖₖ : {{K₂ : Kit k₂}} {{K₃ : Kit k₃}}
                      (ϕ₁ : S₁ –[ Kᵣ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ K₃ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ let instance _ = K₂ ⊔ K₃ in ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityᵣₖₖ _ _ _ = refl

            associativityₛᵣᵣ : (ϕ₁ : S₁ –[ Kₛ ]→ S₂) (ϕ₂ : S₂ –[ Kᵣ ]→ S₃) (ϕ₃ : S₃ –[ Kᵣ ]→ S₄) →   
                        (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₛᵣᵣ _ _ _ = ~-ext λ _ x → ⋯-fusion′ _ _ _

            associativityₛᵣₛ : (ϕ₁ : S₁ –[ Kₛ ]→ S₂) (ϕ₂ : S₂ –[ Kᵣ ]→ S₃) (ϕ₃ : S₃ –[ Kₛ ]→ S₄) →   
                        (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₛᵣₛ _ _ _ = ~-ext λ _ x → ⋯-fusion′ _ _ _

            associativityₛᵣₖ : {{K₃ : Kit k₃}}
                      (ϕ₁ : S₁ –[ Kₛ ]→ S₂) (ϕ₂ : S₂ –[ Kᵣ ]→ S₃) (ϕ₃ : S₃ –[ K₃ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₛᵣₖ _ _ _ = ~-ext λ _ x → ⋯-fusion′ _ _ _

            associativityₛₛᵣ : (ϕ₁ : S₁ –[ Kₛ ]→ S₂) (ϕ₂ : S₂ –[ Kₛ ]→ S₃) (ϕ₃ : S₃ –[ Kᵣ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₛₛᵣ _ _ _ = ~-ext λ _ x → ⋯-fusion′ _ _ _

            associativityₛₛₛ : (ϕ₁ : S₁ –[ Kₛ ]→ S₂) (ϕ₂ : S₂ –[ Kₛ ]→ S₃) (ϕ₃ : S₃ –[ Kₛ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₛₛₛ _ _ _ = ~-ext λ _ x → ⋯-fusion′ _ _ _

            associativityₛₛₖ : {{K₃ : Kit k₃}}
                       (ϕ₁ : S₁ –[ Kₛ ]→ S₂) (ϕ₂ : S₂ –[ Kₛ ]→ S₃) (ϕ₃ : S₃ –[ K₃ ]→ S₄) →   
                       (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₛₛₖ _ _ _ = ~-ext λ _ x → ⋯-fusion′ _ _ _

            associativityₛₖᵣ : {{K₂ : Kit k₂}}
                      (ϕ₁ : S₁ –[ Kₛ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ Kᵣ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₛₖᵣ _ _ _ = ~-ext λ _ x → ⋯-fusion′ _ _ _

            associativityₛₖₛ : {{K₂ : Kit k₂}}
                      (ϕ₁ : S₁ –[ Kₛ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ Kₛ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₛₖₛ _ _ _ = ~-ext λ _ x → ⋯-fusion′ _ _ _

            associativityₛₖₖ : {{K₂ : Kit k₂}} {{K₃ : Kit k₃}}
                      (ϕ₁ : S₁ –[ Kₛ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ K₃ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ let instance _ = K₂ ⊔ K₃ in ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₛₖₖ {{K₂}} {{K₃}} _ _ _ = ~-ext λ _ x → let instance _ = K₂ ⊔ K₃ in ⋯-fusion′ _ _ _
               
            associativityₖᵣᵣ : {{K₁ : Kit k₁}}
                      (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ Kᵣ ]→ S₃) (ϕ₃ : S₃ –[ Kᵣ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₖᵣᵣ {Ren} {{K₁}} _ _ _ rewrite unique K₁ = refl
            associativityₖᵣᵣ {Sub} {{K₁}} _ _ _ rewrite unique K₁ = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kᵣ}} {{Kᵣ}} {{Kᵣ}} {{Cᵣ {{Kᵣ}}}} _ _ _

            associativityₖᵣₛ : {{K₁ : Kit k₁}}
                      (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ Kᵣ ]→ S₃) (ϕ₃ : S₃ –[ Kₛ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₖᵣₛ {Ren} {{K₁}} _ _ _ rewrite unique K₁ = refl
            associativityₖᵣₛ {Sub} {{K₁}} _ _ _ rewrite unique K₁ = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kᵣ}} {{Kₛ}} {{Kₛ}} {{Cᵣ {{Kₛ}}}} _ _ _
            
            associativityₖᵣₖ : {{K₁ : Kit k₁}} {{K₃ : Kit k₃}}
                      (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ Kᵣ ]→ S₃) (ϕ₃ : S₃ –[ K₃ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₖᵣₖ {Ren} {Ren} {{K₁}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₃ = refl
            associativityₖᵣₖ {Ren} {Sub} {{K₁}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₃ = refl
            associativityₖᵣₖ {Sub} {Ren} {{K₁}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₃ = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kᵣ}} {{Kᵣ}} {{Kᵣ}} {{Cᵣ {{Kᵣ}}}} _ _ _
            associativityₖᵣₖ {Sub} {Sub} {{K₁}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₃ = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kᵣ}} {{Kₛ}} {{Kₛ}} {{Cᵣ {{Kₛ}}}} _ _ _
            
            associativityₖₛᵣ : {{K₁ : Kit k₁}}
                      (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ Kₛ ]→ S₃) (ϕ₃ : S₃ –[ Kᵣ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₖₛᵣ {Ren} {{K₁}} _ _ _ rewrite unique K₁ = refl
            associativityₖₛᵣ {Sub} {{K₁}} _ _ _ rewrite unique K₁ = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kₛ}} {{Kᵣ}} {{Kₛ}} {{Cₛ {{Kᵣ}} {{Cᵣ {{Kᵣ}}}}}} _ _ _
            
            associativityₖₛₛ : {{K₁ : Kit k₁}}
                      (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ Kₛ ]→ S₃) (ϕ₃ : S₃ –[ Kₛ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₖₛₛ {Ren} {{K₁}} _ _ _ rewrite unique K₁ = refl
            associativityₖₛₛ {Sub} {{K₁}} _ _ _ rewrite unique K₁ = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kₛ}} {{Kₛ}} {{Kₛ}} {{Cₛ {{Kₛ}} {{Cₛ {{Kᵣ}} {{Cᵣ {{Kᵣ}}}}}}}} _ _ _
            
            associativityₖₛₖ : {{K₁ : Kit k₁}} {{K₃ : Kit k₃}}
                      (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ Kₛ ]→ S₃) (ϕ₃ : S₃ –[ K₃ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₖₛₖ {Ren} {Ren} {{K₁}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₃ = refl
            associativityₖₛₖ {Ren} {Sub} {{K₁}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₃ = refl
            associativityₖₛₖ {Sub} {Ren} {{K₁}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₃ = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kₛ}} {{Kᵣ}} {{Kₛ}} {{Cₛ {{Kᵣ}} {{Cᵣ {{Kᵣ}}}}}} _ _ _
            associativityₖₛₖ {Sub} {Sub} {{K₁}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₃ = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kₛ}} {{Kₛ}} {{Kₛ}} {{Cₛ {{Kₛ}} {{Cₛ {{Kᵣ}} {{Cᵣ {{Kᵣ}}}}}}}} _ _ _
            
            associativityₖₖᵣ : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C₁ : ComposeKit K₁ K₂ Kᵣ}}
                      (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ Kᵣ ]→ S₄) →   
                      (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ let instance _ = K₁ ⊔ K₂ in ϕ₁ ; (ϕ₂ ; ϕ₃)
            associativityₖₖᵣ {Ren} {Ren} {{K₁}} {{K₂}} {{C₁}} _ _ _ rewrite unique K₁ | unique K₂ | unique–Cᵣ {{Kᵣ}} C₁ = refl
            associativityₖₖᵣ {Ren} {Sub} {{K₁}} {{K₂}} {{C₁}} _ _ _ rewrite unique K₁ | unique K₂ = ⊥-elim (impossible–Cᵣ′ {{Kᵣ}} C₁)
            associativityₖₖᵣ {Sub} {Ren} {{K₁}} {{K₂}} {{C₁}} _ _ _ rewrite unique K₁ | unique K₂ = ⊥-elim (impossible–Cᵣ {{Kᵣ}} C₁)
            associativityₖₖᵣ {Sub} {Sub} {{K₁}} {{K₂}} {{C₁}} _ _ _ rewrite unique K₁ | unique K₂ = ⊥-elim (impossible–Cᵣ {{Kₛ}} C₁) 
            

              -- TODO: we currently cannot construct an ComposeKit K₂ Kₛ K₂ with the 
              --       arguments given, but it is required inside the hole
              -- note: K₂ can only be Kₛ for this lemma to work out.
              --       thus, it might be this is an impossible lemma.
              --       but why?
              -- associativityₖₖₛ : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C₁ : ComposeKit K₁ K₂ Kₛ}} 
              --           (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ Kₛ ]→ S₄) →   
              --           (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ let instance _ = K₁ ⊔ K₂ in ϕ₁ ; (ϕ₂ ;[ ? ] ϕ₃)

            associativityₖₖₖ : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} 
                            (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ K₃ ]→ S₄) →   
                            ComposeKit._;_ (C–⊔ {{K₁ ⊔ K₂}}) (ϕ₁ ; ϕ₂) ϕ₃ ≡ let instance _ = (K₂ ⊔ K₃) in ϕ₁ ; (ϕ₂ ; ϕ₃) 
            associativityₖₖₖ {Ren} {Ren} {Ren} {{K₁}} {{K₂}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₂ | unique K₃ 
              = refl
            associativityₖₖₖ {Ren} {Ren} {Sub} {{K₁}} {{K₂}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₂ | unique K₃ 
              = refl
            associativityₖₖₖ {Ren} {Sub} {Ren} {{K₁}} {{K₂}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₂ | unique K₃ 
              = refl
            associativityₖₖₖ {Ren} {Sub} {Sub} {{K₁}} {{K₂}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₂ | unique K₃ 
              = refl
            associativityₖₖₖ {Sub} {Ren} {Ren} {{K₁}} {{K₂}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₂ | unique K₃ 
              = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kᵣ}} {{Kᵣ}} {{Kᵣ}} {{Cᵣ {{Kᵣ}}}} _ _ _
            associativityₖₖₖ {Sub} {Ren} {Sub} {{K₁}} {{K₂}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₂ | unique K₃ 
              = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kᵣ}} {{Kₛ}} {{Kₛ}} {{Cᵣ {{Kₛ}}}} _ _ _
            associativityₖₖₖ {Sub} {Sub} {Ren} {{K₁}} {{K₂}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₂ | unique K₃ 
              = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kₛ}} {{Kᵣ}} {{Kₛ}} {{Cₛ {{Kᵣ}} {{Cᵣ {{Kᵣ}}}}}} _ _ _
            associativityₖₖₖ {Sub} {Sub} {Sub} {{K₁}} {{K₂}} {{K₃}} _ _ _ rewrite unique K₁ | unique K₂ | unique K₃ 
              = ~-ext {{Kₛ}} λ _ x → ⋯-fusion′ {{Kₛ}} {{Kₛ}} {{Kₛ}} {{Cₛ {{Kₛ}} {{Cₛ {{Kᵣ}} {{Cᵣ {{Kᵣ}}}}}}}} _ _ _ 