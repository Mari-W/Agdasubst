-- Author: Hannes Saffrich
-- Modified: Marius Weidner
{-# OPTIONS --rewriting #-}
module Kits where

open import Agda.Builtin.Equality.Rewrite

open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂; module ≡-Reasoning)
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

      record Kit (_∋/⊢_ : SCOPED_BINDABLE) : Set₁ where
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

          _↑ₖ_ : S₁ →ₖ S₂ → ∀ s → (s ∷ S₁) →ₖ (s ∷ S₂)
          ϕ ↑ₖ s = id/` zero ∙ wkmₖ s ϕ

          id : S →ₖ S
          id s x = id/` x 

          wk : ∀ {s} → S →ₖ (s ∷ S)
          wk = wkmₖ _ id
        
        ⦅_⦆ : S ∋/⊢ s → (s ∷ S) →ₖ S
        ⦅ x/t ⦆ = x/t ∙ id

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

          id↑ₖ⋆~id : ∀ S → (id ↑ₖ⋆ S) ~ id {S ++ S′}
          id↑ₖ⋆~id []      sx x = refl
          id↑ₖ⋆~id (s ∷ S) sx x =
            ((id ↑ₖ⋆ S) ↑ₖ s) sx x ≡⟨ cong (λ ■ → (■ ↑ₖ s) sx x) (~-ext (id↑ₖ⋆~id S)) ⟩
            (id ↑ₖ s) sx x        ≡⟨ id↑ₖ~id sx x ⟩
            id sx x              ∎


      _∋/⊢[_]_ : Scope → Kit _∋/⊢_ → BindSort → Set
      _∋/⊢[_]_ {_∋/⊢_} S K s = S ∋/⊢ s
 
      _–[_]→_ : Scope → Kit _∋/⊢_ → Scope → Set
      S₁ –[ K ]→ S₂ = Kit._→ₖ_ K S₁ S₂

      open Kit ⦃ … ⦄ public 

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
            } 
        
        postulate
          unique-Kᵣ-instance : (K : Kit _∋_) → K ≡ Kᵣ
      
        open Kit Kᵣ public using () renaming 
          (_→ₖ_ to _→ᵣ_; _&_ to _&ᵣ_; _∙_ to _∙ᵣ_; id to idᵣ; wk to wkᵣ)

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
            }

        postulate
          unique-Kₛ-instance : (K : Kit _⊢_) → K ≡ Kₛ

        open Kit Kₛ public using () renaming 
          (_→ₖ_ to _→ₛ_; _&_ to _&ₛ_; _∙_ to _∙ₛ_; id to idₛ)

        _⋯ₛ_ : S₁ ⊢ s → S₁ →ₛ S₂ → S₂ ⊢ s
        t ⋯ₛ σ = t ⋯ σ

        _[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
        T [ T′ ] = T ⋯ (T′ ∙ id) 

        _⊔′_ : (K₁ : Kit _∋/⊢₁_) (K₂ : Kit _∋/⊢₂_) → SCOPED_BINDABLE
        mkKit Ren refl _ _ _ _ _ _ _ ⊔′ mkKit Ren refl _ _ _ _ _ _ _ = _∋_
        mkKit Ren refl _ _ _ _ _ _ _ ⊔′ mkKit Sub refl _ _ _ _ _ _ _ = _⊢_
        mkKit Sub refl _ _ _ _ _ _ _ ⊔′ mkKit Ren refl _ _ _ _ _ _ _ = _⊢_
        mkKit Sub refl _ _ _ _ _ _ _ ⊔′ mkKit Sub refl _ _ _ _ _ _ _ = _⊢_

        ⊔′-law₀ : ⦃ K : Kit _∋/⊢_ ⦄ → K ⊔′ K ≡ _∋/⊢_ 
        ⊔′-law₀ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔′-law₀ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl

        ⊔′-law₁ : ⦃ K : Kit _∋/⊢_ ⦄ → K ⊔′ Kᵣ ≡ _∋/⊢_ 
        ⊔′-law₁ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl 
        ⊔′-law₁ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl 

        ⊔′-law₂ : ⦃ K : Kit _∋/⊢_ ⦄ → Kᵣ ⊔′ K ≡ _∋/⊢_
        ⊔′-law₂ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl 
        ⊔′-law₂ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl 

        ⊔′-law₃ : ⦃ K : Kit _∋/⊢_ ⦄ → K ⊔′ Kₛ ≡ _⊢_
        ⊔′-law₃ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl 
        ⊔′-law₃ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl 

        ⊔′-law₄ : ⦃ K : Kit _∋/⊢_ ⦄ → Kₛ ⊔′ K ≡ _⊢_
        ⊔′-law₄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl 
        ⊔′-law₄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl 
        
        {-# REWRITE ⊔′-law₀ ⊔′-law₁ ⊔′-law₂ ⊔′-law₃ ⊔′-law₄ #-}

        _⊔_ : (K₁ : Kit _∋/⊢₁_) (K₂ : Kit _∋/⊢₂_) → Kit (K₁ ⊔′ K₂)
        mkKit Ren refl _ _ _ _ _ _ _ ⊔ mkKit Ren refl _ _ _ _ _ _ _ = Kᵣ
        mkKit Ren refl _ _ _ _ _ _ _ ⊔ mkKit Sub refl _ _ _ _ _ _ _ = Kₛ
        mkKit Sub refl _ _ _ _ _ _ _ ⊔ mkKit Ren refl _ _ _ _ _ _ _ = Kₛ
        mkKit Sub refl _ _ _ _ _ _ _ ⊔ mkKit Sub refl _ _ _ _ _ _ _ = Kₛ

        ⊔-law₀ : ⦃ K : Kit _∋/⊢_ ⦄ → (K ⊔ K) ≡ K
        ⊔-law₀ K@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ rewrite unique-Kᵣ-instance K = refl
        ⊔-law₀ K@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ rewrite unique-Kₛ-instance K = refl 

        ⊔-law₁ : ⦃ K : Kit _∋/⊢_ ⦄ → K ⊔ Kᵣ ≡ K 
        ⊔-law₁ K@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ rewrite unique-Kᵣ-instance K = refl 
        ⊔-law₁ K@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ rewrite unique-Kₛ-instance K = refl 

        ⊔-law₂ : ⦃ K : Kit _∋/⊢_ ⦄ → Kᵣ ⊔ K ≡ K 
        ⊔-law₂ K@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ rewrite unique-Kᵣ-instance K = refl 
        ⊔-law₂ K@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ rewrite unique-Kₛ-instance K = refl 

        ⊔-law₃ : ⦃ K : Kit _∋/⊢_ ⦄ → K ⊔ Kₛ ≡ Kₛ
        ⊔-law₃ K@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ rewrite unique-Kᵣ-instance K = refl 
        ⊔-law₃ K@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ rewrite unique-Kₛ-instance K = refl 

        ⊔-law₄ : ⦃ K : Kit _∋/⊢_ ⦄ → Kₛ ⊔ K ≡ Kₛ
        ⊔-law₄ K@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ rewrite unique-Kᵣ-instance K = refl 
        ⊔-law₄ K@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ rewrite unique-Kₛ-instance K = refl 

        ⊔′-law₅ : ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₃ : Kit _∋/⊢₃_ ⦄ → 
          (K₁ ⊔ K₂) ⊔′ K₃ ≡ K₁ ⊔′ (K₂ ⊔ K₃)
        ⊔′-law₅ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔′-law₅ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔′-law₅ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔′-law₅ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔′-law₅ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔′-law₅ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔′-law₅ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔′-law₅ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl

        {-# REWRITE ⊔-law₀ ⊔-law₁ ⊔-law₂ ⊔-law₃ ⊔-law₄ ⊔′-law₅ #-}

        ⊔-law₅ : ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₃ : Kit _∋/⊢₃_ ⦄ → 
          (K₁ ⊔ K₂) ⊔ K₃ ≡ K₁ ⊔ (K₂ ⊔ K₃)
        ⊔-law₅ K₁@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₂@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔-law₅ K₁@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₂@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl 
        ⊔-law₅ K₁@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₂@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔-law₅ K₁@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₂@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔-law₅ K₁@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₂@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔-law₅ K₁@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₂@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl
        ⊔-law₅ K₁@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₂@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ = refl 
        ⊔-law₅ K₁@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₂@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ = refl

        {-# REWRITE ⊔-law₅ #-}

        module KitsMeta where
          variable 
            T T₁ T₂ T₃ T₄ T′ T₁′ T₂′ T₃′ T₄′ : S ⊢ s
            ρ ρ₁ ρ₂ ρ₃ ρ₄ ρ′ ρ₁′ ρ₂′ ρ₃′ ρ₄′ : S₁ →ᵣ S₂
            σ σ₁ σ₂ σ₃ σ₄ σ′ σ₁′ σ₂′ σ₃′ σ₄′ : S₁ →ₛ S₂

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
        
        wkKit : (K : Kit _∋/⊢_) → WkKit K
        wkKit K@(mkKit Ren refl _ _ _ _ _ _ _) rewrite unique-Kᵣ-instance K = Wᵣ 
        wkKit K@(mkKit Sub refl _ _ _ _ _ _ _) rewrite unique-Kₛ-instance K = Wₛ

        record ComposeKit (K₁ : Kit _∋/⊢₁_) (K₂ : Kit _∋/⊢₂_) : Set where

          private instance _ = K₁; _ = K₂

          infixl 8 _&/⋯_
          field
            _&/⋯_     : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₁ ⊔ K₂ ] s
            
            &/⋯-⋯     : (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                         `/id ⦃ K₁ ⊔ K₂ ⦄ (x/t &/⋯ ϕ) ≡ `/id x/t ⋯ ϕ
            &/⋯-wk-↑ₖ  : (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                         Kit.wk′ (K₁ ⊔ K₂) s′ (x/t &/⋯ ϕ) ≡ wk′ s′ x/t &/⋯ (ϕ ↑ₖ s′)
      
          opaque
            unfolding all_kit_definitions

            import Data.Unit using (⊤; tt)
            all_kit_and_compose_definitions : Data.Unit.⊤
            all_kit_and_compose_definitions = Data.Unit.tt

            _⨟_ : S₁ –[ K₁ ]→ S₂ → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₁ ⊔ K₂ ]→ S₃
            (ϕ₁ ⨟ ϕ₂) _ x = (x & ϕ₁) &/⋯ ϕ₂ 

          opaque
            unfolding all_kit_and_compose_definitions

            &/⋯-& : ∀ (x : S₁ ∋ s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                    `/id ⦃ K₁ ⊔ K₂ ⦄ (id/` ⦃ K₁ ⦄ x &/⋯ ϕ) ≡ `/id (x & ϕ)
            &/⋯-& x ϕ = 
              `/id ⦃ K₁ ⊔ K₂ ⦄ (id/` x &/⋯ ϕ)       ≡⟨ &/⋯-⋯ (id/` x) ϕ ⟩
              `/id ⦃ K₁ ⦄ (id/` x) ⋯ ϕ  ≡⟨ cong (_⋯ ϕ) (`/`-is-` ⦃ K₁ ⦄ x) ⟩
              ` x ⋯ ϕ                   ≡⟨ ⋯-var ⦃ K₂ ⦄ x ϕ ⟩
              `/id ⦃ K₂ ⦄  (x & ϕ)      ∎

            dist-↑ₖ-⨟  : ∀ s (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                       _~_ ⦃ K₁ ⊔ K₂ ⦄ (Kit._↑ₖ_ (K₁ ⊔ K₂) (ϕ₁ ⨟ ϕ₂) s) ((ϕ₁ ↑ₖ s) ⨟ (ϕ₂ ↑ₖ s))
            dist-↑ₖ-⨟ s ϕ₁ ϕ₂ s₁ x@zero = `/id-injective ⦃ K₁ ⊔ K₂ ⦄ (   
              `/id ⦃ K₁ ⊔ K₂ ⦄ (Kit._&_ (K₁ ⊔ K₂) x (Kit._↑ₖ_ (K₁ ⊔ K₂) (ϕ₁ ⨟ ϕ₂) s)) ≡⟨⟩
              `/id ⦃ K₁ ⊔ K₂ ⦄ (id/` ⦃ K₁ ⊔ K₂ ⦄ zero)     ≡⟨ `/`-is-` ⦃ K₁ ⊔ K₂ ⦄ zero ⟩
              ` zero                                        ≡⟨ sym (`/`-is-` ⦃ K₂ ⦄ zero) ⟩
              `/id ⦃ K₂ ⦄ (id/` zero)                       ≡⟨⟩
              `/id ⦃ K₂ ⦄ (zero & (ϕ₂ ↑ₖ s))                 ≡⟨ sym (&/⋯-& (id/` zero) (ϕ₂ ↑ₖ s)) ⟩
              `/id ⦃ K₁ ⊔ K₂ ⦄ (id/` zero &/⋯ (ϕ₂ ↑ₖ s))     ≡⟨⟩
              `/id ⦃ K₁ ⊔ K₂ ⦄ (x & (ϕ₁ ↑ₖ s) &/⋯ (ϕ₂ ↑ₖ s))  ≡⟨⟩
              `/id ⦃ K₁ ⊔ K₂ ⦄ (Kit._&_ (K₁ ⊔ K₂) x ((ϕ₁ ↑ₖ s) ⨟ (ϕ₂ ↑ₖ s)))  ∎
              )
            dist-↑ₖ-⨟ s ϕ₁ ϕ₂ s₁ x@(suc y) = `/id-injective ⦃ K₁ ⊔ K₂ ⦄ (
              `/id ⦃ K₁ ⊔ K₂ ⦄ (Kit._&_ (K₁ ⊔ K₂) x (Kit._↑ₖ_ (K₁ ⊔ K₂) (ϕ₁ ⨟ ϕ₂) s)) ≡⟨⟩
              `/id ⦃ K₁ ⊔ K₂ ⦄ (Kit.wk′ (K₁ ⊔ K₂) _ (Kit._&_ (K₁ ⊔ K₂) y (ϕ₁ ⨟ ϕ₂))) ≡⟨⟩
              `/id ⦃ K₁ ⊔ K₂ ⦄ (Kit.wk′ (K₁ ⊔ K₂) _ (y & ϕ₁ &/⋯ ϕ₂)) ≡⟨ cong (`/id ⦃ K₁ ⊔ K₂ ⦄) (&/⋯-wk-↑ₖ (y & ϕ₁) ϕ₂) ⟩
              `/id ⦃ K₁ ⊔ K₂ ⦄ (wk′ _ (y & ϕ₁) &/⋯ (ϕ₂ ↑ₖ s)) ≡⟨⟩
              `/id ⦃ K₁ ⊔ K₂ ⦄ (x & (ϕ₁ ↑ₖ s) &/⋯ (ϕ₂ ↑ₖ s))   ≡⟨⟩
              `/id ⦃ K₁ ⊔ K₂ ⦄ (Kit._&_ (K₁ ⊔ K₂) x ((ϕ₁ ↑ₖ s) ⨟ (ϕ₂ ↑ₖ s)))  ∎
              )

            dist-↑ₖ⋆-⨟  : ∀ S (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                         _~_ ⦃ K₁ ⊔ K₂ ⦄ (Kit._↑ₖ⋆_ (K₁ ⊔ K₂) (ϕ₁ ⨟ ϕ₂) S) ((ϕ₁ ↑ₖ⋆ S) ⨟ (ϕ₂ ↑ₖ⋆ S))
            dist-↑ₖ⋆-⨟ []      ϕ₁ ϕ₂ sx x = refl
            dist-↑ₖ⋆-⨟ (s ∷ S) ϕ₁ ϕ₂ sx x =
              (Kit._↑ₖ⋆_ (K₁ ⊔ K₂) (ϕ₁ ⨟ ϕ₂) (s ∷ S)) sx x ≡⟨⟩
              (Kit._↑ₖ_ (K₁ ⊔ K₂) (Kit._↑ₖ⋆_ (K₁ ⊔ K₂) (ϕ₁ ⨟ ϕ₂) S) s) sx x ≡⟨ cong (λ ■ → (Kit._↑ₖ_ (K₁ ⊔ K₂) ■  s) sx x) (~-ext ⦃ K₁ ⊔ K₂ ⦄ (dist-↑ₖ⋆-⨟ S ϕ₁ ϕ₂)) ⟩
              (Kit._↑ₖ_ (K₁ ⊔ K₂) ((ϕ₁ ↑ₖ⋆ S) ⨟ (ϕ₂ ↑ₖ⋆ S)) s) sx x ≡⟨ dist-↑ₖ-⨟ s (ϕ₁ ↑ₖ⋆ S) (ϕ₂ ↑ₖ⋆ S) sx x ⟩
              (((ϕ₁ ↑ₖ⋆ S) ↑ₖ s) ⨟ ((ϕ₂ ↑ₖ⋆ S) ↑ₖ s)) sx x ≡⟨⟩
              ((ϕ₁ ↑ₖ⋆ (s ∷ S)) ⨟ (ϕ₂ ↑ₖ⋆ (s ∷ S))) sx x ∎
        
        _⨟[_]_  : ∀ {K₁ : Kit _∋/⊢₁_} {K₂ : Kit _∋/⊢₂_} →
                  S₁ –[ K₁ ]→ S₂ → ComposeKit K₁ K₂ →
                  S₂ –[ K₂ ]→ S₃ → S₁ –[ K₁ ⊔ K₂ ]→ S₃
        ϕ₁ ⨟[ C ] ϕ₂ = ϕ₁ ⨟ ϕ₂ where open ComposeKit C

        open ComposeKit ⦃ … ⦄ public

        record ComposeTraversal : Set₁ where
          field
            ⋯-fusion : ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ C : ComposeKit K₁ K₂ ⦄
                       (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
                       (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ _⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t (ϕ₁ ⨟ ϕ₂)
          
          opaque
            unfolding all_kit_and_compose_definitions
          
            ↑ₖ-wk  : ∀ ⦃ K : Kit _∋/⊢_ ⦄
                    ⦃ C₁ : ComposeKit K Kᵣ ⦄ ⦃ C₂ : ComposeKit Kᵣ K ⦄ 
                    (ϕ : S₁ –[ K ]→ S₂) s → 
                    _~_ ⦃ K ⊔ Kᵣ ⦄ (ϕ ⨟ wkᵣ) (wkᵣ ⨟ (ϕ ↑ₖ s))
            ↑ₖ-wk {S₁} {S₂} ⦃ K ⦄ ϕ s sx x =  `/id-injective ⦃ K ⊔ Kᵣ ⦄ (
              `/id ⦃ K ⊔ Kᵣ ⦄ ((ϕ ⨟ wkᵣ) sx x)         ≡⟨⟩
              `/id ⦃ K ⊔ Kᵣ ⦄ (x & ϕ &/⋯ wkᵣ)          ≡⟨ &/⋯-⋯ (x & ϕ) (wkᵣ) ⟩
              `/id (`/id (x & ϕ) ⋯ wkᵣ)                  ≡⟨ WkKit.wk-`/id (wkKit K) s (x & ϕ) ⟩
              `/id (suc x & (ϕ ↑ₖ s))                     ≡⟨ sym (&/⋯-& (suc x) (ϕ ↑ₖ s)) ⟩
              `/id ⦃ K ⊔ Kᵣ ⦄ (suc x &/⋯ (ϕ ↑ₖ s))      ≡⟨⟩
              `/id ⦃ K ⊔ Kᵣ ⦄ (x & wkᵣ &/⋯ (ϕ ↑ₖ s))    ≡⟨⟩
              `/id ⦃ K ⊔ Kᵣ ⦄ ((wkᵣ ⨟ (ϕ ↑ₖ s)) sx x)  ∎) 
            
            ⋯-↑ₖ-wk  : ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ C₁ : ComposeKit K Kᵣ ⦄ ⦃ C₂ : ComposeKit Kᵣ K ⦄ 
                      (t : S₁ ⊢ s) (ϕ : S₁ –[ K ]→ S₂) s′ → 
                      t ⋯ ϕ ⋯ wkᵣ ≡ t ⋯ wkᵣ ⋯ (ϕ ↑ₖ s′)
            ⋯-↑ₖ-wk t ϕ s =
              t ⋯ ϕ ⋯ wkᵣ          ≡⟨ ⋯-fusion t ϕ (wkᵣ) ⟩
              t ⋯ (ϕ ⨟ wkᵣ)        ≡⟨ cong (t ⋯_) (~-ext (↑ₖ-wk ϕ s)) ⟩
              t ⋯ (wkᵣ ⨟ (ϕ ↑ₖ s))  ≡⟨ sym (⋯-fusion t (wkᵣ) (ϕ ↑ₖ s)) ⟩ 
              t ⋯ wkᵣ ⋯ (ϕ ↑ₖ s)     ∎

            Cᵣ-&/⋯-wk-↑ₖ  : ⦃ K₂ : Kit _∋/⊢_ ⦄ (x/t : S₁ ∋/⊢[ Kᵣ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                           Kit.wk′ K₂ s′ ((K₂ Kit.& x/t) ϕ) ≡ (K₂ Kit.& suc x/t) (ϕ ↑ₖ s′)
            Cᵣ-&/⋯-wk-↑ₖ _ _ = refl

          instance
            Cᵣ : ⦃ K : Kit _∋/⊢_ ⦄ → ComposeKit Kᵣ K
            Cᵣ = record
                    { _&/⋯_      = _&_
                    ; &/⋯-⋯      = λ x ϕ → sym (⋯-var x ϕ)
                    ; &/⋯-wk-↑ₖ  = Cᵣ-&/⋯-wk-↑ₖ }

            Cₛ : ⦃ K : Kit _∋/⊢_ ⦄ ⦃ C : ComposeKit K Kᵣ ⦄ → ComposeKit Kₛ K 
            Cₛ  = record
                    { _&/⋯_      = _⋯_
                    ; &/⋯-⋯      = λ t ϕ → refl
                    ; &/⋯-wk-↑ₖ  = λ t ϕ → ⋯-↑ₖ-wk t ϕ _ }

            {- huh : ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K₃ : Kit _∋/⊢₃_ ⦄ 
                ⦃ C : ComposeKit K₁ K₂ ⦄ → ComposeKit (K₁ ⊔ K₂) K₃
            {-# OVERLAPPING huh #-}  
            huh ⦃ K₁ = mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ C = C ⦄ 
              rewrite unique-Kᵣ-instance K₃ = Cᵣ
            huh ⦃ K₁ = mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _  _ _ _ _ _ ⦄ K₃@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ C = C ⦄ 
              rewrite unique-Kₛ-instance K₃ = Cᵣ
            huh ⦃ K₁ = mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ C = C ⦄ 
              rewrite unique-Kᵣ-instance K₃ = Cₛ
            huh ⦃ K₁ = mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ C = C ⦄ 
              rewrite unique-Kₛ-instance K₃ = Cₛ
            huh ⦃ K₁ = mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ C = C ⦄ 
              rewrite unique-Kᵣ-instance K₃ = Cₛ
            huh ⦃ K₁ = mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ C = C ⦄ 
              rewrite unique-Kₛ-instance K₃ = Cₛ
            huh ⦃ K₁ = mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Ren refl _ _ _ _ _ _ _ ⦄ ⦃ C = C ⦄ 
              rewrite unique-Kᵣ-instance K₃ = Cₛ
            huh ⦃ K₁ = mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ K₃@⦃ mkKit Sub refl _ _ _ _ _ _ _ ⦄ ⦃ C = C ⦄ 
              rewrite unique-Kₛ-instance K₃ = Cₛ -}
               
          Cᵣᵣ : ComposeKit Kᵣ Kᵣ 
          Cᵣᵣ = Cᵣ
          Cᵣₛ : ComposeKit Kᵣ Kₛ 
          Cᵣₛ = Cᵣ
          Cₛᵣ : ComposeKit Kₛ Kᵣ 
          Cₛᵣ = Cₛ
          Cₛₛ : ComposeKit Kₛ Kₛ 
          Cₛₛ = Cₛ 

          opaque
            _⨟ₖ_ : (K₁ : Kit _∋/⊢₁_) (K₂ : Kit _∋/⊢₂_) → ComposeKit K₁ K₂
            K₁@(mkKit Ren refl _ _ _ _ _ _ _) ⨟ₖ K₂@(mkKit Ren refl _ _ _ _ _ _ _) = 
              subst₂ (λ K₁ K₂ → ComposeKit K₁ K₂) (sym (unique-Kᵣ-instance K₁)) (sym (unique-Kᵣ-instance K₂)) Cᵣ
            K₁@(mkKit Ren refl _ _ _ _ _ _ _) ⨟ₖ K₂@(mkKit Sub refl _ _ _ _ _ _ _) =
              subst₂ (λ K₁ K₂ → ComposeKit K₁ K₂) (sym (unique-Kᵣ-instance K₁)) (sym (unique-Kₛ-instance K₂)) Cᵣ
            K₁@(mkKit Sub refl _ _ _ _ _ _ _) ⨟ₖ K₂@(mkKit Ren refl _ _ _ _ _ _ _) =
              subst₂ (λ K₁ K₂ → ComposeKit K₁ K₂) (sym (unique-Kₛ-instance K₁)) (sym (unique-Kᵣ-instance K₂)) Cₛ
            K₁@(mkKit Sub refl _ _ _ _ _ _ _) ⨟ₖ K₂@(mkKit Sub refl _ _ _ _ _ _ _) =
              subst₂ (λ K₁ K₂ → ComposeKit K₁ K₂) (sym (unique-Kₛ-instance K₁)) (sym (unique-Kₛ-instance K₂)) Cₛ
            
            ⨟ₖ-def₁ : Kᵣ ⨟ₖ Kᵣ ≡ Cᵣ
            ⨟ₖ-def₁ rewrite unique-Kᵣ-instance Kᵣ = refl
            ⨟ₖ-def₂ : Kᵣ ⨟ₖ Kₛ ≡ Cᵣ
            ⨟ₖ-def₂ rewrite unique-Kᵣ-instance Kᵣ | unique-Kₛ-instance Kₛ = refl
            ⨟ₖ-def₃ : Kₛ ⨟ₖ Kᵣ ≡ Cₛ
            ⨟ₖ-def₃ rewrite unique-Kᵣ-instance Kᵣ | unique-Kₛ-instance Kₛ = refl
            ⨟ₖ-def₄ : Kₛ ⨟ₖ Kₛ ≡ Cₛ
            ⨟ₖ-def₄ rewrite unique-Kₛ-instance Kₛ = refl

          {-# REWRITE ⨟ₖ-def₁ ⨟ₖ-def₂ ⨟ₖ-def₃ ⨟ₖ-def₄  #-}

          _↑_ : ⦃ K : Kit _∋/⊢_ ⦄ ⦃ C : ComposeKit K Kᵣ ⦄ → S₁ –[ K ]→ S₂ → ∀ s → (s ∷ S₁) –[ K ]→ (s ∷ S₂)
          ϕ ↑ s = id/` zero ∙ (ϕ ⨟ wkᵣ) 

          _↑ₛ_ : S₁ →ₛ S₂ → ∀ s → (s ∷ S₁) →ₛ (s ∷ S₂)
          _↑ₛ_ = _↑_

          _↑ᵣ_ : S₁ →ᵣ S₂ → ∀ s → (s ∷ S₁) →ᵣ (s ∷ S₂)
          _↑ᵣ_ = _↑_ 

          _↑⋆_ : ⦃ K : Kit _∋/⊢_ ⦄ ⦃ C : ComposeKit K Kᵣ ⦄ → S₁ –[ K ]→ S₂ → ∀ S → (S ++ S₁) –[ K ]→ (S ++ S₂)
          ϕ ↑⋆ []       = ϕ
          ϕ ↑⋆ (s ∷ S)  = (ϕ ↑⋆ S) ↑ s 

          _↑ᵣ⋆_ : S₁ →ᵣ S₂ → ∀ S → (S ++ S₁) →ᵣ (S ++ S₂)
          _↑ᵣ⋆_ = _↑⋆_

          _↑ₛ⋆_ : S₁ →ₛ S₂ → ∀ S → (S ++ S₁) →ₛ (S ++ S₂)
          _↑ₛ⋆_ = _↑⋆_

{-        opaque
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
            
            dist-↑ₖ-⦅⦆ :
              ∀  ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
                 ⦃ W₂ : WkKit K₂ ⦄
                 ⦃ C₁ : ComposeKit K₁ K₂ K ⦄ ⦃ C₂ : ComposeKit K₂ K K ⦄
                 (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                 (⦅ x/t ⦆ ⨟[ C₁ ] ϕ) ~ ((ϕ ↑ₖ s) ⨟[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆)
            dist-↑ₖ-⦅⦆ {s = s} ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ x/t ϕ sx x@zero = `/id-injective (
              `/id ⦃ K ⦄ (x & (⦅ x/t ⦆ ⨟[ C₁ ] ϕ))                ≡⟨⟩
              `/id ⦃ K ⦄ (x/t &/⋯ ϕ)                              ≡⟨⟩
              `/id ⦃ K ⦄ (zero & ⦅ (x/t &/⋯ ϕ) ⦆)                 ≡⟨ sym (&/⋯-& ⦃ C₂ ⦄ zero ⦅ (x/t &/⋯ ϕ) ⦆) ⟩
              `/id ⦃ K ⦄ (id/` ⦃ K₂ ⦄ zero &/⋯ ⦅ (x/t &/⋯ ϕ) ⦆)   ≡⟨⟩
              `/id ⦃ K ⦄ (x & ((ϕ ↑ₖ s) ⨟[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆))  ∎)
            dist-↑ₖ-⦅⦆ {s = s} ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ x/t ϕ sx x@(suc y) = `/id-injective (
              `/id (x & (⦅ x/t ⦆ ⨟[ C₁ ] ϕ))                ≡⟨⟩
              `/id (id/` ⦃ K₁ ⦄ y &/⋯ ϕ)                    ≡⟨ &/⋯-& ⦃ C₁ ⦄ y ϕ ⟩
              `/id (y & ϕ)                                  ≡⟨ sym (wk-cancels-⦅⦆-⋯ (`/id (y & ϕ)) (x/t &/⋯ ϕ)) ⟩
              `/id (y & ϕ) ⋯ wkᵣ ⋯ ⦅ (x/t &/⋯ ϕ) ⦆    ≡⟨ cong (_⋯ ⦅ x/t &/⋯ ϕ ⦆) (wk-`/id s (y & ϕ)) ⟩
              `/id (wk′ s (y & ϕ)) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆         ≡⟨ sym (&/⋯-⋯ (wk′ s (y & ϕ)) ⦅ (x/t &/⋯ ϕ) ⦆) ⟩
              `/id (wk′ s (y & ϕ) &/⋯ ⦅ (x/t &/⋯ ϕ) ⦆)       ≡⟨⟩
              `/id (x & ((ϕ ↑ₖ s) ⨟[ C₂ ] ⦅ (x/t &/⋯ ϕ) ⦆))  ∎)
            
            dist-↑ₖ-⦅⦆-⋯ :
              ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
                ⦃ W₁ : WkKit K₁ ⦄ ⦃ W₂ : WkKit K₂ ⦄
                ⦃ C₁ : ComposeKit K₁ K₂ K ⦄ ⦃ C₂ : ComposeKit K₂ K K ⦄
                (t : (s ∷ S₁) ⊢ s′) (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ₖ s) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆
            dist-↑ₖ-⦅⦆-⋯ t x/t ϕ =
              t ⋯ ⦅ x/t ⦆ ⋯ ϕ                   ≡⟨ ⋯-fusion t ⦅ x/t ⦆ ϕ ⟩
              t ⋯ (⦅ x/t ⦆ ⨟ ϕ)                ≡⟨ cong (t ⋯_) (~-ext (dist-↑ₖ-⦅⦆ x/t ϕ)) ⟩
              t ⋯ ((ϕ ↑ₖ _) ⨟ ⦅ (x/t &/⋯ ϕ) ⦆)  ≡⟨ sym (⋯-fusion t (ϕ ↑ₖ _) ⦅ x/t &/⋯ ϕ ⦆ ) ⟩
              t ⋯ (ϕ ↑ₖ _) ⋯ ⦅ (x/t &/⋯ ϕ) ⦆     ∎
 -}