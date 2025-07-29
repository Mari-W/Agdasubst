-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances -WnoUserWarning #-}
module Agdasubst.Lib where

open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim) 
open import Data.Unit using (⊤; tt)

open import Agdasubst.Common 

--! A >

module KitsWithSort (
  --!! SortParam
  Sort : Set

  ) where
    open CommonWithSort Sort 
    open Meta 

    --! Syntax {
    record Syntax : Set₁ where
      --! [
      constructor mkSyntax
      --! ]
      field 
        _⊢_  : Scoped
        `_   : S ∋ s → S ⊢ s
      --! }
        `-injective : ` x₁ ≡ ` x₂ → x₁ ≡ x₂

      --! Image
      image : Tag → Scoped
      image Ren  = _∋_
      image Sub  = _⊢_

      -- prevents users from outside the library to construct more Kit and ComposeKit instances
      -- thus: the unique–Kᴿ, unique–Kˢ, unique–Cᴿ and unique–Cˢ postulates 
      -- cannot do any harm outside this file 
      --! Lock
      private data Lock : Set where
        unlock : Lock 

      --! Kit
      record Kit (k : Tag) : Set₁ where
        _∋/⊢ᴷ_ = image k

        -- KitFields
        field
          K-id/`  : S ∋ s → S ∋/⊢ᴷ s
          K-`/id  : S ∋/⊢ᴷ s → S ⊢ s
          K-wk    : ∀ s′ → S ∋/⊢ᴷ s → (s′ ∷ S) ∋/⊢ᴷ s
          lock    : Lock

          `/`-is-`        : ∀ (x : S ∋ s) → K-`/id (K-id/` x) ≡ ` x
          id/`-injective  : K-id/` x₁ ≡ K-id/` x₂ → x₁ ≡ x₂
          `/id-injective  : ∀ {x/t₁ x/t₂ : S ∋/⊢ᴷ s} →
                              K-`/id x/t₁ ≡ K-`/id x/t₂ → x/t₁ ≡ x/t₂
          wk-id/`         : ∀ {s} s′ (x : S ∋ s) →
                              K-wk s′ (K-id/` x) ≡ K-id/` (suc x) 

        infixl 8 _&_
        opaque 
          kit_ops : ⊤
          kit_ops = tt

          id/` : S ∋ s → S ∋/⊢ᴷ s 
          id/` = K-id/` 

          `/id : S ∋/⊢ᴷ s → S ⊢ s
          `/id = K-`/id

          --! Map
          _→ᴷ_ : Scope → Scope → Set
          S₁ →ᴷ S₂ = ∀ s → S₁ ∋ s → S₂ ∋/⊢ᴷ s

          _&_ : ∀ {s} → S₁ ∋ s → S₁ →ᴷ S₂ → S₂ ∋/⊢ᴷ s
          x & ϕ = ϕ _ x 

          id : S →ᴷ S
          id s x = id/` x 

          _;wk : ∀ {s} → S₁ →ᴷ S₂ → S₁ →ᴷ (s ∷ S₂)
          _;wk ϕ _ x = K-wk _ (ϕ _ x) -- will be rewritten to ϕ ; wk 
                                      -- when composition is defined

          wk : S →ᴷ (s ∷ S)
          wk = id ;wk 

          _∙_ : S₂ ∋/⊢ᴷ s → S₁ →ᴷ S₂ → (s ∷ S₁) →ᴷ S₂
          (q ∙ ϕ) _ zero     = q
          (q ∙ ϕ) _ (suc x)  = ϕ _ x 
        
        
        ⦅_⦆ : S ∋/⊢ᴷ s → (s ∷ S) →ᴷ S
        ⦅ q ⦆ = q ∙ id

        _↑_ : S₁ →ᴷ S₂ → ∀ s → (s ∷ S₁) →ᴷ (s ∷ S₂)
        ϕ ↑ s = (id/` zero) ∙ (ϕ ;wk)

        _↑★_ : S₁ →ᴷ S₂ → ∀ S → (S ++ S₁) →ᴷ (S ++ S₂)
        ϕ ↑★ []       = ϕ
        ϕ ↑★ (s ∷ S)  = (ϕ ↑★ S) ↑ s 

        --! Ext
        _~_ : (ϕ₁ ϕ₂ : S₁ →ᴷ S₂) → Set
        _~_ {S₁} ϕ₁ ϕ₂ = ∀ s (x : S₁ ∋ s) → x & ϕ₁ ≡ x & ϕ₂
        postulate 
          ~-ext : ∀ {ϕ₁ ϕ₂ : S₁ →ᴷ S₂} → ϕ₁ ~ ϕ₂ → ϕ₁ ≡ ϕ₂ 

        opaque 
          unfolding kit_ops

          id↑~id : (id {S} ↑ s) ~ id {s ∷ S}
          id↑~id s zero    = refl
          id↑~id s (suc x) =
            (id ↑ _) s (suc x) ≡⟨⟩
            K-wk _ (id/` x)      ≡⟨ wk-id/` _ x ⟩
            id/` (suc x)         ≡⟨⟩
            id s (suc x)         ∎
          
          id↑≡id :  (id/` (zero {s = s} {S = S})) ∙ (id ;wk) ≡ id
          id↑≡id = ~-ext id↑~id

          id↑★~id : ∀ S → (id ↑★ S) ~ id {S ++ S′}
          id↑★~id []      sx x = refl
          id↑★~id (s ∷ S) sx x =
            ((id ↑★ S) ↑ s) sx x ≡⟨ cong (λ ■ → (■ ↑ s) sx x) (~-ext (id↑★~id S)) ⟩
            (id ↑ s) sx x        ≡⟨ id↑~id sx x ⟩
            id sx x              ∎
          
          id↑★≡id : ∀ S → (id ↑★ S) ≡ id {S ++ S′}
          id↑★≡id S = ~-ext (id↑★~id S)

      --! KitExplicit { 
      _∋/⊢[_]_ : Scope → Kit k → Sort → Set
      _∋/⊢[_]_ {k} S _ s = image k S s
 
      _–[_]→_ : Scope → Kit k → Scope → Set
      S₁ –[ K ]→ S₂ = Kit._→ᴷ_ K S₁ S₂

      id[_] : (K : Kit k) → S –[ K ]→ S
      id[ K ] = Kit.id K 
      --! }

      open Kit {{...}} public hiding (wk)

      _`⋯_ : ∀ {{K : Kit k}} → S₁ ∋ s → S₁ →ᴷ S₂ → S₂ ⊢ s 
      x `⋯ ϕ = `/id (x & ϕ) 

      opaque 
        unfolding kit_ops
        `⋯-id : ∀ {{K : Kit k}} → (x `⋯ id) ≡ (` x)
        `⋯-id {x = x} = `/`-is-` x

      --! Traveral {
      record Traversal : Set₁ where
        --! [
        constructor mkTraversal
        infixl   5  _⋯_
        --! ]
        field  
          _⋯_    : ∀ {{K : Kit k}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
        --! }

          ⋯-id   : ∀ {{K : Kit k}} → (t : S ⊢ s) →
                     t ⋯ id {{K}} ≡ t
          ⋯-var  : ∀ {{K : Kit k}} → (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) →
                     (` x) ⋯ ϕ ≡ `/id {{K}} (x & ϕ)

        --! InstanceRen
        instance opaque 
          Kᴿ : Kit Ren 
          Kᴿ = record
            { K-id/`           = λ x → x
            ; K-`/id           = `_
            ; K-wk             = λ s′ x → suc x
            ; `/`-is-`        = λ x → refl
            ; id/`-injective  = λ eq → eq 
            ; `/id-injective  = `-injective  
            ; wk-id/`         = λ s′ x → refl 
            ; lock            = unlock
            } 
        
        open Kit Kᴿ public using () renaming 
          (_→ᴷ_ to _→ᴿ_; _&_ to _&ᴿ_; _∙_ to _∙ᴿ_; id to idᴿ; wk to wkᴿ; _↑_ to _↑ᴿ_; _↑★_ to _↑ᴿ★_)

        _⋯ᴿ_ : S₁ ⊢ s → S₁ →ᴿ S₂ → S₂ ⊢ s
        t ⋯ᴿ ρ = t ⋯ ρ

        -- opaque
        --   unfolding kit_ops Kᴿ 
        --   private 
        --     Kˢ-wk-id/` : ∀ {S : Scope} {s} (s′) (x : S ∋ s) →
        --                 (` x) ⋯ wkᴿ {s = s′} ≡ (` suc x)
        --     Kˢ-wk-id/` = λ s′ x → ⋯-var x wkᴿ

        --! InstanceSub
        instance opaque
          unfolding kit_ops Kᴿ

          kits : ⊤
          kits = tt

          Kˢ : Kit Sub
          Kˢ = record
            { K-id/`           = `_
            ; K-`/id           = λ t → t
            ; K-wk             = λ s′ t → t ⋯ wkᴿ
            ; `/`-is-`        = λ x → refl
            ; id/`-injective  = `-injective
            ; `/id-injective  = λ eq → eq 
            ; wk-id/`         = λ s′ x → ⋯-var x wkᴿ
            ; lock            = unlock
            }

        open Kit Kˢ public using () renaming 
          (_→ᴷ_ to _→ˢ_; _&_ to _&ˢ_; _∙_ to _∙ˢ_; id to idˢ; _↑_ to _↑ˢ_; _↑★_ to _↑ˢ★_)

        _⋯ˢ_ : S₁ ⊢ s → S₁ →ˢ S₂ → S₂ ⊢ s
        t ⋯ˢ σ = t ⋯ σ 

        --! UniqueKits
        private postulate
          unique–Kᴿ : (K : Kit Ren) → Kᴿ ≡ K
          unique–Kˢ : (K : Kit Sub) → Kˢ ≡ K

        unique–K–by : (k : Tag) → Kit k   
        unique–K–by Ren = Kᴿ
        unique–K–by Sub = Kˢ

        unique–K : (K : Kit k) → K ≡ unique–K–by k 
        unique–K {Ren} K = sym (unique–Kᴿ K)
        unique–K {Sub} K = sym (unique–Kˢ K)

        --! TagLub
        opaque
          _⨆_ : Tag → Tag → Tag
          Ren  ⨆ Ren  = Ren
          Ren  ⨆ Sub  = Sub
          Sub  ⨆ Ren  = Sub
          Sub  ⨆ Sub  = Sub

          --! TagLubLaws
          ⨆-idem       : k ⨆ k    ≡ k 
          ⨆-bot-right  : k ⨆ Ren  ≡ k 
          ⨆-bot-left   : Ren ⨆ k  ≡ k
          ⨆-top-right  : k ⨆ Sub  ≡ Sub
          ⨆-top-left   : Sub ⨆ k  ≡ Sub
          ⨆-assoc      : (k₁ ⨆ k₂) ⨆ k₃  ≡ k₁ ⨆ (k₂ ⨆ k₃)
          ⨆-comm       : (k₁ ⨆ k₂)  ≡ (k₂ ⨆ k₁)

          ⨆-idem {Ren} = refl
          ⨆-idem {Sub} = refl 

          ⨆-bot-right {Ren} = refl 
          ⨆-bot-right {Sub} = refl 

          ⨆-bot-left {Ren} = refl 
          ⨆-bot-left {Sub} = refl 

          ⨆-top-right {Ren} = refl 
          ⨆-top-right {Sub} = refl  

          ⨆-top-left {Ren} = refl 
          ⨆-top-left {Sub} = refl  

          ⨆-assoc {Ren} {Ren} {Ren} = refl
          ⨆-assoc {Ren} {Ren} {Sub} = refl
          ⨆-assoc {Ren} {Sub} {Ren} = refl
          ⨆-assoc {Ren} {Sub} {Sub} = refl
          ⨆-assoc {Sub} {Ren} {Ren} = refl
          ⨆-assoc {Sub} {Ren} {Sub} = refl
          ⨆-assoc {Sub} {Sub} {Ren} = refl
          ⨆-assoc {Sub} {Sub} {Sub} = refl

          ⨆-comm {Ren} {Ren} = refl
          ⨆-comm {Ren} {Sub} = refl
          ⨆-comm {Sub} {Ren} = refl
          ⨆-comm {Sub} {Sub} = refl
        
        --! RewriteTagLubLaws
        {-# REWRITE ⨆-idem ⨆-bot-right ⨆-bot-left ⨆-top-right ⨆-top-left ⨆-assoc #-}

        --! KitLub
        opaque
          unfolding _⨆_
          _⊔_ : (K₁ : Kit k₁) (K₂ : Kit k₂) → Kit (k₁ ⨆ k₂)
          _⊔_ {Ren} {Ren} K₁ K₂ = Kᴿ
          _⊔_ {Ren} {Sub} K₁ K₂ = Kˢ
          _⊔_ {Sub} {Ren} K₁ K₂ = Kˢ
          _⊔_ {Sub} {Sub} K₁ K₂ = Kˢ

          --! KitLubLaws
          ⊔-idem       : {{K : Kit k}} → K ⊔ K   ≡ K
          ⊔-bot-right  : {{K : Kit k}} → K ⊔ Kᴿ  ≡ K
          ⊔-bot-left   : {{K : Kit k}} → Kᴿ ⊔ K  ≡ K  
          ⊔-top-right  : {{K : Kit k}} → K ⊔ Kˢ  ≡ Kˢ
          ⊔-top-left   : {{K : Kit k}} → Kˢ ⊔ K  ≡ Kˢ
          ⊔-assoc      : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} → (K₁ ⊔ K₂) ⊔ K₃ ≡ K₁ ⊔ (K₂ ⊔ K₃)
          ⊔-comm       : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} → (K₁ ⊔ K₂) ≡ subst Kit (⨆-comm {k₂} {k₁}) (K₂ ⊔ K₁)

          ⊔-idem {Ren} {{K}} = unique–Kᴿ K
          ⊔-idem {Sub} {{K}} = unique–Kˢ K

          ⊔-bot-right {Ren} {{K}} = unique–Kᴿ K 
          ⊔-bot-right {Sub} {{K}} = unique–Kˢ K 

          ⊔-bot-left {Ren} {{K}} = unique–Kᴿ K
          ⊔-bot-left {Sub} {{K}} = unique–Kˢ K

          ⊔-top-right {Ren} = refl
          ⊔-top-right {Sub} = refl

          ⊔-top-left {Ren} = refl
          ⊔-top-left {Sub} = refl

          ⊔-assoc {Ren} {Ren} {Ren} = refl
          ⊔-assoc {Ren} {Ren} {Sub} = refl 
          ⊔-assoc {Ren} {Sub} {Ren} = refl
          ⊔-assoc {Ren} {Sub} {Sub} = refl
          ⊔-assoc {Sub} {Ren} {Ren} = refl
          ⊔-assoc {Sub} {Ren} {Sub} = refl
          ⊔-assoc {Sub} {Sub} {Ren} = refl 
          ⊔-assoc {Sub} {Sub} {Sub} = refl

          ⊔-comm {Ren} {Ren} = refl
          ⊔-comm {Ren} {Sub} = refl
          ⊔-comm {Sub} {Ren} = refl 
          ⊔-comm {Sub} {Sub} = refl

        --! RewriteKitLubLaws
        {-# REWRITE ⊔-idem ⊔-bot-right ⊔-bot-left ⊔-top-right ⊔-top-left ⊔-assoc #-}

        module KitsMeta where
          variable 
            t t₁ t₂ t₃ t₄ t₅ t′ t₁′ t₂′ t₃′ t₄′ t₅′ : S ⊢ s
            ρ ρ₁ ρ₂ ρ₃ ρ₄ ρ₅ ρ′ ρ₁′ ρ₂′ ρ₃′ ρ₄′ ρ₅′ : S₁ →ᴿ S₂
            σ σ₁ σ₂ σ₃ σ₄ σ₅ σ′ σ₁′ σ₂′ σ₃′ σ₄′ σ₅′ : S₁ →ˢ S₂

        record WkKit (K : Kit k): Set₁ where 
          private instance _ = K
          field
            wk-`/id  : ∀ s (q : S ∋/⊢[ K ] s′) → `/id q ⋯ᴿ wkᴿ ≡ `/id (K-wk s q)

        open WkKit {{...}} public

        opaque
          unfolding kits
          Wᴿ : WkKit Kᴿ
          Wᴿ = record { wk-`/id =  λ s′ x → ⋯-var x wkᴿ }

          Wˢ : WkKit Kˢ
          Wˢ = record { wk-`/id = λ s q → refl } 
        
        instance
          wkKit : {{K : Kit k}} → WkKit K
          wkKit {Ren} {{K}} = subst WkKit (unique–Kᴿ K) Wᴿ 
          wkKit {Sub} {{K}} = subst WkKit (unique–Kˢ K) Wˢ 


        --! ComposeKit
        record ComposeKit (K₁ : Kit k₁) (K₂ : Kit k₂) (K₃ : Kit k₃) : Set₁ where

          private instance _ = K₁; _ = K₂; _ = K₃

          infixl 8 _&/⋯′_
          field
            _&/⋯′_    : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₃ ] s 
           
            &/⋯-⋯     : (q : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                        `/id q ⋯ ϕ ≡ `/id (q &/⋯′ ϕ)
            &/⋯-wk-↑ : (q : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                       K-wk s′ (q &/⋯′ ϕ) ≡ K-wk s′ q &/⋯′ (ϕ ↑ s′) 
            lock      : Lock

          opaque
            unfolding kits _⊔_
 
            comp_ops : ⊤
            comp_ops = tt 

            infixl 8 _&/⋯_
            --!! LookOrApp
            _&/⋯_ : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₃ ] s
            
            --!! Comp
            _;_ : S₁ –[ K₁ ]→ S₂ → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₃ ]→ S₃

            (ϕ₁ ; ϕ₂) _ x = (x & ϕ₁) &/⋯ ϕ₂
            _&/⋯_ = _&/⋯′_ 
 
          opaque
            unfolding comp_ops 
  
            &/⋯-& : ∀ (x : S₁ ∋ s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                    `/id (id/` {{K₁}} x &/⋯ ϕ) ≡ `/id (x & ϕ)
            &/⋯-& x ϕ = 
              `/id (id/` x &/⋯ ϕ)       ≡⟨ sym (&/⋯-⋯ (id/` x) ϕ) ⟩
              `/id {{K₁}} (id/` x) ⋯ ϕ  ≡⟨ cong (_⋯ ϕ) (`/`-is-` {{K₁}} x) ⟩
              ` x ⋯ ϕ                   ≡⟨ ⋯-var {{K₂}} x ϕ ⟩
              `/id {{K₂}}  (x & ϕ)      ∎

            dist-↑-;  : ∀ s (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                      ((ϕ₁ ; ϕ₂) ↑ s) ~ ((ϕ₁ ↑ s) ; (ϕ₂ ↑ s))
            dist-↑-; s ϕ₁ ϕ₂ s₁ x@zero = `/id-injective (   
              `/id (x & ((ϕ₁ ; ϕ₂) ↑ s))         ≡⟨⟩
              `/id {{K₃}} (id/` zero)             ≡⟨ `/`-is-` {{K₃}} zero ⟩
              ` zero                              ≡⟨ sym (`/`-is-` {{K₂}} zero) ⟩
              `/id {{K₂}} (id/` zero)             ≡⟨⟩
              `/id {{K₂}} (zero & (ϕ₂ ↑ s))      ≡⟨ sym (&/⋯-& (id/` zero) (ϕ₂ ↑ s)) ⟩
              `/id (id/` zero &/⋯ (ϕ₂ ↑ s))      ≡⟨⟩
              `/id (x & (ϕ₁ ↑ s) &/⋯ (ϕ₂ ↑ s))  ≡⟨⟩
              `/id (x & ((ϕ₁ ↑ s) ; (ϕ₂ ↑ s)))  ∎
              )
            dist-↑-; s ϕ₁ ϕ₂ s₁ x@(suc y) = `/id-injective (
              `/id (x & ((ϕ₁ ; ϕ₂) ↑ s))          ≡⟨⟩
              `/id (K-wk _ ( y & (ϕ₁ ; ϕ₂)))       ≡⟨⟩
              `/id (K-wk _ (y & ϕ₁ &/⋯ ϕ₂))        ≡⟨ cong (`/id) (&/⋯-wk-↑ (y & ϕ₁) ϕ₂) ⟩
              `/id (K-wk _ (y & ϕ₁) &/⋯ (ϕ₂ ↑ s)) ≡⟨⟩
              `/id (x & (ϕ₁ ↑ s) &/⋯ (ϕ₂ ↑ s))   ≡⟨⟩
              `/id (x & ((ϕ₁ ↑ s) ; (ϕ₂ ↑ s)))   ∎
              )
            
            dist–↑–; : ∀ s (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                       ((ϕ₁ ↑ s) ; (ϕ₂ ↑ s)) ≡ ((ϕ₁ ; ϕ₂) ↑ s)
            dist–↑–; s ϕ₁ ϕ₂ = sym (~-ext (dist-↑-; s ϕ₁ ϕ₂))

            dist-↑★-;  : ∀ S (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                        ((ϕ₁ ; ϕ₂) ↑★ S) ~ ((ϕ₁ ↑★ S) ; (ϕ₂ ↑★ S))
            dist-↑★-; []      ϕ₁ ϕ₂ sx x = refl
            dist-↑★-; (s ∷ S) ϕ₁ ϕ₂ sx x =
              ((ϕ₁ ; ϕ₂) ↑★ (s ∷ S)) sx x                  ≡⟨⟩
              (((ϕ₁ ; ϕ₂) ↑★ S) ↑ s) sx x                 ≡⟨ cong (λ ■ → ( ■ ↑  s) sx x) (~-ext (dist-↑★-; S ϕ₁ ϕ₂)) ⟩
              (((ϕ₁ ↑★ S) ; (ϕ₂ ↑★ S)) ↑ s) sx x         ≡⟨ dist-↑-; s (ϕ₁ ↑★ S) (ϕ₂ ↑★ S) sx x ⟩
              (((ϕ₁ ↑★ S) ↑ s) ; ((ϕ₂ ↑★ S) ↑ s)) sx x  ≡⟨⟩
              ((ϕ₁ ↑★ (s ∷ S)) ; (ϕ₂ ↑★ (s ∷ S))) sx x    ∎
            
            dist–↑★–;  : ∀ S (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                         ((ϕ₁ ↑★ S) ; (ϕ₂ ↑★ S)) ≡ ((ϕ₁ ; ϕ₂) ↑★ S)
            dist–↑★–; S ϕ₁ ϕ₂ = sym (~-ext (dist-↑★-; S ϕ₁ ϕ₂))
        
        open ComposeKit {{...}} public
        
        --! ComposeExplicit
        _;[_]_  : ∀ {K₁ : Kit k₁} {K₂ : Kit k₂} {K₃ : Kit k₃} →
                  S₁ –[ K₁ ]→ S₂ → ComposeKit K₁ K₂ K₃ →
                  S₂ –[ K₂ ]→ S₃ → S₁ –[ K₃ ]→ S₃
        _;[_]_ {K₁} {K₂} {K₃} ϕ₁ C ϕ₂ = ComposeKit._;_ {K₁} {K₂} {K₃} C ϕ₁ ϕ₂   

        _&/⋯[_]_  : ∀ {K₁ : Kit k₁} {K₂ : Kit k₂} {K₃ : Kit k₃} →
                  S₁ ∋/⊢[ K₁ ] s → ComposeKit K₁ K₂ K₃ → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₃ ] s
        _&/⋯[_]_ {K₁} {K₂} {K₃} q C ϕ₂ = ComposeKit._&/⋯_ {K₁} {K₂} {K₃} C q ϕ₂   

        opaque
          unfolding comp_ops

          `⋯-compositionality : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}} 
                (x : S₁ ∋ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                 ((x `⋯ ϕ₁) ⋯ ϕ₂) ≡ (x `⋯ (ϕ₁ ; ϕ₂))
          `⋯-compositionality x ϕ₁ ϕ₂ = &/⋯-⋯ (ϕ₁ _ x) ϕ₂

        --! compositionality {
        record Compose : Set₁ where
          --! [
          constructor mkCompose 
          --! ]
          field
            ⋯-compositionality : ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}}
                       (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
                       (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
          --! }
          
          opaque
            unfolding comp_ops 
          
            ↑-wk  : ∀ {{K : Kit k}}
                    {{C₁ : ComposeKit K Kᴿ K}} {{C₂ : ComposeKit Kᴿ K K}} 
                    (ϕ : S₁ –[ K ]→ S₂) s → 
                    (ϕ ; wkᴿ) ~ (wkᴿ ; (ϕ ↑ s))
            ↑-wk {S₁} {S₂} {{K}} ϕ s sx x =  `/id-injective (
              `/id ((ϕ ; wkᴿ) sx x)        ≡⟨⟩
              `/id (x & ϕ &/⋯ wkᴿ)         ≡⟨ sym (&/⋯-⋯ (x & ϕ) (wkᴿ)) ⟩
              `/id (`/id (x & ϕ) ⋯ wkᴿ)    ≡⟨ wk-`/id s (x & ϕ) ⟩
              `/id (suc x & (ϕ ↑ s))       ≡⟨ sym (&/⋯-& (suc x) (ϕ ↑ s)) ⟩
              `/id (suc x &/⋯ (ϕ ↑ s))     ≡⟨⟩
              `/id (x & wkᴿ &/⋯ (ϕ ↑ s))   ≡⟨⟩
              `/id ((wkᴿ ; (ϕ ↑ s)) sx x)  ∎) 
            
            ⋯-↑-wk  : ∀ {{K : Kit k}} {{C₁ : ComposeKit K Kᴿ K}} {{C₂ : ComposeKit Kᴿ K K}} 
                      (t : S₁ ⊢ s) (ϕ : S₁ –[ K ]→ S₂) s′ → 
                      t ⋯ ϕ ⋯ wkᴿ ≡ t ⋯ wkᴿ ⋯ (ϕ ↑ s′)
            ⋯-↑-wk t ϕ s =
              t ⋯ ϕ ⋯ wkᴿ           ≡⟨ ⋯-compositionality t ϕ (wkᴿ) ⟩
              t ⋯ (ϕ ; wkᴿ)         ≡⟨ cong (t ⋯_) (~-ext (↑-wk ϕ s)) ⟩
              t ⋯ (wkᴿ ; (ϕ ↑ s))   ≡⟨ sym (⋯-compositionality t (wkᴿ) (ϕ ↑ s)) ⟩  
              t ⋯ wkᴿ ⋯ (ϕ ↑ s)    ∎

          instance opaque 
            unfolding comp_ops
            --! InstanceCRen
            Cᴿ : {{K : Kit k}} → ComposeKit Kᴿ K K

            Cᴿ = record
                    { _&/⋯′_    = _&_ 
                    ; &/⋯-⋯     = λ x ϕ → ⋯-var x ϕ
                    ; &/⋯-wk-↑ = λ x ϕ → refl
                    ; lock      = unlock }

          instance opaque
            unfolding comp_ops Cᴿ 

            lib : ⊤ 
            lib = tt

            --! InstanceCSub
            Cˢ : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} → ComposeKit Kˢ K Kˢ
            Cˢ  = record
                    { _&/⋯′_    = _⋯_
                    ; &/⋯-⋯     = λ x ϕ → refl
                    ; &/⋯-wk-↑ = λ t ϕ → ⋯-↑-wk t ϕ _ 
                    ; lock      = unlock }  

          Cᴿᴿ = Cᴿ {{Kᴿ}}
          Cᴿˢ = Cᴿ {{Kˢ}}
          Cˢᴿ = Cˢ {{Kᴿ}} {{Cᴿ {{Kᴿ}}}}
          Cˢˢ = Cˢ {{Kˢ}} {{Cˢ {{Kᴿ}} {{Cᴿ {{Kᴿ}}}}}}

          --! UniqueCKits
          private postulate
            unique–Cᴿ  : {{K : Kit k}} (C : ComposeKit Kᴿ K K) → C ≡ Cᴿ
            unique–Cˢ  : {{K : Kit k}} {{C′ : ComposeKit K Kᴿ K}} → (C : ComposeKit Kˢ K Kˢ) → C ≡ Cˢ 
            
            -- By assumption all _incoming_ ComposeKits to a function must be valid. 
            -- Invalid ones can be disgarded using the functions below. 
            impossible–Cˢᴷᴿ : {{K : Kit k}} → ¬ ComposeKit Kˢ K Kᴿ
            impossible–Cᴷˢᴿ : {{K : Kit k}} → ¬ ComposeKit K Kˢ Kᴿ
            impossible–Cᴿᴿˢ : ¬ ComposeKit Kᴿ Kᴿ Kˢ  

          opaque
            -- SAFETY: 
            --   For each usage of this definition it must be checked, that no 
            --   invalid ComposeKit (e.g. ComposeKit Kᴿ Kᴿ Kˢ) is created.
            {-# NON_COVERING #-}
            _,_,_ : (K₁ : Kit k₁) (K₂ : Kit k₂) (K₃ : Kit k₃) → ComposeKit K₁ K₂ K₃
            _,_,_ {Ren} {Ren} {Ren} K₁ K₂ K₃ rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ 
              = Cᴿᴿ
            _,_,_ {Ren} {Sub} {Sub} K₁ K₂ K₃ rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ 
              = Cᴿˢ
            _,_,_ {Sub} {Ren} {Sub} K₁ K₂ K₃ rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ 
              = Cˢᴿ
            _,_,_ {Sub} {Sub} {Sub} K₁ K₂ K₃ rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ 
              = Cˢˢ 
            {-# WARNING_ON_USAGE _,_,_ "SAFETY: For each usage of this definition it must be checked, that no invalid ComposeKit (e.g. ComposeKit Kᴿ Kᴿ Kˢ) is created." #-}

            -- SAFETY: By assumption the incoming (C : ComposeKit K₁ K₂ K₃) is valid. 
            --    Thus (K₁ , K₂ , K₃) is too.
            unique–C : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} → (C : ComposeKit K₁ K₂ K₃) → C ≡ K₁ , K₂ , K₃
            unique–C {Ren} {Ren} {Ren} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–Cᴿ {{Kᴿ}} C = refl
            unique–C {Ren} {Ren} {Sub} {{K₁}} {{K₂}} {{K₃}} C rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ = ⊥-elim (impossible–Cᴿᴿˢ C)
            unique–C {_} {Sub} {Ren} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₂ | unique–K K₃ = ⊥-elim (impossible–Cᴷˢᴿ C)
            unique–C {Ren} {Sub} {Sub} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–Cᴿ {{Kˢ}} C = refl
            unique–C {Sub} {_} {Ren} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₁ | unique–K K₃ = ⊥-elim (impossible–Cˢᴷᴿ  C)
            unique–C {Sub} {Ren} {Sub} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–Cˢ {{Kᴿ}} {{Cᴿ {{Kᴿ}}}} C = refl
            unique–C {Sub} {Sub} {Sub} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–Cˢ {{Kˢ}} C = refl

          instance 
            Cᴷᴿᴷ : {{K : Kit k}} → ComposeKit K Kᴿ K 
            {-# INCOHERENT Cᴷᴿᴷ #-}
            -- SAFETY: By induction on K and uniqueness of Kits.
            --  If K = Kᴿ, we have Kᴿ , Kᴿ , Kᴿ ∎
            --  If K = Kˢ, we have Kˢ , Kᴿ , ^Kˢ ∎
            Cᴷᴿᴷ {{K}} = K , Kᴿ , K 

          -- Safe variant of _,_,_.
          _;ᶜ_ : (K₁ : Kit k₁) (K₂ : Kit k₂) → ComposeKit K₁ K₂ (K₁ ⊔ K₂)
          -- SAFETY: By induction on K₁, K₂ and K₃, uniqueness of Kits and the definition of _⊔_ ∎
          K₁ ;ᶜ K₂ = K₁ , K₂ , (K₁ ⊔ K₂)

          -- SAFETY: By induction on K and uniqueness of Kits ∎
          CK–defR : {{K : Kit k}} → Kᴿ , K , K ≡ Cᴿ {{K = K}}
          CK–defR {{K}} = unique–Cᴿ {{K = K}} (Kᴿ , K , K)

          -- SAFETY: By induction on K and uniqueness of Kits ∎
          CK–defS : {{K : Kit k}} → Kˢ , K , Kˢ ≡ Cˢ {{K = K}} {{C = K , Kᴿ , K}} 
          CK–defS {{K}} = unique–Cˢ {{K = K}} {{C′ = K , Kᴿ , K}} (Kˢ , K , Kˢ)

          {-# REWRITE CK–defR CK–defS #-} 
          
          weaken : S ⊢ s → (s′ ∷ S) ⊢ s
          weaken t = t &/⋯ wkᴿ

          _[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
          t [ t′ ] = t &/⋯ (t′ ∙ id) 

          wk : {{K : Kit k}} → S –[ K ]→ (s ∷ S)
          wk = id ; wkᴿ

          opaque
            unfolding lib 
 
            id`–def : ∀ {{K : Kit k}} (x : S ∋ s) → 
              id/` x ≡ x &/⋯ (id {{K}})
            id`–def x = refl 

            postulate 
              `id–def : ∀ {{K : Kit k}} (q : S ∋/⊢[ K ] s) → 
                -- SAFETY: By induction on K and uniqueness of Kits ∎
                `/id q ≡ q &/⋯[ K , Kˢ , Kˢ ] id {{Kˢ}} 
            
            -- SAFETY: By induction on K and uniqueness of Kits ∎
            ;wk–def : ∀ {{K : Kit k}} (ϕ : S₁ –[ K ]→ S₂) → ϕ ;wk ≡ ϕ ;[ K , Kᴿ , K ] (wkᴿ {s = s})
            ;wk–def {Ren} {{K}} ϕ rewrite unique–K K | CK–defR {{Kᴿ}} = refl 
            ;wk–def {Sub} {{K}} ϕ rewrite unique–K K | CK–defS {{Kᴿ}} = refl
            
            idᴿ–def : ∀ (x : S₁ ∋ s) → x &/⋯ id[ Kᴿ ] ≡ x
            idᴿ–def x = refl

            idˢ–def : ∀ (x : S₁ ∋ s) → x &/⋯ id[ Kˢ ] ≡ ` x
            idˢ–def x = refl

            wkᴿ–def : (x : S₁ ∋ s) → x &/⋯ (wkᴿ {s = s}) ≡ (suc x)
            wkᴿ–def _ = wk-id/` _ _

            postulate
              -- abc₁ : {{K : Kit k}} (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) → 
              --   (x &/⋯ ϕ) ≡ (x & ϕ)
              -- abc₂ : (x : S₁ ∋ s) (ϕ : S₁ –[ Kˢ ]→ S₂) → 
              --   (x &/⋯ ϕ) ≡ (x & ϕ)
              -- abc₃ : {{K : Kit k}} (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) → 
              --   (x & ϕ) ≡ (x &/⋯ ϕ)
              comp-def₁ : {{K : Kit k}} (x : S₁ ∋ s) (ϕ₂ : S₁ –[ K ]→ S₂) → 
                x &/⋯ (id[ Kᴿ ] ; ϕ₂) ≡ x &/⋯ ϕ₂ 
                
              comp-def₂ : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} 
                          (x : S₁ ∋ s) (ϕ₂ : S₁ –[ K ]→ S₂) → 
                x &/⋯ (id[ Kˢ ] ; ϕ₂) ≡ ` x &/⋯ ϕ₂  

              comp-def₃ : {{K : Kit k}} (x : S₁ ∋ s) (ϕ₂ : (s′ ∷ S₁) –[ K ]→ S₂) → 
                x &/⋯ (wkᴿ ; ϕ₂) ≡ suc x &/⋯ ϕ₂ 
              
              comp-def₄ : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₂}} 
                         (q : S₂ ∋/⊢ᴷ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
                zero &/⋯ ((q ∙ ϕ₁) ; ϕ₂) ≡ q &/⋯ ϕ₂
            
              comp-def₅ : ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₂}} 
                         (q : S₂ ∋/⊢ᴷ s) (x′ : S₁ ∋ s′) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
                suc x′ &/⋯ ((q ∙ ϕ₁) ; ϕ₂) ≡ x′ &/⋯ (ϕ₁ ; ϕ₂)
           
                

            -- wkˢ–def : (x : S₁ ∋ s) → x &/⋯ (wk[ Kˢ ] {s = s}) ≡ ` (suc x)
            -- wkˢ–def _ = wk-id/` _ _

            ext₀–def : {{K : Kit k}} (q : S₂ ∋/⊢ᴷ s) (ϕ : S₁ –[ K ]→ S₂) → 
              zero &/⋯ (q ∙ ϕ) ≡ q
            ext₀–def _ _ = refl

            extₛ–def : ∀ {{K : Kit k}} (q : S₂ ∋/⊢ᴷ s) (x′ : S₁ ∋ s′) (ϕ : S₁ –[ K ]→ S₂) → 
              suc x′ &/⋯ (q ∙ ϕ) ≡ x′ &/⋯ ϕ
            extₛ–def _ _ _ = refl

            comp–idₗ : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₂}} 
              (ϕ : S₁ –[ K₂ ]→ S₂) → id {{K₁}} ; ϕ ≡ ϕ 
            comp–idₗ {Ren} {k₂} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–C {{K₁}} C | unique–K K₁ | CK–defR {{K₂}}
              =  refl
            comp–idₗ {Sub} {Ren} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–K K₁ | unique–K K₂ = ⊥-elim (impossible–Cˢᴷᴿ {{Kᴿ}} C)
            comp–idₗ {Sub} {Sub} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–C {{K₁}} {{K₂}} {{K₂}} C | unique–K K₁ | unique–K K₂ | CK–defS {{Kˢ}} 
              = ~-ext {{Kˢ}} λ _ x → ⋯-var {{Kˢ}} _ _  

            comp–idᵣ : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₁}} 
              (ϕ : S₁ –[ K₁ ]→ S₂) → ϕ ; id {{K₂}} ≡ ϕ
            comp–idᵣ {Ren} {Ren} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–C {{K₁}} {{K₂}} {{K₁}} C | unique–K K₁ | unique–K K₂ | CK–defR {{Kᴿ}}  
              =  refl
            comp–idᵣ {Ren} {Sub} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–K K₁ | unique–K K₂ = ⊥-elim (impossible–Cᴷˢᴿ {{Kᴿ}} C)
            comp–idᵣ {Sub} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–C {{K₁}} {{K₂}} {{K₁}} C | unique–K K₁ | CK–defS {{K₂}} 
              = ~-ext {{Kˢ}} λ _ x → ⋯-id {{K₂}} _

            -- the idiomatic way to transform a ren into a sub is to compose id sub on the right. 
            -- if its applied on the left, we transform it.   
            norm–idˢ : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} 
              -- SAFETY: By induction on K and uniqueness of Kits ∎
              (ϕ : S₁ –[ K ]→ S₂) → id {{Kˢ}} ; ϕ ≡ (ϕ ;[ K , Kˢ , Kˢ ] id {{Kˢ}}) 
            norm–idˢ {Ren} {{K}} ϕ rewrite unique–K K | CK–defR {{Kˢ}} = 
              ~-ext {{Kˢ}} λ _ x → ⋯-var {{Kᴿ}} _ _
            norm–idˢ {Sub} {{K}} ϕ rewrite unique–K K | CK–defS {{Kˢ}} = 
              ~-ext {{Kˢ}} λ _ x → _ ≡⟨ ⋯-var {{Kˢ}} _ _ ⟩ _ ≡⟨ sym (⋯-id {{Kˢ}} _) ⟩ _ ∎ 

            associativity : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{K₄ : Kit k₄}} {{K₅ : Kit k₅}} 
                            {{C₁ : ComposeKit K₁ K₂ K₃}} {{C₂ : ComposeKit K₃ K₄ K₅}}
              (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ K₄ ]→ S₄) →   
              -- SAFETY: By assumption the incoming C₁ : ComposeKit K₁ K₂ K₃ and C₂ : ComposeKit K₃ K₄ K₅ are valid.
              --         By induction on K₁, K₂, K₃, K₄ and K₅, the definition of _⊔_ and uniqueness of Kits, we prove the cases below ∎
              (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ;[ K₁ , (K₂ ⊔ K₄) , K₅ ](ϕ₂ ;[ K₂ , K₄ , (K₂ ⊔ K₄) ] ϕ₃) 
            associativity {_} {_} {Ren} {Ren} {Sub} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ = ⊥-elim (impossible–Cᴿᴿˢ C₂)
            associativity {_} {_} {_} {Sub} {Ren} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₄ | unique–K K₅ = ⊥-elim (impossible–Cᴷˢᴿ C₂)
            associativity {_} {_} {Sub} {_} {Ren} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₃ | unique–K K₅ = ⊥-elim (impossible–Cˢᴷᴿ C₂)
            associativity {Ren} {Ren} {Sub} {_} {_} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–K K₁ | unique–K K₂ | unique–K K₃ = 
              ⊥-elim (impossible–Cᴿᴿˢ C₁)
            associativity {_} {Sub} {Ren} {_} {_} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–K K₂ | unique–K K₃ = ⊥-elim (impossible–Cᴷˢᴿ C₁)
            associativity {Sub} {_} {Ren} {_} {_} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–K K₁ | unique–K K₃ = ⊥-elim (impossible–Cˢᴷᴿ C₁)
            associativity {Ren} {Ren} {Ren} {Ren} {Ren} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ Kᴿ , Kᴿ , Kᴿ and K₂ , K₄ , (K₂ ⊔ K₄) = Kᴿ , Kᴿ , Kᴿ ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | CK–defR {{Kᴿ}} = refl
            associativity {Ren} {Ren} {Ren} {Sub} {Sub} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ Kᴿ , Kˢ , Kˢ and K₂ , K₄ , (K₂ ⊔ K₄) = Kᴿ , Kˢ , Kˢ ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | CK–defR {{Kᴿ}} | CK–defR {{Kˢ}} = refl
            associativity {Ren} {Sub} {Sub} {Ren} {Sub} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ Kᴿ , Kˢ , Kˢ and K₂ , K₄ , (K₂ ⊔ K₄) = Kˢ , Kˢ , Kˢ ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | CK–defR {{Kˢ}} | CK–defS {{Kᴿ}} = refl
            associativity {Ren} {Sub} {Sub} {Sub} {Sub} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ Kᴿ , Kˢ , Kˢ and K₂ , K₄ , (K₂ ⊔ K₄) = Kˢ , Kˢ , Kˢ ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | CK–defR {{Kˢ}} | CK–defS {{Kˢ}} = refl
            associativity {Sub} {Ren} {Sub} {Ren} {Sub} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ Kˢ , Kᴿ , Kˢ and K₂ , K₄ , (K₂ ⊔ K₄) = Kᴿ , Kᴿ , Kᴿ ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | CK–defS {{Kᴿ}} | CK–defR {{Kᴿ}}
              = ~-ext {{Kˢ}} λ s x →  ⋯-compositionality {{Kᴿ}} {{Kᴿ}} {{Kᴿ}} {{Cᴿᴿ}} _ _ _ 
            associativity {Sub} {Ren} {Sub} {Sub} {Sub} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ Kˢ , Kˢ , Kˢ and K₂ , K₄ , (K₂ ⊔ K₄) = Kᴿ , Kˢ , Kˢ ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | CK–defS {{Kᴿ}} | CK–defS {{Kˢ}} | CK–defR {{Kˢ}}
              = ~-ext {{Kˢ}} λ s x →  ⋯-compositionality {{Kᴿ}} {{Kˢ}} {{Kˢ}} {{Cᴿˢ}} _ _ _
            associativity {Sub} {Sub} {Sub} {Ren} {Sub} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
               -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ Kˢ , Kˢ , Kˢ and K₂ , K₄ , (K₂ ⊔ K₄) = Kˢ , Kᴿ , Kˢ ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | CK–defS {{Kᴿ}} | CK–defS {{Kˢ}} 
              = ~-ext {{Kˢ}} λ s x →  ⋯-compositionality {{Kˢ}} {{Kᴿ}} {{Kˢ}} {{Cˢᴿ}} _ _ _
            associativity {Sub} {Sub} {Sub} {Sub} {Sub} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ Kˢ , Kˢ , Kˢ and K₂ , K₄ , (K₂ ⊔ K₄) = Kˢ , Kˢ , Kˢ ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | CK–defS {{Kˢ}}  
              = ~-ext {{Kˢ}} λ s x →  ⋯-compositionality {{Kˢ}} {{Kˢ}} {{Kˢ}} {{Cˢˢ}} _ _ _
        
            distributivity : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}} 
              (q : S₂ ∋/⊢[ K₁ ] s)  (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
              (q ∙ ϕ₁) ; ϕ₂ ≡ (q &/⋯ ϕ₂) ∙ (ϕ₁ ; ϕ₂)
            distributivity _ _ _ = ~-ext λ { _ zero → refl ; _ (suc x) → refl } 
            
            interact : {{K : Kit k}} 
              (q : S₂ ∋/⊢[ K ] s) (ϕ : S₁ –[ K ]→ S₂) → wkᴿ ; (q ∙ ϕ) ≡ ϕ 
            interact q ϕ = refl
        
            η–id : (zero {s = s} {S = S}) ∙ wkᴿ ≡ id 
            η–id = ~-ext λ { _ zero → refl ; _ (suc x) → refl }

            -- postulate
            --   η–idˢ : (` zero {s = s} {S = S}) ∙ wk ≡ id 
            -- η–idˢ = ~-ext λ { _ zero → refl ; _ (suc x) → ⋯-var {{Kᴿ}} _ _ }
          
            η–law : {{K : Kit k}}
              (ϕ : (s ∷ S₁) –[ K ]→ S₂) → (zero &/⋯ ϕ) ∙ (wkᴿ ; ϕ) ≡ ϕ
            η–law ϕ = ~-ext λ { _ zero → refl ; _ (suc x) → refl }

            -- postulate
            --   η-lawˢ : {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C₁ : ComposeKit Kˢ K₂ K₂}} {{C₂ : ComposeKit K₁ K₂ K₂}}
            --     (ϕ : (s ∷ S₁) –[ K₂ ]→ S₂) → ((` zero) &/⋯ ϕ) ∙ (wk {{K₁}} ; ϕ) ≡ ϕ
            -- η-lawˢ {Ren} {k₂} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–C {{K₁}} C | unique–K K₁ | CK–defR {{K₂}}
            --   = ~-ext λ { _ zero → refl ; _ (suc x) → refl }
            -- η-lawˢ {Sub} {Ren} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–K K₁ | unique–K K₂ = ⊥-elim (impossible–Cˢᴷᴿ {{K = Kᴿ}} C)
            -- η-lawˢ {Sub} {Sub} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–C {{K₁}} {{K₂}} {{K₂}} C | unique–K K₁ | unique–K K₂ | CK–defS {{Kˢ}} 
            --   = ~-ext {{Kˢ}} λ { _ zero → ⋯-var {{Kˢ}} _ _  ; _ (suc x) → 
            --     _ ≡⟨ ⋯-compositionality {{Kᴿ}} {{Kˢ}} {{Kˢ}} {{Cᴿˢ}} _ _ _ ⟩ _ ≡⟨ ⋯-var {{Kˢ}} _ _ ⟩ _ ∎ } 

            postulate
              -- compositionality : ∀ {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{K₄ : Kit k₄}} {{K₅ : Kit k₅}} 
              --                        {{C₁ : ComposeKit Kˢ K₂ K₃}} {{C₂ : ComposeKit K₃ K₄ K₅}} →
              --          (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₂ ]→ S₂) (ϕ₂ : S₂ –[ K₄ ]→ S₃) → 
              --          (t &/⋯ ϕ₁) &/⋯ ϕ₂ ≡ t &/⋯[ Kˢ , K₂ ⊔ K₄ , K₅ ] (ϕ₁ ;[ K₂ , K₄ , (K₂ ⊔ K₄) ] ϕ₂)
-- 
              -- right–id : ∀ {{K : Kit k}} (t : S₁ ⊢ s) →
              --            t &/⋯ id[ K ] ≡ t

              compositionality : ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{K₄ : Kit k₄}} {{K₅ : Kit k₅}} 
                                    {{C₁ : ComposeKit K₁ K₂ K₃}} {{C₂ : ComposeKit K₃ K₄ K₅}} →
                       (q : S₁ ∋/⊢[ K₁ ] s) (ϕ₁ : S₁ –[ K₂ ]→ S₂) (ϕ₂ : S₂ –[ K₄ ]→ S₃) → 
                       (q &/⋯ ϕ₁) &/⋯ ϕ₂ ≡ q &/⋯[ K₁ , K₂ ⊔ K₄ , K₅ ] (ϕ₁ ;[ K₂ , K₄ , (K₂ ⊔ K₄) ] ϕ₂) 

              right–id : ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{C : ComposeKit K₁ K₂ K₁}} (q : S₁ ∋/⊢[ K₁ ] s) →
                         q &/⋯ id[ K₂ ] ≡ q 
-- (t′ &/⋯ (ϕ ↑ type)) [ t &/⋯ ϕ ]

-- (t′ &/⋯ (id/` zero) ∙ (ϕ ;wk)) &/⋯ (t′ ∙ id) 
-- (t′ &/⋯ (zero & idᴷ) ∙ (ϕ ; wkᴿ)) &/⋯ (t′ ∙ id) 
-- t′ &/⋯  ((zero & idᴷ) ∙ (ϕ ; wkᴿ)  ;   t′ ∙ id)
