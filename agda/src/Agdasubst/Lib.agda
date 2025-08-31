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
    private variable
      M M₁ M₂ M₃ M₄ M₅ M₆ M′ M₁′ M₂′ M₃′ M₄′ M₅′ M₆′ : Mode
      s s₁ s₂ s₃ s₄ s₅ s₆ s′ s₁′ s₂′ s₃′ s₄′ s₅′ s₆′ : Sort
      S S₁ S₂ S₃ S₄ S₅ S₆ S′ S₁′ S₂′ S₃′ S₄′ S₅′ S₆′ : Scope
      x x₁ x₂ x₃ x₄ x₅ x₆ x′ x₁′ x₂′ x₃′ x₄′ x₅′ x₆′ : S ∋ s

    record Syntax : Set₁ where
      constructor mkSyntax
      field 
        --!! ScopedT
        _⊢_  : List Sort → Sort → Set

        --!! VarCstr
        `_   : S ∋ s → S ⊢ s

        `-injective : ` x₁ ≡ ` x₂ → x₁ ≡ x₂  

      --! Image
      image : Mode → (List Sort → Sort → Set)
      image Vᴹ  = _∋_
      image Tᴹ  = _⊢_ 

      -- prevents users from outside the library to construct more Kit and ComposeKit instances
      -- thus: the unique–V, unique–T, unique–Cᴿ and unique–Cˢ postulates 
      -- cannot do any harm outside this file 
      --!! Lock
      private data Lock : Set where unlock : Lock 

      --! Kit
      record Kit (k : Mode) : Set₁ where
        _∋/⊢ᴷ_ = image k
        field
          K-id/`  : S ∋ s → S ∋/⊢ᴷ s
          K-`/id  : S ∋/⊢ᴷ s → S ⊢ s
          K-wk    : ∀ s′ → S ∋/⊢ᴷ s → (s′ ∷ S) ∋/⊢ᴷ s
          -- axioms ... 

          --!! LockField
          K-lock    : Lock

          `/`-is-`        : 
            --!! AxiomEx
            ∀ (x : S ∋ s) → K-`/id (K-id/` x) ≡ ` x
          
          id/`-injective  : K-id/` x₁ ≡ K-id/` x₂ → x₁ ≡ x₂
          `/id-injective  : ∀ {x/t₁ x/t₂ : S ∋/⊢ᴷ s} →
                              K-`/id x/t₁ ≡ K-`/id x/t₂ → x/t₁ ≡ x/t₂
          wk-id/`         : ∀ {s} s′ (x : S ∋ s) →
                              K-wk s′ (K-id/` x) ≡ K-id/` (suc x) 

        infixl 8 _&_

 
        opaque
          --! OpaqueFieldsA {
          id/` : S ∋ s → S ∋/⊢ᴷ s 
          id/` = K-id/` 
          --! }

          --! OpaqueFieldsB {
          `/id : S ∋/⊢ᴷ s → S ⊢ s
          `/id = K-`/id 
          --! }
       
          --! MapA {
          _→ᴷ_ : Scope → Scope → Set
          S₁ →ᴷ S₂ = ∀ s → S₁ ∋ s → S₂ ∋/⊢ᴷ s

          _&_ : ∀ {s} → S₁ ∋ s → S₁ →ᴷ S₂ → S₂ ∋/⊢ᴷ s
          x & ϕ = ϕ _ x 

          id : S →ᴷ S
          id s x = K-id/` x 
          --! }
          --! MapB {
          _∙_ : S₂ ∋/⊢ᴷ s → S₁ →ᴷ S₂ → (s ∷ S₁) →ᴷ S₂
          (x/t ∙ ϕ) _ zero     = x/t
          (x/t ∙ ϕ) _ (suc x)  = ϕ _ x 

          _;wk : ∀ {s} → S₁ →ᴷ S₂ → S₁ →ᴷ (s ∷ S₂) 
          _;wk ϕ _ x = K-wk _ (ϕ _ x)            

          wk : S →ᴷ (s ∷ S)
          wk = id ;wk 
          --! }

          kit_ops : ⊤
          kit_ops = tt
        
        
        ⦅_⦆ : S ∋/⊢ᴷ s → (s ∷ S) →ᴷ S
        ⦅ x/t ⦆ = x/t ∙ id

        --! Lifting
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
          
          
          id↑≡id :  
            --!! IdLift 
            (id/` (zero {s = s} {S = S})) ∙ (id ;wk) ≡ id

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
      _∋/⊢[_]_ : Scope → Kit M → Sort → Set
      S ∋/⊢[ K ] s = Kit._∋/⊢ᴷ_ K S s
 
      _–[_]→_ : Scope → Kit M → Scope → Set
      S₁ –[ K ]→ S₂ = Kit._→ᴷ_ K S₁ S₂

      id[_] : (K : Kit M) → S –[ K ]→ S
      id[ K ] = Kit.id K 
      --! }

      --!! OpenKit
      open Kit {{...}} 
      
        public hiding (wk)

      _`⋯_ : ∀ {{K : Kit M}} → S₁ ∋ s → S₁ →ᴷ S₂ → S₂ ⊢ s 
      x `⋯ ϕ = `/id (x & ϕ) 

      opaque 
        unfolding kit_ops
        `⋯-right-id : ∀ {{K : Kit M}} (x : S ∋ s) → (x `⋯ id) ≡ (` x)
        `⋯-right-id x = `/`-is-` x

      record Traversal : Set₁ where
        constructor mkTraversal
        infixl   5  _⋯_
        field
          --! Traversal {  
          _⋯_    : ∀ {{K : Kit M}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
          ⋯-right-id   : ∀ {{K : Kit M}} → (t : S ⊢ s) → t ⋯ id[ K ] ≡ t
          --! }
          ⋯-var  : ∀ {{K : Kit M}} → (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) →
                     (` x) ⋯ ϕ ≡ `/id {{K}} (x & ϕ)

        opaque 
          --! InstanceRen {
          instance 
            V : Kit Vᴹ 
            V = record
              { K-id/`           = λ x → x
              ; K-`/id           = `_
              ; K-wk             = λ s′ x → suc x
              -- axioms ... 
          --! }

              ; `/`-is-`        = λ x → refl
              ; id/`-injective  = λ eq → eq 
              ; `/id-injective  = `-injective  
              ; wk-id/`         = λ s′ x → refl 
              ; K-lock            = unlock
              } 
        
        open Kit V public using () renaming 
          (_→ᴷ_ to _→ᴿ_; _&_ to _&ᴿ_; _∙_ to _∙ᴿ_; id to idᴿ; wk to wk; ⦅_⦆ to ⦅_⦆ᴿ; _↑_ to _↑ᴿ_; _↑★_ to _↑ᴿ★_)

        _⋯ᴿ_ : S₁ ⊢ s → S₁ →ᴿ S₂ → S₂ ⊢ s
        t ⋯ᴿ ρ = t ⋯ ρ

        opaque 
          unfolding kit_ops V
          --! InstanceSub {
          instance
            T : Kit Tᴹ
            T = record
              { K-id/`           = `_
              ; K-`/id           = λ t → t
              ; K-wk             = λ s′ t → t ⋯ wk
              -- axioms ... 
              --! }
              ; `/`-is-`        = λ x → refl
              ; id/`-injective  = `-injective
              ; `/id-injective  = λ eq → eq 
              ; wk-id/`         = λ s′ x → ⋯-var x wk
              ; K-lock            = unlock
              }
          
          kits : ⊤
          kits = tt


        open Kit T public using () renaming 
          (_→ᴷ_ to _→ˢ_; _&_ to _&ˢ_; _∙_ to _∙ˢ_; id to idˢ; ⦅_⦆ to ⦅_⦆ˢ; _↑_ to _↑ˢ_; _↑★_ to _↑ˢ★_)

        _⋯ˢ_ : S₁ ⊢ s → S₁ →ˢ S₂ → S₂ ⊢ s
        t ⋯ˢ σ = t ⋯ σ 

        --! UniqueKits
        private postulate
          unique–V : (K : Kit Vᴹ) → V ≡ K
          unique–T : (K : Kit Tᴹ) → T ≡ K

        unique–K–by : (M : Mode) → Kit M   
        unique–K–by Vᴹ = V
        unique–K–by Tᴹ = T

        unique–K : (K : Kit M) → K ≡ unique–K–by M 
        unique–K {Vᴹ} K = sym (unique–V K)
        unique–K {Tᴹ} K = sym (unique–T K)

        opaque
          --! ModeLub
          _⨆_ : Mode → Mode → Mode
          Vᴹ  ⨆ Vᴹ  = Vᴹ
          Vᴹ  ⨆ Tᴹ  = Tᴹ
          Tᴹ  ⨆ Vᴹ  = Tᴹ
          Tᴹ  ⨆ Tᴹ  = Tᴹ
          --! ModeLubLaws
          ⨆-idem       : M ⨆ M           ≡ M 
          ⨆-assoc      : (M₁ ⨆ M₂) ⨆ M₃  ≡ M₁ ⨆ (M₂ ⨆ M₃)
          ⨆-comm       : (M₁ ⨆ M₂)       ≡ (M₂ ⨆ M₁)
          ⨆-bot-right  : M ⨆ Vᴹ  ≡ M 
          ⨆-bot-left   : Vᴹ ⨆ M  ≡ M
          ⨆-top-right  : M ⨆ Tᴹ  ≡ Tᴹ
          ⨆-top-left   : Tᴹ ⨆ M  ≡ Tᴹ

          ⨆-idem {Vᴹ} = refl
          ⨆-idem {Tᴹ} = refl 

          ⨆-bot-right {Vᴹ} = refl 
          ⨆-bot-right {Tᴹ} = refl 

          ⨆-bot-left {Vᴹ} = refl 
          ⨆-bot-left {Tᴹ} = refl 

          ⨆-top-right {Vᴹ} = refl 
          ⨆-top-right {Tᴹ} = refl  

          ⨆-top-left {Vᴹ} = refl 
          ⨆-top-left {Tᴹ} = refl  

          ⨆-assoc {Vᴹ} {Vᴹ} {Vᴹ} = refl
          ⨆-assoc {Vᴹ} {Vᴹ} {Tᴹ} = refl
          ⨆-assoc {Vᴹ} {Tᴹ} {Vᴹ} = refl
          ⨆-assoc {Vᴹ} {Tᴹ} {Tᴹ} = refl
          ⨆-assoc {Tᴹ} {Vᴹ} {Vᴹ} = refl
          ⨆-assoc {Tᴹ} {Vᴹ} {Tᴹ} = refl
          ⨆-assoc {Tᴹ} {Tᴹ} {Vᴹ} = refl
          ⨆-assoc {Tᴹ} {Tᴹ} {Tᴹ} = refl

          ⨆-comm {Vᴹ} {Vᴹ} = refl
          ⨆-comm {Vᴹ} {Tᴹ} = refl
          ⨆-comm {Tᴹ} {Vᴹ} = refl
          ⨆-comm {Tᴹ} {Tᴹ} = refl
        
        --! RewriteModeLubLaws
        {-# REWRITE ⨆-idem ⨆-bot-right ⨆-bot-left ⨆-top-right ⨆-top-left ⨆-assoc #-}
        opaque
          unfolding _⨆_
        --! KitLub {
          _⊔_ : (K₁ : Kit M₁) (K₂ : Kit M₂) → Kit (M₁ ⨆ M₂)
          _⊔_ {Vᴹ} {Vᴹ} K₁ K₂ = V
          _⊔_ {Vᴹ} {Tᴹ} K₁ K₂ = T
          _⊔_ {Tᴹ} {Vᴹ} K₁ K₂ = T
          _⊔_ {Tᴹ} {Tᴹ} K₁ K₂ = T
        --! }

          --! KitLubLaws {
          ⊔-idem       : {{K : Kit M}} → K ⊔ K   ≡ K
          ⊔-assoc      : {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} → 
            (K₁ ⊔ K₂) ⊔ K₃ ≡ K₁ ⊔ (K₂ ⊔ K₃)
          ⊔-comm       : {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} → 
            (K₁ ⊔ K₂) ≡ subst Kit (⨆-comm {M₂} {M₁}) (K₂ ⊔ K₁) 
          ⊔-bot-right  : {{K : Kit M}} → K ⊔ V  ≡ K
          ⊔-bot-left   : {{K : Kit M}} → V ⊔ K  ≡ K  
          ⊔-top-right  : {{K : Kit M}} → K ⊔ T  ≡ T
          ⊔-top-left   : {{K : Kit M}} → T ⊔ K  ≡ T
          --! }

          --! KitLubExcerpt {
          ⊔-idem {Vᴹ} {{K}} = unique–V K
          ⊔-idem {Tᴹ} {{K}} = unique–T K
          --! }

          ⊔-bot-right {Vᴹ} {{K}} = unique–V K 
          ⊔-bot-right {Tᴹ} {{K}} = unique–T K 

          ⊔-bot-left {Vᴹ} {{K}} = unique–V K
          ⊔-bot-left {Tᴹ} {{K}} = unique–T K

          ⊔-top-right {Vᴹ} = refl
          ⊔-top-right {Tᴹ} = refl

          ⊔-top-left {Vᴹ} = refl
          ⊔-top-left {Tᴹ} = refl

          ⊔-assoc {Vᴹ} {Vᴹ} {Vᴹ} = refl
          ⊔-assoc {Vᴹ} {Vᴹ} {Tᴹ} = refl 
          ⊔-assoc {Vᴹ} {Tᴹ} {Vᴹ} = refl
          ⊔-assoc {Vᴹ} {Tᴹ} {Tᴹ} = refl
          ⊔-assoc {Tᴹ} {Vᴹ} {Vᴹ} = refl
          ⊔-assoc {Tᴹ} {Vᴹ} {Tᴹ} = refl
          ⊔-assoc {Tᴹ} {Tᴹ} {Vᴹ} = refl 
          ⊔-assoc {Tᴹ} {Tᴹ} {Tᴹ} = refl

          ⊔-comm {Vᴹ} {Vᴹ} = refl
          ⊔-comm {Vᴹ} {Tᴹ} = refl
          ⊔-comm {Tᴹ} {Vᴹ} = refl 
          ⊔-comm {Tᴹ} {Tᴹ} = refl

        --! RewriteKitLubLaws
        {-# REWRITE ⊔-idem ⊔-bot-right ⊔-bot-left ⊔-top-right ⊔-top-left ⊔-assoc #-}

        module KitsMeta where
          variable 
            t t₁ t₂ t₃ t₄ t₅ t′ t₁′ t₂′ t₃′ t₄′ t₅′ : S ⊢ s
            ρ ρ₁ ρ₂ ρ₃ ρ₄ ρ₅ ρ′ ρ₁′ ρ₂′ ρ₃′ ρ₄′ ρ₅′ : S₁ →ᴿ S₂
            σ σ₁ σ₂ σ₃ σ₄ σ₅ σ′ σ₁′ σ₂′ σ₃′ σ₄′ σ₅′ : S₁ →ˢ S₂

        record WkKit (K : Kit M): Set₁ where 
          private instance _ = K
          field
            wk-`/id  : ∀ s (x/t : S ∋/⊢[ K ] s′) → `/id x/t ⋯ᴿ wk ≡ `/id (K-wk s x/t)

        open WkKit {{...}} public

        opaque
          unfolding kits
          Wᴿ : WkKit V
          Wᴿ = record { wk-`/id =  λ s′ x → ⋯-var x wk }

          Wˢ : WkKit T
          Wˢ = record { wk-`/id = λ s x/t → refl } 
        
        instance
          wkKit : {{K : Kit M}} → WkKit K
          wkKit {Vᴹ} {{K}} = subst WkKit (unique–V K) Wᴿ 
          wkKit {Tᴹ} {{K}} = subst WkKit (unique–T K) Wˢ 


        --! ComposeKit
        record ComposeKit (K₁ : Kit M₁) (K₂ : Kit M₂) (K₁⊔K₂ : Kit M₃) : Set₁ where
          private instance _ = K₁; _ = K₂; _ = K₁⊔K₂
          field
            C-_&/⋯_    : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₁⊔K₂ ] s
            -- axioms ...
          
          infixl 8 C-_&/⋯_
          field
            &/⋯-⋯     : (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                        `/id x/t ⋯ ϕ ≡ `/id (C- x/t &/⋯ ϕ)
            &/⋯-wk-↑ : (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ : S₁ –[ K₂ ]→ S₂) →
                       K-wk s′ (C- x/t &/⋯ ϕ) ≡ C- K-wk s′ x/t &/⋯ (ϕ ↑ s′) 
            C-lock      : Lock

          opaque
            unfolding kits _⊔_
 
            comp_ops : ⊤
            comp_ops = tt 

            infixl 8 _&/⋯_
            --! LookOrApp {
            _&/⋯_ : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₁⊔K₂ ] s
            _&/⋯_ = C-_&/⋯_ 
            --! }
            
            --! CompDef {
            _;_ : S₁ –[ K₁ ]→ S₂ → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₁⊔K₂ ]→ S₃
            (ϕ₁ ; ϕ₂) _ x = (x & ϕ₁) &/⋯ ϕ₂
            --! }


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
              `/id (x & ((ϕ₁ ; ϕ₂) ↑ s))        ≡⟨⟩
              `/id {{K₁⊔K₂}} (id/` zero)        ≡⟨ `/`-is-` {{K₁⊔K₂}} zero ⟩
              ` zero                            ≡⟨ sym (`/`-is-` {{K₂}} zero) ⟩
              `/id {{K₂}} (id/` zero)           ≡⟨⟩
              `/id {{K₂}} (zero & (ϕ₂ ↑ s))     ≡⟨ sym (&/⋯-& (id/` zero) (ϕ₂ ↑ s)) ⟩
              `/id (id/` zero &/⋯ (ϕ₂ ↑ s))     ≡⟨⟩
              `/id (x & (ϕ₁ ↑ s) &/⋯ (ϕ₂ ↑ s))  ≡⟨⟩
              `/id (x & ((ϕ₁ ↑ s) ; (ϕ₂ ↑ s)))  ∎
              )
            dist-↑-; s ϕ₁ ϕ₂ s₁ x@(suc y) = `/id-injective (
              `/id (x & ((ϕ₁ ; ϕ₂) ↑ s))          ≡⟨⟩
              `/id (K-wk _ ( y & (ϕ₁ ; ϕ₂)))      ≡⟨⟩
              `/id (K-wk _ (y & ϕ₁ &/⋯ ϕ₂))       ≡⟨ cong (`/id) (&/⋯-wk-↑ (y & ϕ₁) ϕ₂) ⟩
              `/id (K-wk _ (y & ϕ₁) &/⋯ (ϕ₂ ↑ s)) ≡⟨⟩
              `/id (x & (ϕ₁ ↑ s) &/⋯ (ϕ₂ ↑ s))    ≡⟨⟩
              `/id (x & ((ϕ₁ ↑ s) ; (ϕ₂ ↑ s)))   ∎
              )
            
            dist–↑–; : ∀ s (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →

                       --!! DistLift 
                       ((ϕ₁ ↑ s) ; (ϕ₂ ↑ s)) ≡ ((ϕ₁ ; ϕ₂) ↑ s)

            dist–↑–; s ϕ₁ ϕ₂ = sym (~-ext (dist-↑-; s ϕ₁ ϕ₂))

            dist-↑★-;  : ∀ S (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                        ((ϕ₁ ; ϕ₂) ↑★ S) ~ ((ϕ₁ ↑★ S) ; (ϕ₂ ↑★ S))
            dist-↑★-; []      ϕ₁ ϕ₂ sx x = refl
            dist-↑★-; (s ∷ S) ϕ₁ ϕ₂ sx x =
              ((ϕ₁ ; ϕ₂) ↑★ (s ∷ S)) sx x               ≡⟨⟩
              (((ϕ₁ ; ϕ₂) ↑★ S) ↑ s) sx x               ≡⟨ cong (λ ■ → ( ■ ↑  s) sx x) (~-ext (dist-↑★-; S ϕ₁ ϕ₂)) ⟩
              (((ϕ₁ ↑★ S) ; (ϕ₂ ↑★ S)) ↑ s) sx x        ≡⟨ dist-↑-; s (ϕ₁ ↑★ S) (ϕ₂ ↑★ S) sx x ⟩
              (((ϕ₁ ↑★ S) ↑ s) ; ((ϕ₂ ↑★ S) ↑ s)) sx x  ≡⟨⟩
              ((ϕ₁ ↑★ (s ∷ S)) ; (ϕ₂ ↑★ (s ∷ S))) sx x    ∎
            
            dist–↑★–;  : ∀ S (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                         ((ϕ₁ ↑★ S) ; (ϕ₂ ↑★ S)) ≡ ((ϕ₁ ; ϕ₂) ↑★ S)
            dist–↑★–; S ϕ₁ ϕ₂ = sym (~-ext (dist-↑★-; S ϕ₁ ϕ₂))
        
        open ComposeKit {{...}} public
        
  
        _;[_]_  : ∀ {K₁ : Kit M₁} {K₂ : Kit M₂} {K₃ : Kit M₃} → 
          S₁ –[ K₁ ]→ S₂ → ComposeKit K₁ K₂ K₃ → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₃ ]→ S₃
        --!! CompExp
        _;[_]_ ϕ₁ C ϕ₂ = ComposeKit._;_ C ϕ₁ ϕ₂   

        _&/⋯[_]_  : ∀ {K₁ : Kit M₁} {K₂ : Kit M₂} {K₃ : Kit M₃} → 
          S₁ ∋/⊢[ K₁ ] s → ComposeKit K₁ K₂ K₃ → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₃ ] s
        --!! LoAExp
        _&/⋯[_]_ x/t C ϕ₂ = ComposeKit._&/⋯_ C x/t ϕ₂   
        

        opaque
          unfolding comp_ops

          `⋯-compositionality : {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{C : ComposeKit K₁ K₂ K₃}}
                (x : S₁ ∋ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
                 ((x `⋯ ϕ₁) ⋯ ϕ₂) ≡ (x `⋯ (ϕ₁ ; ϕ₂))
          `⋯-compositionality x ϕ₁ ϕ₂ = &/⋯-⋯ (ϕ₁ _ x) ϕ₂
        record Compose : Set₁ where
          constructor mkCompose 
          field
            --! Compositionality 
            ⋯-compositionality : ∀ {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{C : ComposeKit K₁ K₂ K₃}}
                       (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
                       (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
          
          opaque
            unfolding comp_ops 
          
            ↑-wk  : ∀ {{K : Kit M}}
                    {{C₁ : ComposeKit K V K}} {{C₂ : ComposeKit V K K}} 
                    (ϕ : S₁ –[ K ]→ S₂) s → 
                    (ϕ ; wk) ~ (wk ; (ϕ ↑ s))
            ↑-wk {S₁} {S₂} {{K}} ϕ s sx x =  `/id-injective (
              `/id ((ϕ ; wk) sx x)        ≡⟨⟩
              `/id (x & ϕ &/⋯ wk)         ≡⟨ sym (&/⋯-⋯ (x & ϕ) (wk)) ⟩
              `/id (`/id (x & ϕ) ⋯ wk)    ≡⟨ wk-`/id s (x & ϕ) ⟩
              `/id (suc x & (ϕ ↑ s))      ≡⟨ sym (&/⋯-& (suc x) (ϕ ↑ s)) ⟩
              `/id (suc x &/⋯ (ϕ ↑ s))    ≡⟨⟩
              `/id (x & wk &/⋯ (ϕ ↑ s))   ≡⟨⟩
              `/id ((wk ; (ϕ ↑ s)) sx x)  ∎) 
            
            ⋯-↑-wk  : ∀ {{K : Kit M}} {{C₁ : ComposeKit K V K}} {{C₂ : ComposeKit V K K}} 
                      (t : S₁ ⊢ s) (ϕ : S₁ –[ K ]→ S₂) s′ → 
                      t ⋯ ϕ ⋯ wk ≡ t ⋯ wk ⋯ (ϕ ↑ s′)
            ⋯-↑-wk t ϕ s =
              t ⋯ ϕ ⋯ wk           ≡⟨ ⋯-compositionality t ϕ (wk) ⟩
              t ⋯ (ϕ ; wk)         ≡⟨ cong (t ⋯_) (~-ext (↑-wk ϕ s)) ⟩
              t ⋯ (wk ; (ϕ ↑ s))   ≡⟨ sym (⋯-compositionality t (wk) (ϕ ↑ s)) ⟩  
              t ⋯ wk ⋯ (ϕ ↑ s)    ∎

          opaque 
            unfolding comp_ops
            --! InstanceCRen {
            instance
              Cᴿ : {{K : Kit M}} → ComposeKit V K K
              Cᴿ = record { C-_&/⋯_ = _&_ -- axioms ... 
              --! }
                      ; &/⋯-⋯     = λ x ϕ → ⋯-var x ϕ
                      ; &/⋯-wk-↑ = λ x ϕ → refl
                      ; C-lock      = unlock }

           
          opaque
            unfolding comp_ops Cᴿ 

            lib : ⊤ 
            lib = tt
            
            --! InstanceCSub {
            instance
              Cˢ : {{K : Kit M}} {{C : ComposeKit K V K}} → ComposeKit T K T
              Cˢ  = record { C-_&/⋯_ = _⋯_ -- axioms ... 
            --! }
                      ; &/⋯-⋯     = λ x ϕ → refl
                      ; &/⋯-wk-↑ = λ t ϕ → ⋯-↑-wk t ϕ _ 
                      ; C-lock      = unlock }  

          Cᴿᴿ = Cᴿ {{V}}
          Cᴿˢ = Cᴿ {{T}}
          Cˢᴿ = Cˢ {{V}} {{Cᴿ {{V}}}}
          Cˢˢ = Cˢ {{T}} {{Cˢ {{V}} {{Cᴿ {{V}}}}}}

          --! UniqueCKits
          private postulate
            unique–Cᴿ  : {{K : Kit M}} (C : ComposeKit V K K) → C ≡ Cᴿ
            unique–Cˢ  : {{K : Kit M}} {{C′ : ComposeKit K V K}} → (C : ComposeKit T K T) → C ≡ Cˢ
            
            -- By assumption all _incoming_ ComposeKits to a function must be valid. 
            -- Invalid ones can be disgarded using the functions below. 
            --! UnqiueCKitsImp
          private postulate
            impossible–Cˢᴷᴿ : {{K : Kit M}} → ¬ ComposeKit T K V
            impossible–Cᴷˢᴿ : {{K : Kit M}} → ¬ ComposeKit K T V
            impossible–Cᴿᴿˢ : ¬ ComposeKit V V T  

          
        
            -- SAFETY: 
            --   For each usage of this definition it must be checked, that no 
            --   invalid ComposeKit (e.g. ComposeKit V V T) is created.
          --! CKitUnsafe
          opaque private
            {-# NON_COVERING #-}
            _,_,_ : (K₁ : Kit M₁) (K₂ : Kit M₂) (K₃ : Kit M₃) → ComposeKit K₁ K₂ K₃
            _,_,_ {Vᴹ} {Vᴹ} {Vᴹ} K₁ K₂ K₃ rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ = Cᴿ
            _,_,_ {Vᴹ} {Tᴹ} {Tᴹ} K₁ K₂ K₃ rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ = Cᴿ
            _,_,_ {Tᴹ} {Vᴹ} {Tᴹ} K₁ K₂ K₃ rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ = Cˢ
            _,_,_ {Tᴹ} {Tᴹ} {Tᴹ} K₁ K₂ K₃ rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ = Cˢ

            {-# WARNING_ON_USAGE _,_,_ "SAFETY: For each usage of this definition it must be checked, that no invalid ComposeKit (e.g. ComposeKit V V T) is created." #-}

            -- SAFETY: By assumption the incoming (C : ComposeKit K₁ K₂ K₃) is valid. 
            --    Thus (K₁ , K₂ , K₃) is too.
            unique–C : {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} → (C : ComposeKit K₁ K₂ K₃) → C ≡ K₁ , K₂ , K₃
            unique–C {Vᴹ} {Vᴹ} {Vᴹ} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–Cᴿ {{V}} C = refl
            unique–C {Vᴹ} {Vᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} C rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ = ⊥-elim (impossible–Cᴿᴿˢ C)
            unique–C {_} {Tᴹ} {Vᴹ} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₂ | unique–K K₃ = ⊥-elim (impossible–Cᴷˢᴿ C)
            unique–C {Vᴹ} {Tᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–Cᴿ {{T}} C = refl
            unique–C {Tᴹ} {_} {Vᴹ} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₁ | unique–K K₃ = ⊥-elim (impossible–Cˢᴷᴿ  C)
            unique–C {Tᴹ} {Vᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–Cˢ {{V}} {{Cᴿ {{V}}}} C = refl
            unique–C {Tᴹ} {Tᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} C 
              rewrite unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–Cˢ {{T}} {{Cˢ {{V}} {{Cᴿ {{V}}}}}} C = refl

          -- instance 
          --   Cˢ : {{K : Kit M}} → ComposeKit T K T
          --   Cˢ {{K}} = Cˢ′ {{K = K}} {{C = K , V , K}}

          -- Safe variant of _,_,_.
          --!! CompCKitSafe
          _;ᴷ_ : (K₁ : Kit M₁) (K₂ : Kit M₂) → ComposeKit K₁ K₂ (K₁ ⊔ K₂)
          
          -- SAFETY: By induction on K₁, K₂ and K₃, uniqueness of Kits and the definition of _⊔_ ∎
          --!! CompCKitSafeDef
          K₁ ;ᴷ K₂ = K₁ , K₂ , (K₁ ⊔ K₂)

          -- SAFETY: By induction on K and uniqueness of Kits ∎
          C–defᴿ : 
            --!! CKitRenRed
            {{K : Kit M}} → V , K , K ≡ Cᴿ {{K = K}}

          C–defᴿ {{K}} = unique–Cᴿ {{K = K}} (V , K , K)

          -- SAFETY: By induction on K and uniqueness of Kits ∎
          C–defˢ : 
            --!! CKitSubRed
            {{K : Kit M}} → T , K , T ≡ Cˢ {{K = K}} {{C = K , V , K}}

          C–defˢ {{K}} = unique–Cˢ {{K = K}} {{C′ = K , V , K}} (T , K , T)

          {-# REWRITE C–defᴿ C–defˢ #-} 

          weaken : S ⊢ s → (s′ ∷ S) ⊢ s
          weaken t = t &/⋯ wk

          _[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
          t [ t′ ] = t &/⋯ (t′ ∙ id) 

          module _ where
             private postulate 
               --! AssocTryO
               associativity : 
                 {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{K₄ : Kit M₄}} {{K₅ : Kit M₅}} {{K₆ : Kit M₆}}
                 {{C₁ : ComposeKit K₁ K₂ K₃}} {{C₂ : ComposeKit K₃ K₄ K₅}} {{C₃ : ComposeKit K₁ K₆ K₅}} {{C₄ : ComposeKit K₂ K₄ K₆}}  
                 (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ K₄ ]→ S₄) →   
                 (ϕ₁ ;[ C₁ ] ϕ₂) ;[ C₂ ] ϕ₃ ≡ ϕ₁ ;[ C₃ ] (ϕ₂ ;[ C₄ ] ϕ₃) 

          opaque
            unfolding lib

            postulate
              compositionality–safe : ∀  {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{K₄ : Kit M₄}} 
                                    {{C₁ : ComposeKit K₁ K₂ K₃}} {{C₂ : ComposeKit K₃ K₄ T}} →
                       (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ₁ : S₁ –[ K₂ ]→ S₂) (ϕ₂ : S₂ –[ K₄ ]→ S₃) → 
                       (x/t &/⋯ ϕ₁) &/⋯ ϕ₂ ≡ x/t &/⋯[ K₁ , K₂ ⊔ K₄ , T ] (ϕ₁ ;[ K₂ , K₄ , (K₂ ⊔ K₄) ] ϕ₂)

              compositionality : ∀ {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{K₄ : Kit M₄}} {{K₅ : Kit M₅}} 
                                    {{C₁ : ComposeKit K₁ K₂ K₃}} {{C₂ : ComposeKit K₃ K₄ K₅}} →
                       (x/t : S₁ ∋/⊢[ K₁ ] s) (ϕ₁ : S₁ –[ K₂ ]→ S₂) (ϕ₂ : S₂ –[ K₄ ]→ S₃) → 
                       (x/t &/⋯ ϕ₁) &/⋯ ϕ₂ ≡ x/t &/⋯[ K₁ , K₂ ⊔ K₄ , K₅ ] (ϕ₁ ;[ K₂ , K₄ , (K₂ ⊔ K₄) ] ϕ₂) 

              right–id : ∀ {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{C : ComposeKit K₁ K₂ K₁}} (x/t : S₁ ∋/⊢[ K₁ ] s) →
                         x/t &/⋯ id[ K₂ ] ≡ x/t 
 
            id`–def : ∀ {{K : Kit M}} (x : S ∋ s) → 
              id/` x ≡ x &/⋯ (id {{K}})
            id`–def x = refl 
 
            `id–def : ∀ {{K : Kit M}} (x/t : S ∋/⊢[ K ] s) → 
              -- SAFETY: By induction on K and uniqueness of Kits ∎
              `/id x/t ≡ x/t &/⋯[ K , T , T ] id {{T}}  
            `id–def {Vᴹ} {{K}} x/t rewrite unique–K K | C–defᴿ {{T}} = refl
            `id–def {Tᴹ} {{K}} x/t rewrite unique–K K | C–defˢ {{T}} = sym (right–id {{T}} {{T}} {{Cˢˢ}} _)
            
            ;wk–def : ∀ {{K : Kit M}} (ϕ : S₁ –[ K ]→ S₂) →  
              -- SAFETY: By induction on K and uniqueness of Kits ∎
              ϕ ;wk ≡ ϕ ;[ K , V , K ] (wk {s = s})
            ;wk–def {Vᴹ} {{K}} ϕ rewrite unique–K K | C–defᴿ {{V}} = refl 
            ;wk–def {Tᴹ} {{K}} ϕ rewrite unique–K K | C–defˢ {{V}} = refl

            idˢ–def : ∀ (x : S₁ ∋ s) → x &/⋯ id[ T ] ≡ ` x
            idˢ–def x = refl

            wk–def : (x : S₁ ∋ s) → x &/⋯ (wk {s = s′}) ≡ (suc x)
            wk–def _ = wk-id/` _ _

            ext₀–def : {{K : Kit M}} (x/t : S₂ ∋/⊢ᴷ s) (ϕ : S₁ –[ K ]→ S₂) → 
              zero &/⋯ (x/t ∙ ϕ) ≡ x/t
            ext₀–def _ _ = refl

            extₛ–def : ∀ {{K : Kit M}} (x/t : S₂ ∋/⊢ᴷ s) (x′ : S₁ ∋ s′) (ϕ : S₁ –[ K ]→ S₂) → 
              suc x′ &/⋯ (x/t ∙ ϕ) ≡ x′ &/⋯ ϕ
            extₛ–def _ _ _ = refl

            comp–def : {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{K₄ : Kit M₄}} {{K₅ : Kit M₅}} 
                       {{C₁ : ComposeKit K₁ K₂ K₃}} {{C₂ : ComposeKit K₃ K₄ K₅}}
                      (x : S₁ ∋ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
                      x &/⋯ (ϕ₁ ; ϕ₂) ≡ (x &/⋯ ϕ₁) &/⋯ ϕ₂
            comp–def _ _ _ = refl 

            comp–def–safe : (x : S₁ ∋ s) (ϕ₁ : S₁ –[ V ]→ S₂) (ϕ₂ : S₂ –[ V ]→ S₃) → 
                      x &/⋯ (ϕ₁ ; ϕ₂) ≡ (x &/⋯ ϕ₁) &/⋯ ϕ₂
            comp–def–safe _ _ _ = refl

            compₗ–idˢ–def : {{K : Kit M}} 
                        (x : S₁ ∋ s) (ϕ₂ : S₁ –[ V ]→ S₂) → 
              x &/⋯ (id[ T ] ; ϕ₂) ≡ ` (x &/⋯ ϕ₂)
            compₗ–idˢ–def _ _ = ⋯-var _ _ 

            compᵣ–idˢ–def : (x : S₁ ∋ s) (ϕ : S₁ –[ V ]→ S₂) → 
                x &/⋯ (ϕ ; idˢ) ≡ ` (x &/⋯ ϕ)
            compᵣ–idˢ–def _ _ = refl
 
            compₗ–wk–def : {{K : Kit M}} (x : S₁ ∋ s) (ϕ₂ : (s′ ∷ S₁) –[ K ]→ S₂) → 
              x &/⋯ (wk ; ϕ₂) ≡ (suc x) &/⋯ ϕ₂ 
            compₗ–wk–def _ _ = refl 

            compₗ–ext₀–def  : {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{C : ComposeKit K₁ K₂ K₃}} 
                       (x/t : S₂ ∋/⊢ᴷ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
              zero &/⋯ ((x/t ∙ ϕ₁) ; ϕ₂) ≡ x/t &/⋯ ϕ₂
            compₗ–ext₀–def _ _ _ = refl
            
            compₗ–extₛ–def : ∀ {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{C : ComposeKit K₁ K₂ K₃}} 
                       (x/t : S₂ ∋/⊢ᴷ s) (x′ : S₁ ∋ s′) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
              suc x′ &/⋯ ((x/t ∙ ϕ₁) ; ϕ₂) ≡ x′ &/⋯ (ϕ₁ ; ϕ₂)
            compₗ–extₛ–def _ _ _ _ = refl
                
            compₗ–id : {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{C : ComposeKit K₁ K₂ K₂}} 
              (ϕ : S₁ –[ K₂ ]→ S₂) → id {{K₁}} ; ϕ ≡ ϕ 
            compₗ–id {Vᴹ} {M₂} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–C {{K₁}} C | unique–K K₁ | C–defᴿ {{K₂}}
              =  refl
            compₗ–id {Tᴹ} {Vᴹ} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–K K₁ | unique–K K₂ = ⊥-elim (impossible–Cˢᴷᴿ {{V}} C)
            compₗ–id {Tᴹ} {Tᴹ} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–C {{K₁}} {{K₂}} {{K₂}} C | unique–K K₁ | unique–K K₂ | C–defˢ {{T}} 
              = ~-ext {{T}} λ _ x → ⋯-var {{T}} _ _  

            compᵣ–id : {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{C : ComposeKit K₁ K₂ K₁}} 
              (ϕ : S₁ –[ K₁ ]→ S₂) → ϕ ; id {{K₂}} ≡ ϕ 
            compᵣ–id {Vᴹ} {Vᴹ} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–C {{K₁}} {{K₂}} {{K₁}} C | unique–K K₁ | unique–K K₂ | C–defᴿ {{V}}  
              =  refl
            compᵣ–id {Vᴹ} {Tᴹ} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–K K₁ | unique–K K₂ = ⊥-elim (impossible–Cᴷˢᴿ {{V}} C)
            compᵣ–id {Tᴹ} {{K₁}} {{K₂}} {{C}} ϕ rewrite unique–C {{K₁}} {{K₂}} {{K₁}} C | unique–K K₁ | C–defˢ {{K₂}} 
              = ~-ext {{T}} λ _ x → ⋯-right-id {{K₂}} _
 
            -- the idiomatic way to transform a ren/sub into a sub is to compose id sub on the right. 
            -- if its applied on the left, we transform it.   
            postulate
              norm–idˢ : {{K : Kit M}} {{C : ComposeKit K T T}}
                -- SAFETY: By induction on K and uniqueness of Kits ∎
                (ϕ : S₁ –[ K ]→ S₂) →
                  --!! NormId 
                  ϕ ; id[ T ] ≡ id[ T ] ;[ T ;ᴷ K ] ϕ 

            -- norm–idˢ {Vᴹ} {{K}} ϕ rewrite unique–K K | C–defᴿ {{T}} = 
            --   ~-ext {{T}} λ _ x → ⋯-var {{V}} _ _
            -- norm–idˢ {Tᴹ} {{K}} ϕ rewrite unique–K K | C–defˢ {{T}} = 
            --   ~-ext {{T}} λ _ x → _ ≡⟨ ⋯-var {{T}} _ _ ⟩ _ ≡⟨ sym (⋯-right-id {{T}} _) ⟩ _ ∎  

            --! AssocTryT
            associativity : 
              {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{K₄ : Kit M₄}} {{K₅ : Kit M₅}} 
              {{C₁ : ComposeKit K₁ K₂ K₃}} {{C₂ : ComposeKit K₃ K₄ K₅}}
              (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ K₄ ]→ S₄) →   
              -- SAFETY: Assume the incoming Compose Kits C₁ and C₂ are valid.
              --         By case analysis on K₁, K₂, K₃, K₄ and K₅, the definition of _⊔_ and 
              --         the uniqueness of (Compose-) Kits, we know the outgoing Compose Kits 
              --         K₁ , (K₂ ⊔ K₄) , K₅ and K₂ , K₄ , (K₂ ⊔ K₄) are valid too. ∎
              (ϕ₁ ; ϕ₂) ; ϕ₃ ≡ ϕ₁ ;[ K₁ , (K₂ ⊔ K₄) , K₅ ] (ϕ₂ ;[ K₂ , K₄ , (K₂ ⊔ K₄) ] ϕ₃) 
              
            associativity {_} {_} {Vᴹ} {Vᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ = ⊥-elim (impossible–Cᴿᴿˢ C₂)
            associativity {_} {_} {_} {Tᴹ} {Vᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₄ | unique–K K₅ = ⊥-elim (impossible–Cᴷˢᴿ C₂)
            associativity {_} {_} {Tᴹ} {_} {Vᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
             rewrite unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₃ | unique–K K₅ = ⊥-elim (impossible–Cˢᴷᴿ C₂)
            associativity {Vᴹ} {Vᴹ} {Tᴹ} {_} {_} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–K K₁ | unique–K K₂ | unique–K K₃ = 
              ⊥-elim (impossible–Cᴿᴿˢ C₁)
            associativity {_} {Tᴹ} {Vᴹ} {_} {_} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–K K₂ | unique–K K₃ = ⊥-elim (impossible–Cᴷˢᴿ C₁)
            associativity {Tᴹ} {_} {Vᴹ} {_} {_} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–K K₁ | unique–K K₃ = ⊥-elim (impossible–Cˢᴷᴿ C₁)
            associativity {Vᴹ} {Vᴹ} {Vᴹ} {Vᴹ} {Vᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ V , V , V and K₂ , K₄ , (K₂ ⊔ K₄) = V , V , V ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | C–defᴿ {{V}} = refl
            associativity {Vᴹ} {Vᴹ} {Vᴹ} {Tᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ V , T , T and K₂ , K₄ , (K₂ ⊔ K₄) = V , T , T ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | C–defᴿ {{V}} | C–defᴿ {{T}} = refl
            associativity {Vᴹ} {Tᴹ} {Tᴹ} {Vᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ V , T , T and K₂ , K₄ , (K₂ ⊔ K₄) = T , T , T ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | C–defᴿ {{T}} | C–defˢ {{V}} = refl
            associativity {Vᴹ} {Tᴹ} {Tᴹ} {Tᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ V , T , T and K₂ , K₄ , (K₂ ⊔ K₄) = T , T , T ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | C–defᴿ {{T}} | C–defˢ {{T}} = refl
            associativity {Tᴹ} {Vᴹ} {Tᴹ} {Vᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ T , V , T and K₂ , K₄ , (K₂ ⊔ K₄) = V , V , V ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | C–defˢ {{V}} | C–defᴿ {{V}}
              = ~-ext {{T}} λ s x →  ⋯-compositionality {{V}} {{V}} {{V}} {{Cᴿᴿ}} _ _ _ 
            associativity {Tᴹ} {Vᴹ} {Tᴹ} {Tᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ T , T , T and K₂ , K₄ , (K₂ ⊔ K₄) = V , T , T ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | C–defˢ {{V}} | C–defˢ {{T}} | C–defᴿ {{T}}
              = ~-ext {{T}} λ s x →  ⋯-compositionality {{V}} {{T}} {{T}} {{Cᴿˢ}} _ _ _
            associativity {Tᴹ} {Tᴹ} {Tᴹ} {Vᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
               -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ T , T , T and K₂ , K₄ , (K₂ ⊔ K₄) = T , V , T ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | C–defˢ {{V}} | C–defˢ {{T}} 
              = ~-ext {{T}} λ s x →  ⋯-compositionality {{T}} {{V}} {{T}} {{Cˢᴿ}} _ _ _
            associativity {Tᴹ} {Tᴹ} {Tᴹ} {Tᴹ} {Tᴹ} {{K₁}} {{K₂}} {{K₃}} {{K₄}} {{K₅}} {{C₁}} {{C₂}} ϕ₁ ϕ₂ ϕ₃ 
              -- SAFETY: K₁ , (K₂ ⊔ K₄) , K₅ ≡ T , T , T and K₂ , K₄ , (K₂ ⊔ K₄) = T , T , T ∎
              rewrite unique–C {{K₁}} {{K₂}} {{K₃}} C₁ | unique–C {{K₃}} {{K₄}} {{K₅}} C₂ | unique–K K₁ | unique–K K₂ | unique–K K₃ | unique–K K₄ | unique–K K₅ | C–defˢ {{T}}  
              = ~-ext {{T}} λ s x →  ⋯-compositionality {{T}} {{T}} {{T}} {{Cˢˢ}} _ _ _
        
            distributivity : {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{C : ComposeKit K₁ K₂ K₃}} 
              (x/t : S₂ ∋/⊢[ K₁ ] s)  (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
              (x/t ∙ ϕ₁) ; ϕ₂ ≡ (x/t &/⋯ ϕ₂) ∙ (ϕ₁ ; ϕ₂)
            distributivity _ _ _ = ~-ext λ { _ zero → refl ; _ (suc x) → refl } 
            
            interact : {{K : Kit M}} 
              (x/t : S₂ ∋/⊢[ K ] s) (ϕ : S₁ –[ K ]→ S₂) → wk ; (x/t ∙ ϕ) ≡ ϕ 
            interact x/t ϕ = refl
        
            η–id : (zero {s = s} {S = S}) ∙ wk ≡ id 
            η–id = ~-ext λ { _ zero → refl ; _ (suc x) → refl }
 
            η–law : {{K : Kit M}}
              (ϕ : (s ∷ S₁) –[ K ]→ S₂) → (zero &/⋯ ϕ) ∙ (wk ; ϕ) ≡ ϕ
            η–law ϕ = ~-ext λ { _ zero → refl ; _ (suc x) → refl } 
            postulate
              coincidence : {{K : Kit M}} {{C : ComposeKit K T T}}
                               (t : S₁ ⊢ s) (ϕ : S₁ –[ K ]→ S₂) → 
                  t &/⋯ (ϕ ; idˢ) ≡ let instance _ = K , V , K in t &/⋯ ϕ
            -- coincidence {Vᴹ} {{K}} {{C}} t ϕ rewrite unique–C C | unique–K K = {! cong (_⋯_ {{K = ?}} t) ?  !}
            -- coincidence {Tᴹ} {{K}} {{C}} t ϕ rewrite unique–C C | unique–K K | C–defˢ {{T}} = 
            --   cong (_⋯_ {{K = T}} t) {!   !}
            --   
            postulate
              
              -- coincidenceₓ²
              -- coincidenceₜ²
              coincidence–foldᴷ : {{K : Kit M}} {{C : ComposeKit K T T}}
                            (t : (s′ ∷ S₁) ⊢ s) (x/t : S₂ ∋/⊢[ K ] s′) (ϕ : S₁ –[ K ]→ S₂) → 
                t &/⋯ ((x/t &/⋯ id[ T ]) ∙ (ϕ ; idˢ)) ≡ let instance _ = K , V , K in 
                  (t &/⋯ (x/t ∙ ϕ))
              coincidence–foldᵀ : {{K : Kit M}} {{C : ComposeKit K T T}} {{C : ComposeKit K V K}}
                            (t : (s′ ∷ S₁) ⊢ s) (t′ : S₁ ⊢ s′) (ϕ : S₁ –[ K ]→ S₂) → 
                t &/⋯ ((t′ &/⋯ ϕ) ∙ (ϕ ; idˢ)) ≡ (t &/⋯ (t′ ∙ idˢ)) &/⋯ ϕ
              -- coincidence–push : {{K : Kit M}} {{C : ComposeKit K T T}}
              --               (t : (s′ ∷ S₁) ⊢ s) (t′ : S₂ ⊢ s′) (ϕ : S₁ –[ K ]→ S₂) → 
              --   t &/⋯ (t′ ∙ (ϕ ; idˢ)) ≡ let instance _ = K , V , K in t &/⋯ (t′ ∙ (idˢ ; ϕ))
              -- coincidence-ext²  
              -- coincidence–push₂ : {{K : Kit M}} {{C : ComposeKit K T T}} 
              --               (t : (s′ ∷ S₁) ⊢ s) (t′ : S₂ ⊢ s′) (ϕ : S₁ –[ K ]→ S₂) → 
              --   t &/⋯ ((t′) ∙ (ϕ ; idˢ)) ≡  let instance _ = K , V , K in t &/⋯ ((((id/` zero) ∙ (ϕ ; wk)) ; (t′ ∙ idˢ)))
              -- coincidence-ext²   