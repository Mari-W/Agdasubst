{-# OPTIONS --rewriting --experimental-lazy-instances --allow-unsolved-metas #-}
module examples where

open import Data.List.Membership.Propositional  
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
  fun-exti : ∀{ℓ₁ ℓ₂} → ExtensionalityImplicit  ℓ₁ ℓ₂


--! E >
open import Agda.Builtin.Equality.Rewrite public

record _a : Set₁ where
  field 
    --!! SortTy
    Sort : Set


  postulate
    --!! ScopeDefTy 
    Scope : Set
    --! ScopeDef
    []   : Scope 
    _∷_  : Sort → Scope → Scope

  Scoped = Scope → Sort → Set

  variable 
    S S₁ S₂ S₃ S₄ : Scope 
    s s′ : Sort 
  module _a where
    postulate
      --!! VarsTy
      _∋_ : Scope → Sort → Set 

  data _∋_ : Scope → Sort → Set where
    --! Vars
    zero  : (s ∷ S) ∋ s
    suc   :  S ∋ s → (s′ ∷ S) ∋ s

  record _b : Set₁ where
    field
      --!! TmC
      _⊢_ : Scope → Sort → Set   

      --! VarC
      `_ : S ∋ s → S ⊢ s

  
    -- postulate
    --   Mode : Set 
    --   Vᴹ  : Mode
    --   Tᴹ  : Mode
    --   _⨆_ : Mode → Mode → Mode
-- 
    -- 
    -- variable
    --   M M₁ M₂ M₃ M₄ M₅ : Mode

    postulate
      --!! KitDefTy
      Kit : Set 
      --! KitDef
      V    : Kit
      T    : Kit
      _⊔_  : Kit → Kit → Kit 

    variable
      K K₁ K₂ K₃ : Kit

    postulate
      --!! VarTrmTy
      _∋/⊢[_]_ : Scope → Kit → Sort → Set

      --!! PrimsTy
      _–[_]→_  : Scope → Kit → Scope → Set
      --! Prims
      id   : S –[ K ]→ S
      wk   : S –[ V ]→ (s ∷ S)
      _∙_  : S₂ ∋/⊢[ K ] s → S₁ –[ K ]→ S₂ → (s ∷ S₁) –[ K ]→ S₂
      _;_  : S₁ –[ K₁ ]→ S₂ → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₃ ]→ S₃ 

      --! VarTrmApp
      _&/⋯_ : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₃ ] s

      _;[_,_,_]_   : S₁ –[ K₁ ]→ S₂ → Kit → Kit → Kit → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₃ ]→ S₃
      _&/⋯[_,_,_]_ : S₁ ∋/⊢[ K₁ ] s → Kit → Kit → Kit → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₃ ] s
      id[_]   : Kit → S –[ K ]→ S
      _∙[_]_  : S₂ ∋/⊢[ K ] s → Kit → S₁ –[ K ]→ S₂ → (s ∷ S₁) –[ K ]→ S₂

      -- --! TypeLevelMode
      -- ＋botᴿ   : M  ⨆ Vᴹ         ≡ M             
      -- ＋botₗ   : Vᴹ ⨆ M          ≡ M              
      -- ＋topᴿ   : M ⨆ Tᴹ          ≡ Tᴹ              
      -- ＋topₗ   : Tᴹ ⨆ M          ≡ Tᴹ     
      -- ＋idem   : M ⨆ M           ≡ M                      
      -- ＋assoc  : (M₁ ⨆ M₂) ⨆ M₃  ≡ M₁ ⨆ (M₂ ⨆ M₃)  

    -- {-# REWRITE ＋botᴿ ＋botₗ ＋topᴿ ＋topₗ ＋idem ＋assoc #-}
    postulate
      --! TypeLevel   
      botᴿ   : K ⊔ V           ≡ K               
      botₗ   : V ⊔ K           ≡ K               
      topᴿ   : K ⊔ T           ≡ T              
      topₗ   : T ⊔ K           ≡ T     
      idem   : K ⊔ K           ≡ K                        
      assoc  : (K₁ ⊔ K₂) ⊔ K₃  ≡ K₁ ⊔ (K₂ ⊔ K₃)  

    {-# REWRITE botᴿ botₗ topᴿ topₗ idem assoc #-}
    postulate
      --! DefLawTy
      imgⱽ : S ∋/⊢[ V ] s ≡ S ∋ s   
      imgᵀ : S ∋/⊢[ T ] s ≡ S ⊢ s 

    {-# REWRITE imgⱽ imgᵀ #-}
    module foo
       {{K₁ : Kit}} {{K₂ : Kit}} {{K₃ : Kit}} {{K₄ : Kit}} {{K₅ : Kit}}
       (ρ : S₁ –[ V ]→ S₂) (ρ₁ : S₁ –[ V ]→ S₂) (ρ₂ : S₂ –[ V ]→ S₃) (ρ₄ : S₃ –[ V ]→ S₄)
       (σ : S₁ –[ T ]→ S₂) (σ₁ : S₁ –[ T ]→ S₂) (σ₂ : S₂ –[ T ]→ S₃) (σ₄ : S₃ –[ T ]→ S₄)
      (ϕ : S₁ –[ K₁ ]→ S₂) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₄ : S₃ –[ K₄ ]→ S₄)
      (x/t : S₂ ∋/⊢[ K₁ ] s)   (x/t₁ : S₂ ∋/⊢[ K₁ ] s) (t : S₂ ⊢ s) (t′ : S₂ ⊢ s′) (x : S₁ ∋ s) (x′ : S₁ ∋ s′) (ϕ′ : (s ∷ S₁) –[ K₂ ]→ S₂) 
      where 

      postulate
        --! DefLaw {
        ＋idˢ   : x &/⋯[ V , T , T ] id[ T ]                 ≡ ` x
        ＋wk    : x &/⋯[ V , V , V ] wk                      ≡ suc x
        ext₀    : zero &/⋯[ V , K , K ] (x/t ∙[ K ] ϕ)       ≡ x/t
        extₛ    : suc x′ &/⋯[ V , K , K ] (x/t ∙[ K ] ϕ)     ≡ 
                 x′ &/⋯[ V , K , K ] ϕ
        comp    : x &/⋯[ V , V , V ] (ρ₁ ;[ V , V , V ] ρ₂)  ≡ 
                 (x &/⋯[ V , V , V ] ρ₁) &/⋯[ V , V , V ] ρ₂
        --! }

        --! CompGeneral 
        comp–general : 
          x/t &/⋯[ K₃ , K₄ , K₅ ] (ϕ₁ ;[ K₁ , K₂ , K₃ ] ϕ₂) ≡ 
          (x/t &/⋯[ K₁ , K₂ , K₃ ] ϕ₁) &/⋯[ K₃ , K₄ , K₅ ] ϕ₂


        --! SpecialDefLaws
        compᵣ–idˢ   : x &/⋯[ V , T , T ] (ρ₁ ;[ V , T , T ] id[ T ])    ≡ 
                      ` (x &/⋯[ V , V , V ] ρ₁)
        compₗ–idˢ   : x &/⋯[ V , T , T ]  (id[ T ] ;[ T , V , T ] ρ₂)  ≡ 
                      ` (x &/⋯[ V , V , V ] ρ₂)  
        compₗ–wk    : x &/⋯[ V , K , K ] (wk ;[ V , K , K ] ϕ′)        ≡ 
                      suc x &/⋯[ V , K , K ] ϕ′ 
        compₗ–ext₀  : zero &/⋯[ V , K₃ , K₃ ] ((x/t₁ ∙[ K₁ ] ϕ₁) ;[ K₁ , K₂ , K₃ ] ϕ₂)    ≡ 
                      x/t &/⋯[ K₁ , K₂ , K₃ ] ϕ₂
        compₗ–extₛ  : suc x′ &/⋯[ V , K₃ , K₃ ] ((x/t₁ ∙[ K₁ ] ϕ₁) ;[ K₁ , K₂ , K₃ ] ϕ₂)  ≡ 
                      x′ &/⋯[ V , K₃ , K₃ ] (ϕ₁ ;[ K₁ , K₂ , K₃ ] ϕ₂)
    
        --! Interaction
        comp-idₗ        : id[ K ] ;[ K , K , K ] ϕ                                  ≡  ϕ
        comp-idᵣ        : ϕ ;[ K , K , K ] id[ K ]                                  ≡ ϕ
        associativity   : (ϕ₁ ;[ K₁ , K₂ , K₃ ] ϕ₂) ;[ K₃ , K₄ , K₅ ] ϕ₄            ≡ 
                          ϕ₁ ;[ K₁ , (K₂ ⊔ K₄) , K₅ ] (ϕ₂ ;[ K₂ , K₄ , (K₂ ⊔ K₄) ] ϕ₄) 
        distributivity  : (x/t₁ ∙[ K₁ ] ϕ₁) ;[ K₁ , K₂ , K₃ ] ϕ₂                      ≡ 
                          (x/t₁ &/⋯[ K₁ , K₂ , K₃ ] ϕ₂) ∙[ K₃ ] (ϕ₁ ;[ K₁ , K₂ , K₃ ] ϕ₂)
        interact        : wk ;[ V , K , K ] (x/t ∙[ K ] ϕ)                            ≡ ϕ 
        η–id            : zero ∙[ V ] wk                                            ≡ id[ V ]
        η–law           : (zero &/⋯[ V , K , K ] ϕ′) ∙[ K ] (wk ;[ V , K , K ] ϕ′)  ≡ ϕ′

      record _c : Set₁ where
        field
          --! Monad
          right-id          : x/t₁ &/⋯[ K₁ , K₂ , K₁ ] id[ K₂ ] ≡ x/t₁
          compositionality  : (x/t₁ &/⋯[ K₁ , K₂ , K₃ ] ϕ₁) &/⋯[ K₃ , K₄ , T ] ϕ₄  ≡ 
                              x/t₁ &/⋯[ K₁ , K₂ ⊔ K₄ , T ] (ϕ₁ ;[ K₂ , K₄ , (K₂ ⊔ K₄) ] ϕ₂)

          --! CompoGeneral
          compositionality–general  : 
            (x/t₁ &/⋯[ K₁ , K₂ , K₃ ] ϕ₁) &/⋯[ K₃ , K₄ , K₅ ] ϕ₄  ≡ 
            x/t₁ &/⋯[ K₁ , K₂ ⊔ K₄ , K₅ ] (ϕ₁ ;[ K₂ , K₄ , (K₂ ⊔ K₄) ] ϕ₂)

          --! Coincidence Laws
          coincidence       : t &/⋯[ T , T , T ] (ϕ ;[ K , T , T ] id[ T ])  ≡ 
                              t &/⋯[ T , K , T ] ϕ  
          coincidence–fold : t &/⋯[ T , T , T ] ((x/t &/⋯[ K , T , T ] id[ T ]) ∙ (ϕ ;[ K , T , T ] id[ T ]))   ≡ 
                             (t &/⋯[ T , K , T ] (x/t ∙ ϕ))
          
          coincidence–push : t &/⋯[ T , T , T ] (t′ ∙ (ϕ ;[ K , T , T ] id[ T ])) ≡ 
                             t &/⋯[ T , T , T ] (t′ ∙ (id[ T ] ;[ T , K , T ]  ϕ))
          

    
      record _d : Set₁ where
        field
          --! TravL
          var : (` x) &/⋯[  T , K , T ] ϕ ≡ 
                (x &/⋯[ V , K , K ] ϕ) &/⋯[ K , T , T ] id[ T ]
        


open import Data.List hiding ([_])
open import Data.Nat hiding (_⊔_)
open import Data.Fin using (Fin)

--! Rewrite
+–idᵣ : ∀ n → n + 0 ≡ n
+–idᵣ zero     = refl
+–idᵣ (suc n)  = cong suc (+–idᵣ n)

--! RewriteIt
{-# REWRITE +–idᵣ #-}

--! RewriteEx
_ : ∀ {n} → n + 0 ≡ n
_ = refl

--! Default
record Default {ℓ} (A : Set ℓ) : Set ℓ where
  field default : A

--! DefFields
open Default {{...}} public

--! DefInst
instance 
  default–ℕ : Default ℕ
  default–ℕ .default = 0 

--! DefEx
_ : default ≡ 0
_ = refl

--! Opaque
opaque
  forty–two : ℕ
  forty–two = 42
  
--! OpaqueExO 
_ : forty–two ≡ 42
_ = {!  !} -- not provable.

--! OpaqueExT {
opaque   
  unfolding forty–two

  _ : forty–two ≡ 42
  _ = refl
--! }

module C where
  data Sort : Set where 
    expr type kind : Sort 

  variable 
    s s′ : Sort 
    S S₁ S₂ S₃ S₄ : List Sort

  Scope = List Sort
  Scoped = Scope → Sort → Set

  data _∋_ : Scoped where
    zero  : ∀ {S s} → (s ∷ S) ∋ s
    suc   : ∀ {S s s′} → S ∋ s → (s′ ∷ S) ∋ s

  data _⊢_ : Scoped where 
    `_       : S ∋ s → S ⊢ s     
    λx_      : (expr ∷ S) ⊢ expr → S ⊢ expr
    Λα_      : (type ∷ S) ⊢ expr → S ⊢ expr
    ∀[α∶_]_  : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
    _·_      : S ⊢ expr → S ⊢ expr → S ⊢ expr
    _•_      : S ⊢ expr → S ⊢ type → S ⊢ expr
    _⇒_      : S ⊢ type → S ⊢ type → S ⊢ type
    ★        : S ⊢ kind

  data Tag : Set where 
    instance Ren Sub : Tag 

  image : Tag → Scoped 
  image Ren = _∋_
  image Sub = _⊢_

  _∋/⊢[_]_ : Scope → Tag → Sort → Set
  S ∋/⊢[ k ] s = image k S s 

  opaque 
    _→ᴷ_ : {{k : Tag}} → Scope → Scope → Set
    _→ᴷ_ {{k}} S₁ S₂ = ∀ {s} → S₁ ∋ s → S₂ ∋/⊢[ k ] s

  _–[_]→_ : Scope → Tag → Scope → Set
  S₁ –[ k ]→ S₂ = _→ᴷ_ {{k}} S₁ S₂

  _→ᴿ_ : Scope → Scope → Set
  _→ᴿ_ = _–[ Ren ]→_

  _→ˢ_ : Scope → Scope → Set
  _→ˢ_ = _–[ Sub ]→_

  opaque
    unfolding _→ᴷ_

    _&_ : ∀ {{k : Tag}} → S₁ ∋ s → S₁ –[ k ]→ S₂ → S₂ ∋/⊢[ k ] s
    x & ϕ = ϕ x

    _∙_ : ∀ {{k : Tag}} → S₂ ∋/⊢[ k ] s → S₁ –[ k ]→ S₂ → (s ∷ S₁) –[ k ]→ S₂
    (x/t ∙ _) zero   = x/t
    (_ ∙ ϕ) (suc x)  = ϕ x

    id : ∀ {{k : Tag}} → S –[ k ]→ S 
    id {{Ren}} x = x 
    id {{Sub}} x = ` x 

    wk : S →ᴿ (s ∷ S)
    wk x = suc x

    _;ᴿᴷ_ : ∀ {{k : Tag}} → S₁ →ᴿ S₂ → S₂ –[ k ]→ S₃ → S₁ –[ k ]→ S₃
    (ρ₁ ;ᴿᴷ ϕ₂) x = ϕ₂ (ρ₁ x) 

  _↑ᴿ_ : S₁ →ᴿ S₂ → ∀ s → (s ∷ S₁) →ᴿ (s ∷ S₂)
  ρ ↑ᴿ _ = zero ∙ (ρ ;ᴿᴷ wk) 

  _⋯ᴿ_ : S₁ ⊢ s → S₁ →ᴿ S₂ → S₂ ⊢ s
  -- Traversal Laws
  (` x)         ⋯ᴿ ρ = ` (x & ρ)
  (λx e)        ⋯ᴿ ρ = λx (e ⋯ᴿ (ρ ↑ᴿ _))
  (Λα e)        ⋯ᴿ ρ = Λα (e ⋯ᴿ (ρ ↑ᴿ _))
  (∀[α∶ k ] t)  ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] (t ⋯ᴿ (ρ ↑ᴿ _))
  (e₁ · e₂)     ⋯ᴿ ρ = (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)
  (e • t)       ⋯ᴿ ρ = (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
  (t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
  ★             ⋯ᴿ ρ = ★  

  opaque
    unfolding 
      _→ᴷ_ _&_ _∙_ id wk _;ᴿᴷ_

    _;ˢᴿ_ : S₁ →ˢ S₂ → S₂ →ᴿ S₃ → S₁ →ˢ S₃
    (σ₁ ;ˢᴿ ρ₂) x = (σ₁ x) ⋯ᴿ ρ₂
  
  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  (σ ↑ˢ _) = (` zero) ∙ (σ ;ˢᴿ wk)

  _⋯ˢ_ : S₁ ⊢ s → S₁ →ˢ S₂ → S₂ ⊢ s
  -- Traversal Laws
  (` x)         ⋯ˢ σ = (x & σ)
  (λx e)        ⋯ˢ σ = λx (e ⋯ˢ (σ ↑ˢ _))
  (Λα e)        ⋯ˢ σ = Λα (e ⋯ˢ (σ ↑ˢ _))
  (∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  (e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  (e • t)       ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  ★             ⋯ˢ σ = ★

  opaque
    unfolding 
      _→ᴷ_ _&_ _∙_ id wk _;ᴿᴷ_ id _;ˢᴿ_

    _;ˢˢ_ :  S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
    (σ₁ ;ˢˢ σ₂) x = (σ₁ x) ⋯ˢ σ₂

--! Scoped {
data Kind : Set where
  ★  : Kind

data Type (n : ℕ) : Set where
  `_       : Fin n → Type n 
  ∀[α:_]_  : Type (suc n) → Type n
  _⇒_      : Type n → Type n → Type n

data Expr (n m : ℕ) : Set where
  `_   : Fin m → Expr n m
  λx_  : Expr n (suc m) → Expr n m
  Λα_  : Expr (suc n) m → Expr n m
  _·_  : Expr n m → Expr n m → Expr n m
  _•_  : Expr n m → Type n → Expr n m
--! }

--! MultiSorted {
data Sort : Set where 
  expr type kind : Sort 
--! [
variable 

  s s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort
--! ]

Scope = List Sort
Scoped = Scope → Sort → Set

data _∋_ : Scoped where
  zero  : ∀ {S s} → (s ∷ S) ∋ s
  suc   : ∀ {S s s′} → S ∋ s → (s′ ∷ S) ∋ s

data _⊢_ : Scoped where 
  `_       : S ∋ s → S ⊢ s     
  λx_      : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_      : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_  : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_      : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _•_      : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_      : S ⊢ type → S ⊢ type → S ⊢ type
  ★        : S ⊢ kind
--! } 

variable
  e e₁ e₂ e′ : S ⊢ expr
  k k′ : S ⊢ kind
  x x′ : S ∋ s
  t t₁ t₂ t′ : S ⊢ s

--! Ren {
opaque
  _→ᴿ_ : Scope → Scope → Set
  S₁ →ᴿ S₂ = ∀ {s} → S₁ ∋ s → S₂ ∋ s 

  _&ᴿ_ : S₁ ∋ s → S₁ →ᴿ S₂ → S₂ ∋ s
  x &ᴿ ρ = ρ x
  
  idᴿ : S →ᴿ S 
  idᴿ x = x 

  wk : S →ᴿ (s ∷ S)
  wk x = suc x

  _∙ᴿ_ : S₂ ∋ s → S₁ →ᴿ S₂ → (s ∷ S₁) →ᴿ S₂
  (x ∙ᴿ _) zero     = x
  (_ ∙ᴿ ρ) (suc x)  = ρ x

  _;ᴿᴿ_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
  (ρ₁ ;ᴿᴿ ρ₂) x = ρ₂ (ρ₁ x)

_↑ᴿ_ : S₁ →ᴿ S₂ → ∀ s → (s ∷ S₁) →ᴿ (s ∷ S₂)
ρ ↑ᴿ _ = zero ∙ᴿ (ρ ;ᴿᴿ wk)

_⋯ᴿ_ : S₁ ⊢ s → S₁ →ᴿ S₂ → S₂ ⊢ s
-- Traversal Laws
(` x)         ⋯ᴿ ρ = ` (x &ᴿ ρ)
(λx e)        ⋯ᴿ ρ = λx (e ⋯ᴿ (ρ ↑ᴿ _))
(Λα e)        ⋯ᴿ ρ = Λα (e ⋯ᴿ (ρ ↑ᴿ _))
(∀[α∶ k ] t)  ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] (t ⋯ᴿ (ρ ↑ᴿ _))
(e₁ · e₂)     ⋯ᴿ ρ = (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)
(e • t)       ⋯ᴿ ρ = (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
(t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
★             ⋯ᴿ ρ = ★ 
--! }

--! Sub {
opaque
  unfolding 
    _→ᴿ_ _&ᴿ_ idᴿ wk _∙ᴿ_ _;ᴿᴿ_

  _→ˢ_ : Scope → Scope → Set
  S₁ →ˢ S₂ = ∀ {s} → S₁ ∋ s → S₂ ⊢ s

  _&ˢ_ : S₁ ∋ s → S₁ →ˢ S₂ → S₂ ⊢ s
  x &ˢ σ = σ x

  idˢ : S →ˢ S
  idˢ = `_

  _∙ˢ_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂
  (t ∙ˢ _) zero     = t
  (_ ∙ˢ σ) (suc x)  = σ x
  
  _;ᴿˢ_ : S₁ →ᴿ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (ρ₁ ;ᴿˢ σ₂) x = σ₂ (ρ₁ x)

  _;ˢᴿ_ : S₁ →ˢ S₂ → S₂ →ᴿ S₃ → S₁ →ˢ S₃
  (σ₁ ;ˢᴿ ρ₂) x = (σ₁ x) ⋯ᴿ ρ₂
  

_↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
(σ ↑ˢ _) = (` zero) ∙ˢ (σ ;ˢᴿ wk)

_⋯ˢ_ : S₁ ⊢ s → S₁ →ˢ S₂ → S₂ ⊢ s
-- Traversal Laws
(` x)         ⋯ˢ σ = (x &ˢ σ)
(λx e)        ⋯ˢ σ = λx (e ⋯ˢ (σ ↑ˢ _))
(Λα e)        ⋯ˢ σ = Λα (e ⋯ˢ (σ ↑ˢ _))
(∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
(e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
(e • t)       ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
(t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
★             ⋯ˢ σ = ★

opaque
  unfolding 
    _→ᴿ_ _&ᴿ_ idᴿ wk _∙ᴿ_ _;ᴿᴿ_ 
    _→ˢ_ _&ˢ_ idˢ _∙ˢ_ _;ᴿˢ_ _;ˢᴿ_

  _;ˢˢ_ :  S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ;ˢˢ σ₂) x = (σ₁ x) ⋯ˢ σ₂
--! }

variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂ 
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂ 

module _B where
  record _d : Set where
    field
      --! MonadLaws {
      -- Monad Laws
      ＋right-idᴿ  : (t : S ⊢ s) → t ⋯ᴿ idᴿ  ≡ t
      ＋right-idˢ  : (t : S ⊢ s) → t ⋯ˢ idˢ  ≡ t

      ＋compositionalityᴿᴿ  : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂  ≡ t ⋯ᴿ (ρ₁ ;ᴿᴿ ρ₂)
      ＋compositionalityᴿˢ  : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (ρ₁ ;ᴿˢ σ₂)
      ＋compositionalityˢᴿ  : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂  ≡ t ⋯ˢ (σ₁ ;ˢᴿ ρ₂)
      ＋compositionalityˢˢ  : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (σ₁ ;ˢˢ σ₂)

      -- Coincidence Laws
      ＋coincidence       : (t : S₁ ⊢ s) → t ⋯ˢ (ρ ;ᴿˢ idˢ)  ≡ t ⋯ᴿ ρ
      ＋coincidence-fold  : (t : (s′ ∷ S₁) ⊢ s) → t ⋯ˢ ((` x) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ t ⋯ᴿ (x ∙ᴿ ρ)
      --! } 
      ＋coincidence-push  : (t : (s′ ∷ S₁) ⊢ s) → t ⋯ˢ (t′ ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ t ⋯ˢ (t′ ∙ˢ (idˢ ;ˢᴿ ρ))
  opaque 
    unfolding _→ᴿ_ _&ᴿ_ idᴿ wk _∙ᴿ_ _;ᴿᴿ_ _→ˢ_ _&ˢ_ idˢ _∙ˢ_ _;ᴿˢ_ _;ˢᴿ_ _;ˢˢ_

    --! DefLaws {
    -- Definitional Laws 
    ＋idᴿ  : x &ᴿ idᴿ             ≡ x
    ＋wk   : x &ᴿ wk {s = s′}     ≡ suc x
    ext₀ᴿ  : zero &ᴿ (x ∙ᴿ ρ)     ≡ x
    extˢᴿ  : (suc x′) &ᴿ (x ∙ᴿ ρ) ≡ x′ &ᴿ ρ 

    ＋idˢ  : x &ˢ idˢ             ≡ ` x
    ext₀ˢ  : zero &ˢ (t ∙ˢ σ)     ≡ t
    extˢˢ  : (suc x) &ˢ (t ∙ˢ σ)  ≡ x &ˢ σ

    compᴿᴿ  : x &ᴿ (ρ₁ ;ᴿᴿ ρ₂)  ≡ (x &ᴿ ρ₁) &ᴿ ρ₂
    compᴿˢ  : x &ˢ (ρ₁ ;ᴿˢ σ₂)  ≡ (x &ᴿ ρ₁) &ˢ σ₂
    compˢᴿ  : x &ˢ (σ₁ ;ˢᴿ ρ₂)  ≡ (x &ˢ σ₁) ⋯ᴿ ρ₂
    compˢˢ  : x &ˢ (σ₁ ;ˢˢ σ₂)  ≡ (x &ˢ σ₁) ⋯ˢ σ₂
    --! }

    --! InteractLaws {
    -- Interaction Laws
    comp-idₗᴿᴿ  : idᴿ ;ᴿᴿ ρ  ≡ ρ;    comp-idₗᴿˢ  : idᴿ ;ᴿˢ σ  ≡ σ
    comp-idᴿᴿᴿ  : ρ ;ᴿᴿ idᴿ  ≡ ρ 
    comp-idᴿˢˢ  : σ ;ˢˢ idˢ  ≡ σ;    comp-idᴿˢᴿ  : σ ;ˢᴿ idᴿ  ≡ σ 
    comp-idₗˢˢ  : idˢ ;ˢˢ σ  ≡ σ

    associativityᴿᴿᴿ  : (ρ₁ ;ᴿᴿ ρ₂) ;ᴿᴿ ρ₃  ≡ ρ₁ ;ᴿᴿ (ρ₂ ;ᴿᴿ ρ₃)
    associativityᴿᴿˢ  : (ρ₁ ;ᴿᴿ ρ₂) ;ᴿˢ σ₃  ≡ ρ₁ ;ᴿˢ (ρ₂ ;ᴿˢ σ₃)
    associativityᴿˢᴿ  : (ρ₁ ;ᴿˢ σ₂) ;ˢᴿ ρ₃  ≡ ρ₁ ;ᴿˢ (σ₂ ;ˢᴿ ρ₃)
    associativityᴿˢˢ  : (ρ₁ ;ᴿˢ σ₂) ;ˢˢ σ₃  ≡ ρ₁ ;ᴿˢ (σ₂ ;ˢˢ σ₃)
    associativityˢᴿᴿ  : (σ₁ ;ˢᴿ ρ₂) ;ˢᴿ ρ₃  ≡ σ₁ ;ˢᴿ (ρ₂ ;ᴿᴿ ρ₃)
    associativityˢᴿˢ  : (σ₁ ;ˢᴿ ρ₂) ;ˢˢ σ₃  ≡ σ₁ ;ˢˢ (ρ₂ ;ᴿˢ σ₃)
    associativityˢˢᴿ  : (σ₁ ;ˢˢ σ₂) ;ˢᴿ ρ₃  ≡ σ₁ ;ˢˢ (σ₂ ;ˢᴿ ρ₃)
    associativityˢˢˢ  : (σ₁ ;ˢˢ σ₂) ;ˢˢ σ₃  ≡ σ₁ ;ˢˢ (σ₂ ;ˢˢ σ₃)

    distributivityᴿᴿ  : (x ∙ᴿ ρ₁) ;ᴿᴿ ρ₂  ≡ ((x &ᴿ ρ₂) ∙ᴿ (ρ₁ ;ᴿᴿ ρ₂))
    distributivityᴿˢ  : (x ∙ᴿ ρ₁) ;ᴿˢ σ₂  ≡ ((x &ˢ σ₂) ∙ˢ (ρ₁ ;ᴿˢ σ₂))
    distributivityˢᴿ  : (t ∙ˢ σ₁) ;ˢᴿ ρ₂  ≡ ((t ⋯ᴿ ρ₂) ∙ˢ (σ₁ ;ˢᴿ ρ₂))
    distributivityˢˢ  : (t ∙ˢ σ₁) ;ˢˢ σ₂  ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ;ˢˢ σ₂))

    interactᴿ : wk ;ᴿᴿ (x ∙ᴿ ρ) ≡ ρ;   interactˢ : wk ;ᴿˢ (t ∙ˢ σ) ≡ σ

    η-id    : zero {S = S} {s = s} ∙ᴿ wk  ≡ idᴿ
    η-lawᴿ  : (zero &ᴿ ρ) ∙ᴿ (wk ;ᴿᴿ ρ)   ≡ ρ
    η-lawˢ  : (zero &ˢ σ) ∙ˢ (wk ;ᴿˢ σ)   ≡ σ
  
    --! }
    η-idˢ  : (` (zero {S = S} {s = s})) ∙ˢ (wk ;ᴿˢ idˢ) ≡ idˢ

 
    right-idᴿ  : (t : S ⊢ s) → t ⋯ᴿ idᴿ  ≡ t
    right-idˢ  : (t : S ⊢ s) → t ⋯ˢ idˢ  ≡ t 
 
    compositionalityᴿᴿ  : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂  ≡ t ⋯ᴿ (ρ₁ ;ᴿᴿ ρ₂)
    compositionalityᴿˢ  : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (ρ₁ ;ᴿˢ σ₂)
    compositionalityˢᴿ  : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂  ≡ t ⋯ˢ (σ₁ ;ˢᴿ ρ₂)
    compositionalityˢˢ  : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (σ₁ ;ˢˢ σ₂)

    coincidence  : (t : S₁ ⊢ s) → t ⋯ˢ (ρ ;ᴿˢ idˢ)  ≡ t ⋯ᴿ ρ
    coincidence-fold  : (t : (s′ ∷ S₁) ⊢ s) → t ⋯ˢ ((` x) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ t ⋯ᴿ (x ∙ᴿ ρ)

    -- All proofs
    ＋idᴿ = refl 
    ＋wk = refl 
    ext₀ᴿ = refl
    extˢᴿ = refl
    ＋idˢ = refl
    ext₀ˢ = refl
    extˢˢ = refl

    compᴿᴿ = refl
    compᴿˢ = refl
    compˢᴿ = refl
    compˢˢ = refl

    interactᴿ = refl
    interactˢ = refl

    η-id = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    η-idˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    η-lawᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    η-lawˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))

    distributivityᴿᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    distributivityᴿˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    distributivityˢᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    distributivityˢˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))

    comp-idₗᴿᴿ = refl
    comp-idᴿᴿᴿ = refl
    comp-idₗᴿˢ = refl
    comp-idₗˢˢ = refl
    comp-idᴿˢᴿ {σ = σ} = fun-exti (fun-ext λ x → right-idᴿ (x &ˢ σ))
    comp-idᴿˢˢ {σ = σ} = fun-exti (fun-ext λ x → right-idˢ (x &ˢ σ))

    right-idᴿ (` x)        = refl
    right-idᴿ (λx e)       = cong λx_ (trans (cong (_⋯ᴿ_ {S₂ = expr ∷ _} e) η-id) (right-idᴿ e))
    right-idᴿ (Λα e)       = cong Λα_ (trans (cong (_⋯ᴿ_ {S₂ = type ∷ _} e) η-id) (right-idᴿ e))
    right-idᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idᴿ k) (trans (cong (_⋯ᴿ_ {S₂ = type ∷ _} t) η-id) (right-idᴿ t))
    right-idᴿ (e₁ · e₂)    = cong₂ _·_ (right-idᴿ e₁) (right-idᴿ e₂)
    right-idᴿ (e • t)      = cong₂ _•_ (right-idᴿ e) (right-idᴿ t)
    right-idᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idᴿ t₁) (right-idᴿ t₂)
    right-idᴿ ★            = refl

    right-idˢ (` x)        = refl
    right-idˢ (λx e)       = cong λx_ (trans (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) η-idˢ) (right-idˢ e))
    right-idˢ (Λα e)       = cong Λα_ (trans (cong (_⋯ˢ_ {S₂ = type ∷ _} e) η-idˢ) (right-idˢ e))
    right-idˢ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idˢ k) (trans (cong (_⋯ˢ_ {S₂ = type ∷ _} t) η-idˢ) (right-idˢ t))
    right-idˢ (e₁ · e₂)    = cong₂ _·_ (right-idˢ e₁) (right-idˢ e₂)
    right-idˢ (e • t)      = cong₂ _•_ (right-idˢ e) (right-idˢ t)
    right-idˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idˢ t₁) (right-idˢ t₂)
    right-idˢ ★            = refl

    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (` x)        = refl
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (λx e)       = cong λx_ (trans (compositionalityᴿᴿ {ρ₁ = (ρ₁ ↑ᴿ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} e) (cong (_⋯ᴿ_ {S₂ = expr ∷ _} e) (distributivityᴿᴿ {ρ₂ = (ρ₂ ↑ᴿ _) })))
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (Λα e)       = cong Λα_ (trans (compositionalityᴿᴿ {ρ₁ = (ρ₁ ↑ᴿ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} e) (cong (_⋯ᴿ_ {S₂ = type ∷ _} e) (distributivityᴿᴿ {ρ₂ = (ρ₂ ↑ᴿ _) })))
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿᴿ k) (trans (compositionalityᴿᴿ {ρ₁ = (ρ₁ ↑ᴿ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} t) (cong (_⋯ᴿ_ {S₂ = type ∷ _} t) (distributivityᴿᴿ {ρ₂ = (ρ₂ ↑ᴿ _) })))
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿᴿ e₁) (compositionalityᴿᴿ e₂)
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e • t)      = cong₂ _•_ (compositionalityᴿᴿ e) (compositionalityᴿᴿ t)
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿᴿ t₁) (compositionalityᴿᴿ t₂)
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} ★            = refl

    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (` x)        = refl
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compositionalityᴿˢ {ρ₁ = (ρ₁ ↑ᴿ _)} {σ₂ = (σ₂ ↑ˢ _)} e) (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) (distributivityᴿˢ {σ₂ = (σ₂ ↑ˢ _)})))
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityᴿˢ {ρ₁ = (ρ₁ ↑ᴿ _)} {σ₂ = (σ₂ ↑ˢ _)} e) (cong (_⋯ˢ_ {S₂ = type ∷ _} e) (distributivityᴿˢ {σ₂ = (σ₂ ↑ˢ _)})))
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿˢ k) (trans (compositionalityᴿˢ {ρ₁ = (ρ₁ ↑ᴿ _)} {σ₂ = (σ₂ ↑ˢ _)} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (distributivityᴿˢ {σ₂ = (σ₂ ↑ˢ _)})))
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿˢ e₁) (compositionalityᴿˢ e₂)
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (e • t)      = cong₂ _•_ (compositionalityᴿˢ e) (compositionalityᴿˢ t)
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿˢ t₁) (compositionalityᴿˢ t₂)
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} ★            = refl

    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (` x)        = refl
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (λx e)       = cong λx_ (trans (compositionalityˢᴿ {σ₁ = (σ₁ ↑ˢ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} e) (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿᴿ _) (sym (compositionalityᴿᴿ _)) }))))
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (Λα e)       = cong Λα_ (trans (compositionalityˢᴿ {σ₁ = (σ₁ ↑ˢ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} e) (cong (_⋯ˢ_ {S₂ = type ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿᴿ _) (sym (compositionalityᴿᴿ _)) }))))
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢᴿ k) (trans (compositionalityˢᴿ {σ₁ = (σ₁ ↑ˢ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿᴿ _) (sym (compositionalityᴿᴿ _)) })))) 
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityˢᴿ e₁) (compositionalityˢᴿ e₂)
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (e • t)      = cong₂ _•_ (compositionalityˢᴿ e) (compositionalityˢᴿ t)
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢᴿ t₁) (compositionalityˢᴿ t₂)
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} ★            = refl

    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (` x)        = refl
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compositionalityˢˢ {σ₁ = (σ₁ ↑ˢ _)} {σ₂ = (σ₂ ↑ˢ _)} e) (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿˢ (σ₁ x)) (sym (compositionalityˢᴿ (σ₁ x))) }))))
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityˢˢ {σ₁ = (σ₁ ↑ˢ _)} {σ₂ = (σ₂ ↑ˢ _)} e) (cong (_⋯ˢ_ {S₂ = type ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿˢ (σ₁ x)) (sym (compositionalityˢᴿ (σ₁ x))) }))))
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢˢ k) (trans (compositionalityˢˢ {σ₁ = (σ₁ ↑ˢ _)} {σ₂ = (σ₂ ↑ˢ _)} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿˢ (σ₁ x)) (sym (compositionalityˢᴿ (σ₁ x))) }))))
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityˢˢ e₁) (compositionalityˢˢ e₂)
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (e • t)      = cong₂ _•_ (compositionalityˢˢ e) (compositionalityˢˢ t)
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢˢ t₁) (compositionalityˢˢ t₂)
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} ★            = refl
    
    coincidence = {!   !} 
    coincidence-fold = {!   !} 

    associativityᴿᴿᴿ = refl
    associativityᴿᴿˢ = refl
    associativityᴿˢᴿ = refl
    associativityᴿˢˢ = refl 
    associativityˢᴿᴿ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityᴿᴿ (x &ˢ σ₁))
    associativityˢᴿˢ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityᴿˢ (x &ˢ σ₁))
    associativityˢˢᴿ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityˢᴿ (x &ˢ σ₁))
    associativityˢˢˢ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityˢˢ (x &ˢ σ₁))

  --! RewriteSys {
  {-# REWRITE 
    ＋idᴿ ＋wk ext₀ᴿ extˢᴿ
    ＋idˢ ext₀ˢ extˢˢ
    compᴿᴿ compᴿˢ compˢᴿ compˢˢ
    comp-idₗᴿᴿ comp-idₗᴿˢ comp-idᴿᴿᴿ 
    comp-idᴿˢˢ comp-idᴿˢᴿ comp-idₗˢˢ
    associativityᴿᴿᴿ associativityᴿᴿˢ 
    associativityᴿˢᴿ associativityᴿˢˢ
    associativityˢᴿᴿ associativityˢᴿˢ 
    associativityˢˢᴿ associativityˢˢˢ
    distributivityᴿᴿ distributivityᴿˢ 
    distributivityˢᴿ distributivityˢˢ
    interactᴿ interactˢ
    η-id η-lawᴿ η-lawˢ
    right-idᴿ right-idˢ
    compositionalityᴿᴿ compositionalityᴿˢ 
    compositionalityˢᴿ compositionalityˢˢ
    coincidence coincidence-fold
  #-}
    --! }

  -- Typing ----------------------------------------------------------------------

  ↑ᵗ_ : Sort → Sort 
  ↑ᵗ expr = type
  ↑ᵗ type = kind
  ↑ᵗ kind = kind

  _∶⊢_ : Scope → Sort → Set
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

  weaken : S ⊢ s → (s′ ∷ S) ⊢ s
  weaken t = t ⋯ᴿ wk

  _[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
  t [ t′ ] = t ⋯ˢ (t′ ∙ˢ idˢ) 

  wk-drop-∈ : (x : S ∋ s) → drop-∈ x S ⊢ s′ → S ⊢ s′
  wk-drop-∈ zero t = weaken t 
  wk-drop-∈ (suc x)  t = weaken (wk-drop-∈ x t) 

  wk-telescope : Ctx S → S ∋ s → S ∶⊢ s
  wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

  infix   4  _∋_∶_
  _∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
  Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

  variable 
    Γ Γ₁ Γ₂ Γ₃ Γ′ Γ₁′ Γ₂′ Γ₃′ : Ctx S

  data _⊢_∶_ : {s : Sort} → Ctx S → S ⊢ s → S ∶⊢ s → Set where
    ⊢` : ∀ {x : S ∋ s} {t} → 
      Γ ∋ x ∶ t →
      -------------
      Γ ⊢ (` x) ∶ t
    ⊢λ : 
      (t ∷ₜ Γ) ⊢ e ∶ (weaken t′) → 
      ------------------------
      Γ ⊢ (λx e) ∶ (t ⇒ t′)
    ⊢Λ : 
      (k ∷ₜ Γ) ⊢ e ∶ t →  
      -------------------------
      Γ ⊢ (Λα e) ∶ (∀[α∶ k ] t)
    ⊢· : 
      Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
      Γ ⊢ e₂ ∶ t₁ →
      --------------------
      Γ ⊢ (e₁ · e₂) ∶ t₂
    ⊢∙ : 
      Γ ⊢ e ∶ (∀[α∶ k ] t′) →
      Γ ⊢ t ∶ k →
      (k ∷ₜ Γ) ⊢ t′ ∶ k′ →
      ------------------------
      Γ ⊢ (e • t) ∶ (t′ [ t ])
    ⊢★ : {t : S ⊢ type} →
      ---------
      Γ ⊢ t ∶ ★

  _∶_→ᴿ_ : S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set
  _∶_→ᴿ_ {S₁} {S₂} ρ Γ₁ Γ₂ = ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) → (Γ₁ ∋ x ∶ t) → Γ₂ ∋ (x &ᴿ ρ) ∶ t ⋯ᴿ ρ 

  _∶_→ˢ_ : S₁ →ˢ S₂ → Ctx S₁ → Ctx S₂ → Set
  _∶_→ˢ_ {S₁} {S₂} σ Γ₁ Γ₂ = ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) → (Γ₁ ∋ x ∶ t) → Γ₂ ⊢ (x &ˢ σ) ∶ (t ⋯ˢ σ) 


  