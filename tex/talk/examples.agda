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
      botᵣ   : K ⊔ V           ≡ K               
      botₗ   : V ⊔ K           ≡ K               
      topᵣ   : K ⊔ T           ≡ T              
      topₗ   : T ⊔ K           ≡ T     
      idem   : K ⊔ K           ≡ K                        
      assoc  : (K₁ ⊔ K₂) ⊔ K₃  ≡ K₁ ⊔ (K₂ ⊔ K₃)  

    {-# REWRITE botᵣ botₗ topᵣ topₗ idem assoc #-}
    postulate
      --! DefLawTy
      imgⱽ : S ∋/⊢[ V ] s ≡ S ∋ s   
      imgᵀ : S ∋/⊢[ T ] s ≡ S ⊢ s 

    {-# REWRITE imgⱽ imgᵀ #-}
    module foo
       {{K₁ : Kit}} {{K₂ : Kit}} {{K₃ : Kit}} {{K₄ : Kit}} {{K₅ : Kit}}
       (ρ : S₁ –[ V ]→ S₂) (ρ₁ : S₁ –[ V ]→ S₂) (ρ₂ : S₂ –[ V ]→ S₃) (ρ₄ : S₃ –[ V ]→ S₄)
       (σ : S₁ –[ T ]→ S₂) (σ₁ : S₁ –[ T ]→ S₂) (σ₂ : S₂ –[ T ]→ S₃) (σ₄ : S₃ –[ T ]→ S₄)
      (ϕ : S₁ –[ K₁ ]→ S₂) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)  (ϕ₃ : S₃ –[ K₃ ]→ S₄) (ϕ₄ : S₃ –[ K₄ ]→ S₄)
      (x/t : S₂ ∋/⊢[ K₁ ] s)   (x/t₁ : S₂ ∋/⊢[ K₁ ] s) (t : S₂ ⊢ s) (t′ : S₂ ⊢ s′) (x : S₁ ∋ s) (x′ : S₁ ∋ s′) (ϕ′ : (s ∷ S₁) –[ K₂ ]→ S₂) 
      where 
 
      _&_ = _&/⋯[ V , T , T ]_
      postulate
        ＋idˢ   : x &/⋯[ V , T , T ] id[ T ]                 ≡ ` x
        ＋wk    : x &/⋯[ V , V , V ] wk                      ≡ suc x

        --! ExtLaws
        ext₀    : zero    & (x/t ∙[ K ] ϕ)     ≡ x/t
        extₛ    : suc x′  & (x/t ∙[ K ] ϕ)     ≡ x′ & ϕ

        comp    : x &/⋯[ V , V , V ] (ρ₁ ;[ V , V , V ] ρ₂)  ≡ 
                 (x &/⋯[ V , V , V ] ρ₁) &/⋯[ V , V , V ] ρ₂

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
        compₗ–ext₀  : zero &/⋯[ V , K₃ , K₃ ] 
                           ((x/t₁ ∙[ K₁ ] ϕ₁) ;[ K₁ , K₂ , K₃ ] ϕ₂)    ≡ 
                      x/t &/⋯[ K₁ , K₂ , K₃ ] ϕ₂
        compₗ–extₛ  : suc x′ &/⋯[ V , K₃ , K₃ ] 
                             ((x/t₁ ∙[ K₁ ] ϕ₁) ;[ K₁ , K₂ , K₃ ] ϕ₂)  ≡ 
                      x′ &/⋯[ V , K₃ , K₃ ] (ϕ₁ ;[ K₁ , K₂ , K₃ ] ϕ₂)
    
        --! Interaction
        comp-idₗ        : id[ K ] ;[ K , K , K ] ϕ                                  ≡  ϕ
        comp-idᵣ        : ϕ ;[ K , K , K ] id[ K ]                                  ≡ ϕ

        --! EAssoc
        associativity   : 
          (ϕ₁ ;[ K₁ , K₂ , (K₁ ⊔ K₂) ] ϕ₂) 
            ;[ (K₁ ⊔ K₂) , K₃ , ((K₁ ⊔ K₂) ⊔ K₃) ] ϕ₃  
              ≡  
            ϕ₁ ;[ K₁ , (K₂ ⊔ K₃) , ((K₁ ⊔ K₂) ⊔ K₃) ] 
          (ϕ₂ ;[ K₂ , K₃ , (K₂ ⊔ K₃) ] ϕ₃) 

        distributivity  : (x/t₁ ∙[ K₁ ] ϕ₁) ;[ K₁ , K₂ , K₃ ] ϕ₂                      ≡ 
                          (x/t₁ &/⋯[ K₁ , K₂ , K₃ ] ϕ₂) ∙[ K₃ ] (ϕ₁ ;[ K₁ , K₂ , K₃ ] ϕ₂)
        interact        : wk ;[ V , K , K ] (x/t ∙[ K ] ϕ)                            ≡ ϕ 
        η–id            : zero ∙[ V ] wk                                            ≡ id[ V ]
        η–law           : (zero &/⋯[ V , K , K ] ϕ′) ∙[ K ] (wk ;[ V , K , K ] ϕ′)  ≡ ϕ′

        --! Coincidence Laws
        coincidence       : t &/⋯[ T , T , T ] (ϕ ;[ K , T , T ] id[ T ])  ≡ 
                            t &/⋯[ T , K , T ] ϕ  
        coincidence–foldᴷ : t &/⋯[ T , T , T ]  ((x/t &/⋯[ K , T , T ] id[ T ]) ∙[ T ] 
                                                (ϕ ;[ K , T , T ] id[ T ]))             ≡ 
                            (t &/⋯[ T , K , T ] (x/t ∙[ K ] ϕ))
        coincidence–foldᵀ : t &/⋯[ T , T , T ]  ((t′ &/⋯[ T , K , T ] ϕ) ∙[ T ] 
                                                (ϕ ;[ K , T , T ] id[ T ]))             ≡ 
                            (t &/⋯[ T , T , T ] (t′ ∙[ T ] (id[ T ]))) &/⋯[ T , K , T ] ϕ

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
          

    
      record _d : Set₁ where
        field
          --! TravL
          var : (` x) &/⋯[  T , K , T ] ϕ ≡ 
                (x &/⋯[ V , K , K ] ϕ) &/⋯[ K , T , T ] id[ T ]


open import Data.List hiding ([_])
open import Data.Nat hiding (_⊔_)
open import Data.Fin using (Fin)
open import Data.String using (String)

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
record Default (A : Set) : Set where
  field default : A

--! DefFields
open Default {{...}}

--! DefInst
instance 
  default–ℕ : Default ℕ
  default–ℕ .default = 0 

--! DefInstS
instance 
  default–String : Default String
  default–String .default = ""
--! DefEx
_ : default ≡ 0
_ = refl

--! DefExS
_ : default ≡ ""
_ = refl


--! Opaque
opaque
  forty–two : ℕ
  forty–two = 42
  
--! OpaqueExO 
_ : forty–two ≡ 42
_ = {!   !} -- not provable.

--! OpaqueExT {
opaque   
  unfolding forty–two

  _ : forty–two ≡ 42
  _ = refl
--! }

module XX where 

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
    Ξ_      : (expr ∷ S) ⊢ expr → S ⊢ expr
    _·_      : S ⊢ expr → S ⊢ expr → S ⊢ expr

  variable
    e e₁ e₂ e′ : S ⊢ expr
    k k′ : S ⊢ kind
    x x′ : S ∋ s
    t t₁ t₂ t′ : S ⊢ s

  
  _→ˢ_ : Scope → Scope → Set
  S₁ →ˢ S₂ = ∀ {s} → S₁ ∋ s → S₂ ⊢ s

  _&_ : S₁ ∋ s → (S₁ →ˢ S₂) → S₂ ⊢ s

  --! XLookUp
  x & σ = σ x

  id : S →ˢ S

  --! XId
  id x = ` x

  wk : S →ˢ (s ∷ S)

  --! XWk
  wk x = ` suc x

  _∙_ : S₂ ⊢ s → (S₁ →ˢ S₂) → ((s ∷ S₁) →ˢ S₂)

  --! XExt
  (t ∙ σ)  zero     = t
  (t ∙ σ)  (suc x)  = x & σ

  _⋯_ : S₁ ⊢ s → (S₁ →ˢ S₂) → S₂ ⊢ s
  _;_ :  (S₁ →ˢ S₂) → (S₂ →ˢ S₃) → (S₁ →ˢ S₃)
  _↑ : (S₁ →ˢ S₂) → ∀ {s} → ((s ∷ S₁) →ˢ (s ∷ S₂))

  --! SRFail {
  (σ₁ ; σ₂) x = (x & σ₁) ⋯ σ₂

  σ ↑ = (` zero) ∙ (σ ; wk)

  (` x)         ⋯ σ = (x & σ)
  (Ξ e)         ⋯ σ = Ξ (e ⋯ (σ ↑))
  (e₁ · e₂)     ⋯ σ = (e₁ ⋯ σ) · (e₂ ⋯ σ)
  --! }
 

--! Scoped {
data Kind : Set where
  ★  : Kind

data Type (n : ℕ) : Set where
  `_       : Fin n → Type n 
  ∀[α:_]_  : Type (suc n) → Type n
  _⇒_      : Type n → Type n → Type n

data Expr (n m : ℕ) : Set where
  `_   : Fin m → Expr n m
  Ξ_  : Expr n (suc m) → Expr n m
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
  Ξ_      : (expr ∷ S) ⊢ expr → S ⊢ expr
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


opaque
  _→ᴿ_ : Scope → Scope → Set
  S₁ →ᴿ S₂ = ∀ {s} → S₁ ∋ s → S₂ ∋ s 

  _&ᴿ_ : S₁ ∋ s → (S₁ →ᴿ S₂) → S₂ ∋ s

  --! YRLookUp
  x &ᴿ ρ = ρ x
  
  idᴿ : S →ᴿ S 

  --! YRId
  idᴿ x = x 

  wk : S →ᴿ (s ∷ S)

  --! YRWk
  wk x = suc x

  _∙ᴿ_ : S₂ ∋ s → (S₁ →ᴿ S₂) → ((s ∷ S₁) →ᴿ S₂)

  --! YRExt
  (x ∙ᴿ _) zero     = x
  (_ ∙ᴿ ρ) (suc x)  = ρ x

  _;ᴿᴿ_ : (S₁ →ᴿ S₂) → (S₂ →ᴿ S₃) → (S₁ →ᴿ S₃)

  --! YRCompR
  (ρ₁ ;ᴿᴿ ρ₂) x = ρ₂ (ρ₁ x)

-- opaque end

_↑ᴿ : (S₁ →ᴿ S₂) → ∀ {s} → ((s ∷ S₁) →ᴿ (s ∷ S₂))

--! YRLift
ρ ↑ᴿ = zero ∙ᴿ (ρ ;ᴿᴿ wk)

_⋯ᴿ_ : S₁ ⊢ s → (S₁ →ᴿ S₂) → S₂ ⊢ s
-- Traversal Laws

--! YRTrav
(` x)         ⋯ᴿ ρ = ` (x &ᴿ ρ)
(Ξ e)         ⋯ᴿ ρ = Ξ (e ⋯ᴿ (ρ ↑ᴿ))
(e₁ · e₂)     ⋯ᴿ ρ = (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)

(Λα e)        ⋯ᴿ ρ = Λα (e ⋯ᴿ (ρ ↑ᴿ))
(∀[α∶ k ] t)  ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] (t ⋯ᴿ (ρ ↑ᴿ))
(e • t)       ⋯ᴿ ρ = (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
(t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
★             ⋯ᴿ ρ = ★ 


opaque 
  unfolding 
    _→ᴿ_ _&ᴿ_ idᴿ wk _∙ᴿ_ _;ᴿᴿ_

  _→ˢ_ : Scope → Scope → Set
  S₁ →ˢ S₂ = ∀ {s} → S₁ ∋ s → S₂ ⊢ s

  _&ˢ_ : S₁ ∋ s → (S₁ →ˢ S₂) → S₂ ⊢ s

  --! YSLookUp
  x &ˢ σ = σ x

  idˢ : S →ˢ S
  --! YSId
  idˢ = λ x → ` x

  _∙ˢ_ : S₂ ⊢ s → (S₁ →ˢ S₂) → ((s ∷ S₁) →ˢ S₂)

  --! YSExt
  (t ∙ˢ _)  zero     = t
  (_ ∙ˢ σ)  (suc x)  = σ x
  
  _;ᴿˢ_ : (S₁ →ᴿ S₂) → (S₂ →ˢ S₃) → (S₁ →ˢ S₃)

  --! YRCompS
  (ρ₁ ;ᴿˢ σ₂) x = σ₂ (ρ₁ x)

  _;ˢᴿ_ : (S₁ →ˢ S₂) → (S₂ →ᴿ S₃) → (S₁ →ˢ S₃)

  --! YSCompR
  (σ₁ ;ˢᴿ ρ₂) x = (σ₁ x) ⋯ᴿ ρ₂

-- opaque end  

_↑ˢ : (S₁ →ˢ S₂) → ∀ {s} → ((s ∷ S₁) →ˢ (s ∷ S₂))

--! YSLift
σ ↑ˢ = (` zero) ∙ˢ (σ ;ˢᴿ wk)

_⋯ˢ_ : S₁ ⊢ s → (S₁ →ˢ S₂) → S₂ ⊢ s
-- Traversal Laws
--! YSTrav
(` x)         ⋯ˢ σ = (x &ˢ σ)
(Ξ e)         ⋯ˢ σ = Ξ (e ⋯ˢ (σ ↑ˢ))
(e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)

(Λα e)        ⋯ˢ σ = Λα (e ⋯ˢ (σ ↑ˢ))
(∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ))
(e • t)       ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
(t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
★             ⋯ˢ σ = ★

opaque
  unfolding 
    _→ᴿ_ _&ᴿ_ idᴿ wk _∙ᴿ_ _;ᴿᴿ_ 
    _→ˢ_ _&ˢ_ idˢ _∙ˢ_ _;ᴿˢ_ _;ˢᴿ_

  _;ˢˢ_ :  (S₁ →ˢ S₂) → (S₂ →ˢ S₃) → (S₁ →ˢ S₃)

  --! YSCompS
  (σ₁ ;ˢˢ σ₂) x = (σ₁ x) ⋯ˢ σ₂

variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂ 
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂ 

module _B where
  record _d : Set where
    field

      -- Monad Laws
      ＋right-idᴿ  : t ⋯ᴿ idᴿ  ≡ t
      ＋right-idˢ  : t ⋯ˢ idˢ  ≡ t
      
      --! MonadComp
      ＋compositionalityᴿᴿ  : (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂  ≡ t ⋯ᴿ (ρ₁ ;ᴿᴿ ρ₂)
      ＋compositionalityᴿˢ  : (t ⋯ᴿ ρ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (ρ₁ ;ᴿˢ σ₂)
      ＋compositionalityˢᴿ  : (t ⋯ˢ σ₁) ⋯ᴿ ρ₂  ≡ t ⋯ˢ (σ₁ ;ˢᴿ ρ₂)
      ＋compositionalityˢˢ  : (t ⋯ˢ σ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (σ₁ ;ˢˢ σ₂)

  opaque 
    unfolding _→ᴿ_ _&ᴿ_ idᴿ wk _∙ᴿ_ _;ᴿᴿ_ _→ˢ_ _&ˢ_ idˢ _∙ˢ_ _;ᴿˢ_ _;ˢᴿ_ _;ˢˢ_


    -- Definitional Laws 
    ＋idᴿ  : x &ᴿ idᴿ             ≡ x
    ＋wk   : x &ᴿ wk {s = s′}     ≡ suc x
    --! DefLaws {
    ext₀ᴿ  : zero &ᴿ (x ∙ᴿ ρ)     ≡ x
    extₛᴿ  : (suc x′) &ᴿ (x ∙ᴿ ρ) ≡ x′ &ᴿ ρ 

    ext₀ˢ  : zero &ˢ (t ∙ˢ σ)     ≡ t
    extₛˢ  : (suc x) &ˢ (t ∙ˢ σ)  ≡ x &ˢ σ
    --! }
    ＋idˢ  : x &ˢ idˢ             ≡ ` x

    compᴿᴿ  : x &ᴿ (ρ₁ ;ᴿᴿ ρ₂)  ≡ (x &ᴿ ρ₁) &ᴿ ρ₂
    compᴿˢ  : x &ˢ (ρ₁ ;ᴿˢ σ₂)  ≡ (x &ᴿ ρ₁) &ˢ σ₂
    compˢᴿ  : x &ˢ (σ₁ ;ˢᴿ ρ₂)  ≡ (x &ˢ σ₁) ⋯ᴿ ρ₂
    compˢˢ  : x &ˢ (σ₁ ;ˢˢ σ₂)  ≡ (x &ˢ σ₁) ⋯ˢ σ₂

    -- Interaction Laws
    comp-idₗᴿᴿ  : idᴿ ;ᴿᴿ ρ  ≡ ρ;    comp-idₗᴿˢ  : idᴿ ;ᴿˢ σ  ≡ σ
    comp-idᵣᴿᴿ  : ρ ;ᴿᴿ idᴿ  ≡ ρ 
    comp-idᵣˢˢ  : σ ;ˢˢ idˢ  ≡ σ;    comp-idᵣˢᴿ  : σ ;ˢᴿ idᴿ  ≡ σ 
    comp-idₗˢˢ  : idˢ ;ˢˢ σ  ≡ σ
    
    --! Assoc
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

    -- Coincidence Laws
    --! CoincidenceLaw
    coincidence        : t ⋯ˢ (ρ ;ᴿˢ idˢ)  ≡ t ⋯ᴿ ρ

    coincidence-foldⱽ  : (ρ : S₁ →ᴿ S₂) (t : (s′ ∷ S₁) ⊢ s) → t ⋯ˢ ((` x) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ t ⋯ᴿ (x ∙ᴿ ρ)
    coincidence-foldᵀ  : (ρ : S₁ →ᴿ S₂) (t′ : S₁ ⊢ s′) (t : (s′ ∷ S₁) ⊢ s) → t ⋯ˢ ((t′ ⋯ᴿ ρ) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ (t ⋯ˢ (t′ ∙ˢ idˢ)) ⋯ᴿ ρ

    η-idˢ  : (` (zero {S = S} {s = s})) ∙ˢ (wk ;ᴿˢ idˢ) ≡ idˢ

 
    right-idᴿ  : (t : S ⊢ s) → t ⋯ᴿ idᴿ  ≡ t
    right-idˢ  : (t : S ⊢ s) → t ⋯ˢ idˢ  ≡ t 
 
    compositionalityᴿᴿ  : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂  ≡ t ⋯ᴿ (ρ₁ ;ᴿᴿ ρ₂)
    compositionalityᴿˢ  : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (ρ₁ ;ᴿˢ σ₂)
    compositionalityˢᴿ  : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂  ≡ t ⋯ˢ (σ₁ ;ˢᴿ ρ₂)
    compositionalityˢˢ  : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (σ₁ ;ˢˢ σ₂)
    
    -- All proofs
    ＋idᴿ = refl 
    ＋wk = refl 
    ext₀ᴿ = refl
    extₛᴿ = refl
    ＋idˢ = refl
    ext₀ˢ = refl
    extₛˢ = refl

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
    comp-idᵣᴿᴿ = refl
    comp-idₗᴿˢ = refl
    comp-idₗˢˢ = refl
    comp-idᵣˢᴿ {σ = σ} = fun-exti (fun-ext λ x → right-idᴿ (x &ˢ σ))
    comp-idᵣˢˢ {σ = σ} = fun-exti (fun-ext λ x → right-idˢ (x &ˢ σ))

    right-idᴿ (` x)        = refl
    right-idᴿ (Ξ e)       = cong Ξ_ (trans (cong (_⋯ᴿ_ {S₂ = expr ∷ _} e) η-id) (right-idᴿ e))
    right-idᴿ (Λα e)       = cong Λα_ (trans (cong (_⋯ᴿ_ {S₂ = type ∷ _} e) η-id) (right-idᴿ e))
    right-idᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idᴿ k) (trans (cong (_⋯ᴿ_ {S₂ = type ∷ _} t) η-id) (right-idᴿ t))
    right-idᴿ (e₁ · e₂)    = cong₂ _·_ (right-idᴿ e₁) (right-idᴿ e₂)
    right-idᴿ (e • t)      = cong₂ _•_ (right-idᴿ e) (right-idᴿ t)
    right-idᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idᴿ t₁) (right-idᴿ t₂)
    right-idᴿ ★            = refl

    right-idˢ (` x)        = refl
    right-idˢ (Ξ e)       = cong Ξ_ (trans (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) η-idˢ) (right-idˢ e))
    right-idˢ (Λα e)       = cong Λα_ (trans (cong (_⋯ˢ_ {S₂ = type ∷ _} e) η-idˢ) (right-idˢ e))
    right-idˢ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idˢ k) (trans (cong (_⋯ˢ_ {S₂ = type ∷ _} t) η-idˢ) (right-idˢ t))
    right-idˢ (e₁ · e₂)    = cong₂ _·_ (right-idˢ e₁) (right-idˢ e₂)
    right-idˢ (e • t)      = cong₂ _•_ (right-idˢ e) (right-idˢ t)
    right-idˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idˢ t₁) (right-idˢ t₂)
    right-idˢ ★            = refl

    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (` x)        = refl
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (Ξ e)       = cong Ξ_ (trans (compositionalityᴿᴿ {ρ₁ = (ρ₁ ↑ᴿ)} {ρ₂ = (ρ₂ ↑ᴿ)} e) (cong (_⋯ᴿ_ {S₂ = expr ∷ _} e) (distributivityᴿᴿ {ρ₂ = (ρ₂ ↑ᴿ) })))
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (Λα e)       = cong Λα_ (trans (compositionalityᴿᴿ {ρ₁ = (ρ₁ ↑ᴿ)} {ρ₂ = (ρ₂ ↑ᴿ)} e) (cong (_⋯ᴿ_ {S₂ = type ∷ _} e) (distributivityᴿᴿ {ρ₂ = (ρ₂ ↑ᴿ) })))
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿᴿ k) (trans (compositionalityᴿᴿ {ρ₁ = (ρ₁ ↑ᴿ)} {ρ₂ = (ρ₂ ↑ᴿ)} t) (cong (_⋯ᴿ_ {S₂ = type ∷ _} t) (distributivityᴿᴿ {ρ₂ = (ρ₂ ↑ᴿ) })))
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿᴿ e₁) (compositionalityᴿᴿ e₂)
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e • t)      = cong₂ _•_ (compositionalityᴿᴿ e) (compositionalityᴿᴿ t)
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿᴿ t₁) (compositionalityᴿᴿ t₂)
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} ★            = refl

    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (` x)        = refl
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (Ξ e)       = cong Ξ_ (trans (compositionalityᴿˢ {ρ₁ = (ρ₁ ↑ᴿ)} {σ₂ = (σ₂ ↑ˢ )} e) (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) (distributivityᴿˢ {σ₂ = (σ₂ ↑ˢ )})))
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityᴿˢ {ρ₁ = (ρ₁ ↑ᴿ)} {σ₂ = (σ₂ ↑ˢ )} e) (cong (_⋯ˢ_ {S₂ = type ∷ _} e) (distributivityᴿˢ {σ₂ = (σ₂ ↑ˢ )})))
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿˢ k) (trans (compositionalityᴿˢ {ρ₁ = (ρ₁ ↑ᴿ)} {σ₂ = (σ₂ ↑ˢ )} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (distributivityᴿˢ {σ₂ = (σ₂ ↑ˢ )})))
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿˢ e₁) (compositionalityᴿˢ e₂)
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (e • t)      = cong₂ _•_ (compositionalityᴿˢ e) (compositionalityᴿˢ t)
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿˢ t₁) (compositionalityᴿˢ t₂)
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} ★            = refl

    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (` x)        = refl
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (Ξ e)       = cong Ξ_ (trans (compositionalityˢᴿ {σ₁ = (σ₁ ↑ˢ )} {ρ₂ = (ρ₂ ↑ᴿ)} e) (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿᴿ _) (sym (compositionalityᴿᴿ _)) }))))
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (Λα e)       = cong Λα_ (trans (compositionalityˢᴿ {σ₁ = (σ₁ ↑ˢ )} {ρ₂ = (ρ₂ ↑ᴿ)} e) (cong (_⋯ˢ_ {S₂ = type ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿᴿ _) (sym (compositionalityᴿᴿ _)) }))))
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢᴿ k) (trans (compositionalityˢᴿ {σ₁ = (σ₁ ↑ˢ )} {ρ₂ = (ρ₂ ↑ᴿ)} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿᴿ _) (sym (compositionalityᴿᴿ _)) })))) 
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityˢᴿ e₁) (compositionalityˢᴿ e₂)
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (e • t)      = cong₂ _•_ (compositionalityˢᴿ e) (compositionalityˢᴿ t)
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢᴿ t₁) (compositionalityˢᴿ t₂)
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} ★            = refl

    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (` x)        = refl
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Ξ e)       = cong Ξ_ (trans (compositionalityˢˢ {σ₁ = (σ₁ ↑ˢ )} {σ₂ = (σ₂ ↑ˢ )} e) (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿˢ (σ₁ x)) (sym (compositionalityˢᴿ (σ₁ x))) }))))
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityˢˢ {σ₁ = (σ₁ ↑ˢ )} {σ₂ = (σ₂ ↑ˢ )} e) (cong (_⋯ˢ_ {S₂ = type ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿˢ (σ₁ x)) (sym (compositionalityˢᴿ (σ₁ x))) }))))
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢˢ k) (trans (compositionalityˢˢ {σ₁ = (σ₁ ↑ˢ )} {σ₂ = (σ₂ ↑ˢ )} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿˢ (σ₁ x)) (sym (compositionalityˢᴿ (σ₁ x))) }))))
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityˢˢ e₁) (compositionalityˢˢ e₂)
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (e • t)      = cong₂ _•_ (compositionalityˢˢ e) (compositionalityˢˢ t)
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢˢ t₁) (compositionalityˢˢ t₂)
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} ★            = refl
    
    associativityᴿᴿᴿ = refl
    associativityᴿᴿˢ = refl
    associativityᴿˢᴿ = refl
    associativityᴿˢˢ = refl 
    associativityˢᴿᴿ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityᴿᴿ (x &ˢ σ₁))
    associativityˢᴿˢ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityᴿˢ (x &ˢ σ₁))
    associativityˢˢᴿ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityˢᴿ (x &ˢ σ₁))
    associativityˢˢˢ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityˢˢ (x &ˢ σ₁))

    -- Coincidence Laws
    coincidence {t = t} {ρ = ρ} = (t ⋯ˢ (ρ ;ᴿˢ idˢ)) ≡⟨ sym (compositionalityᴿˢ t) ⟩ ((t ⋯ᴿ ρ) ⋯ˢ idˢ) ≡⟨ right-idˢ (t  ⋯ᴿ ρ) ⟩ (t ⋯ᴿ ρ) ∎

    coincidence-foldⱽ {x = x} ρ t = 
      (t ⋯ˢ ((` _) ∙ˢ (ρ ;ᴿˢ idˢ))) ≡⟨ cong (_⋯ˢ_ t) (sym (distributivityᴿˢ {ρ₁ = ρ} {σ₂ = idˢ})) ⟩ 
      (t ⋯ˢ ((x ∙ᴿ ρ) ;ᴿˢ idˢ))     ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
      (t ⋯ˢ idˢ) ⋯ᴿ (x ∙ᴿ ρ)        ≡⟨ cong (_⋯ᴿ (x ∙ᴿ ρ)) (right-idˢ _) ⟩  
      (t ⋯ᴿ (_ ∙ᴿ ρ))               ∎

    
    
    swap-id : (ρ : S₁ →ᴿ S₂) → ρ ;ᴿˢ idˢ ≡ idˢ ;ˢᴿ ρ 
    swap-id _ = refl

    coincidence-foldᵀ ρ t′ t rewrite swap-id ρ = 
      (t ⋯ˢ ((t′ ⋯ᴿ ρ) ∙ˢ (λ x → ` ρ x))) ≡⟨ cong (_⋯ˢ_ t) (sym (distributivityˢᴿ {σ₁ = idˢ} {ρ₂ = ρ})) ⟩ 
      (t ⋯ˢ ((t′ ∙ˢ idˢ) ;ˢᴿ ρ))     ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
      ((t ⋯ˢ (t′ ∙ˢ idˢ)) ⋯ᴿ ρ)      ∎
  --! RewriteSys {
  {-# REWRITE 
    ＋idᴿ ＋wk ext₀ᴿ extₛᴿ
    ＋idˢ ext₀ˢ extₛˢ
    compᴿᴿ compᴿˢ compˢᴿ compˢˢ

    comp-idₗᴿᴿ comp-idₗᴿˢ comp-idᵣᴿᴿ 
    comp-idᵣˢˢ comp-idᵣˢᴿ comp-idₗˢˢ
    associativityᴿᴿᴿ associativityᴿᴿˢ 
    associativityᴿˢᴿ associativityᴿˢˢ
    associativityˢᴿᴿ associativityˢᴿˢ 
    associativityˢˢᴿ associativityˢˢˢ
    distributivityᴿᴿ distributivityᴿˢ 
    distributivityˢᴿ distributivityˢˢ
    interactᴿ interactˢ
    η-id η-lawᴿ η-lawˢ

    coincidence 
    coincidence-foldⱽ coincidence-foldᵀ

    right-idᴿ right-idˢ
    compositionalityᴿᴿ compositionalityᴿˢ 
    compositionalityˢᴿ compositionalityˢˢ
    
  #-}
  --! }