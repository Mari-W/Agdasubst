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

  
    postulate
      --!! KitDefTy
      Kit : Set 
      --! KitDef
      𝓡   : Kit 
      𝓢   : Kit 
      _⊔_  : Kit → Kit → Kit 

    variable
      𝓚 𝓚₁ 𝓚₂ 𝓚₃ : Kit

    postulate
      --!! VarTrmTy
      _∋/⊢[_]_ : Scope → Kit → Sort → Set

      --!! PrimsTy
      _–[_]→_  : Scope → Kit → Scope → Set
      --! Prims
      id   : S –[ 𝓚 ]→ S
      wk  : S –[ 𝓡 ]→ (s ∷ S)
      _∙_  : S₂ ∋/⊢[ 𝓚 ] s → S₁ –[ 𝓚 ]→ S₂ → (s ∷ S₁) –[ 𝓚 ]→ S₂
      _;_  : S₁ –[ 𝓚₁ ]→ S₂ → S₂ –[ 𝓚₂ ]→ S₃ → S₁ –[ 𝓚₃ ]→ S₃ 

      --! VarTrmApp
      _&/⋯_ : S₁ ∋/⊢[ 𝓚₁ ] s → S₁ –[ 𝓚₂ ]→ S₂ → S₂ ∋/⊢[ 𝓚₃ ] s

      _;[_,_,_]_   : S₁ –[ 𝓚₁ ]→ S₂ → Kit → Kit → Kit → S₂ –[ 𝓚₂ ]→ S₃ → S₁ –[ 𝓚₃ ]→ S₃
      _&/⋯[_,_,_]_ : S₁ ∋/⊢[ 𝓚₁ ] s → Kit → Kit → Kit → S₁ –[ 𝓚₂ ]→ S₂ → S₂ ∋/⊢[ 𝓚₃ ] s
      id[_]   : Kit → S –[ 𝓚 ]→ S
      _∙[_]_  : S₂ ∋/⊢[ 𝓚 ] s → Kit → S₁ –[ 𝓚 ]→ S₂ → (s ∷ S₁) –[ 𝓚 ]→ S₂
    
      --! TypeLevel   
      botᵣ   : 𝓚 ⊔ 𝓡           ≡ 𝓚               
      botₗ   : 𝓡 ⊔ 𝓚           ≡ 𝓚               
      topᵣ   : 𝓚 ⊔ 𝓢           ≡ 𝓢              
      topₗ   : 𝓢 ⊔ 𝓚           ≡ 𝓢     
      idem   : 𝓚 ⊔ 𝓚           ≡ 𝓚                        
      assoc  : (𝓚₁ ⊔ 𝓚₂) ⊔ 𝓚₃  ≡ 𝓚₁ ⊔ (𝓚₂ ⊔ 𝓚₃)  

    {-# REWRITE botᵣ botₗ topᵣ topₗ idem assoc #-}
    postulate
      --! DefLawTy
      imgˢ : S ∋/⊢[ 𝓡 ] s ≡ S ∋ s   
      imgᴿ : S ∋/⊢[ 𝓢 ] s ≡ S ⊢ s 

    {-# REWRITE imgˢ imgᴿ #-}
    module foo
       {{𝓚₁ : Kit}} {{𝓚₂ : Kit}} {{𝓚₃ : Kit}} {{𝓚₄ : Kit}} {{𝓚₅ : Kit}}
       (ρ : S₁ –[ 𝓡 ]→ S₂) (ρ₁ : S₁ –[ 𝓡 ]→ S₂) (ρ₂ : S₂ –[ 𝓡 ]→ S₃) (ρ₄ : S₃ –[ 𝓡 ]→ S₄)
       (σ : S₁ –[ 𝓢 ]→ S₂) (σ ₁ : S₁ –[ 𝓢 ]→ S₂) (σ ₂ : S₂ –[ 𝓢 ]→ S₃) (σ₄ : S₃ –[ 𝓢 ]→ S₄)
      (ϕ : S₁ –[ 𝓚₁ ]→ S₂) (ϕ₁ : S₁ –[ 𝓚₁ ]→ S₂) (ϕ₂ : S₂ –[ 𝓚₂ ]→ S₃) (ϕ₄ : S₃ –[ 𝓚₄ ]→ S₄)
      (x/t : S₂ ∋/⊢[ 𝓚₁ ] s)   (x/t₁ : S₂ ∋/⊢[ 𝓚₁ ] s) (t : S₂ ⊢ s) (x : S₁ ∋ s) (x′ : S₁ ∋ s′) (ϕ′ : (s ∷ S₁) –[ 𝓚₂ ]→ S₂) 
      where 

      postulate
        --! DefLaw
        ＋idˢ  : x &/⋯[ 𝓡 , 𝓢 , 𝓢 ] id[ 𝓢 ]                ≡ ` x
        ＋wk   : x &/⋯[ 𝓡 , 𝓡 , 𝓡 ] wk                     ≡ suc x
        ext₀   : zero &/⋯[ 𝓡 , 𝓚 , 𝓚 ] (x/t ∙[ 𝓚 ] ϕ)        ≡ x/t
        extₛ   : suc x′ &/⋯[ 𝓡 , 𝓚 , 𝓚 ] (x/t ∙[ 𝓚 ] ϕ)      ≡ 
                 x′ &/⋯[ 𝓡 , 𝓚 , 𝓚 ] ϕ
        comp   : x &/⋯[ 𝓡 , 𝓡 , 𝓡 ] (ρ₁ ;[ 𝓡 , 𝓡 , 𝓡 ] ρ₂) ≡ 
                 (x &/⋯[ 𝓡 , 𝓡 , 𝓡 ] ρ₁) &/⋯[ 𝓡 , 𝓡 , 𝓡 ] ρ₂
        compₗ–idˢ     : x &/⋯[ 𝓡 , 𝓢 , 𝓢 ]  (id[ 𝓢 ] ;[ 𝓢 , 𝓚 , 𝓢 ] ϕ₂)  ≡ 
                        (` x) &/⋯[ 𝓢 , 𝓚 , 𝓢 ] ϕ₂  
        compₗ–wk      : x &/⋯[ 𝓡 , 𝓚 , 𝓚 ] (wk ;[ 𝓡 , 𝓚 , 𝓚 ] ϕ′)        ≡ 
                        suc x &/⋯[ 𝓡 , 𝓚 , 𝓚 ] ϕ′ 
        compₗ–ext₀    : zero &/⋯[ 𝓡 , 𝓚₃ , 𝓚₃ ] ((x/t₁ ∙[ 𝓚₁ ] ϕ₁) ;[ 𝓚₁ , 𝓚₂ , 𝓚₃ ] ϕ₂)    ≡ 
                        x/t &/⋯[ 𝓚₁ , 𝓚₂ , 𝓚₃ ] ϕ₂
        compₗ–extₛ    : suc x′ &/⋯[ 𝓡 , 𝓚₃ , 𝓚₃ ] ((x/t₁ ∙[ 𝓚₁ ] ϕ₁) ;[ 𝓚₁ , 𝓚₂ , 𝓚₃ ] ϕ₂)  ≡ 
                        x′ &/⋯[ 𝓡 , 𝓚₃ , 𝓚₃ ] (ϕ₁ ;[ 𝓚₁ , 𝓚₂ , 𝓚₃ ] ϕ₂)
        coincidenceₓ  : x &/⋯[ 𝓡 , 𝓢 , 𝓢 ] (ρ ;[ 𝓡 , 𝓢 , 𝓢 ] id[ 𝓢 ])                     ≡ 
                        ` (x &/⋯[ 𝓡 , 𝓡 , 𝓡 ] ρ)
        --! Interaction
        comp-idₗ        : id[ 𝓚 ] ;[ 𝓚 , 𝓚 , 𝓚 ] ϕ                                  ≡  ϕ
        comp-idᴿ        : ϕ ;[ 𝓚 , 𝓚 , 𝓚 ] id[ 𝓚 ]                                  ≡ ϕ
        norm-idˢ        : id[ 𝓢 ] ;[ 𝓢 , 𝓚 , 𝓢 ] ϕ                                  ≡  
                          ϕ ;[ 𝓚 , 𝓢 , 𝓢 ] id[ 𝓢 ]
        associativity   : (ϕ₁ ;[ 𝓚₁ , 𝓚₂ , 𝓚₃ ] ϕ₂) ;[ 𝓚₃ , 𝓚₄ , 𝓚₅ ] ϕ₄            ≡ 
                          ϕ₁ ;[ 𝓚₁ , (𝓚₂ ⊔ 𝓚₄) , 𝓚₅ ] (ϕ₂ ;[ 𝓚₂ , 𝓚₄ , (𝓚₂ ⊔ 𝓚₄) ] ϕ₄) 
        distributivity  : (x/t₁ ∙[ 𝓚₁ ] ϕ₁) ;[ 𝓚₁ , 𝓚₂ , 𝓚₃ ] ϕ₂                      ≡ 
                          (x/t₁ &/⋯[ 𝓚₁ , 𝓚₂ , 𝓚₃ ] ϕ₂) ∙[ 𝓚₃ ] (ϕ₁ ;[ 𝓚₁ , 𝓚₂ , 𝓚₃ ] ϕ₂)
        interact        : wk ;[ 𝓡 , 𝓚 , 𝓚 ] (x/t ∙[ 𝓚 ] ϕ)                            ≡ ϕ 
        η–id            : zero ∙[ 𝓡 ] wk                                            ≡ id[ 𝓡 ]
        η–law           : (zero &/⋯[ 𝓡 , 𝓚 , 𝓚 ] ϕ′) ∙[ 𝓚 ] (wk ;[ 𝓡 , 𝓚 , 𝓚 ] ϕ′)  ≡ ϕ′

      record _c : Set₁ where
        field
          --! Monad
          compositionality  : (x/t₁ &/⋯[ 𝓚₁ , 𝓚₂ , 𝓚₃ ] ϕ₁) ;[ 𝓚₃ , 𝓚₄ , 𝓢 ] ϕ₄  ≡ 
                              x/t₁ &/⋯[ 𝓚₁ , 𝓚₂ ⊔ 𝓚₄ , 𝓢 ] (ϕ₁ ;[ 𝓚₂ , 𝓚₄ , (𝓚₂ ⊔ 𝓚₄) ] ϕ₂)
          right-id          : x/t₁ &/⋯[ 𝓚₁ , 𝓚₂ , 𝓚₁ ] id[ 𝓚₂ ] ≡ x/t₁
          coincidenceₜ      : t &/⋯[ 𝓢 , 𝓢 , 𝓢 ] (ρ ;[ 𝓡 , 𝓢 , 𝓢 ] id[ 𝓢 ])  ≡ 
                              t &/⋯[ 𝓢 , 𝓡 , 𝓢 ] ρ 
    
      record _d : Set₁ where
        field
          --! TravL
          var : (` x) &/⋯[  𝓢 , 𝓚 , 𝓢 ] ϕ ≡ 
                (x &/⋯[ 𝓡 , 𝓚 , 𝓚 ] ϕ) &/⋯[ 𝓚 , 𝓢 , 𝓢 ] id[ 𝓢 ]
        


open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Fin using (Fin)

--! Rewrite
+–idᴿ : ∀ n → n + 0 ≡ n
+–idᴿ zero     = refl
+–idᴿ (suc n)  = cong suc (+–idᴿ n)

--! RewriteIt
{-# REWRITE +–idᴿ #-}

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

      ＋coincidence  : (t : S₁ ⊢ s) → t ⋯ˢ (ρ ;ᴿˢ idˢ)  ≡ t ⋯ᴿ ρ
      --! } 
  opaque
    unfolding _→ᴿ_ _&ᴿ_ idᴿ wk _∙ᴿ_ _;ᴿᴿ_ _→ˢ_ _&ˢ_ idˢ _∙ˢ_ _;ᴿˢ_ _;ˢᴿ_ _;ˢˢ_

    --! DefLaws {
    -- Definitional Laws 
    ＋idᴿ  : x &ᴿ idᴿ             ≡ x
    ＋wk   : x &ᴿ wk {s = s′}     ≡ suc x
    ext₀ᴿ  : zero &ᴿ (x ∙ᴿ ρ)     ≡ x
    extₛᴿ  : (suc x′) &ᴿ (x ∙ᴿ ρ) ≡ x′ &ᴿ ρ 

    ＋idˢ  : x &ˢ idˢ             ≡ ` x
    ext₀ˢ  : zero &ˢ (t ∙ˢ σ)     ≡ t
    extₛˢ  : (suc x) &ˢ (t ∙ˢ σ)  ≡ x &ˢ σ

    compᴿᴿ  : x &ᴿ (ρ₁ ;ᴿᴿ ρ₂)  ≡ (x &ᴿ ρ₁) &ᴿ ρ₂
    compᴿˢ  : x &ˢ (ρ₁ ;ᴿˢ σ₂)  ≡ (x &ᴿ ρ₁) &ˢ σ₂
    compˢᴿ  : x &ˢ (σ₁ ;ˢᴿ ρ₂)  ≡ (x &ˢ σ₁) ⋯ᴿ ρ₂
    compˢˢ  : x &ˢ (σ₁ ;ˢˢ σ₂)  ≡ (x &ˢ σ₁) ⋯ˢ σ₂
    --! }

    --! InteractLaws {
    -- Interaction Laws
    comp-idₗᴿᴿ  : idᴿ ;ᴿᴿ ρ  ≡ ρ;    comp-idₗᴿˢ  : idᴿ ;ᴿˢ σ  ≡ σ
    comp-idᵣᴿᴿ  : ρ ;ᴿᴿ idᴿ  ≡ ρ 
    comp-idᵣˢˢ  : σ ;ˢˢ idˢ  ≡ σ;    comp-idᵣˢᴿ  : σ ;ˢᴿ idᴿ  ≡ σ 
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
      right-idᴿ right-idˢ
      compositionalityᴿᴿ compositionalityᴿˢ 
      compositionalityˢᴿ compositionalityˢˢ
      coincidence
    #-}
    --! }