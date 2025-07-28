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

record _A : Set₁ where
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
      Kᴿ   : Kit 
      Kˢ   : Kit 
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
      _∙_  : S₂ ∋/⊢[ K ] s → S₁ –[ K ]→ S₂ → (s ∷ S₁) –[ K ]→ S₂
      _;_  : S₁ –[ K₁ ]→ S₂ → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₁ ⊔ K₂ ]→ S₃ 
      wkᴿ   : S –[ Kᴿ ]→ (s ∷ S)

      --! VarTrmApp
      _&/⋯_ : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₁ ⊔ K₂ ] s

      idᴿ : S –[ Kᴿ ]→ S
      idˢ : S –[ Kˢ ]→ S

      -- wkᴿ : S –[ Kᴿ ]→ (s ∷ S)
      -- wkˢ : S –[ Kˢ ]→ (s ∷ S)

      _&/⋯ᴿᴿ_ : S₁ ∋ s → S₁ –[ Kᴿ ]→ S₂ → S₂ ∋ s
      _&/⋯ᴿᴷ_ : S₁ ∋ s → S₁ –[ K ]→ S₂ → S₂ ∋/⊢[ K ] s
      _&/⋯ᴿˢ_ : S₁ ∋ s → S₁ –[ Kˢ ]→ S₂ → S₂ ⊢ s
      _&/⋯ᴷᴿ_ : S₂ ∋ s → S₁ –[ K ]→ S₂ → S₂ ∋/⊢[ K ] s
      _&/⋯ˢᴿ_ : S₁ ⊢ s → S₁ –[ Kᴿ ]→ S₂ → S₂ ⊢ s
      _&/⋯ᴷˢ_ : S₂ ∋/⊢[ K ] s → S₁ –[ Kˢ ]→ S₂ → S₂ ⊢ s
      _&/⋯ˢˢ_ : S₁ ⊢ s → S₁ –[ Kˢ ]→ S₂ → S₂ ⊢ s
      _&/⋯ˢᴷ_ : S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
      _&/⋯ᴷᴷ_ : S₂ ∋/⊢[ K ] s → S₁ –[ K ]→ S₂ → S₂ ∋/⊢[ K ] s

      _;ᴷᴷ_  : S₁ –[ K ]→ S₂ → S₂ –[ K ]→ S₃ → S₁ –[ K ]→ S₃
      _;ˢᴷ_  : S₁ –[ Kˢ ]→ S₂ → S₂ –[ K ]→ S₃ → S₁ –[ Kˢ ]→ S₃ 
      _;ᴷˢ_  : S₁ –[ K ]→ S₂ → S₂ –[ Kˢ ]→ S₃ → S₁ –[ Kˢ ]→ S₃   
      _;ᴿᴷ_  : S₁ –[ Kᴿ ]→ S₂ → S₂ –[ K ]→ S₃ → S₁ –[ K ]→ S₃ 
    
      --! TypeLevel
      botᴿ   : K ⊔ Kᴿ          ≡ K               
      botₗ   : Kᴿ ⊔ K          ≡ K               
      topᴿ   : K ⊔ Kˢ          ≡ Kˢ              
      topₗ   : Kˢ ⊔ K          ≡ Kˢ     
      idem   : K ⊔ K           ≡ K                        
      assoc  : (K₁ ⊔ K₂) ⊔ K₃  ≡ K₁ ⊔ (K₂ ⊔ K₃)  

    {-# REWRITE botᴿ botₗ topᴿ topₗ idem assoc #-}
    postulate
      --! DefLawTy
      imgˢ : S ∋/⊢[ Kᴿ ] s ≡ S ∋ s   
      imgᴿ : S ∋/⊢[ Kˢ ] s ≡ S ⊢ s 

    {-# REWRITE imgˢ imgᴿ #-}
    module foo
       {{K₁ : Kit}} {{K₂ : Kit}} {{K₃ : Kit}} {{K₄ : Kit}} {{K₅ : Kit}}
      (ϕ : S₁ –[ K₁ ]→ S₂) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) (ϕ₃ : S₃ –[ K₄ ]→ S₄)
      (q : S₂ ∋/⊢[ K₁ ] s) (t : S₂ ⊢ s) (x : S₁ ∋ s) (x′ : S₁ ∋ s′) (ϕ′ : (s ∷ S₁) –[ K₂ ]→ S₂) 
      where 

      postulate
         --! DefLaw
        ＋idᴿ  :  x &/⋯ᴿᴿ idᴿ         ≡ x
        ＋idˢ  :  x &/⋯ᴿˢ idˢ         ≡ ` x
        extᶻ  : zero &/⋯ᴿᴷ (q ∙ ϕ)    ≡ q
        extˢ  : suc x′ &/⋯ᴿᴷ (q ∙ ϕ)  ≡ x′ &/⋯ᴿᴷ ϕ
        ＋wkᴿ  :  x &/⋯ᴿᴿ wkᴿ         ≡ suc x
        comp  : x &/⋯ᴿᴷ (ϕ₁ ; ϕ₂)     ≡ (x &/⋯ᴿᴷ ϕ₁) &/⋯  ϕ₂
        --＋wkˢ  :  x &/⋯ᴿˢ wkˢ       ≡ ` suc x

        --! Interaction
        comp-idₗ        : id ;ᴷᴷ ϕ                         ≡  ϕ
        comp-idᴿ        : ϕ ;ᴷᴷ id                         ≡  ϕ
        norm-idˢ        : id ;ˢᴷ ϕ                         ≡  ϕ ;ᴷˢ id
        associativity   : (ϕ₁ ; ϕ₂) ; ϕ₃                   ≡  ϕ₁ ; (ϕ₂ ; ϕ₃) 
        distributivity  : (q ∙ ϕ₁) ; ϕ₂                    ≡ (q &/⋯ ϕ₂) ∙ (ϕ₁ ; ϕ₂)
        interact        : wkᴿ ;ᴿᴷ (q ∙ ϕ)                  ≡ ϕ 
        η–id            : (zero &/⋯ᴿᴷ id) ∙ wkᴿ            ≡ id
        η–law           : (zero &/⋯ᴿᴷ ϕ′) ∙ (wkᴿ ;ᴿᴷ ϕ′)   ≡ ϕ′
        

        --! Monad
        compositionality  : (t &/⋯ ϕ₁) &/⋯ ϕ₂  ≡ t &/⋯ (ϕ₁ ; ϕ₂)
        right-id          :  t &/⋯ id          ≡ t

        --! TravL
        var : (` x) &/⋯ˢᴷ ϕ ≡ (x &/⋯ᴿᴷ ϕ) &/⋯ᴷˢ idˢ


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

  opaque 
    _→ᴷ_ : {_∋/⊢_ : Scoped} → Scope → Scope → Set
    _→ᴷ_ {_∋/⊢_} S₁ S₂ = ∀ {s} → S₁ ∋ s → S₂ ∋/⊢ s

  _–[_]→_ : Scope → Scoped → Scope → Set
  S₁ –[ _∋/⊢_ ]→ S₂ = _→ᴷ_ {_∋/⊢_} S₁ S₂

  _→ᴿ_ : Scope → Scope → Set
  _→ᴿ_ = _→ᴷ_ {_∋_}

  opaque
    unfolding _→ᴷ_

    _&_ : {_∋/⊢_ : Scoped} → S₁ ∋ s → S₁ –[ _∋/⊢_ ]→ S₂ → S₂ ∋/⊢ s
    x & ϕ = ϕ x

    _∙_ : {_∋/⊢_ : Scoped} → S₂ ∋/⊢ s → S₁ –[ _∋/⊢_ ]→ S₂ → (s ∷ S₁) –[ _∋/⊢_ ]→ S₂
    (x/t ∙ _) zero   = x/t
    (_ ∙ ϕ) (suc x)  = ϕ x

    idᴿ : S →ᴿ S 
    idᴿ x = x 

    wkᴿ : S →ᴿ (s ∷ S)
    wkᴿ x = suc x

    _;ᴿᴷ_ : {_∋/⊢_ : Scoped} → S₁ →ᴿ S₂ → S₂ –[ _∋/⊢_ ]→ S₃ → S₁ –[ _∋/⊢_ ]→ S₃
    (ρ₁ ;ᴿᴷ ϕ₂) x = ϕ₂ (ρ₁ x)

  _↑ᴿ_ : S₁ →ᴿ S₂ → ∀ s → (s ∷ S₁) →ᴿ (s ∷ S₂)
  ρ ↑ᴿ _ = zero ∙ (ρ ;ᴿᴷ wkᴿ)

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

  _→ˢ_ : Scope → Scope → Set
  _→ˢ_ = _→ᴷ_ {_⊢_}
  opaque
    unfolding 
      _→ᴷ_ _&_ _∙_ idᴿ wkᴿ _;ᴿᴷ_

    idˢ : S →ˢ S
    idˢ = `_

    _;ˢᴿ_ : S₁ →ˢ S₂ → S₂ →ᴿ S₃ → S₁ →ˢ S₃
    (σ₁ ;ˢᴿ ρ₂) x = (σ₁ x) ⋯ᴿ ρ₂
  
  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  (σ ↑ˢ _) = (` zero) ∙ (σ ;ˢᴿ wkᴿ)

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
      _→ᴷ_ _&_ _∙_ idᴿ wkᴿ _;ᴿᴷ_ idˢ _;ˢᴿ_

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

  wkᴿ : S →ᴿ (s ∷ S)
  wkᴿ x = suc x

  _∙ᴿ_ : S₂ ∋ s → S₁ →ᴿ S₂ → (s ∷ S₁) →ᴿ S₂
  (x ∙ᴿ _) zero     = x
  (_ ∙ᴿ ρ) (suc x)  = ρ x

  _;ᴿᴿ_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
  (ρ₁ ;ᴿᴿ ρ₂) x = ρ₂ (ρ₁ x)

_↑ᴿ_ : S₁ →ᴿ S₂ → ∀ s → (s ∷ S₁) →ᴿ (s ∷ S₂)
ρ ↑ᴿ _ = zero ∙ᴿ (ρ ;ᴿᴿ wkᴿ)

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
    _→ᴿ_ _&ᴿ_ idᴿ wkᴿ _∙ᴿ_ _;ᴿᴿ_

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
(σ ↑ˢ _) = (` zero) ∙ˢ (σ ;ˢᴿ wkᴿ)

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
    _→ᴿ_ _&ᴿ_ idᴿ wkᴿ _∙ᴿ_ _;ᴿᴿ_ 
    _→ˢ_ _&ˢ_ idˢ _∙ˢ_ _;ᴿˢ_ _;ˢᴿ_

  _;ˢˢ_ :  S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ;ˢˢ σ₂) x = (σ₁ x) ⋯ˢ σ₂
--! }

variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂ 
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂ 

module _B where
  opaque
    unfolding _→ᴿ_ _&ᴿ_ idᴿ wkᴿ _∙ᴿ_ _;ᴿᴿ_ _→ˢ_ _&ˢ_ idˢ _∙ˢ_ _;ᴿˢ_ _;ˢᴿ_ _;ˢˢ_

    --! DefLaws {
    -- Definitional Laws 
    ＋idᴿ    : x &ᴿ idᴿ ≡ x
    ＋wkᴿ    : x &ᴿ wkᴿ {s = s′} ≡ suc x
    extᶻᴿ  : zero &ᴿ (x ∙ᴿ ρ) ≡ x
    extˢᴿ  : (suc x′) &ᴿ (x ∙ᴿ ρ) ≡ x′ &ᴿ ρ 

    ＋idˢ    : x &ˢ idˢ ≡ ` x
    extᶻˢ  : zero &ˢ (t ∙ˢ σ) ≡ t
    extˢˢ  : (suc x) &ˢ (t ∙ˢ σ) ≡ x &ˢ σ

    compᴿᴿ : x &ᴿ (ρ₁ ;ᴿᴿ ρ₂) ≡ (x &ᴿ ρ₁) &ᴿ ρ₂
    compᴿˢ : x &ˢ (ρ₁ ;ᴿˢ σ₂) ≡ (x &ᴿ ρ₁) &ˢ σ₂
    compˢᴿ : x &ˢ (σ₁ ;ˢᴿ ρ₂) ≡ (x &ˢ σ₁) ⋯ᴿ ρ₂
    compˢˢ : x &ˢ (σ₁ ;ˢˢ σ₂) ≡ (x &ˢ σ₁) ⋯ˢ σ₂
    --! }

    --! InteractLaws {
    -- Interaction Laws
    comp-idₗᴿᴿ : idᴿ ;ᴿᴿ ρ ≡ ρ;    comp-idₗᴿˢ : idᴿ ;ᴿˢ σ ≡ σ
    comp-idᵣᴿᴿ : ρ ;ᴿᴿ idᴿ ≡ ρ
    comp-idₗˢˢ : idˢ ;ˢˢ σ ≡ σ;    comp-idᵣˢᴿ : σ ;ˢᴿ idᴿ ≡ σ 
    comp-idᵣˢˢ : σ ;ˢˢ idˢ ≡ σ
    norm-id : idˢ ;ˢᴿ ρ ≡ ρ ;ᴿˢ idˢ

    associativityᴿᴿᴿ : (ρ₁ ;ᴿᴿ ρ₂) ;ᴿᴿ ρ₃ ≡ ρ₁ ;ᴿᴿ (ρ₂ ;ᴿᴿ ρ₃)
    associativityᴿᴿˢ : (ρ₁ ;ᴿᴿ ρ₂) ;ᴿˢ σ₃ ≡ ρ₁ ;ᴿˢ (ρ₂ ;ᴿˢ σ₃)
    associativityᴿˢᴿ : (ρ₁ ;ᴿˢ σ₂) ;ˢᴿ ρ₃ ≡ ρ₁ ;ᴿˢ (σ₂ ;ˢᴿ ρ₃)
    associativityᴿˢˢ : (ρ₁ ;ᴿˢ σ₂) ;ˢˢ σ₃ ≡ ρ₁ ;ᴿˢ (σ₂ ;ˢˢ σ₃)
    associativityˢᴿᴿ : (σ₁ ;ˢᴿ ρ₂) ;ˢᴿ ρ₃ ≡ σ₁ ;ˢᴿ (ρ₂ ;ᴿᴿ ρ₃)
    associativityˢᴿˢ : (σ₁ ;ˢᴿ ρ₂) ;ˢˢ σ₃ ≡ σ₁ ;ˢˢ (ρ₂ ;ᴿˢ σ₃)
    associativityˢˢᴿ : (σ₁ ;ˢˢ σ₂) ;ˢᴿ ρ₃ ≡ σ₁ ;ˢˢ (σ₂ ;ˢᴿ ρ₃)
    associativityˢˢˢ : (σ₁ ;ˢˢ σ₂) ;ˢˢ σ₃ ≡ σ₁ ;ˢˢ (σ₂ ;ˢˢ σ₃)

    distributivityᴿᴿ : (x ∙ᴿ ρ₁) ;ᴿᴿ ρ₂ ≡ ((x &ᴿ ρ₂) ∙ᴿ (ρ₁ ;ᴿᴿ ρ₂))
    distributivityᴿˢ : (x ∙ᴿ ρ₁) ;ᴿˢ σ₂ ≡ ((x &ˢ σ₂) ∙ˢ (ρ₁ ;ᴿˢ σ₂))
    distributivityˢᴿ : (t ∙ˢ σ₁) ;ˢᴿ ρ₂ ≡ ((t ⋯ᴿ ρ₂) ∙ˢ (σ₁ ;ˢᴿ ρ₂))
    distributivityˢˢ : (t ∙ˢ σ₁) ;ˢˢ σ₂ ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ;ˢˢ σ₂))

    interactᴿ : wkᴿ ;ᴿᴿ (x ∙ᴿ ρ) ≡ ρ;   interactˢ : wkᴿ ;ᴿˢ (t ∙ˢ σ) ≡ σ

    η-idᴿ  : zero {S = S} {s = s} ∙ᴿ wkᴿ ≡ idᴿ
    -- η-idˢ  : (` (zero {S = S} {s = s})) ∙ˢ (wkᴿ ;ᴿˢ idˢ) ≡ idˢ
    η-lawᴿ : (zero &ᴿ ρ) ∙ᴿ (wkᴿ ;ᴿᴿ ρ) ≡ ρ
    η-lawˢ : (zero &ˢ σ) ∙ˢ (wkᴿ ;ᴿˢ σ) ≡ σ
    --! }

    --! MonadLaws {
    -- Monad Laws
    right-idᴿ : (t : S ⊢ s) → t ⋯ᴿ idᴿ ≡ t
    right-idˢ : (t : S ⊢ s) → t ⋯ˢ idˢ ≡ t 

    compositionalityᴿᴿ : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂ ≡ t ⋯ᴿ (ρ₁ ;ᴿᴿ ρ₂)
    compositionalityᴿˢ : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂ ≡ t ⋯ˢ (ρ₁ ;ᴿˢ σ₂)
    compositionalityˢᴿ : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂ ≡ t ⋯ˢ (σ₁ ;ˢᴿ ρ₂)
    compositionalityˢˢ : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂ ≡ t ⋯ˢ (σ₁ ;ˢˢ σ₂)
    --! } 

    -- All proofs
    ＋idᴿ = refl
    ＋wkᴿ = refl 
    extᶻᴿ = refl
    extˢᴿ = refl
    ＋idˢ = refl
    extᶻˢ = refl
    extˢˢ = refl

    compᴿᴿ = refl
    compᴿˢ = refl
    compˢᴿ = refl
    compˢˢ = refl

    interactᴿ = refl
    interactˢ = refl

    η-idᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    η-idˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    η-lawᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    η-lawˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))

    distributivityᴿᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    distributivityᴿˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    distributivityˢᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    distributivityˢˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))

    right-idᴿ (` x)        = refl
    right-idᴿ (λx e)       = cong λx_ (trans (cong (_⋯ᴿ_ {S₂ = expr ∷ _} e) η-idᴿ) (right-idᴿ e))
    right-idᴿ (Λα e)       = cong Λα_ (trans (cong (_⋯ᴿ_ {S₂ = type ∷ _} e) η-idᴿ) (right-idᴿ e))
    right-idᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idᴿ k) (trans (cong (_⋯ᴿ_ {S₂ = type ∷ _} t) η-idᴿ) (right-idᴿ t))
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

    comp-idₗᴿᴿ = refl
    comp-idᵣᴿᴿ = refl
    comp-idₗᴿˢ = refl
    norm-id = refl 
    comp-idₗˢˢ = refl
    comp-idᵣˢᴿ {σ = σ} = fun-exti (fun-ext λ x → right-idᴿ (x &ˢ σ))
    comp-idᵣˢˢ {σ = σ} = fun-exti (fun-ext λ x → right-idˢ (x &ˢ σ))

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
      ＋idᴿ ＋wkᴿ extᶻᴿ extˢᴿ
      ＋idˢ extᶻˢ extˢˢ
      compᴿᴿ compᴿˢ compˢᴿ compˢˢ
      comp-idₗᴿᴿ comp-idₗᴿˢ comp-idᵣᴿᴿ 
      comp-idₗˢˢ comp-idᵣˢˢ 
      norm-id
      associativityᴿᴿᴿ associativityᴿᴿˢ 
      associativityᴿˢᴿ associativityᴿˢˢ
      associativityˢᴿᴿ associativityˢᴿˢ 
      associativityˢˢᴿ associativityˢˢˢ
      distributivityᴿᴿ distributivityᴿˢ 
      distributivityˢᴿ distributivityˢˢ
      interactᴿ interactˢ
      η-idᴿ η-idˢ η-lawᴿ η-lawˢ
      right-idᴿ right-idˢ
      compositionalityᴿᴿ compositionalityᴿˢ 
      compositionalityˢᴿ compositionalityˢˢ
    #-}
    --! }