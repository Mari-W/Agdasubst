{-# OPTIONS --rewriting --local-confluence-check #-}
module systemf1 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; drop)

--! E >

--! MultiSorted {
data Sort : Set where  expr type kind : Sort 
--! [

variable 
  s s₁ s₂ s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort
--! ]
Scope = List Sort

data Mode : Set where  V T : Mode
--! [
variable
  m  : Mode

--! ]

data _⊢[_]_ : Scope → Mode → Sort → Set 

_⊢_ = _⊢[ T ]_; _∋_ = _⊢[ V ]_

data _⊢[_]_ where 
  zero     : (s ∷ S) ∋ s
  suc      : S ∋ s → (s′ ∷ S) ∋ s
  `_       : S ∋ s → S ⊢ s 
  λx_      : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_      : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_  : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_      : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _•_      : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_      : S ⊢ type → S ⊢ type → S ⊢ type
  *        : S ⊢ kind
--! }
variable
  e e₁ e₂ e′ : S ⊢ expr
  k k′ : S ⊢ kind
  x x′ : S ∋ s
  t t₁ t₂ t′ : S ⊢ s
  x/t x/t′ : S ⊢[ m ] s


--! Sub {
_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s 

--! [
variable
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂  
--! ]


opaque  
  postulate
    wkˢ : ∀ s → S →ˢ (s ∷ S)
  
  idˢ : S →ˢ S
  idˢ _ = `_
 
  _∙_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂    
  _∙_  t σ _ zero = t
  (t ∙ σ) _ (suc x) = σ _ x 

  postulate
    _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  

  _⋯ˢ_ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
  _⋯ˢ_ {m = V} x σ = σ _ x
  (` x)         ⋯ˢ σ = x ⋯ˢ σ
  (λx e)        ⋯ˢ σ = λx (e ⋯ˢ (σ ↑ˢ _))
  -- ... 
  --! [
  (Λα e)        ⋯ˢ σ = Λα (e ⋯ˢ (σ ↑ˢ _))
  (∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  (e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  (e • t)       ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  *             ⋯ˢ σ = *
  --! ]

  _⨟_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂
--! }
  -- σₛ­ₚ calculus with first class renamings
  -- rewrite system
postulate
  --! DefLaws {
  -- first-class renamings 

  -- beta laws
  beta-ext-zero           : zero ⋯ˢ (t ∙ σ)   ≡ t                             
  beta-ext-suc            : suc x ⋯ˢ (t ∙ σ)  ≡ x ⋯ˢ σ 
  beta-lift               : σ ↑ˢ s            ≡ (` zero) ∙ (σ ⨟ wkˢ _)
  --! }

  --! InteractLaws {
  -- interaction laws
  associativity           : (σ₁ ⨟ σ₂) ⨟ σ₃                      ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  distributivityˢ         : (t ∙ σ₁) ⨟ σ₂                       ≡ ((t ⋯ˢ σ₂) ∙ (σ₁ ⨟ σ₂)) 

  interact                : wkˢ s ⨟ (t ∙ σ)                     ≡ σ                                        
  comp-idᵣ                : σ ⨟ idˢ                             ≡ σ                                               
  comp-idₗ                : idˢ ⨟ σ                             ≡ σ                                               
  η-id                    : (` zero {s = s} {S = S}) ∙ (wkˢ _)  ≡ idˢ
  η-lawˢ                  : (zero ⋯ˢ σ) ∙ (wkˢ _ ⨟ σ)           ≡ σ
 
  --! }

  --! MonadLaws {
  -- monad laws
  compositionalityˢˢ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ x/t ⋯ˢ (σ₁ ⨟ σ₂)
  --! }

  --! TraversalLaws {
  -- traveral laws
  traversal-x             : (` x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  traversal-λ             : (λx e)        ⋯ˢ σ  ≡ λx (e ⋯ˢ (σ ↑ˢ _))
  traversal-Λ             : (Λα e)        ⋯ˢ σ  ≡ Λα (e ⋯ˢ (σ ↑ˢ _))
  traversal-∀             : (∀[α∶ k ] t)  ⋯ˢ σ  ≡ ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  traversal-∙             : (e₁ · e₂)     ⋯ˢ σ  ≡ (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  traversal-•             : (e • t)       ⋯ˢ σ  ≡ (e ⋯ˢ σ) • (t ⋯ˢ σ)
  traversal-⇒             : (t₁ ⇒ t₂)     ⋯ˢ σ  ≡ (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  traversal-*             : *             ⋯ˢ σ  ≡ * 
  --! }

  --! CoincidenceLaws {
 

  -- not part of the theory.
  right-idˢ               : ∀ (t : S ⊢[ T ] s) → t ⋯ˢ idˢ                   ≡ t    

  id-beta : ∀ (x : S ⊢[ V ] s) → x ⋯ˢ idˢ                   ≡ ` x     
  wk-beta : x ⋯ˢ (wkˢ s) ≡ ` suc x
  wk-beta-compˢ           : x ⋯ˢ (wkˢ s ⨟ σ) ≡ suc x ⋯ˢ σ            

--! RewriteSys {
{-# REWRITE
  wk-beta-compˢ 
  wk-beta 
  id-beta

  beta-ext-zero 
  beta-ext-suc  
  beta-lift     

  associativity  
  distributivityˢ
  interact
  comp-idᵣ       
  comp-idₗ       
  η-id           
  η-lawˢ    

  right-idˢ     

  compositionalityˢˢ

  traversal-x
  traversal-λ
  traversal-Λ
  traversal-∀
  traversal-∙
  traversal-• 
  traversal-⇒
  traversal-*
#-}
--! }

