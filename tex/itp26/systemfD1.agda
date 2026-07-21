{-# OPTIONS --rewriting --local-confluence-check  #-}  -- confluence-check off: σ-laws confluent as a theory (ACCL), non-confluent-but-minimal as oriented rules — see note
module systemfD1 where

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
data Sort : Set where 
  expr type kind : Sort 
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

_⊢_ = _⊢[ T ]_ 
_∋_ = _⊢[ V ]_

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

--! Ren {
_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s 
--! [
variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂
--! ]
opaque
  idᴿ : S →ᴿ S
  idᴿ _ x = x

  wkᴿ : ∀ s → S →ᴿ (s ∷ S)
  wkᴿ _ _ = suc

  _∘_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → 
    S₁ →ᴿ S₃
  (ρ₁ ∘ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

  _∙ᴿ_ :  S₂ ∋ s → S₁ →ᴿ S₂ → 
    (s ∷ S₁) →ᴿ S₂    
  (x ∙ᴿ ρ) _ zero = x
  (_ ∙ᴿ ρ) _ (suc x) = ρ _ x


_↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → 
  ((s ∷ S₁) →ᴿ (s ∷ S₂))
(ρ ↑ᴿ _) = zero ∙ᴿ (ρ ∘ (wkᴿ _))

opaque
  _⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → 
    S₂ ⊢[ m ] s 
  _⋯ᴿ_ {m = V} x   ρ = ρ _ x
  (` x)         ⋯ᴿ ρ = ` ρ _ x
  (λx e)        ⋯ᴿ ρ = λx (e ⋯ᴿ (ρ ↑ᴿ _))
  (Λα e)        ⋯ᴿ ρ = Λα (e ⋯ᴿ (ρ ↑ᴿ _))
  (∀[α∶ k ] t)  ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] 
                       (t ⋯ᴿ (ρ ↑ᴿ _))
  (e₁ · e₂)     ⋯ᴿ ρ = (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)
  (e • t)       ⋯ᴿ ρ = (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
  (t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
  *             ⋯ᴿ ρ = * 
--! }
--! Sub {
_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s 

opaque
  ⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂ 
  ⟨ ρ ⟩ _ x = ` ρ _ x

idˢ : S →ˢ S
idˢ = ⟨ idᴿ ⟩
{-# INLINE idˢ #-}

wkˢ : ∀ s → S →ˢ (s ∷ S)
wkˢ _ = ⟨ wkᴿ _ ⟩
{-# INLINE wkˢ #-}
--! }

--! SubT {
opaque
  unfolding _⋯ᴿ_ 

  _∙ˢ_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂    
  (t ∙ˢ σ) _ zero = t
  (t ∙ˢ σ) _ (suc x) = σ _ x 

  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  σ ↑ˢ s =  (` zero) ∙ˢ λ _ x → (σ _ x) ⋯ᴿ wkᴿ _

  _⋯ˢ_ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
  _⋯ˢ_ {m = V} x σ = σ _ x
  (` x)         ⋯ˢ σ = σ _ x
  (λx e)        ⋯ˢ σ = λx (e ⋯ˢ (σ ↑ˢ _))
  (Λα e)        ⋯ˢ σ = Λα (e ⋯ˢ (σ ↑ˢ _))
  (∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  (e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  (e • t)       ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  *             ⋯ˢ σ = *

  _⨟_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂
--! }
variable
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂ 

opaque
  unfolding idᴿ _⋯ᴿ_ _∙ˢ_ ⟨_⟩ 
  -- σₛ­ₚ calculus with first class renamings
  -- rewrite system

  --! DefLaws {
  -- definitional rules
  def-∙ˢ-zero           : zero ⋯ˢ (t ∙ˢ σ)   ≡ t                             
  def-∙ˢ-suc            : suc x ⋯ˢ (t ∙ˢ σ)  ≡ x ⋯ˢ σ 
  def-⨟ : ((x ⋯ˢ σ₁) ⋯ˢ σ₂) ≡ (x ⋯ˢ (σ₁ ⨟ σ₂))
  def-↑ˢ               : σ ↑ˢ s ≡ (` zero) ∙ˢ (σ ⨟ wkˢ _)
  --! }
  def-id                : x ⋯ᴿ idᴿ ≡ x
  def-wk                : x ⋯ᴿ (wkᴿ s) ≡ suc x  
  def-∙ᴿ-zero           : zero ⋯ᴿ (x ∙ᴿ ρ)     ≡ x         
  def-∙ᴿ-suc            : (suc x) ⋯ᴿ (x′ ∙ᴿ ρ)  ≡ x ⋯ᴿ ρ      
  def-∘                 : (x ⋯ᴿ ρ₁) ⋯ᴿ ρ₂ ≡ x ⋯ᴿ (ρ₁ ∘ ρ₂)

  --! InteractLaws {
  -- interaction rules
  assoc : (σ₁ ⨟ σ₂) ⨟ σ₃ ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  dist : (t ∙ˢ σ₁)  ⨟ σ₂  ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ⨟ σ₂)) 
  interact                : wkˢ s ⨟ (t ∙ˢ σ) ≡ σ                                        
  comp-idᵣ                : σ ⨟ idˢ         ≡ σ                                               
  comp-idₗ                : idˢ ⨟ σ         ≡ σ                                               
  η-id    : (` zero {s} {S}) ∙ˢ (wkˢ _)      ≡ idˢ
  η-law  : (zero ⋯ˢ σ) ∙ˢ (wkˢ _ ⨟ σ)        ≡ σ
  id-var    : x ⋯ˢ idˢ            ≡ ` x
  wk-var    : x ⋯ˢ wkˢ s          ≡ ` (suc x)
  wk-comp   : x ⋯ˢ (wkˢ s ⨟ σ)    ≡ suc x ⋯ˢ σ
  wk-compᴿ  : x ⋯ᴿ (wkᴿ s ∘ ρ)    ≡ suc x ⋯ᴿ ρ
  comp-wkᴿ  : x ⋯ᴿ (ρ ∘ wkᴿ s)    ≡ suc (x ⋯ᴿ ρ)
  def-compˢᴿ : ∀ {S₁ S₂ S₃ s} {x : S₁ ∋ s} {σ₁ : S₁ →ˢ S₂} {ρ₂ : S₂ →ᴿ S₃} → (x ⋯ˢ σ₁) ⋯ᴿ ρ₂ ≡ x ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)
  def-compᴿˢ : (x ⋯ᴿ ρ₁) ⋯ˢ σ₂    ≡ x ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)
  dist-⟨⟩   : ⟨ x ∙ᴿ ρ ⟩ ⨟ σ      ≡ (x ⋯ˢ σ) ∙ˢ (⟨ ρ ⟩ ⨟ σ)
  assoc-⟨⟩  : ⟨ ρ₁ ∘ ρ₂ ⟩ ⨟ σ     ≡ ⟨ ρ₁ ⟩ ⨟ (⟨ ρ₂ ⟩ ⨟ σ)
  --! }
  assocᴿ           : (ρ₁ ∘ ρ₂) ∘ ρ₃ ≡ ρ₁ ∘ (ρ₂ ∘ ρ₃)                     
  distᴿ : (x ∙ᴿ ρ₁)  ∘ ρ₂  ≡ ((x ⋯ᴿ ρ₂) ∙ᴿ (ρ₁ ∘ ρ₂)) 
  interactᴿ                : wkᴿ s ∘ (x ∙ᴿ ρ) ≡ ρ                                        
  comp-idᵣᴿ                : ρ ∘ idᴿ         ≡ ρ                                               
  comp-idₗᴿ                : idᴿ ∘ ρ         ≡ ρ                                               
  η-idᴿ    : (zero {s} {S}) ∙ᴿ (wkᴿ _)      ≡ idᴿ
  η-lawᴿ  : (zero ⋯ᴿ ρ) ∙ᴿ (wkᴿ _ ∘ ρ)        ≡ ρ

  --! MonadLaws {
  -- monad rules
  right-id : ∀ (t : S ⊢ s) → t ⋯ᴿ idᴿ                   ≡ t   
  compositionalityᴿᴿ      : ∀ (t : S ⊢ s) → 
    (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ t ⋯ᴿ (ρ₁ ∘ ρ₂)     
  compositionalityᴿˢ      : ∀ (t : S ⊢ s) → 
    (t ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ t ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                                    
  compositionalityˢᴿ      : ∀ (t : S ⊢ s) → 
    (t ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ t ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
  compositionalityˢˢ      : ∀ (t : S ⊢ s) → 
    (t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ t ⋯ˢ (σ₁ ⨟ σ₂)
  --! } 

  --! TraversalLaws {
  -- traversal rules
  inst-x             : (` x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  inst-λ             : (λx e)        ⋯ˢ σ  ≡  
    λx (e ⋯ˢ (σ ↑ˢ _))
  inst-Λ             : (Λα e)        ⋯ˢ σ  ≡  
    Λα (e ⋯ˢ (σ ↑ˢ _))
  inst-∀             : (∀[α∶ k ] t)  ⋯ˢ σ  ≡  
    ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  inst-·             : (e₁ · e₂)     ⋯ˢ σ  ≡ 
    (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  inst-•             : (e • t)       ⋯ˢ σ  ≡ 
    (e ⋯ˢ σ) • (t ⋯ˢ σ)
  inst-⇒             : (t₁ ⇒ t₂)     ⋯ˢ σ  ≡ 
    (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  inst-*             : *             ⋯ˢ σ  ≡ * 
  --! }
  instᴿ-x             : (` x)         ⋯ᴿ ρ  ≡ ` (x ⋯ᴿ ρ)
  instᴿ-λ             : (λx e)        ⋯ᴿ ρ  ≡ 
    λx (e ⋯ᴿ (ρ ↑ᴿ _))
  instᴿ-Λ             : (Λα e)        ⋯ᴿ ρ  ≡ 
    Λα (e ⋯ᴿ (ρ ↑ᴿ _))
  instᴿ-∀             : (∀[α∶ k ] t)  ⋯ᴿ ρ  ≡ 
    ∀[α∶ k ⋯ᴿ ρ ] 
    (t ⋯ᴿ (ρ ↑ᴿ _))
  instᴿ-·            : (e₁ · e₂)     ⋯ᴿ ρ  ≡ 
    (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)
  instᴿ-•             : (e • t)       ⋯ᴿ ρ  ≡ 
    (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
  instᴿ-⇒             : (t₁ ⇒ t₂)     ⋯ᴿ ρ  ≡ 
    (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
  instᴿ-*             : *             ⋯ᴿ ρ  ≡ * 

  --! CoincidenceLaws {
  -- coincidence rules
  coincidence : ∀ (t : S ⊢ s) →
    t ⋯ˢ ⟨ ρ ⟩ ≡ (t ⋯ᴿ ρ)
  -- generalised: the law holds for an arbitrary head term/tail substitution,
  -- not just (t ⋯ᴿ ρ) ∙ˢ idˢ.  Removing the reducible (t ⋯ᴿ ρ) from the LHS
  -- kills the critical pairs against every instᴿ-*/compositionality rule.
  coincidence-fold :
    ⟨ ρ ↑ᴿ s ⟩ ⨟ (t ∙ˢ σ)  ≡ t ∙ˢ (⟨ ρ ⟩ ⨟ σ)
  --! }
  coincidence-var :
    x ⋯ˢ ⟨ ρ ⟩ ≡ ` (x ⋯ᴿ ρ)
  -- completion rules (resolve coincidence/composition critical pairs):
  coincidence-comp : ⟨ ρ₁ ⟩ ⨟ ⟨ ρ₂ ⟩ ≡ ⟨ ρ₁ ∘ ρ₂ ⟩
  coincidence-ext  : (` x) ∙ˢ ⟨ ρ ⟩ ≡ ⟨ x ∙ᴿ ρ ⟩

  -- proofs 

  -- not part of the theory.
  right-idˢ               : ∀ (t : S ⊢ s) → t ⋯ˢ idˢ                   ≡ t      

  def-∙ˢ-zero = refl
  def-∙ˢ-suc  = refl
  def-⨟     = refl
  id-var    = refl
  wk-var    = refl
  wk-comp   = refl
  wk-compᴿ  = refl
  comp-wkᴿ  = refl
  def-compˢᴿ {x = x} {σ₁ = σ₁} = sym (coincidence (σ₁ _ x))
  def-compᴿˢ = refl
  dist-⟨⟩   = ext λ { zero → refl ; (suc x) → refl }
  assoc-⟨⟩  = ext λ x → refl
  def-↑ˢ {σ = σ} = cong ((` zero) ∙ˢ_) (sym (ext λ x → coincidence (σ _ x)))

  def-id      = refl
  def-wk      = refl      
  def-∙ᴿ-zero = refl
  def-∙ᴿ-suc  = refl
  def-∘       = refl

  assoc {σ₁ = σ₁} = ext (λ x → compositionalityˢˢ (σ₁ _ x))
  dist = ext λ { zero → refl; (suc x) → refl }
  interact = refl
  comp-idᵣ = ext λ x → (right-idˢ _)
  comp-idₗ = refl
  η-id = ext λ { zero → refl; (suc x) → refl }
  η-law = ext λ { zero → refl; (suc x) → refl }

  assocᴿ = refl
  distᴿ = ext λ { zero → refl; (suc x) → refl }
  interactᴿ = refl
  comp-idᵣᴿ = refl
  comp-idₗᴿ = refl
  η-idᴿ = ext λ { zero → refl; (suc x) → refl }
  η-lawᴿ = ext λ { zero → refl; (suc x) → refl }


  lift-idᴿ : idᴿ {S = S} ↑ᴿ s ≡ idᴿ
  lift-idᴿ = ext λ { zero → refl; (suc x) → refl }
  right-id (` x)        = refl
  right-id (λx e)       = cong λx_ (trans (cong (e ⋯ᴿ_) lift-idᴿ) (right-id e))
  right-id (Λα e)       = cong Λα_ (trans (cong (e ⋯ᴿ_) lift-idᴿ) (right-id e))
  right-id (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-id k) (trans (cong (t ⋯ᴿ_) lift-idᴿ) (right-id t))
  right-id (e₁ · e₂)    = cong₂ _·_ (right-id e₁) (right-id e₂)
  right-id (e • t)      = cong₂ _•_ (right-id e) (right-id t)
  right-id (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-id t₁) (right-id t₂)
  right-id *            = refl

  right-idˢ (` x)        = refl
  right-idˢ (λx e)       = cong λx_ (trans (cong (e ⋯ˢ_) η-id) (right-idˢ e))
  right-idˢ (Λα e)       = cong Λα_ (trans (cong (e ⋯ˢ_) η-id) (right-idˢ e))
  right-idˢ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idˢ k) (trans (cong (t ⋯ˢ_) η-id) (right-idˢ t))
  right-idˢ (e₁ · e₂)    = cong₂ _·_ (right-idˢ e₁) (right-idˢ e₂)
  right-idˢ (e • t)      = cong₂ _•_ (right-idˢ e) (right-idˢ t)
  right-idˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idˢ t₁) (right-idˢ t₂)
  right-idˢ *            = refl

  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (` x)        = refl
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (λx e)       = cong λx_ (trans (compositionalityᴿᴿ e) (cong (e ⋯ᴿ_) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (Λα e)       = cong Λα_ (trans (compositionalityᴿᴿ e) (cong (e ⋯ᴿ_) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿᴿ k) (trans (compositionalityᴿᴿ t) (cong (t ⋯ᴿ_) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿᴿ e₁) (compositionalityᴿᴿ e₂)
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e • t)      = cong₂ _•_ (compositionalityᴿᴿ e) (compositionalityᴿᴿ t)
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿᴿ t₁) (compositionalityᴿᴿ t₂)
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} *            = refl

  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (` x)        = refl
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compositionalityᴿˢ e) (cong (e ⋯ˢ_) (lift-dist-compᴿˢ {σ₂ = σ₂})))
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityᴿˢ e) (cong (e ⋯ˢ_) (lift-dist-compᴿˢ {σ₂ = σ₂})))
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿˢ k) (trans (compositionalityᴿˢ t) (cong (t ⋯ˢ_) (lift-dist-compᴿˢ {σ₂ = σ₂})))
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿˢ e₁) (compositionalityᴿˢ e₂)
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (e • t)      = cong₂ _•_ (compositionalityᴿˢ e) (compositionalityᴿˢ t)
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿˢ t₁) (compositionalityᴿˢ t₂)
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} *            = refl

  lift-dist-compˢᴿ : ((σ₁ ↑ˢ s) ⨟ ⟨ ρ₂ ↑ᴿ s ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ s)
  lift-dist-compˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    (t ⋯ᴿ (wkᴿ _)) ⋯ˢ ⟨ ρ₂ ↑ᴿ _ ⟩ ≡⟨ (coincidence (t ⋯ᴿ (wkᴿ _))) ⟩ 
    (t ⋯ᴿ (wkᴿ _)) ⋯ᴿ (ρ₂ ↑ᴿ _)   ≡⟨ compositionalityᴿᴿ t ⟩ 
    t ⋯ᴿ (wkᴿ _ ∘ (ρ₂ ↑ᴿ _))    ≡⟨ sym (compositionalityᴿᴿ t) ⟩ 
    (t ⋯ᴿ ρ₂) ⋯ᴿ wkᴿ _          ≡⟨ cong (_⋯ᴿ (wkᴿ _)) (sym (coincidence t)) ⟩ 
    (t ⋯ˢ ⟨ ρ₂ ⟩) ⋯ᴿ wkᴿ _      ∎ }
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (` x)         = sym (coincidence (σ₁ _ x))
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (λx e)        = cong λx_ (trans (compositionalityˢᴿ e) (cong (e ⋯ˢ_) (lift-dist-compˢᴿ {σ₁ = σ₁})))
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (Λα e)        = cong Λα_ (trans (compositionalityˢᴿ e) (cong (e ⋯ˢ_) (lift-dist-compˢᴿ {σ₁ = σ₁})))
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t)  = cong₂ ∀[α∶_]_ (compositionalityˢᴿ k) (trans (compositionalityˢᴿ t) (cong (t ⋯ˢ_) (lift-dist-compˢᴿ {σ₁ = σ₁})))
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (e₁ · e₂)     = cong₂ _·_ (compositionalityˢᴿ e₁) (compositionalityˢᴿ e₂)
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (e • t)       = cong₂ _•_ (compositionalityˢᴿ e) (compositionalityˢᴿ t)
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)     = cong₂ _⇒_ (compositionalityˢᴿ t₁) (compositionalityˢᴿ t₂)
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} *             = refl

  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s)
  lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    begin
    (t ⋯ᴿ (wkᴿ _)) ⋯ˢ (σ₂ ↑ˢ _)    ≡⟨ compositionalityᴿˢ t ⟩ 
    t ⋯ˢ (⟨ (wkᴿ _) ⟩ ⨟ (σ₂ ↑ˢ _)) ≡⟨ cong (t ⋯ˢ_) (ext λ x → sym (coincidence (σ₂ _ x))) ⟩   
    t ⋯ˢ (σ₂ ⨟ ⟨ (wkᴿ _) ⟩)        ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
    (t ⋯ˢ σ₂) ⋯ᴿ (wkᴿ _)           ∎ }
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (` x)        = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compositionalityˢˢ e) (cong (e ⋯ˢ_) (lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂})))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityˢˢ e) (cong (e ⋯ˢ_) (lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂})))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢˢ k) (trans (compositionalityˢˢ t) (cong (t ⋯ˢ_) (lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂})))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityˢˢ e₁) (compositionalityˢˢ e₂)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (e • t)      = cong₂ _•_ (compositionalityˢˢ e) (compositionalityˢˢ t)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢˢ t₁) (compositionalityˢˢ t₂)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} *            = refl 
    

  inst-x = refl
  inst-λ = refl
  inst-Λ = refl
  inst-∀ = refl
  inst-· = refl
  inst-• = refl
  inst-⇒ = refl
  inst-* = refl

  instᴿ-x = refl
  instᴿ-λ = refl
  instᴿ-Λ = refl
  instᴿ-∀ = refl
  instᴿ-· = refl
  instᴿ-• = refl
  instᴿ-⇒ = refl
  instᴿ-* = refl

  coincidence {ρ = ρ} t = 
    t ⋯ˢ (⟨ ρ ⟩ ⨟ idˢ) ≡⟨ sym (compositionalityᴿˢ t) ⟩ 
    (t ⋯ᴿ ρ) ⋯ˢ idˢ    ≡⟨ right-idˢ _ ⟩ 
    t ⋯ᴿ ρ             ∎

  coincidence-fold = ext λ { zero → refl; (suc x) → refl }
  coincidence-var = refl
  coincidence-comp = ext λ x → refl
  coincidence-ext  = ext λ { zero → refl; (suc x) → refl }
  
  demo1 : σ ⨟ idˢ ≡ σ
  demo1 {σ = σ} = 
      --!! IdLaw 
      σ ⨟ idˢ

        ≡⟨⟩ 
      --!! IdLawUnfolded
      (λ _ x → σ _ x ⋯ˢ (λ _ → `_))

        ≡⟨ comp-idᵣ ⟩
      σ
      ∎ 

  demo2 : 
    --!! FunAppInterp
    (σ₁ ⨟ σ₂) _ x ≡ (x ⋯ˢ σ₁) ⋯ˢ σ₂

  demo2 = refl

--! RewriteSys {
-- complete rewrite system 
{-# REWRITE 
def-∙ˢ-zero def-∙ˢ-suc def-↑ˢ def-⨟   
assoc dist interact       
comp-idᵣ comp-idₗ η-id η-law
inst-x inst-λ inst-Λ inst-∀ inst-· inst-•
inst-⇒ inst-*
right-id         
compositionalityᴿᴿ compositionalityᴿˢ
compositionalityˢᴿ compositionalityˢˢ
coincidence  coincidence-comp 

def-id def-wk def-∙ᴿ-zero def-∙ᴿ-suc def-∘
assocᴿ distᴿ interactᴿ       
comp-idᵣᴿ comp-idₗᴿ η-idᴿ η-lawᴿ
instᴿ-x instᴿ-λ instᴿ-Λ instᴿ-∀ instᴿ-· instᴿ-•
instᴿ-⇒ instᴿ-* 
coincidence-var
 right-idˢ
 id-var
 wk-var
 wk-comp
 wk-compᴿ
 comp-wkᴿ
 def-compˢᴿ
 def-compᴿˢ
 dist-⟨⟩
 assoc-⟨⟩
#-}
