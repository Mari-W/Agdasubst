-- agda version 2.8.0
-- agdasubst version: 0.1.0
module Agdasubst where

open import Data.List using (List; []; _∷_; _++_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning) public
open ≡-Reasoning public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit) public
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂ 

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

open import Agda.Builtin.Equality.Rewrite public 

data Mode : Set where
  V T : Mode

variable 
  m m₁ m₂ m₃ m₄ m′ : Mode

module WithSort (Sort : Set) where
  variable 
    s s₁ s₂ s₃ s₄ s′ : Sort 
    S S₁ S₂ S₃ S₄ S′ : List Sort
  
  Scope = List Sort
  Scoped = List Sort → Sort → Set

  data _∋_ : Scoped where
    zero     : (s ∷ S) ∋ s
    suc      : S ∋ s → (s′ ∷ S) ∋ s
  
  private variable
    x x₁ x₂ x₃ x₄ x′ : S ∋ s

  _→ᴿ_ : Scope → Scope → Set
  S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s 

  private variable
    ρ ρ₁ ρ₂ ρ₃ ρ₄ ρ′ : S₁ →ᴿ S₂

  idᴿ : S →ᴿ S
  idᴿ _ x = x

  _↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → ((s ∷ S₁) →ᴿ (s ∷ S₂))
  (ρ ↑ᴿ _) _ zero    = zero
  (ρ ↑ᴿ _) _ (suc x) = suc (ρ _ x)

  _↑ᴿ*_ : (S₁ →ᴿ S₂) → ∀ S → ((S ++ S₁) →ᴿ (S ++ S₂))
  ρ ↑ᴿ* [] = ρ
  ρ ↑ᴿ* (s ∷ S) = (ρ ↑ᴿ* S) ↑ᴿ s

  _∘_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
  _∘_ = λ z z₁ s z₂ → z₁ s (z s z₂)

  wk : ∀ s → S →ᴿ (s ∷ S)
  wk _ _ = suc

  module WithSyntax (_⊢_ : Scoped) (`_ : ∀ {S s} → S ∋ s → S ⊢ s) where
    _⊢[_]_ : Scope → Mode → Sort → Set 
    S ⊢[ V ] s = S ∋ s
    S ⊢[ T ] s = S ⊢ s
  
    _→ˢ_ : Scope → Scope → Set
    S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s

    private variable
      σ σ₁ σ₂ σ₃ σ₄ σ′ : S₁ →ˢ S₂

    ⟪_⟫ : S₁ →ᴿ S₂ → S₁ →ˢ S₂ 
    ⟪ ρ ⟫ _ x = ` ρ _ x
    {-# INLINE ⟪_⟫ #-}

    wkˢ : ∀ s → S →ˢ (s ∷ S)
    wkˢ _ _ x =  ` suc x
    {-# INLINE wkˢ #-}

    idˢ : S →ˢ S
    idˢ _ = `_
    {-# INLINE idˢ #-}

    _→[_]_ : Scope → Mode → Scope → Set
    S₁ →[ m ] S₂ = ∀ s → S₁ ∋ s → S₂ ⊢[ m ] s 

    Traversal : Set 
    Traversal = ∀ {S₁ S₂ s} m → 
      (_↑*_ : ∀ {S₁ S₂} → S₁ →[ m ] S₂ → ∀ S → (S ++ S₁) →[ m ] (S ++ S₂)) → 
      S₁ ⊢ s → S₁ →[ m ] S₂ → S₂ ⊢ s

    _⟨_⟩ : ∀ m → S ⊢[ m ] s → S ⊢ s
    _⟨_⟩ V x = ` x
    _⟨_⟩ T t = t

    module WithTraversal ([_,_]_⋯_ : Traversal) where
      _⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → S₂ ⊢ s
      _⋯ᴿ_ {m = V} x ρ = ` ρ _ x
      _⋯ᴿ_ {m = T} {s = s} t ρ = [ V , _↑ᴿ*_ ] t ⋯ ρ
      {-# INLINE _⋯ᴿ_ #-}

      opaque
        import Data.Unit
        substitution_primitives : Data.Unit.⊤
        substitution_primitives = Data.Unit.tt

        _∙_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂    
        (t ∙ σ) _ zero = t
        (t ∙ σ) _ (suc x) = σ _ x 

        _⋯ˢ_ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s

        _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
        σ ↑ˢ s =  (` zero) ∙ λ s₁ x → (σ _ x) ⋯ᴿ (wk _) 

        _↑ˢ*_ : (S₁ →ˢ S₂) → ∀ S → ((S ++ S₁) →ˢ (S ++ S₂))
        σ ↑ˢ* [] = σ
        σ ↑ˢ* (s ∷ S) = (σ ↑ˢ* S) ↑ˢ s

        _⋯ˢ_ {m = V} x σ = σ _ x
        _⋯ˢ_ {m = T} t σ = [ T , _↑ˢ*_ ] t ⋯ σ

        _;_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
        (σ₁ ; σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂

        private variable
          t t₁ t₂ t₃ t₄ t′ : S ⊢ s
          x/t x/t₁ x/t₂ x/t₃ x/t₄ x/t′ : S ⊢[ m ] s

        _⋯ᴿˣ_ : S₁ ∋ s → S₁ →ᴿ S₂ → S₂ ⊢ s
        _⋯ᴿˣ_ = _⋯ᴿ_ {m = V}
        {-# INLINE _⋯ᴿˣ_ #-}
        
        _⋯ᴿᵗ_ : S₁ ⊢ s → S₁ →ᴿ S₂ → S₂ ⊢ s
        _⋯ᴿᵗ_ = _⋯ᴿ_ {m = T}
        {-# INLINE _⋯ᴿᵗ_ #-}

        _⋯ˢˣ_ : S₁ ∋ s → S₁ →ˢ S₂ → S₂ ⊢ s
        _⋯ˢˣ_ = _⋯ˢ_ {m = V}
        {-# INLINE _⋯ˢˣ_ #-}

        _⋯ˢᵗ_ : S₁ ⊢ s → S₁ →ˢ S₂ → S₂ ⊢ s
        _⋯ˢᵗ_ = _⋯ˢ_ {m = T}
        {-# INLINE _⋯ˢᵗ_ #-}

        [_]_⋯ᴿ_ : ∀ m → S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → S₂ ⊢ s
        [ m ] x/t ⋯ᴿ ρ = _⋯ᴿ_ {m = m} x/t ρ
        {-# INLINE [_]_⋯ᴿ_ #-}

        [_]_⋯ˢ_ : ∀ m → S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
        [ m ] x/t ⋯ˢ ρ = _⋯ˢ_ {m = m} x/t ρ
        {-# INLINE [_]_⋯ˢ_ #-}
        
        postulate
          beta-lift-id            : idᴿ {S = S} ↑ᴿ s ≡ idᴿ 

          beta-ext-zero           : zero ⋯ˢˣ (t ∙ σ)   ≡ t                             
          beta-ext-suc            : (suc x) ⋯ˢˣ (t ∙ σ)  ≡ x ⋯ˢˣ σ 

          associativity           : (σ₁ ; σ₂) ; σ₃                      ≡ σ₁ ; (σ₂ ; σ₃)                     
          distributivityˢ         : (t ∙ σ₁) ; σ₂                       ≡ ((t ⋯ˢ σ₂) ∙ (σ₁ ; σ₂)) 
          interact                : wkˢ s ; (t ∙ σ)                     ≡ σ                                        
          comp-idᵣ                : σ ; idˢ                             ≡ σ                                                                      
          η-id                    : (` zero {s = s} {S = S}) ∙ (wkˢ _)  ≡ idˢ
          η-lawˢ                  : (zero  ⋯ˢˣ σ) ∙ (wkˢ _ ; σ)          ≡ σ
          η-lawᴿ                  : (zero ⋯ᴿˣ ρ) ∙ ((wkˢ _ ; ⟪ ρ ⟫))     ≡ ⟪ ρ ⟫


          right-idˢ               : ∀ (t : S ⊢ s) → t ⋯ˢ idˢ                   ≡ t      
          right-idᴿ               : ∀ (t : S ⊢ s) → t ⋯ᴿ idᴿ                   ≡ t   
          compositionalityᴿˢ      : ∀ (x/t : S ⊢[ m ] s) → ([ m ] x/t ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ [ m ] x/t ⋯ˢ (⟪ ρ₁ ⟫ ; σ₂)                    
          compositionalityᴿᴿ      : ∀ (x/t : S ⊢[ m ] s) → ([ m ] x/t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ [ m ] x/t ⋯ᴿ (ρ₁ ∘ ρ₂)                     

          coincidence              : {x/t : S₁ ⊢[ m ] s} →
            [ m ] x/t ⋯ˢ ⟪ ρ ⟫ ≡ [ m ] x/t  ⋯ᴿ ρ
          comp-idₗ                : idˢ ; σ                             ≡ σ                        

          compositionalityˢᴿ      : ∀ (x/t : S ⊢[ m ] s) → ([ m ] x/t ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ [ m ] x/t ⋯ˢ (σ₁ ; ⟪ ρ₂ ⟫)                         
          compositionalityˢˢ      : ∀ (x/t : S ⊢[ m ] s) → ([ m ] x/t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ [ m ] x/t ⋯ˢ (σ₁ ; σ₂)

          coincidence-fold         : {x/t : (s′ ∷ S₁) ⊢[ m ] s} {x/t′ : S₁ ⊢[ m′ ] s′}  →
            [ m ] x/t ⋯ˢ (⟪ ρ ↑ᴿ s′ ⟫ ; (([ m′ ] x/t′ ⋯ᴿ ρ) ∙ idˢ))  ≡ [ m ] x/t ⋯ˢ (([ m′ ] x/t′ ⋯ᴿ ρ) ∙ ⟪ ρ ⟫)

          beta-lift               : σ ↑ˢ s            ≡ (` zero) ∙ (σ ; wkˢ _)
          distributivityᴿ         : (t ∙ σ₁) ; ⟪ ρ₂ ⟫                   ≡ ((t ⋯ᴿ ρ₂) ∙ (σ₁ ; ⟪ ρ₂ ⟫)) 





