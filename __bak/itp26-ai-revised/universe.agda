{-# OPTIONS --rewriting --double-check --local-confluence-check #-}
module universe where

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
open import Data.List using (List; []; _∷_; _++_; drop)
open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)

data Sort : Set where  expr type kind : Sort 

variable 
  s s₁ s₂ s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort

Scope = List Sort
data Mode : Set where  V T : Mode

variable
  m  : Mode

Scoped = Scope → Sort → Set

data Desc : Set₁ where
  `σ : (A : Set) → (A → Desc) → Desc
  `X : Scope → Sort → Desc → Desc
  `■ : Sort → Desc

variable
  d′ : Desc

⟦_⟧ : Desc → Scoped → Scoped
⟦ `σ A d      ⟧ X S s = Σ[ a ∈ A ] (⟦ d a ⟧ X S s)
⟦ `X S′ s′ d  ⟧ X S s = X (S′ ++ S) s′ × ⟦ d ⟧ X S s
⟦ `■ s′ ⟧ X S s = s ≡ s′
  
data Tm (d : Desc) : Mode → Scope → Sort → Set where
  zero : Tm d V (s ∷ S) s
  suc  : Tm d V S s → Tm d V (s′ ∷ S) s
  var : Tm d V S s → Tm d T S s
  con : ⟦ d ⟧ (Tm d T) S s → Tm d T S s
  
module _ (d : Desc) where 
  _⊢[_]_ : Scope → Mode → Sort → Set
  S ⊢[ m ] s = Tm d m S s
  
  _⊢_ = _⊢[ T ]_
  _∋_ = _⊢[ V ]_

  `_ : S ∋ s → S ⊢ s
  `_ = var

  variable
    x x′ : S ∋ s
    t t₁ t₂ t′ : S ⊢ s
    x/t x/t′ : S ⊢[ m ] s

  _→ᴿ_ : Scope → Scope → Set
  S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s 

  variable
    ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂

  idᴿ : S →ᴿ S
  idᴿ _ x = x

  wk : ∀ s → S →ᴿ (s ∷ S)
  wk _ _ = suc

  _∘_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
  (ρ₁ ∘ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

  _↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → 
    ((s ∷ S₁) →ᴿ (s ∷ S₂))
  (ρ ↑ᴿ _) _ zero    = zero
  (ρ ↑ᴿ _) _ (suc x) = suc (ρ _ x)

  _↑ᴿ*_ : (S₁ →ᴿ S₂) → ∀ S → ((S ++ S₁) →ᴿ (S ++ S₂))
  ρ ↑ᴿ* []      = ρ
  ρ ↑ᴿ* (s ∷ S) = (ρ ↑ᴿ* S) ↑ᴿ s

  _⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → S₂ ⊢ s 
  _⋯ᴿ′_ : ⟦ d′ ⟧ (Tm d T) S₁ s → S₁ →ᴿ S₂ → ⟦ d′ ⟧ (Tm d T) S₂ s
  _⋯ᴿ_ {m = V} x   ρ = ` (ρ _ x)
  (var x) ⋯ᴿ ρ = ` (ρ _ x)
  (con t) ⋯ᴿ ρ = con (t ⋯ᴿ′ ρ)
  _⋯ᴿ′_ {d′ = `σ A d′}     (a , D′) ρ = a , D′ ⋯ᴿ′ ρ
  _⋯ᴿ′_ {d′ = `X S′ M′ d′} (e , e′) ρ = e ⋯ᴿ (ρ ↑ᴿ* S′) , e′ ⋯ᴿ′ ρ
  _⋯ᴿ′_ {d′ = `■ M′}       e        ρ = e

  _→ˢ_ : Scope → Scope → Set
  S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s 

  --! [
  variable
    σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂  
  --! ]
  ⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂ 
  ⟨ ρ ⟩ _ x = ` ρ _ x
  {-# INLINE ⟨_⟩ #-}

  idˢ : S →ˢ S
  idˢ _ = `_
  {-# INLINE idˢ #-}

  wkˢ : ∀ s → S →ˢ (s ∷ S)
  wkˢ _ = ⟨ wk _ ⟩
  {-# INLINE wkˢ #-}

  opaque  
    _∙_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂    
    (t ∙ σ) _ zero = t
    (t ∙ σ) _ (suc x) = σ _ x 

    _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
    σ ↑ˢ s =  (` zero) ∙ λ s₁ x → (σ _ x) ⋯ᴿ wk _

  _↑ˢ*_ : (S₁ →ˢ S₂) → ∀ S → ((S ++ S₁) →ˢ (S ++ S₂))
  σ ↑ˢ* [] = σ
  σ ↑ˢ* (s ∷ S) = (σ ↑ˢ* S) ↑ˢ s

  opaque
    unfolding  _∙_ _↑ˢ_
    _⋯ˢ_ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
    _⋯ˢ′_ : ⟦ d′ ⟧ (Tm d T) S₁ s → S₁ →ˢ S₂ → ⟦ d′ ⟧ (Tm d T) S₂ s
    _⋯ˢ_ {m = V} x σ = σ _ x
    (var x) ⋯ˢ σ = (σ _ x)
    con t ⋯ˢ σ = con (t ⋯ˢ′ σ)
    _⋯ˢ′_ {d′ = `σ A d′}     (a , D′) σ = a , D′ ⋯ˢ′ σ
    _⋯ˢ′_ {d′ = `X S′ M′ d′} (e , e′) σ = e ⋯ˢ (σ ↑ˢ* S′) , e′ ⋯ˢ′ σ
    _⋯ˢ′_ {d′ = `■ M′}       e        σ = e

    _⨟_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
    (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂

    lift-id            : idᴿ {S = S} ↑ᴿ s ≡ idᴿ 
    def-ext-zero           : zero ⋯ˢ (t ∙ σ)   ≡ t                             
    def-ext-suc            : suc x ⋯ˢ (t ∙ σ)  ≡ x ⋯ˢ σ 
    def-lift               : σ ↑ˢ s ≡ (` zero) ∙ (σ ⨟ wkˢ _)

    associativity           : (σ₁ ⨟ σ₂)  ⨟ σ₃ ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
    distributivity          : (t ∙ σ₁)  ⨟ σ₂  ≡ ((t ⋯ˢ σ₂) ∙ (σ₁ ⨟ σ₂)) 
    interact                : wkˢ s ⨟ (t ∙ σ) ≡ σ                                        
    comp-idᵣ                : σ ⨟ idˢ         ≡ σ                                               
    comp-idₗ                : idˢ ⨟ σ         ≡ σ                                               
    η-id                    : (` zero {s = s} {S = S}) ∙ (wkˢ _)      ≡ idˢ
    η-lawˢ                  : (zero ⋯ˢ σ) ∙ (wkˢ _ ⨟ σ)        ≡ σ
    η-lawᴿ                  : (zero ⋯ᴿ ρ) ∙ ((wkˢ _ ⨟ ⟨ ρ ⟩))  ≡ ⟨ ρ ⟩

    right-id : ∀ (t : S ⊢ s) → t ⋯ᴿ idᴿ                   ≡ t   
    compositionalityᴿˢ      : ∀ (x/t : S ⊢[ m ] s) → 
      (x/t ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ x/t ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                    
    compositionalityᴿᴿ      : ∀ (x/t : S ⊢[ m ] s) → 
      (x/t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ x/t ⋯ᴿ (ρ₁ ∘ ρ₂)                     
    compositionalityˢᴿ      : ∀ (x/t : S ⊢[ m ] s) → 
      (x/t ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ x/t ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
    compositionalityˢˢ      : ∀ (x/t : S ⊢[ m ] s) → 
      (x/t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ x/t ⋯ˢ (σ₁ ⨟ σ₂)

    traversal-x             : (var x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
    traversal-t             : t ⋯ˢ σ  ≡ {!   !}

    coincidence              : x/t ⋯ˢ ⟨ ρ ⟩ ≡ x/t ⋯ᴿ ρ
    coincidence-fold         : 
      x/t ⋯ˢ (⟨ ρ ↑ᴿ s ⟩ ⨟ ((x/t′ ⋯ᴿ ρ) ∙ idˢ))  ≡ 
      x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩)

    right-idˢ               : ∀ (t : S ⊢ s) → t ⋯ˢ idˢ                   ≡ t      

    {- lift-id = ext λ { zero → refl; (suc x) → refl }

    def-ext-zero = refl
    def-ext-suc  = refl
    def-lift     = cong ((` zero) ∙_) (sym (ext λ x → coincidence))

    associativity {σ₁ = σ₁} = ext λ x → compositionalityˢˢ (σ₁ _ x) 
    distributivity = ext λ { zero → refl; (suc x) → refl }

    interact = refl
    comp-idᵣ = ext λ x → (right-idˢ _)
    comp-idₗ = refl
    η-id     = ext λ { zero → refl; (suc x) → refl }
    η-lawˢ   = ext λ { zero → refl; (suc x) → refl }
    η-lawᴿ   = ext λ { zero → refl; (suc x) → refl }

    lift-idˢ* : ∀ S → (idˢ {S = S₁} ↑ˢ* S) ≡ idˢ 
    lift-idˢ* []    = refl
    lift-idˢ* {S₁} (_ ∷ S) rewrite lift-idˢ* {S₁} S = η-lawᴿ

    lift-id* : ∀ S → (idᴿ {S = S₁} ↑ᴿ* S) ≡ idᴿ
    lift-id* []    = refl
    lift-id* {S₁}  (_ ∷ S) rewrite lift-id* {S₁} S = lift-id

    right-id (var x)        = refl
    right-id t       = {!   !}

    right-idˢ (var x)        = refl
    right-idˢ t       = {!   !}

    lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
    lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }
    compositionalityᴿᴿ {m = V}             x            = refl
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (var x)        = refl
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} t       = {!   !}

    lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
    lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }
    compositionalityᴿˢ {m = V}              x            = refl
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} t        = {!   !}

    lift-dist-compˢᴿ : ((σ₁ ↑ˢ s) ⨟ ⟨ ρ₂ ↑ᴿ s ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ s)
    lift-dist-compˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} = ext λ { zero → refl; (suc x) → 
      let t = σ₁ _ x in
      (t ⋯ᴿ (wk _)) ⋯ˢ ⟨ ρ₂ ↑ᴿ _ ⟩ ≡⟨ coincidence ⟩ 
      (t ⋯ᴿ (wk _)) ⋯ᴿ (ρ₂ ↑ᴿ _)   ≡⟨ compositionalityᴿᴿ t ⟩ 
      t ⋯ᴿ (wk _ ∘ (ρ₂ ↑ᴿ _))    ≡⟨ sym (compositionalityᴿᴿ t) ⟩ 
      (t ⋯ᴿ ρ₂) ⋯ᴿ wk _          ≡⟨ cong (_⋯ᴿ (wk _)) (sym coincidence) ⟩ 
      (t ⋯ˢ ⟨ ρ₂ ⟩) ⋯ᴿ wk _      ∎ }
    compositionalityˢᴿ {m = V}              x            = sym coincidence
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (var x)         = sym coincidence
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} t        = {!   !}

    lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s)
    lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl; (suc x) → 
      let t = σ₁ _ x in
      begin
      (t ⋯ᴿ (wk _)) ⋯ˢ (σ₂ ↑ˢ _)    ≡⟨ compositionalityᴿˢ t ⟩ 
      t ⋯ˢ (⟨ (wk _) ⟩ ⨟ (σ₂ ↑ˢ _)) ≡⟨ cong (t ⋯ˢ_) (ext λ y → sym coincidence) ⟩   
      t ⋯ˢ (σ₂ ⨟ ⟨ (wk _) ⟩)        ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
      (t ⋯ˢ σ₂) ⋯ᴿ (wk _)           ∎ }
    compositionalityˢˢ {m = V}              x           = refl
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (var x)        = refl
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} t       = {!   !}

    coincidence {x/t = x/t} {ρ = ρ} = 
      x/t ⋯ˢ (⟨ ρ ⟩ ⨟ idˢ) ≡⟨ sym (compositionalityᴿˢ x/t) ⟩ 
      (x/t ⋯ᴿ ρ) ⋯ˢ idˢ    ≡⟨ right-idˢ _ ⟩ 
      x/t ⋯ᴿ ρ             ∎

    coincidence-fold {x/t = x/t} {ρ = ρ} {x/t′ = x/t′} = 
      (x/t ⋯ˢ (⟨ ρ ↑ᴿ _ ⟩ ⨟ ((x/t′ ⋯ᴿ ρ) ∙ idˢ))) ≡⟨ cong (x/t ⋯ˢ_) (ext λ { zero → refl; (suc x) → refl }) ⟩ 
      (x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩))              ∎

  {-# REWRITE 
  lift-id def-ext-zero def-ext-suc def-lift    

  associativity distributivity interact       
  comp-idᵣ comp-idₗ η-id η-lawˢ η-lawᴿ      

  traversal-x traversal-t

  right-id         
  compositionalityᴿˢ compositionalityᴿᴿ
  compositionalityˢᴿ compositionalityˢˢ

  coincidence coincidence-fold 
  #-} 
 -}