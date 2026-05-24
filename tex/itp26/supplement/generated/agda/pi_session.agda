{-# OPTIONS --rewriting --confluence-check --double-check #-}
module pi_session where
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Data.String using (String)

data Const : Set where
  fork : Const
  recv send term : Const

cong1 : ∀ {A1 A2 : Set} (f : A1 → A2) {a1 a2} →
  a1 ≡ a2 → f a1 ≡ f a2
cong1 f refl = refl

cong2 : ∀ {A1 A2 A3 : Set} (f : A1 → A2 → A3) {a1 a2 a3 a4} →
  a1 ≡ a2 → a3 ≡ a4 → f a1 a3 ≡ f a2 a4
cong2 f refl refl = refl

open import Data.List using (List; []; _∷_; _++_)

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

data Mode : Set where 
  V T : Mode

private variable
  m  : Mode

data Sort : Set where 
  expr : Sort

Scope = List Sort

private variable 
  s s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort

data _⊢[_]_ : Scope → Mode → Sort → Set 

_⊢_ = _⊢[ T ]_
_∋_ = _⊢[ V ]_

data _⊢[_]_ where 
  zero : (s ∷ S) ∋ s
  suc  : S ∋ s → (s′ ∷ S) ∋ s
  var  : S ∋ s → S ⊢ s 

  ✶            : S ⊢ expr
  #_           : Const → S ⊢ expr
  ‵_           : String → S ⊢ expr
  λx_          : (expr ∷ S) ⊢ expr → S ⊢ expr
  ⟨_,_⟩        : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _·_          : S ⊢ expr → S ⊢ expr → S ⊢ expr
  let✶_ın_     : S ⊢ expr → S ⊢ expr → S ⊢ expr
  let⟨x,y⟩_ın_ : S ⊢ expr → (expr ∷ expr ∷ S) ⊢ expr → S ⊢ expr

private variable
  x x′     : S ∋ s
  t t′     : S ⊢ s
  x/t x/t′ : S ⊢[ m ] s

_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s 

private variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂

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

_↑ᴿ*_ : (S₁ →ᴿ S₂) → ∀ S → ((S ++ S₁) →ᴿ (S ++ S₂))
ρ ↑ᴿ* []      = ρ
ρ ↑ᴿ* (s ∷ S) = (ρ ↑ᴿ* S) ↑ᴿ s

opaque
  _⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → 
    S₂ ⊢[ m ] s 
  _⋯ᴿ_ {m = V} x   ρ  = ρ _ x
  (var x)         ⋯ᴿ ρ = var (ρ _ x)

  ✶                          ⋯ᴿ ρ = ✶
  (#_ const0)                ⋯ᴿ ρ = #_ const0
  (‵_ string0)               ⋯ᴿ ρ = ‵_ string0
  (λx_ expr0)                ⋯ᴿ ρ = λx_ (expr0 ⋯ᴿ (ρ ↑ᴿ* _))
  (⟨_,_⟩ expr0 expr1)        ⋯ᴿ ρ = ⟨_,_⟩ (expr0 ⋯ᴿ ρ) (expr1 ⋯ᴿ ρ)
  (_·_ expr0 expr1)          ⋯ᴿ ρ = _·_ (expr0 ⋯ᴿ ρ) (expr1 ⋯ᴿ ρ)
  (let✶_ın_ expr0 expr1)     ⋯ᴿ ρ = let✶_ın_ (expr0 ⋯ᴿ ρ) (expr1 ⋯ᴿ ρ)
  (let⟨x,y⟩_ın_ expr0 expr1) ⋯ᴿ ρ = let⟨x,y⟩_ın_ (expr0 ⋯ᴿ ρ) (expr1 ⋯ᴿ (ρ ↑ᴿ* _))

variable
  const0 : Const
  expr0 expr1 : S ⊢ expr
  string0 : String

_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s 

variable
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂  

opaque
  ⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂ 
  ⟨ ρ ⟩ _ x = var (ρ _ x)

idˢ : S →ˢ S
idˢ = ⟨ idᴿ ⟩
{-# INLINE idˢ #-}

wkˢ : ∀ s → S →ˢ (s ∷ S)
wkˢ _ = ⟨ wkᴿ _ ⟩
{-# INLINE wkˢ #-}

opaque  
  unfolding _⋯ᴿ_ 
  _∙ˢ_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂    
  _∙ˢ_  t σ _ zero = t
  (t ∙ˢ σ) _ (suc x) = σ _ x 

  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  σ ↑ˢ s =  (var zero) ∙ˢ λ _ x → (σ _ x) ⋯ᴿ wkᴿ _

_↑ˢ*_ : (S₁ →ˢ S₂) → ∀ S → ((S ++ S₁) →ˢ (S ++ S₂))
σ ↑ˢ* [] = σ
σ ↑ˢ* (s ∷ S) = (σ ↑ˢ* S) ↑ˢ s

opaque
  unfolding idᴿ _⋯ᴿ_ ⟨_⟩ _∙ˢ_
  _⋯ˢ_ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
  _⋯ˢ_ {m = V} x σ = σ _ x
  (var x) ⋯ˢ σ = σ _ x

  ✶                          ⋯ˢ σ = ✶
  (#_ const0)                ⋯ˢ σ = #_ const0
  (‵_ string0)               ⋯ˢ σ = ‵_ string0
  (λx_ expr0)                ⋯ˢ σ = λx_ (expr0 ⋯ˢ (σ ↑ˢ* _))
  (⟨_,_⟩ expr0 expr1)        ⋯ˢ σ = ⟨_,_⟩ (expr0 ⋯ˢ σ) (expr1 ⋯ˢ σ)
  (_·_ expr0 expr1)          ⋯ˢ σ = _·_ (expr0 ⋯ˢ σ) (expr1 ⋯ˢ σ)
  (let✶_ın_ expr0 expr1)     ⋯ˢ σ = let✶_ın_ (expr0 ⋯ˢ σ) (expr1 ⋯ˢ σ)
  (let⟨x,y⟩_ın_ expr0 expr1) ⋯ˢ σ = let⟨x,y⟩_ın_ (expr0 ⋯ˢ σ) (expr1 ⋯ˢ (σ ↑ˢ* _))

  _⨟_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂

  def-∙ˢ-zero           : zero ⋯ˢ (t ∙ˢ σ)   ≡ t                             
  def-∙ˢ-suc            : suc x ⋯ˢ (t ∙ˢ σ)  ≡ x ⋯ˢ σ 
  def-⨟ : (x ⋯ˢ (σ₁ ⨟ σ₂)) ≡ ((x ⋯ˢ σ₁) ⋯ˢ σ₂)
  def-↑ˢ               : σ ↑ˢ s ≡ (var zero) ∙ˢ (σ ⨟ wkˢ _)

  def-id                : x ⋯ᴿ idᴿ ≡ x
  def-wkᴿ                : x ⋯ᴿ (wkᴿ s) ≡ suc x  
  def-∙ᴿ-zero           : zero ⋯ᴿ (x ∙ᴿ ρ)     ≡ x         
  def-∙ᴿ-suc            : (suc x) ⋯ᴿ (x′ ∙ᴿ ρ)  ≡ x ⋯ᴿ ρ      
  def-∘                 : x ⋯ᴿ (ρ₁ ∘ ρ₂) ≡ (x ⋯ᴿ ρ₁) ⋯ᴿ ρ₂

  assoc : (σ₁ ⨟ σ₂) ⨟ σ₃ ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  dist : (t ∙ˢ σ₁)  ⨟ σ₂  ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ⨟ σ₂)) 
  interact                : wkˢ s ⨟ (t ∙ˢ σ) ≡ σ                                        
  comp-idᵣ                : σ ⨟ idˢ         ≡ σ                                               
  comp-idₗ                : idˢ ⨟ σ         ≡ σ                                               
  η-id    : (var (zero {s} {S})) ∙ˢ (wkˢ _)      ≡ idˢ
  η-law  : (zero ⋯ˢ σ) ∙ˢ (wkˢ _ ⨟ σ)        ≡ σ

  assocᴿ           : (ρ₁ ∘ ρ₂) ∘ ρ₃ ≡ ρ₁ ∘ (ρ₂ ∘ ρ₃)                     
  distᴿ : (x ∙ᴿ ρ₁)  ∘ ρ₂  ≡ ((x ⋯ᴿ ρ₂) ∙ᴿ (ρ₁ ∘ ρ₂)) 
  interactᴿ                : wkᴿ s ∘ (x ∙ᴿ ρ) ≡ ρ                                        
  comp-idᵣᴿ                : ρ ∘ idᴿ         ≡ ρ                                               
  comp-idₗᴿ                : idᴿ ∘ ρ         ≡ ρ                                               
  η-idᴿ    : (zero {s} {S}) ∙ᴿ (wkᴿ _)      ≡ idᴿ
  η-lawᴿ  : (zero ⋯ᴿ ρ) ∙ᴿ (wkᴿ _ ∘ ρ)        ≡ ρ

  right-id                : ∀ (t : S ⊢ s) → t ⋯ᴿ idᴿ                   ≡ t   
  compositionalityᴿᴿ      : ∀ (t : S ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ t ⋯ᴿ (ρ₁ ∘ ρ₂)     
  compositionalityᴿˢ      : ∀ (t : S ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ t ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                                    
  compositionalityˢᴿ      : ∀ (t : S ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ t ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
  compositionalityˢˢ      : ∀ (t : S ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ t ⋯ˢ (σ₁ ⨟ σ₂)


  inst-var           : (var x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  inst-var = refl

  instᴿ-var           : (var x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  instᴿ-var = refl

  instᴿ-✶            : ✶ ⋯ᴿ ρ                          ≡ ✶
  instᴿ-✶            = refl
  instᴿ-#_           : (#_ const0) ⋯ᴿ ρ                ≡ #_ const0
  instᴿ-#_           = refl
  instᴿ-‵_           : (‵_ string0) ⋯ᴿ ρ               ≡ ‵_ string0
  instᴿ-‵_           = refl
  instᴿ-λx_          : (λx_ expr0) ⋯ᴿ ρ                ≡ λx_ (expr0 ⋯ᴿ (ρ ↑ᴿ* (expr ∷ [])))
  instᴿ-λx_          = refl
  instᴿ-⟨_,_⟩        : (⟨_,_⟩ expr0 expr1) ⋯ᴿ ρ        ≡ ⟨_,_⟩ (expr0 ⋯ᴿ ρ) (expr1 ⋯ᴿ ρ)
  instᴿ-⟨_,_⟩        = refl
  instᴿ-_·_          : (_·_ expr0 expr1) ⋯ᴿ ρ          ≡ _·_ (expr0 ⋯ᴿ ρ) (expr1 ⋯ᴿ ρ)
  instᴿ-_·_          = refl
  instᴿ-let✶_ın_     : (let✶_ın_ expr0 expr1) ⋯ᴿ ρ     ≡ let✶_ın_ (expr0 ⋯ᴿ ρ) (expr1 ⋯ᴿ ρ)
  instᴿ-let✶_ın_     = refl
  instᴿ-let⟨x,y⟩_ın_ : (let⟨x,y⟩_ın_ expr0 expr1) ⋯ᴿ ρ ≡ let⟨x,y⟩_ın_ (expr0 ⋯ᴿ ρ) (expr1 ⋯ᴿ (ρ ↑ᴿ* (expr ∷ expr ∷ [])))
  instᴿ-let⟨x,y⟩_ın_ = refl
  inst-✶            : ✶ ⋯ˢ σ                          ≡ ✶
  inst-✶            = refl
  inst-#_           : (#_ const0) ⋯ˢ σ                ≡ #_ const0
  inst-#_           = refl
  inst-‵_           : (‵_ string0) ⋯ˢ σ               ≡ ‵_ string0
  inst-‵_           = refl
  inst-λx_          : (λx_ expr0) ⋯ˢ σ                ≡ λx_ (expr0 ⋯ˢ (σ ↑ˢ* (expr ∷ [])))
  inst-λx_          = refl
  inst-⟨_,_⟩        : (⟨_,_⟩ expr0 expr1) ⋯ˢ σ        ≡ ⟨_,_⟩ (expr0 ⋯ˢ σ) (expr1 ⋯ˢ σ)
  inst-⟨_,_⟩        = refl
  inst-_·_          : (_·_ expr0 expr1) ⋯ˢ σ          ≡ _·_ (expr0 ⋯ˢ σ) (expr1 ⋯ˢ σ)
  inst-_·_          = refl
  inst-let✶_ın_     : (let✶_ın_ expr0 expr1) ⋯ˢ σ     ≡ let✶_ın_ (expr0 ⋯ˢ σ) (expr1 ⋯ˢ σ)
  inst-let✶_ın_     = refl
  inst-let⟨x,y⟩_ın_ : (let⟨x,y⟩_ın_ expr0 expr1) ⋯ˢ σ ≡ let⟨x,y⟩_ın_ (expr0 ⋯ˢ σ) (expr1 ⋯ˢ (σ ↑ˢ* (expr ∷ expr ∷ [])))
  inst-let⟨x,y⟩_ın_ = refl

  coincidence     : t ⋯ˢ ⟨ ρ ⟩ ≡ t ⋯ᴿ ρ
  coincidence-var : x ⋯ˢ ⟨ ρ ⟩ ≡ var (x ⋯ᴿ ρ)

  def-∙ˢ-zero = refl
  def-∙ˢ-suc  = refl
  def-↑ˢ {σ = σ} = cong1 ((var zero) ∙ˢ_) (sym (ext λ x → coincidence {t = (σ _ x)}))
  def-⨟      = refl

  def-id      = refl
  def-wkᴿ      = refl      
  def-∙ᴿ-zero = refl
  def-∙ᴿ-suc  = refl
  def-∘       = refl

  η-lawˢᴿ  : (var (zero ⋯ᴿ ρ)) ∙ˢ (wkˢ _ ⨟ ⟨ ρ ⟩)  ≡ ⟨ ρ ⟩
  η-lawˢᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-idˢ* : ∀ S → (idˢ {S = S₁} ↑ˢ* S) ≡ idˢ 
  lift-idˢ* []    = refl
  lift-idˢ* {S₁} (_ ∷ S) rewrite lift-idˢ* {S₁} S = η-lawˢᴿ

  right-idˢ               : ∀ (t : S ⊢ s) → t ⋯ˢ idˢ                   ≡ t 
  right-idˢ (var x)        = refl
  right-idˢ ✶                          = refl
  right-idˢ (#_ const0)                = cong1 #_ refl
  right-idˢ (‵_ string0)               = cong1 ‵_ refl
  right-idˢ (λx_ expr0)                = cong1 λx_ (trans (cong1 (expr0 ⋯ˢ_) (lift-idˢ* (expr ∷ []))) (right-idˢ expr0))
  right-idˢ (⟨_,_⟩ expr0 expr1)        = cong2 ⟨_,_⟩ (right-idˢ expr0) (right-idˢ expr1)
  right-idˢ (_·_ expr0 expr1)          = cong2 _·_ (right-idˢ expr0) (right-idˢ expr1)
  right-idˢ (let✶_ın_ expr0 expr1)     = cong2 let✶_ın_ (right-idˢ expr0) (right-idˢ expr1)
  right-idˢ (let⟨x,y⟩_ın_ expr0 expr1) = cong2 let⟨x,y⟩_ın_ (right-idˢ expr0) (trans (cong1 (expr1 ⋯ˢ_) (lift-idˢ* (expr ∷ expr ∷ []))) (right-idˢ expr1))

  assoc {σ₁ = σ₁} = ext λ x → compositionalityˢˢ (σ₁ _ x) 
  dist = ext λ { zero → refl; (suc x) → refl }
  interact        = refl
  comp-idᵣ        = ext λ x → (right-idˢ _)
  comp-idₗ        = refl
  η-id            = ext λ { zero → refl; (suc x) → refl }
  η-law          = ext λ { zero → refl; (suc x) → refl }

  assocᴿ = refl
  distᴿ = ext λ { zero → refl; (suc x) → refl }
  interactᴿ = refl
  comp-idᵣᴿ = refl
  comp-idₗᴿ = refl
  η-idᴿ = ext λ { zero → refl; (suc x) → refl }
  η-lawᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-id : idᴿ {S = S} ↑ᴿ s ≡ idᴿ
  lift-id = ext λ { zero → refl; (suc x) → refl }

  lift-id* : ∀ S → (idᴿ {S = S₁} ↑ᴿ* S) ≡ idᴿ
  lift-id* []    = refl
  lift-id* {S₁}  (_ ∷ S) rewrite lift-id* {S₁} S = lift-id

  right-id (var x)        = refl
  right-id ✶                          = refl
  right-id (#_ const0)                = cong1 #_ refl
  right-id (‵_ string0)               = cong1 ‵_ refl
  right-id (λx_ expr0)                = cong1 λx_ (trans (cong1 (expr0 ⋯ᴿ_) (lift-id* (expr ∷ []))) (right-id expr0))
  right-id (⟨_,_⟩ expr0 expr1)        = cong2 ⟨_,_⟩ (right-id expr0) (right-id expr1)
  right-id (_·_ expr0 expr1)          = cong2 _·_ (right-id expr0) (right-id expr1)
  right-id (let✶_ın_ expr0 expr1)     = cong2 let✶_ın_ (right-id expr0) (right-id expr1)
  right-id (let⟨x,y⟩_ın_ expr0 expr1) = cong2 let⟨x,y⟩_ın_ (right-id expr0) (trans (cong1 (expr1 ⋯ᴿ_) (lift-id* (expr ∷ expr ∷ []))) (right-id expr1))

  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿᴿ : ∀ S → ((ρ₁ ↑ᴿ* S) ∘ (ρ₂ ↑ᴿ* S)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ* S)
  lift-dist-comp*ᴿᴿ []      = refl 
  lift-dist-comp*ᴿᴿ (_ ∷ S) = trans lift-dist-compᴿᴿ (cong1 (_↑ᴿ _) (lift-dist-comp*ᴿᴿ S))

  compositionalityᴿᴿ (var x)  = refl
  compositionalityᴿᴿ ✶                           = refl
  compositionalityᴿᴿ  (#_ const0)                = cong1 #_ refl
  compositionalityᴿᴿ  (‵_ string0)               = cong1 ‵_ refl
  compositionalityᴿᴿ  (λx_ expr0)                = cong1 λx_ (trans (compositionalityᴿᴿ expr0) (cong1 (expr0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (expr ∷ []))))
  compositionalityᴿᴿ  (⟨_,_⟩ expr0 expr1)        = cong2 ⟨_,_⟩ (compositionalityᴿᴿ expr0) (compositionalityᴿᴿ expr1)
  compositionalityᴿᴿ  (_·_ expr0 expr1)          = cong2 _·_ (compositionalityᴿᴿ expr0) (compositionalityᴿᴿ expr1)
  compositionalityᴿᴿ  (let✶_ın_ expr0 expr1)     = cong2 let✶_ın_ (compositionalityᴿᴿ expr0) (compositionalityᴿᴿ expr1)
  compositionalityᴿᴿ  (let⟨x,y⟩_ın_ expr0 expr1) = cong2 let⟨x,y⟩_ın_ (compositionalityᴿᴿ expr0) (trans (compositionalityᴿᴿ expr1) (cong1 (expr1 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (expr ∷ expr ∷ []))))

  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ {σ₂ = σ₂} (_ ∷ S) = trans (lift-dist-compᴿˢ {σ₂ = σ₂ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} S))

  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ ✶                                    = refl
  compositionalityᴿˢ {σ₂ = σ₂} (#_ const0)                = cong1 #_ refl
  compositionalityᴿˢ {σ₂ = σ₂} (‵_ string0)               = cong1 ‵_ refl
  compositionalityᴿˢ {σ₂ = σ₂} (λx_ expr0)                = cong1 λx_ (trans (compositionalityᴿˢ expr0) (cong1 (expr0 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (expr ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (⟨_,_⟩ expr0 expr1)        = cong2 ⟨_,_⟩ (compositionalityᴿˢ expr0) (compositionalityᴿˢ expr1)
  compositionalityᴿˢ {σ₂ = σ₂} (_·_ expr0 expr1)          = cong2 _·_ (compositionalityᴿˢ expr0) (compositionalityᴿˢ expr1)
  compositionalityᴿˢ {σ₂ = σ₂} (let✶_ın_ expr0 expr1)     = cong2 let✶_ın_ (compositionalityᴿˢ expr0) (compositionalityᴿˢ expr1)
  compositionalityᴿˢ {σ₂ = σ₂} (let⟨x,y⟩_ın_ expr0 expr1) = cong2 let⟨x,y⟩_ın_ (compositionalityᴿˢ expr0) (trans (compositionalityᴿˢ expr1) (cong1 (expr1 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (expr ∷ expr ∷ []))))

  lift-dist-compˢᴿ : ((σ₁ ↑ˢ s) ⨟ ⟨ ρ₂ ↑ᴿ s ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ s)
  lift-dist-compˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    (t ⋯ᴿ (wkᴿ _)) ⋯ˢ ⟨ ρ₂ ↑ᴿ _ ⟩ ≡⟨ coincidence {t = t ⋯ᴿ (wkᴿ _)} ⟩ 
    (t ⋯ᴿ (wkᴿ _)) ⋯ᴿ (ρ₂ ↑ᴿ _)   ≡⟨ compositionalityᴿᴿ t ⟩ 
    t ⋯ᴿ (wkᴿ _ ∘ (ρ₂ ↑ᴿ _))    ≡⟨ sym (compositionalityᴿᴿ t) ⟩ 
    (t ⋯ᴿ ρ₂) ⋯ᴿ wkᴿ _          ≡⟨ cong1 (_⋯ᴿ (wkᴿ _)) (sym (coincidence {t = t})) ⟩ 
    (t ⋯ˢ ⟨ ρ₂ ⟩) ⋯ᴿ wkᴿ _      ∎ }

  lift-dist-compˢ*ᴿ : ∀ S → ((σ₁ ↑ˢ* S) ⨟ ⟨ ρ₂ ↑ᴿ* S ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ* S )
  lift-dist-compˢ*ᴿ []      = refl 
  lift-dist-compˢ*ᴿ {σ₁ = σ₁} (_ ∷ S) =  trans (lift-dist-compˢᴿ {σ₁ = σ₁ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-compˢ*ᴿ {σ₁ = σ₁} S))
 
  compositionalityˢᴿ {σ₁ = σ₁} (var x)  = sym (coincidence {t = σ₁ _ x})
  compositionalityˢᴿ ✶                                    = refl
  compositionalityˢᴿ {σ₁ = σ₁} (#_ const0)                = cong1 #_ refl
  compositionalityˢᴿ {σ₁ = σ₁} (‵_ string0)               = cong1 ‵_ refl
  compositionalityˢᴿ {σ₁ = σ₁} (λx_ expr0)                = cong1 λx_ (trans (compositionalityˢᴿ expr0) (cong1 (expr0 ⋯ˢ_) (lift-dist-compˢ*ᴿ {σ₁ = σ₁} (expr ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (⟨_,_⟩ expr0 expr1)        = cong2 ⟨_,_⟩ (compositionalityˢᴿ expr0) (compositionalityˢᴿ expr1)
  compositionalityˢᴿ {σ₁ = σ₁} (_·_ expr0 expr1)          = cong2 _·_ (compositionalityˢᴿ expr0) (compositionalityˢᴿ expr1)
  compositionalityˢᴿ {σ₁ = σ₁} (let✶_ın_ expr0 expr1)     = cong2 let✶_ın_ (compositionalityˢᴿ expr0) (compositionalityˢᴿ expr1)
  compositionalityˢᴿ {σ₁ = σ₁} (let⟨x,y⟩_ın_ expr0 expr1) = cong2 let⟨x,y⟩_ın_ (compositionalityˢᴿ expr0) (trans (compositionalityˢᴿ expr1) (cong1 (expr1 ⋯ˢ_) (lift-dist-compˢ*ᴿ {σ₁ = σ₁} (expr ∷ expr ∷ []))))
  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s)
  lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    begin
    (t ⋯ᴿ (wkᴿ _)) ⋯ˢ (σ₂ ↑ˢ _)    ≡⟨ compositionalityᴿˢ t ⟩ 
    t ⋯ˢ (⟨ (wkᴿ _) ⟩ ⨟ (σ₂ ↑ˢ _)) ≡⟨ cong1 (t ⋯ˢ_) (ext λ x → sym (coincidence {t = σ₂ _ x})) ⟩   
    t ⋯ˢ (σ₂ ⨟ ⟨ (wkᴿ _) ⟩)        ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
    (t ⋯ˢ σ₂) ⋯ᴿ (wkᴿ _)           ∎ }
  
  lift-dist-compˢ*ˢ : ∀ S →  ((σ₁ ↑ˢ* S) ⨟ (σ₂ ↑ˢ* S)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ* S)
  lift-dist-compˢ*ˢ []      = refl 
  lift-dist-compˢ*ˢ  {σ₁ = σ₁} {σ₂ = σ₂} (_ ∷ S) =  trans (lift-dist-compˢˢ {σ₁ = σ₁ ↑ˢ* S} {σ₂ = σ₂ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-compˢ*ˢ {σ₁ = σ₁} {σ₂ = σ₂} S))

  compositionalityˢˢ (var x)  = refl
  compositionalityˢˢ ✶                                              = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (#_ const0)                = cong1 #_ refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (‵_ string0)               = cong1 ‵_ refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (λx_ expr0)                = cong1 λx_ (trans (compositionalityˢˢ expr0) (cong1 (expr0 ⋯ˢ_) (lift-dist-compˢ*ˢ {σ₁ = σ₁} {σ₂ = σ₂} (expr ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (⟨_,_⟩ expr0 expr1)        = cong2 ⟨_,_⟩ (compositionalityˢˢ expr0) (compositionalityˢˢ expr1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (_·_ expr0 expr1)          = cong2 _·_ (compositionalityˢˢ expr0) (compositionalityˢˢ expr1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (let✶_ın_ expr0 expr1)     = cong2 let✶_ın_ (compositionalityˢˢ expr0) (compositionalityˢˢ expr1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (let⟨x,y⟩_ın_ expr0 expr1) = cong2 let⟨x,y⟩_ın_ (compositionalityˢˢ expr0) (trans (compositionalityˢˢ expr1) (cong1 (expr1 ⋯ˢ_) (lift-dist-compˢ*ˢ {σ₁ = σ₁} {σ₂ = σ₂} (expr ∷ expr ∷ []))))

  coincidence {t = t} {ρ = ρ} = 
    t ⋯ˢ (⟨ ρ ⟩ ⨟ idˢ) ≡⟨ sym (compositionalityᴿˢ t) ⟩ 
    (t ⋯ᴿ ρ) ⋯ˢ idˢ    ≡⟨ right-idˢ _ ⟩ 
    t ⋯ᴿ ρ             ∎

  coincidence-var = refl

{-# REWRITE
  def-∙ˢ-zero def-∙ˢ-suc def-↑ˢ def-⨟   
  assoc dist interact       
  comp-idᵣ comp-idₗ η-id η-law
  right-id         
  compositionalityᴿᴿ compositionalityᴿˢ
  compositionalityˢᴿ compositionalityˢˢ
  coincidence 

  inst-var instᴿ-var
  inst-✶ instᴿ-✶
  inst-#_ instᴿ-#_
  inst-‵_ instᴿ-‵_
  inst-λx_ instᴿ-λx_
  inst-⟨_,_⟩ instᴿ-⟨_,_⟩
  inst-_·_ instᴿ-_·_
  inst-let✶_ın_ instᴿ-let✶_ın_
  inst-let⟨x,y⟩_ın_ instᴿ-let⟨x,y⟩_ın_
  def-id def-wkᴿ def-∙ᴿ-zero def-∙ᴿ-suc def-∘      
  assocᴿ distᴿ interactᴿ       
  comp-idᵣᴿ comp-idₗᴿ η-idᴿ η-lawᴿ
  coincidence-var
#-}
