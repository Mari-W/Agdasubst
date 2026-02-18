{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module cps where
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

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
  typ exp val : Sort

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

  imp    : S ⊢ typ → S ⊢ typ → S ⊢ typ
  and    : S ⊢ typ → S ⊢ typ → S ⊢ typ
  unit   : S ⊢ typ
  value  : S ⊢ val → S ⊢ exp
  lam    : (val ∷ S) ⊢ exp → S ⊢ val
  app    : S ⊢ exp → S ⊢ exp → S ⊢ exp
  mkpair : S ⊢ exp → S ⊢ exp → S ⊢ exp
  pair   : S ⊢ val → S ⊢ val → S ⊢ val
  fst    : S ⊢ exp → S ⊢ exp
  snd    : S ⊢ exp → S ⊢ exp
  one    : S ⊢ val
  letC   : S ⊢ exp → (val ∷ S) ⊢ exp → S ⊢ exp

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

  (imp typ0 typ1)    ⋯ᴿ ρ = imp (typ0 ⋯ᴿ ρ) (typ1 ⋯ᴿ ρ)
  (and typ0 typ1)    ⋯ᴿ ρ = and (typ0 ⋯ᴿ ρ) (typ1 ⋯ᴿ ρ)
  unit               ⋯ᴿ ρ = unit
  (value val0)       ⋯ᴿ ρ = value (val0 ⋯ᴿ ρ)
  (lam exp0)         ⋯ᴿ ρ = lam (exp0 ⋯ᴿ (ρ ↑ᴿ* _))
  (app exp0 exp1)    ⋯ᴿ ρ = app (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ)
  (mkpair exp0 exp1) ⋯ᴿ ρ = mkpair (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ)
  (pair val0 val1)   ⋯ᴿ ρ = pair (val0 ⋯ᴿ ρ) (val1 ⋯ᴿ ρ)
  (fst exp0)         ⋯ᴿ ρ = fst (exp0 ⋯ᴿ ρ)
  (snd exp0)         ⋯ᴿ ρ = snd (exp0 ⋯ᴿ ρ)
  one                ⋯ᴿ ρ = one
  (letC exp0 exp1)   ⋯ᴿ ρ = letC (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ (ρ ↑ᴿ* _))

variable
  exp0 exp1 : S ⊢ exp
  typ0 typ1 : S ⊢ typ
  val0 val1 : S ⊢ val

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

  (imp typ0 typ1)    ⋯ˢ σ = imp (typ0 ⋯ˢ σ) (typ1 ⋯ˢ σ)
  (and typ0 typ1)    ⋯ˢ σ = and (typ0 ⋯ˢ σ) (typ1 ⋯ˢ σ)
  unit               ⋯ˢ σ = unit
  (value val0)       ⋯ˢ σ = value (val0 ⋯ˢ σ)
  (lam exp0)         ⋯ˢ σ = lam (exp0 ⋯ˢ (σ ↑ˢ* _))
  (app exp0 exp1)    ⋯ˢ σ = app (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  (mkpair exp0 exp1) ⋯ˢ σ = mkpair (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  (pair val0 val1)   ⋯ˢ σ = pair (val0 ⋯ˢ σ) (val1 ⋯ˢ σ)
  (fst exp0)         ⋯ˢ σ = fst (exp0 ⋯ˢ σ)
  (snd exp0)         ⋯ˢ σ = snd (exp0 ⋯ˢ σ)
  one                ⋯ˢ σ = one
  (letC exp0 exp1)   ⋯ˢ σ = letC (exp0 ⋯ˢ σ) (exp1 ⋯ˢ (σ ↑ˢ* _))

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

  instᴿ-imp    : (imp typ0 typ1) ⋯ᴿ ρ    ≡ imp (typ0 ⋯ᴿ ρ) (typ1 ⋯ᴿ ρ)
  instᴿ-imp    = refl
  instᴿ-and    : (and typ0 typ1) ⋯ᴿ ρ    ≡ and (typ0 ⋯ᴿ ρ) (typ1 ⋯ᴿ ρ)
  instᴿ-and    = refl
  instᴿ-unit   : unit ⋯ᴿ ρ               ≡ unit
  instᴿ-unit   = refl
  instᴿ-value  : (value val0) ⋯ᴿ ρ       ≡ value (val0 ⋯ᴿ ρ)
  instᴿ-value  = refl
  instᴿ-lam    : (lam exp0) ⋯ᴿ ρ         ≡ lam (exp0 ⋯ᴿ (ρ ↑ᴿ* (val ∷ [])))
  instᴿ-lam    = refl
  instᴿ-app    : (app exp0 exp1) ⋯ᴿ ρ    ≡ app (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ)
  instᴿ-app    = refl
  instᴿ-mkpair : (mkpair exp0 exp1) ⋯ᴿ ρ ≡ mkpair (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ)
  instᴿ-mkpair = refl
  instᴿ-pair   : (pair val0 val1) ⋯ᴿ ρ   ≡ pair (val0 ⋯ᴿ ρ) (val1 ⋯ᴿ ρ)
  instᴿ-pair   = refl
  instᴿ-fst    : (fst exp0) ⋯ᴿ ρ         ≡ fst (exp0 ⋯ᴿ ρ)
  instᴿ-fst    = refl
  instᴿ-snd    : (snd exp0) ⋯ᴿ ρ         ≡ snd (exp0 ⋯ᴿ ρ)
  instᴿ-snd    = refl
  instᴿ-one    : one ⋯ᴿ ρ                ≡ one
  instᴿ-one    = refl
  instᴿ-letC   : (letC exp0 exp1) ⋯ᴿ ρ   ≡ letC (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ (ρ ↑ᴿ* (val ∷ [])))
  instᴿ-letC   = refl
  inst-imp    : (imp typ0 typ1) ⋯ˢ σ    ≡ imp (typ0 ⋯ˢ σ) (typ1 ⋯ˢ σ)
  inst-imp    = refl
  inst-and    : (and typ0 typ1) ⋯ˢ σ    ≡ and (typ0 ⋯ˢ σ) (typ1 ⋯ˢ σ)
  inst-and    = refl
  inst-unit   : unit ⋯ˢ σ               ≡ unit
  inst-unit   = refl
  inst-value  : (value val0) ⋯ˢ σ       ≡ value (val0 ⋯ˢ σ)
  inst-value  = refl
  inst-lam    : (lam exp0) ⋯ˢ σ         ≡ lam (exp0 ⋯ˢ (σ ↑ˢ* (val ∷ [])))
  inst-lam    = refl
  inst-app    : (app exp0 exp1) ⋯ˢ σ    ≡ app (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  inst-app    = refl
  inst-mkpair : (mkpair exp0 exp1) ⋯ˢ σ ≡ mkpair (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  inst-mkpair = refl
  inst-pair   : (pair val0 val1) ⋯ˢ σ   ≡ pair (val0 ⋯ˢ σ) (val1 ⋯ˢ σ)
  inst-pair   = refl
  inst-fst    : (fst exp0) ⋯ˢ σ         ≡ fst (exp0 ⋯ˢ σ)
  inst-fst    = refl
  inst-snd    : (snd exp0) ⋯ˢ σ         ≡ snd (exp0 ⋯ˢ σ)
  inst-snd    = refl
  inst-one    : one ⋯ˢ σ                ≡ one
  inst-one    = refl
  inst-letC   : (letC exp0 exp1) ⋯ˢ σ   ≡ letC (exp0 ⋯ˢ σ) (exp1 ⋯ˢ (σ ↑ˢ* (val ∷ [])))
  inst-letC   = refl

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
  right-idˢ (imp typ0 typ1)    = cong2 imp (right-idˢ typ0) (right-idˢ typ1)
  right-idˢ (and typ0 typ1)    = cong2 and (right-idˢ typ0) (right-idˢ typ1)
  right-idˢ unit               = refl
  right-idˢ (value val0)       = cong1 value (right-idˢ val0)
  right-idˢ (lam exp0)         = cong1 lam (trans (cong1 (exp0 ⋯ˢ_) (lift-idˢ* (val ∷ []))) (right-idˢ exp0))
  right-idˢ (app exp0 exp1)    = cong2 app (right-idˢ exp0) (right-idˢ exp1)
  right-idˢ (mkpair exp0 exp1) = cong2 mkpair (right-idˢ exp0) (right-idˢ exp1)
  right-idˢ (pair val0 val1)   = cong2 pair (right-idˢ val0) (right-idˢ val1)
  right-idˢ (fst exp0)         = cong1 fst (right-idˢ exp0)
  right-idˢ (snd exp0)         = cong1 snd (right-idˢ exp0)
  right-idˢ one                = refl
  right-idˢ (letC exp0 exp1)   = cong2 letC (right-idˢ exp0) (trans (cong1 (exp1 ⋯ˢ_) (lift-idˢ* (val ∷ []))) (right-idˢ exp1))

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
  right-id (imp typ0 typ1)    = cong2 imp (right-id typ0) (right-id typ1)
  right-id (and typ0 typ1)    = cong2 and (right-id typ0) (right-id typ1)
  right-id unit               = refl
  right-id (value val0)       = cong1 value (right-id val0)
  right-id (lam exp0)         = cong1 lam (trans (cong1 (exp0 ⋯ᴿ_) (lift-id* (val ∷ []))) (right-id exp0))
  right-id (app exp0 exp1)    = cong2 app (right-id exp0) (right-id exp1)
  right-id (mkpair exp0 exp1) = cong2 mkpair (right-id exp0) (right-id exp1)
  right-id (pair val0 val1)   = cong2 pair (right-id val0) (right-id val1)
  right-id (fst exp0)         = cong1 fst (right-id exp0)
  right-id (snd exp0)         = cong1 snd (right-id exp0)
  right-id one                = refl
  right-id (letC exp0 exp1)   = cong2 letC (right-id exp0) (trans (cong1 (exp1 ⋯ᴿ_) (lift-id* (val ∷ []))) (right-id exp1))

  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿᴿ : ∀ S → ((ρ₁ ↑ᴿ* S) ∘ (ρ₂ ↑ᴿ* S)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ* S)
  lift-dist-comp*ᴿᴿ []      = refl 
  lift-dist-comp*ᴿᴿ (_ ∷ S) = trans lift-dist-compᴿᴿ (cong1 (_↑ᴿ _) (lift-dist-comp*ᴿᴿ S))

  compositionalityᴿᴿ (var x)  = refl
  compositionalityᴿᴿ  (imp typ0 typ1)    = cong2 imp (compositionalityᴿᴿ typ0) (compositionalityᴿᴿ typ1)
  compositionalityᴿᴿ  (and typ0 typ1)    = cong2 and (compositionalityᴿᴿ typ0) (compositionalityᴿᴿ typ1)
  compositionalityᴿᴿ unit                = refl
  compositionalityᴿᴿ  (value val0)       = cong1 value (compositionalityᴿᴿ val0)
  compositionalityᴿᴿ  (lam exp0)         = cong1 lam (trans (compositionalityᴿᴿ exp0) (cong1 (exp0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (val ∷ []))))
  compositionalityᴿᴿ  (app exp0 exp1)    = cong2 app (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1)
  compositionalityᴿᴿ  (mkpair exp0 exp1) = cong2 mkpair (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1)
  compositionalityᴿᴿ  (pair val0 val1)   = cong2 pair (compositionalityᴿᴿ val0) (compositionalityᴿᴿ val1)
  compositionalityᴿᴿ  (fst exp0)         = cong1 fst (compositionalityᴿᴿ exp0)
  compositionalityᴿᴿ  (snd exp0)         = cong1 snd (compositionalityᴿᴿ exp0)
  compositionalityᴿᴿ one                 = refl
  compositionalityᴿᴿ  (letC exp0 exp1)   = cong2 letC (compositionalityᴿᴿ exp0) (trans (compositionalityᴿᴿ exp1) (cong1 (exp1 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (val ∷ []))))

  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ {σ₂ = σ₂} (_ ∷ S) = trans (lift-dist-compᴿˢ {σ₂ = σ₂ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} S))

  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ {σ₂ = σ₂} (imp typ0 typ1)    = cong2 imp (compositionalityᴿˢ typ0) (compositionalityᴿˢ typ1)
  compositionalityᴿˢ {σ₂ = σ₂} (and typ0 typ1)    = cong2 and (compositionalityᴿˢ typ0) (compositionalityᴿˢ typ1)
  compositionalityᴿˢ unit                         = refl
  compositionalityᴿˢ {σ₂ = σ₂} (value val0)       = cong1 value (compositionalityᴿˢ val0)
  compositionalityᴿˢ {σ₂ = σ₂} (lam exp0)         = cong1 lam (trans (compositionalityᴿˢ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (val ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (app exp0 exp1)    = cong2 app (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1)
  compositionalityᴿˢ {σ₂ = σ₂} (mkpair exp0 exp1) = cong2 mkpair (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1)
  compositionalityᴿˢ {σ₂ = σ₂} (pair val0 val1)   = cong2 pair (compositionalityᴿˢ val0) (compositionalityᴿˢ val1)
  compositionalityᴿˢ {σ₂ = σ₂} (fst exp0)         = cong1 fst (compositionalityᴿˢ exp0)
  compositionalityᴿˢ {σ₂ = σ₂} (snd exp0)         = cong1 snd (compositionalityᴿˢ exp0)
  compositionalityᴿˢ one                          = refl
  compositionalityᴿˢ {σ₂ = σ₂} (letC exp0 exp1)   = cong2 letC (compositionalityᴿˢ exp0) (trans (compositionalityᴿˢ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (val ∷ []))))

  lift-dist-compˢᴿ : ((σ₁ ↑ˢ s) ⨟ ⟨ ρ₂ ↑ᴿ s ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ s)
  lift-dist-compˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    (t ⋯ᴿ (wkᴿ _)) ⋯ˢ ⟨ ρ₂ ↑ᴿ _ ⟩ ≡⟨ coincidence {t = t ⋯ᴿ (wkᴿ _)} ⟩ 
    (t ⋯ᴿ (wkᴿ _)) ⋯ᴿ (ρ₂ ↑ᴿ _)   ≡⟨ compositionalityᴿᴿ t ⟩ 
    t ⋯ᴿ (wkᴿ _ ∘ (ρ₂ ↑ᴿ _))    ≡⟨ sym (compositionalityᴿᴿ t) ⟩ 
    (t ⋯ᴿ ρ₂) ⋯ᴿ wkᴿ _          ≡⟨ cong1 (_⋯ᴿ (wkᴿ _)) (sym (coincidence {t = t})) ⟩ 
    (t ⋯ˢ ⟨ ρ₂ ⟩) ⋯ᴿ wkᴿ _      ∎ }

  lift-dist-comp*ˢᴿ : ∀ S → ((σ₁ ↑ˢ* S) ⨟ ⟨ ρ₂ ↑ᴿ* S ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ* S )
  lift-dist-comp*ˢᴿ []      = refl 
  lift-dist-comp*ˢᴿ {σ₁ = σ₁} (_ ∷ S) =  trans (lift-dist-compˢᴿ {σ₁ = σ₁ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} S))
 
  compositionalityˢᴿ {σ₁ = σ₁} (var x)  = sym (coincidence {t = σ₁ _ x})
  compositionalityˢᴿ {σ₁ = σ₁} (imp typ0 typ1)    = cong2 imp (compositionalityˢᴿ typ0) (compositionalityˢᴿ typ1)
  compositionalityˢᴿ {σ₁ = σ₁} (and typ0 typ1)    = cong2 and (compositionalityˢᴿ typ0) (compositionalityˢᴿ typ1)
  compositionalityˢᴿ unit                         = refl
  compositionalityˢᴿ {σ₁ = σ₁} (value val0)       = cong1 value (compositionalityˢᴿ val0)
  compositionalityˢᴿ {σ₁ = σ₁} (lam exp0)         = cong1 lam (trans (compositionalityˢᴿ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (val ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (app exp0 exp1)    = cong2 app (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1)
  compositionalityˢᴿ {σ₁ = σ₁} (mkpair exp0 exp1) = cong2 mkpair (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1)
  compositionalityˢᴿ {σ₁ = σ₁} (pair val0 val1)   = cong2 pair (compositionalityˢᴿ val0) (compositionalityˢᴿ val1)
  compositionalityˢᴿ {σ₁ = σ₁} (fst exp0)         = cong1 fst (compositionalityˢᴿ exp0)
  compositionalityˢᴿ {σ₁ = σ₁} (snd exp0)         = cong1 snd (compositionalityˢᴿ exp0)
  compositionalityˢᴿ one                          = refl
  compositionalityˢᴿ {σ₁ = σ₁} (letC exp0 exp1)   = cong2 letC (compositionalityˢᴿ exp0) (trans (compositionalityˢᴿ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (val ∷ []))))
  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s)
  lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    begin
    (t ⋯ᴿ (wkᴿ _)) ⋯ˢ (σ₂ ↑ˢ _)    ≡⟨ compositionalityᴿˢ t ⟩ 
    t ⋯ˢ (⟨ (wkᴿ _) ⟩ ⨟ (σ₂ ↑ˢ _)) ≡⟨ cong1 (t ⋯ˢ_) (ext λ x → sym (coincidence {t = σ₂ _ x})) ⟩   
    t ⋯ˢ (σ₂ ⨟ ⟨ (wkᴿ _) ⟩)        ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
    (t ⋯ˢ σ₂) ⋯ᴿ (wkᴿ _)           ∎ }
  
  lift-dist-comp*ˢˢ : ∀ S →  ((σ₁ ↑ˢ* S) ⨟ (σ₂ ↑ˢ* S)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ˢˢ []      = refl 
  lift-dist-comp*ˢˢ  {σ₁ = σ₁} {σ₂ = σ₂} (_ ∷ S) =  trans (lift-dist-compˢˢ {σ₁ = σ₁ ↑ˢ* S} {σ₂ = σ₂ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} S))

  compositionalityˢˢ (var x)  = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (imp typ0 typ1)    = cong2 imp (compositionalityˢˢ typ0) (compositionalityˢˢ typ1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (and typ0 typ1)    = cong2 and (compositionalityˢˢ typ0) (compositionalityˢˢ typ1)
  compositionalityˢˢ unit                                   = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (value val0)       = cong1 value (compositionalityˢˢ val0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (lam exp0)         = cong1 lam (trans (compositionalityˢˢ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (val ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (app exp0 exp1)    = cong2 app (compositionalityˢˢ exp0) (compositionalityˢˢ exp1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (mkpair exp0 exp1) = cong2 mkpair (compositionalityˢˢ exp0) (compositionalityˢˢ exp1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (pair val0 val1)   = cong2 pair (compositionalityˢˢ val0) (compositionalityˢˢ val1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (fst exp0)         = cong1 fst (compositionalityˢˢ exp0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (snd exp0)         = cong1 snd (compositionalityˢˢ exp0)
  compositionalityˢˢ one                                    = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (letC exp0 exp1)   = cong2 letC (compositionalityˢˢ exp0) (trans (compositionalityˢˢ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (val ∷ []))))

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
  inst-imp instᴿ-imp
  inst-and instᴿ-and
  inst-unit instᴿ-unit
  inst-value instᴿ-value
  inst-lam instᴿ-lam
  inst-app instᴿ-app
  inst-mkpair instᴿ-mkpair
  inst-pair instᴿ-pair
  inst-fst instᴿ-fst
  inst-snd instᴿ-snd
  inst-one instᴿ-one
  inst-letC instᴿ-letC
  def-id def-wkᴿ def-∙ᴿ-zero def-∙ᴿ-suc def-∘      
  assocᴿ distᴿ interactᴿ       
  comp-idᵣᴿ comp-idₗᴿ η-idᴿ η-lawᴿ
  coincidence-var
#-}
