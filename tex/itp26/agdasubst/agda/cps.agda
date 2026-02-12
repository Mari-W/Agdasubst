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

variable
  x x′     : S ∋ s
  t t′     : S ⊢ s
  x/t x/t′ : S ⊢[ m ] s

--! Ren {
_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s 

--! [
variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂
--! ]
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

_⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → 
  S₂ ⊢ s 
_⋯ᴿ_ {m = V} x   ρ  = var (ρ _ x)
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

⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂ 
⟨ ρ ⟩ _ x = var (ρ _ x)
{-# INLINE ⟨_⟩ #-}

wkˢ : ∀ s → S →ˢ (s ∷ S)
wkˢ _ = ⟨ wk _ ⟩
{-# INLINE wkˢ #-}

idˢ : S →ˢ S
idˢ _ = var
{-# INLINE idˢ #-}

opaque  
  _∙_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂    
  _∙_  t σ _ zero = t
  (t ∙ σ) _ (suc x) = σ _ x 

  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  σ ↑ˢ s =  (var zero) ∙ λ s₁ x → (σ _ x) ⋯ᴿ wk _

_↑ˢ*_ : (S₁ →ˢ S₂) → ∀ S → ((S ++ S₁) →ˢ (S ++ S₂))
σ ↑ˢ* [] = σ
σ ↑ˢ* (s ∷ S) = (σ ↑ˢ* S) ↑ˢ s

opaque
  unfolding  _∙_ _↑ˢ_ 
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

  lift-id            : idᴿ {S = S} ↑ᴿ s ≡ idᴿ 

  ext-zero           : zero ⋯ˢ (t ∙ σ)   ≡ t                             
  ext-suc            : suc x ⋯ˢ (t ∙ σ)  ≡ x ⋯ˢ σ 
  lift               : σ ↑ˢ s            ≡ (var zero) ∙ (σ ⨟ wkˢ _)

  associativity           : (σ₁ ⨟ σ₂) ⨟ σ₃                      ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  distributivityˢ         : (t ∙ σ₁) ⨟ σ₂                       ≡ ((t ⋯ˢ σ₂) ∙ (σ₁ ⨟ σ₂)) 
  distributivityᴿ         : (t ∙ σ₁) ⨟ ⟨ ρ₂ ⟩                   ≡ ((t ⋯ᴿ ρ₂) ∙ (σ₁ ⨟ ⟨ ρ₂ ⟩)) 
  interact                : wkˢ s ⨟ (t ∙ σ)                     ≡ σ                                        
  comp-idᵣ                : σ ⨟ idˢ                             ≡ σ                                               
  comp-idₗ                : idˢ ⨟ σ                             ≡ σ                                               
  η-id                    : (var (zero {s = s} {S = S})) ∙ (wkˢ _)  ≡ idˢ
  η-lawˢ                  : (zero ⋯ˢ σ) ∙ (wkˢ _ ⨟ σ)           ≡ σ
  η-lawᴿ                  : (zero ⋯ᴿ ρ) ∙ ((wkˢ _ ⨟ ⟨ ρ ⟩))     ≡ ⟨ ρ ⟩

  right-id                : ∀ (t : S ⊢ s) → t ⋯ᴿ idᴿ                   ≡ t   
  compositionalityᴿˢ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ x/t ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                    
  compositionalityᴿᴿ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ x/t ⋯ᴿ (ρ₁ ∘ ρ₂)                     
  compositionalityˢᴿ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ x/t ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
  compositionalityˢˢ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ x/t ⋯ˢ (σ₁ ⨟ σ₂)


  traversal-var           : (var x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  traversal-var = refl

  traversal-imp    : (imp typ0 typ1) ⋯ˢ σ    ≡ imp (typ0 ⋯ˢ σ) (typ1 ⋯ˢ σ)
  traversal-imp    = refl
  traversal-and    : (and typ0 typ1) ⋯ˢ σ    ≡ and (typ0 ⋯ˢ σ) (typ1 ⋯ˢ σ)
  traversal-and    = refl
  traversal-unit   : unit ⋯ˢ σ               ≡ unit
  traversal-unit   = refl
  traversal-value  : (value val0) ⋯ˢ σ       ≡ value (val0 ⋯ˢ σ)
  traversal-value  = refl
  traversal-lam    : (lam exp0) ⋯ˢ σ         ≡ lam (exp0 ⋯ˢ (σ ↑ˢ* (val ∷ [])))
  traversal-lam    = refl
  traversal-app    : (app exp0 exp1) ⋯ˢ σ    ≡ app (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  traversal-app    = refl
  traversal-mkpair : (mkpair exp0 exp1) ⋯ˢ σ ≡ mkpair (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  traversal-mkpair = refl
  traversal-pair   : (pair val0 val1) ⋯ˢ σ   ≡ pair (val0 ⋯ˢ σ) (val1 ⋯ˢ σ)
  traversal-pair   = refl
  traversal-fst    : (fst exp0) ⋯ˢ σ         ≡ fst (exp0 ⋯ˢ σ)
  traversal-fst    = refl
  traversal-snd    : (snd exp0) ⋯ˢ σ         ≡ snd (exp0 ⋯ˢ σ)
  traversal-snd    = refl
  traversal-one    : one ⋯ˢ σ                ≡ one
  traversal-one    = refl
  traversal-letC   : (letC exp0 exp1) ⋯ˢ σ   ≡ letC (exp0 ⋯ˢ σ) (exp1 ⋯ˢ (σ ↑ˢ* (val ∷ [])))
  traversal-letC   = refl

  coincidence              : x/t ⋯ˢ ⟨ ρ ⟩                                  ≡ x/t ⋯ᴿ ρ
  coincidence-fold         : x/t ⋯ˢ (⟨ ρ ↑ᴿ s ⟩ ⨟ ((x/t′ ⋯ᴿ ρ) ∙ idˢ))  ≡ x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩)


  lift-id = ext λ { zero → refl; (suc x) → refl }

  ext-zero = refl
  ext-suc  = refl
  lift     = cong1 ((var zero) ∙_) (sym (ext λ x → coincidence))

  lift-idˢ* : ∀ S → (idˢ {S = S₁} ↑ˢ* S) ≡ idˢ 
  lift-idˢ* []    = refl
  lift-idˢ* {S₁} (_ ∷ S) rewrite lift-idˢ* {S₁} S = η-lawᴿ

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

  associativity {σ₁ = σ₁} = ext λ x → compositionalityˢˢ (σ₁ _ x) 
  distributivityˢ = ext λ { zero → refl; (suc x) → refl }
  distributivityᴿ = ext λ { zero → coincidence; (suc x) → refl }
  interact        = refl
  comp-idᵣ        = ext λ x → (right-idˢ _)
  comp-idₗ        = refl
  η-id            = ext λ { zero → refl; (suc x) → refl }
  η-lawˢ          = ext λ { zero → refl; (suc x) → refl }
  η-lawᴿ          = ext λ { zero → refl; (suc x) → refl }

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

  compositionalityᴿᴿ {m = V} x  = refl
  compositionalityᴿᴿ (var x)  = refl
  compositionalityᴿᴿ (imp typ0 typ1)    = cong2 imp (compositionalityᴿᴿ typ0) (compositionalityᴿᴿ typ1)
  compositionalityᴿᴿ (and typ0 typ1)    = cong2 and (compositionalityᴿᴿ typ0) (compositionalityᴿᴿ typ1)
  compositionalityᴿᴿ unit               = refl
  compositionalityᴿᴿ (value val0)       = cong1 value (compositionalityᴿᴿ val0)
  compositionalityᴿᴿ (lam exp0)         = cong1 lam (trans (compositionalityᴿᴿ exp0) (cong1 (exp0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (val ∷ []))))
  compositionalityᴿᴿ (app exp0 exp1)    = cong2 app (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1)
  compositionalityᴿᴿ (mkpair exp0 exp1) = cong2 mkpair (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1)
  compositionalityᴿᴿ (pair val0 val1)   = cong2 pair (compositionalityᴿᴿ val0) (compositionalityᴿᴿ val1)
  compositionalityᴿᴿ (fst exp0)         = cong1 fst (compositionalityᴿᴿ exp0)
  compositionalityᴿᴿ (snd exp0)         = cong1 snd (compositionalityᴿᴿ exp0)
  compositionalityᴿᴿ one                = refl
  compositionalityᴿᴿ (letC exp0 exp1)   = cong2 letC (compositionalityᴿᴿ exp0) (trans (compositionalityᴿᴿ exp1) (cong1 (exp1 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (val ∷ []))))
  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ (_ ∷ S) = trans lift-dist-compᴿˢ (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ S))

  compositionalityᴿˢ {m = V} x  = refl
  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ (imp typ0 typ1)    = cong2 imp (compositionalityᴿˢ typ0) (compositionalityᴿˢ typ1)
  compositionalityᴿˢ (and typ0 typ1)    = cong2 and (compositionalityᴿˢ typ0) (compositionalityᴿˢ typ1)
  compositionalityᴿˢ unit               = refl
  compositionalityᴿˢ (value val0)       = cong1 value (compositionalityᴿˢ val0)
  compositionalityᴿˢ (lam exp0)         = cong1 lam (trans (compositionalityᴿˢ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (val ∷ []))))
  compositionalityᴿˢ (app exp0 exp1)    = cong2 app (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1)
  compositionalityᴿˢ (mkpair exp0 exp1) = cong2 mkpair (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1)
  compositionalityᴿˢ (pair val0 val1)   = cong2 pair (compositionalityᴿˢ val0) (compositionalityᴿˢ val1)
  compositionalityᴿˢ (fst exp0)         = cong1 fst (compositionalityᴿˢ exp0)
  compositionalityᴿˢ (snd exp0)         = cong1 snd (compositionalityᴿˢ exp0)
  compositionalityᴿˢ one                = refl
  compositionalityᴿˢ (letC exp0 exp1)   = cong2 letC (compositionalityᴿˢ exp0) (trans (compositionalityᴿˢ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ᴿˢ (val ∷ []))))
  lift-dist-compˢᴿ : ((σ₁ ↑ˢ s) ⨟ ⟨ ρ₂ ↑ᴿ s ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ s)
  lift-dist-compˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    (t ⋯ᴿ (wk _)) ⋯ˢ ⟨ ρ₂ ↑ᴿ _ ⟩ ≡⟨ coincidence ⟩ 
    (t ⋯ᴿ (wk _)) ⋯ᴿ (ρ₂ ↑ᴿ _)   ≡⟨ compositionalityᴿᴿ t ⟩ 
    t ⋯ᴿ (wk _ ∘ (ρ₂ ↑ᴿ _))    ≡⟨ sym (compositionalityᴿᴿ t) ⟩ 
    (t ⋯ᴿ ρ₂) ⋯ᴿ wk _          ≡⟨ cong1 (_⋯ᴿ (wk _)) (sym coincidence) ⟩ 
    (t ⋯ˢ ⟨ ρ₂ ⟩) ⋯ᴿ wk _      ∎ }

  lift-dist-comp*ˢᴿ : ∀ S → ((σ₁ ↑ˢ* S) ⨟ ⟨ ρ₂ ↑ᴿ* S ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ* S )
  lift-dist-comp*ˢᴿ []      = refl 
  lift-dist-comp*ˢᴿ (_ ∷ S) =  trans lift-dist-compˢᴿ (cong1 (_↑ˢ _) (lift-dist-comp*ˢᴿ S))
 
  compositionalityˢᴿ {m = V} x  = sym coincidence
  compositionalityˢᴿ (var x)  = sym coincidence
  compositionalityˢᴿ (imp typ0 typ1)    = cong2 imp (compositionalityˢᴿ typ0) (compositionalityˢᴿ typ1)
  compositionalityˢᴿ (and typ0 typ1)    = cong2 and (compositionalityˢᴿ typ0) (compositionalityˢᴿ typ1)
  compositionalityˢᴿ unit               = refl
  compositionalityˢᴿ (value val0)       = cong1 value (compositionalityˢᴿ val0)
  compositionalityˢᴿ (lam exp0)         = cong1 lam (trans (compositionalityˢᴿ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (val ∷ []))))
  compositionalityˢᴿ (app exp0 exp1)    = cong2 app (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1)
  compositionalityˢᴿ (mkpair exp0 exp1) = cong2 mkpair (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1)
  compositionalityˢᴿ (pair val0 val1)   = cong2 pair (compositionalityˢᴿ val0) (compositionalityˢᴿ val1)
  compositionalityˢᴿ (fst exp0)         = cong1 fst (compositionalityˢᴿ exp0)
  compositionalityˢᴿ (snd exp0)         = cong1 snd (compositionalityˢᴿ exp0)
  compositionalityˢᴿ one                = refl
  compositionalityˢᴿ (letC exp0 exp1)   = cong2 letC (compositionalityˢᴿ exp0) (trans (compositionalityˢᴿ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ˢᴿ (val ∷ []))))
  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s)
  lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    begin
    (t ⋯ᴿ (wk _)) ⋯ˢ (σ₂ ↑ˢ _)    ≡⟨ compositionalityᴿˢ t ⟩ 
    t ⋯ˢ (⟨ (wk _) ⟩ ⨟ (σ₂ ↑ˢ _)) ≡⟨ cong1 (t ⋯ˢ_) (ext λ y → sym coincidence) ⟩   
    t ⋯ˢ (σ₂ ⨟ ⟨ (wk _) ⟩)        ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
    (t ⋯ˢ σ₂) ⋯ᴿ (wk _)           ∎ }
  
  lift-dist-comp*ˢˢ : ∀ S →  ((σ₁ ↑ˢ* S) ⨟ (σ₂ ↑ˢ* S)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ˢˢ []      = refl 
  lift-dist-comp*ˢˢ (_ ∷ S) =  trans lift-dist-compˢˢ (cong1 (_↑ˢ _) (lift-dist-comp*ˢˢ S))

  compositionalityˢˢ {m = V} x  = refl
  compositionalityˢˢ (var x)  = refl
  compositionalityˢˢ (imp typ0 typ1)    = cong2 imp (compositionalityˢˢ typ0) (compositionalityˢˢ typ1)
  compositionalityˢˢ (and typ0 typ1)    = cong2 and (compositionalityˢˢ typ0) (compositionalityˢˢ typ1)
  compositionalityˢˢ unit               = refl
  compositionalityˢˢ (value val0)       = cong1 value (compositionalityˢˢ val0)
  compositionalityˢˢ (lam exp0)         = cong1 lam (trans (compositionalityˢˢ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ˢˢ (val ∷ []))))
  compositionalityˢˢ (app exp0 exp1)    = cong2 app (compositionalityˢˢ exp0) (compositionalityˢˢ exp1)
  compositionalityˢˢ (mkpair exp0 exp1) = cong2 mkpair (compositionalityˢˢ exp0) (compositionalityˢˢ exp1)
  compositionalityˢˢ (pair val0 val1)   = cong2 pair (compositionalityˢˢ val0) (compositionalityˢˢ val1)
  compositionalityˢˢ (fst exp0)         = cong1 fst (compositionalityˢˢ exp0)
  compositionalityˢˢ (snd exp0)         = cong1 snd (compositionalityˢˢ exp0)
  compositionalityˢˢ one                = refl
  compositionalityˢˢ (letC exp0 exp1)   = cong2 letC (compositionalityˢˢ exp0) (trans (compositionalityˢˢ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ˢˢ (val ∷ []))))
  coincidence {x/t = x/t} {ρ = ρ} = 
    x/t ⋯ˢ (⟨ ρ ⟩ ⨟ idˢ) ≡⟨ sym (compositionalityᴿˢ x/t) ⟩ 
    (x/t ⋯ᴿ ρ) ⋯ˢ idˢ    ≡⟨ right-idˢ _ ⟩ 
    x/t ⋯ᴿ ρ             ∎

  coincidence-fold {x/t = x/t} {ρ = ρ} {x/t′ = x/t′} = 
    (x/t ⋯ˢ (⟨ ρ ↑ᴿ _ ⟩ ⨟ ((x/t′ ⋯ᴿ ρ) ∙ idˢ))) ≡⟨ cong1 (x/t ⋯ˢ_) (ext λ { zero → refl; (suc x) → refl }) ⟩ 
    (x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩))              ∎

{-# REWRITE
  lift-id ext-zero ext-suc lift
  associativity distributivityˢ distributivityᴿ interact
  comp-idᵣ comp-idₗ η-id η-lawˢ η-lawᴿ
  traversal-var traversal-imp traversal-and traversal-unit traversal-value traversal-lam traversal-app traversal-mkpair traversal-pair traversal-fst traversal-snd traversal-one traversal-letC
  right-id
  compositionalityᴿˢ compositionalityᴿᴿ
  compositionalityˢᴿ compositionalityˢˢ
  coincidence coincidence-fold
#-}
