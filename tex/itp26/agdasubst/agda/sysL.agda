{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module sysL where
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
  tm stack cmd : Sort

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

  lam  : (tm ∷ S) ⊢ tm → S ⊢ tm
  mu   : (stack ∷ S) ⊢ cmd → S ⊢ tm
  cons : S ⊢ tm → S ⊢ stack → S ⊢ stack
  cut  : S ⊢ tm → S ⊢ stack → S ⊢ cmd

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

(lam tm0)         ⋯ᴿ ρ = lam (tm0 ⋯ᴿ (ρ ↑ᴿ* _))
(mu cmd0)         ⋯ᴿ ρ = mu (cmd0 ⋯ᴿ (ρ ↑ᴿ* _))
(cons tm0 stack0) ⋯ᴿ ρ = cons (tm0 ⋯ᴿ ρ) (stack0 ⋯ᴿ ρ)
(cut tm0 stack0)  ⋯ᴿ ρ = cut (tm0 ⋯ᴿ ρ) (stack0 ⋯ᴿ ρ)

variable
  cmd0 : S ⊢ cmd
  stack0 : S ⊢ stack
  tm0 : S ⊢ tm

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

  (lam tm0)         ⋯ˢ σ = lam (tm0 ⋯ˢ (σ ↑ˢ* _))
  (mu cmd0)         ⋯ˢ σ = mu (cmd0 ⋯ˢ (σ ↑ˢ* _))
  (cons tm0 stack0) ⋯ˢ σ = cons (tm0 ⋯ˢ σ) (stack0 ⋯ˢ σ)
  (cut tm0 stack0)  ⋯ˢ σ = cut (tm0 ⋯ˢ σ) (stack0 ⋯ˢ σ)

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

  traversal-lam  : (lam tm0) ⋯ˢ σ         ≡ lam (tm0 ⋯ˢ (σ ↑ˢ* (tm ∷ [])))
  traversal-lam  = refl
  traversal-mu   : (mu cmd0) ⋯ˢ σ         ≡ mu (cmd0 ⋯ˢ (σ ↑ˢ* (stack ∷ [])))
  traversal-mu   = refl
  traversal-cons : (cons tm0 stack0) ⋯ˢ σ ≡ cons (tm0 ⋯ˢ σ) (stack0 ⋯ˢ σ)
  traversal-cons = refl
  traversal-cut  : (cut tm0 stack0) ⋯ˢ σ  ≡ cut (tm0 ⋯ˢ σ) (stack0 ⋯ˢ σ)
  traversal-cut  = refl

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

  right-idˢ (lam tm0)         = cong1 lam (trans (cong1 (tm0 ⋯ˢ_) (lift-idˢ* (tm ∷ []))) (right-idˢ tm0))
  right-idˢ (mu cmd0)         = cong1 mu (trans (cong1 (cmd0 ⋯ˢ_) (lift-idˢ* (stack ∷ []))) (right-idˢ cmd0))
  right-idˢ (cons tm0 stack0) = cong2 cons (right-idˢ tm0) (right-idˢ stack0)
  right-idˢ (cut tm0 stack0)  = cong2 cut (right-idˢ tm0) (right-idˢ stack0)

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

  right-id (lam tm0)         = cong1 lam (trans (cong1 (tm0 ⋯ᴿ_) (lift-id* (tm ∷ []))) (right-id tm0))
  right-id (mu cmd0)         = cong1 mu (trans (cong1 (cmd0 ⋯ᴿ_) (lift-id* (stack ∷ []))) (right-id cmd0))
  right-id (cons tm0 stack0) = cong2 cons (right-id tm0) (right-id stack0)
  right-id (cut tm0 stack0)  = cong2 cut (right-id tm0) (right-id stack0)
  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿᴿ : ∀ S → ((ρ₁ ↑ᴿ* S) ∘ (ρ₂ ↑ᴿ* S)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ* S)
  lift-dist-comp*ᴿᴿ []      = refl 
  lift-dist-comp*ᴿᴿ (_ ∷ S) = trans lift-dist-compᴿᴿ (cong1 (_↑ᴿ _) (lift-dist-comp*ᴿᴿ S))

  compositionalityᴿᴿ {m = V} x  = refl
  compositionalityᴿᴿ (var x)  = refl
  compositionalityᴿᴿ (lam tm0)         = cong1 lam (trans (compositionalityᴿᴿ tm0) (cong1 (tm0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (tm ∷ []))))
  compositionalityᴿᴿ (mu cmd0)         = cong1 mu (trans (compositionalityᴿᴿ cmd0) (cong1 (cmd0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (stack ∷ []))))
  compositionalityᴿᴿ (cons tm0 stack0) = cong2 cons (compositionalityᴿᴿ tm0) (compositionalityᴿᴿ stack0)
  compositionalityᴿᴿ (cut tm0 stack0)  = cong2 cut (compositionalityᴿᴿ tm0) (compositionalityᴿᴿ stack0)
  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ (_ ∷ S) = trans lift-dist-compᴿˢ (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ S))

  compositionalityᴿˢ {m = V} x  = refl
  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ (lam tm0)         = cong1 lam (trans (compositionalityᴿˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (tm ∷ []))))
  compositionalityᴿˢ (mu cmd0)         = cong1 mu (trans (compositionalityᴿˢ cmd0) (cong1 (cmd0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (stack ∷ []))))
  compositionalityᴿˢ (cons tm0 stack0) = cong2 cons (compositionalityᴿˢ tm0) (compositionalityᴿˢ stack0)
  compositionalityᴿˢ (cut tm0 stack0)  = cong2 cut (compositionalityᴿˢ tm0) (compositionalityᴿˢ stack0)
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
  compositionalityˢᴿ (lam tm0)         = cong1 lam (trans (compositionalityˢᴿ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (tm ∷ []))))
  compositionalityˢᴿ (mu cmd0)         = cong1 mu (trans (compositionalityˢᴿ cmd0) (cong1 (cmd0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (stack ∷ []))))
  compositionalityˢᴿ (cons tm0 stack0) = cong2 cons (compositionalityˢᴿ tm0) (compositionalityˢᴿ stack0)
  compositionalityˢᴿ (cut tm0 stack0)  = cong2 cut (compositionalityˢᴿ tm0) (compositionalityˢᴿ stack0)
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
  compositionalityˢˢ (lam tm0)         = cong1 lam (trans (compositionalityˢˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢˢ (tm ∷ []))))
  compositionalityˢˢ (mu cmd0)         = cong1 mu (trans (compositionalityˢˢ cmd0) (cong1 (cmd0 ⋯ˢ_) (lift-dist-comp*ˢˢ (stack ∷ []))))
  compositionalityˢˢ (cons tm0 stack0) = cong2 cons (compositionalityˢˢ tm0) (compositionalityˢˢ stack0)
  compositionalityˢˢ (cut tm0 stack0)  = cong2 cut (compositionalityˢˢ tm0) (compositionalityˢˢ stack0)
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
  traversal-var traversal-lam traversal-mu traversal-cons traversal-cut
  right-id
  compositionalityᴿˢ compositionalityᴿᴿ
  compositionalityˢᴿ compositionalityˢˢ
  coincidence coincidence-fold
#-}
