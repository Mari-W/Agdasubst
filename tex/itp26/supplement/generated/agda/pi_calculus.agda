{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module pi_calculus where
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

cong3 : ∀ {A1 A2 A3 A4 : Set} (f : A1 → A2 → A3 → A4) {a1 a2 a3 a4 a5 a6} →
  a1 ≡ a2 → a3 ≡ a4 → a5 ≡ a6 → f a1 a3 a5 ≡ f a2 a4 a6
cong3 f refl refl refl = refl

open import Data.List using (List; []; _∷_; _++_)

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

data Mode : Set where 
  V T : Mode

private variable
  m  : Mode

data Sort : Set where 
  chan proc : Sort

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

  Nil  : S ⊢ proc
  Bang : S ⊢ proc → S ⊢ proc
  Res  : (chan ∷ S) ⊢ proc → S ⊢ proc
  Par  : S ⊢ proc → S ⊢ proc → S ⊢ proc
  In   : S ⊢ chan → (chan ∷ S) ⊢ proc → S ⊢ proc
  Out  : S ⊢ chan → S ⊢ chan → S ⊢ proc → S ⊢ proc

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

  Nil                     ⋯ᴿ ρ = Nil
  (Bang proc0)            ⋯ᴿ ρ = Bang (proc0 ⋯ᴿ ρ)
  (Res proc0)             ⋯ᴿ ρ = Res (proc0 ⋯ᴿ (ρ ↑ᴿ* _))
  (Par proc0 proc1)       ⋯ᴿ ρ = Par (proc0 ⋯ᴿ ρ) (proc1 ⋯ᴿ ρ)
  (In chan0 proc0)        ⋯ᴿ ρ = In (chan0 ⋯ᴿ ρ) (proc0 ⋯ᴿ (ρ ↑ᴿ* _))
  (Out chan0 chan1 proc0) ⋯ᴿ ρ = Out (chan0 ⋯ᴿ ρ) (chan1 ⋯ᴿ ρ) (proc0 ⋯ᴿ ρ)

variable
  chan0 chan1 : S ⊢ chan
  proc0 proc1 : S ⊢ proc

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

  Nil                     ⋯ˢ σ = Nil
  (Bang proc0)            ⋯ˢ σ = Bang (proc0 ⋯ˢ σ)
  (Res proc0)             ⋯ˢ σ = Res (proc0 ⋯ˢ (σ ↑ˢ* _))
  (Par proc0 proc1)       ⋯ˢ σ = Par (proc0 ⋯ˢ σ) (proc1 ⋯ˢ σ)
  (In chan0 proc0)        ⋯ˢ σ = In (chan0 ⋯ˢ σ) (proc0 ⋯ˢ (σ ↑ˢ* _))
  (Out chan0 chan1 proc0) ⋯ˢ σ = Out (chan0 ⋯ˢ σ) (chan1 ⋯ˢ σ) (proc0 ⋯ˢ σ)

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

  instᴿ-Nil  : Nil ⋯ᴿ ρ                     ≡ Nil
  instᴿ-Nil  = refl
  instᴿ-Bang : (Bang proc0) ⋯ᴿ ρ            ≡ Bang (proc0 ⋯ᴿ ρ)
  instᴿ-Bang = refl
  instᴿ-Res  : (Res proc0) ⋯ᴿ ρ             ≡ Res (proc0 ⋯ᴿ (ρ ↑ᴿ* (chan ∷ [])))
  instᴿ-Res  = refl
  instᴿ-Par  : (Par proc0 proc1) ⋯ᴿ ρ       ≡ Par (proc0 ⋯ᴿ ρ) (proc1 ⋯ᴿ ρ)
  instᴿ-Par  = refl
  instᴿ-In   : (In chan0 proc0) ⋯ᴿ ρ        ≡ In (chan0 ⋯ᴿ ρ) (proc0 ⋯ᴿ (ρ ↑ᴿ* (chan ∷ [])))
  instᴿ-In   = refl
  instᴿ-Out  : (Out chan0 chan1 proc0) ⋯ᴿ ρ ≡ Out (chan0 ⋯ᴿ ρ) (chan1 ⋯ᴿ ρ) (proc0 ⋯ᴿ ρ)
  instᴿ-Out  = refl
  inst-Nil  : Nil ⋯ˢ σ                     ≡ Nil
  inst-Nil  = refl
  inst-Bang : (Bang proc0) ⋯ˢ σ            ≡ Bang (proc0 ⋯ˢ σ)
  inst-Bang = refl
  inst-Res  : (Res proc0) ⋯ˢ σ             ≡ Res (proc0 ⋯ˢ (σ ↑ˢ* (chan ∷ [])))
  inst-Res  = refl
  inst-Par  : (Par proc0 proc1) ⋯ˢ σ       ≡ Par (proc0 ⋯ˢ σ) (proc1 ⋯ˢ σ)
  inst-Par  = refl
  inst-In   : (In chan0 proc0) ⋯ˢ σ        ≡ In (chan0 ⋯ˢ σ) (proc0 ⋯ˢ (σ ↑ˢ* (chan ∷ [])))
  inst-In   = refl
  inst-Out  : (Out chan0 chan1 proc0) ⋯ˢ σ ≡ Out (chan0 ⋯ˢ σ) (chan1 ⋯ˢ σ) (proc0 ⋯ˢ σ)
  inst-Out  = refl

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
  right-idˢ Nil                     = refl
  right-idˢ (Bang proc0)            = cong1 Bang (right-idˢ proc0)
  right-idˢ (Res proc0)             = cong1 Res (trans (cong1 (proc0 ⋯ˢ_) (lift-idˢ* (chan ∷ []))) (right-idˢ proc0))
  right-idˢ (Par proc0 proc1)       = cong2 Par (right-idˢ proc0) (right-idˢ proc1)
  right-idˢ (In chan0 proc0)        = cong2 In (right-idˢ chan0) (trans (cong1 (proc0 ⋯ˢ_) (lift-idˢ* (chan ∷ []))) (right-idˢ proc0))
  right-idˢ (Out chan0 chan1 proc0) = cong3 Out (right-idˢ chan0) (right-idˢ chan1) (right-idˢ proc0)

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
  right-id Nil                     = refl
  right-id (Bang proc0)            = cong1 Bang (right-id proc0)
  right-id (Res proc0)             = cong1 Res (trans (cong1 (proc0 ⋯ᴿ_) (lift-id* (chan ∷ []))) (right-id proc0))
  right-id (Par proc0 proc1)       = cong2 Par (right-id proc0) (right-id proc1)
  right-id (In chan0 proc0)        = cong2 In (right-id chan0) (trans (cong1 (proc0 ⋯ᴿ_) (lift-id* (chan ∷ []))) (right-id proc0))
  right-id (Out chan0 chan1 proc0) = cong3 Out (right-id chan0) (right-id chan1) (right-id proc0)

  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿᴿ : ∀ S → ((ρ₁ ↑ᴿ* S) ∘ (ρ₂ ↑ᴿ* S)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ* S)
  lift-dist-comp*ᴿᴿ []      = refl 
  lift-dist-comp*ᴿᴿ (_ ∷ S) = trans lift-dist-compᴿᴿ (cong1 (_↑ᴿ _) (lift-dist-comp*ᴿᴿ S))

  compositionalityᴿᴿ (var x)  = refl
  compositionalityᴿᴿ Nil                      = refl
  compositionalityᴿᴿ  (Bang proc0)            = cong1 Bang (compositionalityᴿᴿ proc0)
  compositionalityᴿᴿ  (Res proc0)             = cong1 Res (trans (compositionalityᴿᴿ proc0) (cong1 (proc0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (chan ∷ []))))
  compositionalityᴿᴿ  (Par proc0 proc1)       = cong2 Par (compositionalityᴿᴿ proc0) (compositionalityᴿᴿ proc1)
  compositionalityᴿᴿ  (In chan0 proc0)        = cong2 In (compositionalityᴿᴿ chan0) (trans (compositionalityᴿᴿ proc0) (cong1 (proc0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (chan ∷ []))))
  compositionalityᴿᴿ  (Out chan0 chan1 proc0) = cong3 Out (compositionalityᴿᴿ chan0) (compositionalityᴿᴿ chan1) (compositionalityᴿᴿ proc0)

  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ {σ₂ = σ₂} (_ ∷ S) = trans (lift-dist-compᴿˢ {σ₂ = σ₂ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} S))

  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ Nil                               = refl
  compositionalityᴿˢ {σ₂ = σ₂} (Bang proc0)            = cong1 Bang (compositionalityᴿˢ proc0)
  compositionalityᴿˢ {σ₂ = σ₂} (Res proc0)             = cong1 Res (trans (compositionalityᴿˢ proc0) (cong1 (proc0 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (chan ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (Par proc0 proc1)       = cong2 Par (compositionalityᴿˢ proc0) (compositionalityᴿˢ proc1)
  compositionalityᴿˢ {σ₂ = σ₂} (In chan0 proc0)        = cong2 In (compositionalityᴿˢ chan0) (trans (compositionalityᴿˢ proc0) (cong1 (proc0 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (chan ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (Out chan0 chan1 proc0) = cong3 Out (compositionalityᴿˢ chan0) (compositionalityᴿˢ chan1) (compositionalityᴿˢ proc0)

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
  compositionalityˢᴿ Nil                               = refl
  compositionalityˢᴿ {σ₁ = σ₁} (Bang proc0)            = cong1 Bang (compositionalityˢᴿ proc0)
  compositionalityˢᴿ {σ₁ = σ₁} (Res proc0)             = cong1 Res (trans (compositionalityˢᴿ proc0) (cong1 (proc0 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (chan ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (Par proc0 proc1)       = cong2 Par (compositionalityˢᴿ proc0) (compositionalityˢᴿ proc1)
  compositionalityˢᴿ {σ₁ = σ₁} (In chan0 proc0)        = cong2 In (compositionalityˢᴿ chan0) (trans (compositionalityˢᴿ proc0) (cong1 (proc0 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (chan ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (Out chan0 chan1 proc0) = cong3 Out (compositionalityˢᴿ chan0) (compositionalityˢᴿ chan1) (compositionalityˢᴿ proc0)
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
  compositionalityˢˢ Nil                                         = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Bang proc0)            = cong1 Bang (compositionalityˢˢ proc0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Res proc0)             = cong1 Res (trans (compositionalityˢˢ proc0) (cong1 (proc0 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (chan ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Par proc0 proc1)       = cong2 Par (compositionalityˢˢ proc0) (compositionalityˢˢ proc1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (In chan0 proc0)        = cong2 In (compositionalityˢˢ chan0) (trans (compositionalityˢˢ proc0) (cong1 (proc0 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (chan ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Out chan0 chan1 proc0) = cong3 Out (compositionalityˢˢ chan0) (compositionalityˢˢ chan1) (compositionalityˢˢ proc0)

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
  inst-Nil instᴿ-Nil
  inst-Bang instᴿ-Bang
  inst-Res instᴿ-Res
  inst-Par instᴿ-Par
  inst-In instᴿ-In
  inst-Out instᴿ-Out
  def-id def-wkᴿ def-∙ᴿ-zero def-∙ᴿ-suc def-∘      
  assocᴿ distᴿ interactᴿ       
  comp-idᵣᴿ comp-idₗᴿ η-idᴿ η-lawᴿ
  coincidence-var
#-}
