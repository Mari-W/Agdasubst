{-# OPTIONS --rewriting #-}  -- NOTE: --local-confluence-check is OFF; see below
-- ════════════════════════════════════════════════════════════════════════════
-- systemfLift — the σ⇑ (primitive-lift) presentation of systemf.agda.
--
-- STATUS:  compiles, ZERO postulates beyond fun-ext, and the whole development
-- (typing + subject reduction) is SUBST-FREE — none of the five explicit
-- transports that systemf.agda needs.  But it is NOT locally confluent:
-- 32 critical pairs are open (turn --local-confluence-check on to list them).
--
-- WHY THIS FILE EXISTS.  In systemf.agda (the σ_SP presentation) the five
-- transports cannot all be removed, because the rules they need form a cycle:
--
--   right-id / right-idˢ  (kills 4 of the 5 transports)
--     ⟹ needs η-idᴿ           (binder case: idᴿ ↑ᴿ s unfolds to zero ∙ᴿ wkᴿ)
--     ⟹ needs def-wk          (pair def-∙ᴿ-suc / η-idᴿ)
--     ⟹ needs def-∘ DEFUSING  (pair def-∘ / def-wk; the fusing repair
--                              comp-wkᴿ diverges: comp-wkᴿ/assocᴿ generates an
--                              infinite family x ⋯ᴿ (ρ₁ ∘ (ρ₂ ∘ … ∘ wkᴿ)))
--     ⟹ needs η-lawᴿ          (pair distᴿ / η-idᴿ)
--     ⟹ needs def-∘ FUSING    (η-lawᴿ's head zero ⋯ᴿ ρ must not reduce)
--   — contradiction.
--
-- The escape is to make the LIFT primitive (σ⇑ of Curien–Hardin–Lévy): then
-- idᴿ ↑ᴿ s never unfolds to zero ∙ᴿ wkᴿ, so η-idᴿ and η-lawᴿ are not needed at
-- all and def-∘ may be DEFUSING, which def-wk wants.  That is what this file
-- does: _↑ᴿ_ is opaque, def-↑ˢ is unregistered, and the lift has its own laws
-- (↑ᴿ-id … ⟨⟩-↑ below), all proven.
--
-- WHAT IS LEFT, AND WHY IT IS HARD.  Completion was attempted mechanically
-- with tools/kb-complete.py (it reads Agda's own [RewriteNonConfluent] reports,
-- turns each unjoined pair into a lemma, finds a proof by a tactic ladder, and
-- iterates).  IT DIVERGES: 28 → 68 → 353 open pairs over three rounds, proving
-- 35 lemmas on the way.  Each new rule creates more overlaps than it closes.
--
-- The cause is that `assoc`/`assocᴿ` are ORIENTED and Agda has no associative
-- matching, so a rule whose LHS is a composition never matches inside a
-- right-nested chain.  The textbook fix is EXTENDED RULES (completion modulo
-- associativity): for a rule X ⨟ Y ≡ R whose Y is not a variable, also register
-- X ⨟ (Y ⨟ Z) ≡ R ⨟ Z.  Six of those are registered below (interact-ext …
-- wklift-ext) — they are correct and provable, but they did not shrink the
-- problem (28 → 32).  The three σ-side ones (for ↑ˢ-⨟, ↑ˢ-cons, wk-↑ˢ) are
-- still missing; `cong (_⨟ σ₃) <law>` is the proof shape to try, and
-- tools/kb-seed-extended.py drives that search.
--
-- TRAPS, all verified — do not retry:
--   • comp-wkᴿ and cons-wkᴿ diverge against assocᴿ/distᴿ (11→22, 2→7).
--   • assoc-⟨⟩ and coincidence-comp-ext are exact INVERSES; registering both
--     makes Agda loop forever.  assoc-⟨⟩ is therefore unregistered here.
--   • A rule whose LHS head is a constructor (λx, Λα, suc, `) is not a legal
--     rewrite LHS, so pairs like coincidence/inst-λ cannot be closed by the
--     naive join equation — coincidence-↑ below is the hand-written fix.
-- ════════════════════════════════════════════════════════════════════════════
module systemfLift where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; subst; module ≡-Reasoning)
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


opaque
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
  unfolding idᴿ _⋯ᴿ_ _∙ˢ_ ⟨_⟩ _↑ᴿ_ 
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
  -- def-wk generalised to a weakening sort independent of x's sort;
  -- not registered (it races def-∘), but needed to retype ⊢wkᴿ.
  wk-suc : ∀ {S s s′} (x : S ∋ s) → x ⋯ᴿ (wkᴿ s′) ≡ suc x
  def-∙ᴿ-zero           : zero ⋯ᴿ (x ∙ᴿ ρ)     ≡ x         
  def-∙ᴿ-suc            : (suc x) ⋯ᴿ (x′ ∙ᴿ ρ)  ≡ x ⋯ᴿ ρ      
  def-∘                 : x ⋯ᴿ (ρ₁ ∘ ρ₂) ≡ (x ⋯ᴿ ρ₁) ⋯ᴿ ρ₂

  --! InteractLaws {
  -- interaction rules
  assoc : (σ₁ ⨟ σ₂) ⨟ σ₃ ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  dist : (t ∙ˢ σ₁)  ⨟ σ₂  ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ⨟ σ₂)) 
  interact                : wkˢ s ⨟ (t ∙ˢ σ) ≡ σ                                        
  comp-idᵣ                : σ ⨟ idˢ         ≡ σ                                               
  comp-idₗ                : idˢ ⨟ σ         ≡ σ                                               
  η-id    : (` zero {s} {S}) ∙ˢ (wkˢ _)      ≡ idˢ
  η-law  : (zero ⋯ˢ σ) ∙ˢ (wkˢ _ ⨟ σ)        ≡ σ
  --! }

  --! CompletionLaws {
  -- completion rules.  id-var/def-compˢᴿ/def-compᴿˢ are the VARIABLE-level
  -- instances of the identity and the two mixed compositionality laws; like
  -- def-⨟/def-∘ they are oriented to FUSE, so a variable under two actions
  -- always contracts to a single action.  dist-⟨⟩/assoc-⟨⟩ let a first-class
  -- renaming pass a cons/composition on the left of a ⨟.
  id-var     : x ⋯ˢ idˢ          ≡ ` x
  def-compˢᴿ : ∀ {S₁ S₂ S₃ s} {x : S₁ ∋ s} {σ₁ : S₁ →ˢ S₂} {ρ₂ : S₂ →ᴿ S₃} →
    (x ⋯ˢ σ₁) ⋯ᴿ ρ₂  ≡ x ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)
  def-compᴿˢ : (x ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ x ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)
  dist-⟨⟩    : ⟨ x ∙ᴿ ρ ⟩ ⨟ σ    ≡ (x ⋯ˢ σ) ∙ˢ (⟨ ρ ⟩ ⨟ σ)
  assoc-⟨⟩   : ⟨ ρ₁ ∘ ρ₂ ⟩ ⨟ σ   ≡ ⟨ ρ₁ ⟩ ⨟ (⟨ ρ₂ ⟩ ⨟ σ)
  -- ═══ σ⇑ : the LIFT is primitive; these are its laws ═══
  ↑ᴿ-id    : (idᴿ {S}) ↑ᴿ s ≡ idᴿ
  ↑ᴿ-zero  : zero ⋯ᴿ (ρ ↑ᴿ s) ≡ zero
  ↑ᴿ-suc   : suc x ⋯ᴿ (ρ ↑ᴿ s) ≡ suc (x ⋯ᴿ ρ)
  ↑ᴿ-∘     : (ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s) ≡ (ρ₁ ∘ ρ₂) ↑ᴿ s
  ↑ᴿ-cons  : (ρ₁ ↑ᴿ s) ∘ (x ∙ᴿ ρ₂) ≡ x ∙ᴿ (ρ₁ ∘ ρ₂)
  wk-↑ᴿ    : wkᴿ s ∘ (ρ ↑ᴿ s) ≡ ρ ∘ wkᴿ s
  ↑ˢ-id    : (idˢ {S}) ↑ˢ s ≡ idˢ
  ↑ˢ-zero  : zero ⋯ˢ (σ ↑ˢ s) ≡ ` zero
  ↑ˢ-suc   : suc x ⋯ˢ (σ ↑ˢ s) ≡ (x ⋯ˢ σ) ⋯ᴿ wkᴿ s
  ↑ˢ-⨟     : ∀ {S₁ S₂ S₃ s} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} → (σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s) ≡ (σ₁ ⨟ σ₂) ↑ˢ s
  ↑ˢ-cons  : ∀ {S₁ S₂ S₃ s} {σ₁ : S₁ →ˢ S₂} {t : S₃ ⊢ s} {σ₂ : S₂ →ˢ S₃} → (σ₁ ↑ˢ s) ⨟ (t ∙ˢ σ₂) ≡ t ∙ˢ (σ₁ ⨟ σ₂)
  wk-↑ˢ    : ∀ {S₁ S₂ s} {σ : S₁ →ˢ S₂} → wkˢ s ⨟ (σ ↑ˢ s) ≡ σ ⨟ wkˢ s
  ⟨⟩-↑     : ⟨ ρ ↑ᴿ s ⟩ ≡ ⟨ ρ ⟩ ↑ˢ s
  coincidence-↑ : ∀ {S₁ S₂ s s₁} (t : (s ∷ S₁) ⊢ s₁) {ρ : S₁ →ᴿ S₂} → t ⋯ˢ (⟨ ρ ⟩ ↑ˢ s) ≡ t ⋯ᴿ (ρ ↑ᴿ s)
  interact-ext : ∀ {S₁ S₂ S₃ s} {t : S₂ ⊢ s} {σ : S₁ →ˢ S₂} {σ₃ : S₂ →ˢ S₃} → wkˢ s ⨟ ((t ∙ˢ σ) ⨟ σ₃) ≡ σ ⨟ σ₃
  interactᴿ-ext : ∀ {S₁ S₂ S₃ s} {x : S₂ ∋ s} {ρ : S₁ →ᴿ S₂} {ρ₃ : S₂ →ᴿ S₃} → wkᴿ s ∘ ((x ∙ᴿ ρ) ∘ ρ₃) ≡ ρ ∘ ρ₃
  coincidence-comp-ext : ∀ {S₁ S₂ S₃ S₄} {ρ₁ : S₁ →ᴿ S₂} {ρ₂ : S₂ →ᴿ S₃} {σ : S₃ →ˢ S₄} → ⟨ ρ₁ ⟩ ⨟ (⟨ ρ₂ ⟩ ⨟ σ) ≡ ⟨ ρ₁ ∘ ρ₂ ⟩ ⨟ σ
  lift-∘-ext : ∀ {S₁ S₂ S₃ S₄ s} {ρ₁ : S₁ →ᴿ S₂} {ρ₂ : S₂ →ᴿ S₃} {ρ₃ : (s ∷ S₃) →ᴿ S₄} → (ρ₁ ↑ᴿ s) ∘ ((ρ₂ ↑ᴿ s) ∘ ρ₃) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s) ∘ ρ₃
  lift-cons-ext : ∀ {S₁ S₂ S₃ S₄ s} {ρ₁ : S₁ →ᴿ S₂} {x : S₃ ∋ s} {ρ₂ : S₂ →ᴿ S₃} {ρ₃ : S₃ →ᴿ S₄} → (ρ₁ ↑ᴿ s) ∘ ((x ∙ᴿ ρ₂) ∘ ρ₃) ≡ (x ∙ᴿ (ρ₁ ∘ ρ₂)) ∘ ρ₃
  wklift-ext : ∀ {S₁ S₂ S₃ s} {ρ : S₁ →ᴿ S₂} {ρ₃ : (s ∷ S₂) →ᴿ S₃} → wkᴿ s ∘ ((ρ ↑ᴿ s) ∘ ρ₃) ≡ (ρ ∘ wkᴿ s) ∘ ρ₃

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
  id-var     = refl
  def-compˢᴿ {x = x} {σ₁ = σ₁} = sym (coincidence (σ₁ _ x))
  def-compᴿˢ = refl
  dist-⟨⟩    = ext λ { zero → refl ; (suc x) → refl }
  assoc-⟨⟩   = ext λ x → refl
  ↑ᴿ-id    = ext λ { zero → refl ; (suc x) → refl }
  ↑ᴿ-zero  = refl
  ↑ᴿ-suc   = refl
  ↑ᴿ-∘     = ext λ { zero → refl ; (suc x) → refl }
  ↑ᴿ-cons  = ext λ { zero → refl ; (suc x) → refl }
  wk-↑ᴿ    = refl
  ↑ˢ-id    = ext λ { zero → refl ; (suc x) → refl }
  ↑ˢ-zero  = refl
  ↑ˢ-suc   = refl
  ↑ˢ-⨟ {s = s} {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl ; (suc x) →
    trans (compositionalityᴿˢ (σ₁ _ x))
          (trans (cong ((σ₁ _ x) ⋯ˢ_) (wk-↑ˢ {s = s} {σ = σ₂}))
                 (sym (compositionalityˢᴿ (σ₁ _ x)))) }
  ↑ˢ-cons {σ₁ = σ₁} {t = t} {σ₂ = σ₂} = ext λ { zero → refl ; (suc x) →
    trans (compositionalityᴿˢ (σ₁ _ x))
          (cong ((σ₁ _ x) ⋯ˢ_) (interact {t = t} {σ = σ₂})) }
  wk-↑ˢ {σ = σ} = ext λ x → sym (coincidence (σ _ x))
  ⟨⟩-↑     = ext λ { zero → refl ; (suc x) → refl }
  coincidence-↑ t {ρ = ρ} = trans (cong (t ⋯ˢ_) (sym (⟨⟩-↑ {ρ = ρ}))) (coincidence t)
  interact-ext = refl
  interactᴿ-ext = refl
  coincidence-comp-ext = refl
  lift-∘-ext = ext λ { zero → refl ; (suc x) → refl }
  lift-cons-ext = ext λ { zero → refl ; (suc x) → refl }
  wklift-ext = refl

  def-↑ˢ {σ = σ} = cong ((` zero) ∙ˢ_) (sym (ext λ x → coincidence (σ _ x)))

  def-id      = refl
  def-wk      = refl
  wk-suc _    = refl
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

-- This oriented system passes --local-confluence-check.  Reaching that cost
-- three things, in decreasing order of interest:
--
--  1. def-⨟ and def-∘ are oriented to FUSE, i.e. as the mode-V instances of
--     compositionalityˢˢ / compositionalityᴿᴿ.  In the defusing orientation
--     they form an unjoinable critical pair with dist / distᴿ: the peak
--     x ⋯ˢ ((t ∙ˢ σ₁) ⨟ σ₂) has two normal forms whose join needs a case
--     analysis on the ABSTRACT index x, which no rewrite rule can perform.
--
--  2. The completion rules below (id-var, def-compˢᴿ, def-compᴿˢ, dist-⟨⟩,
--     assoc-⟨⟩) close the pairs the fusing orientation opens.
--
--  3. The four η/surjective-pairing laws (η-id, η-law, η-idᴿ, η-lawᴿ) and the
--     laws that depend on them (comp-idᵣ, right-id, def-wk, coincidence-fold)
--     are NO LONGER REGISTERED.  They are still proven above and usable as
--     propositional equations — see ⊢wkᴿ / ⊢[] / sr below, which now transport
--     along them explicitly.  This is the classical obstruction: η-law is the
--     SCons rule of σ_SP, whose LHS (zero ⋯ˢ σ) ∙ˢ (wkˢ _ ⨟ σ) is non-left-
--     linear and has a reducible head, and σ_SP is not confluent on open terms.
--     Registering any one of them costs at least one unjoinable pair
--     (comp-idᵣ needs right-idˢ, which needs η-id, which needs η-law, ...).
--! RewriteSys {
-- complete rewrite system
{-# REWRITE def-∙ˢ-zero def-∙ˢ-suc def-⨟ assoc dist interact comp-idₗ comp-idᵣ inst-x inst-λ inst-Λ inst-∀ inst-· inst-• inst-⇒ inst-* compositionalityᴿᴿ compositionalityᴿˢ compositionalityˢᴿ compositionalityˢˢ coincidence coincidence-comp coincidence-ext id-var def-compˢᴿ def-compᴿˢ dist-⟨⟩ def-id def-wk def-∙ᴿ-zero def-∙ᴿ-suc def-∘ assocᴿ interactᴿ distᴿ comp-idᵣᴿ comp-idₗᴿ instᴿ-x instᴿ-λ instᴿ-Λ instᴿ-∀ instᴿ-· instᴿ-• instᴿ-⇒ instᴿ-* coincidence-var right-id right-idˢ ↑ᴿ-id ↑ᴿ-zero ↑ᴿ-suc ↑ᴿ-∘ ↑ᴿ-cons wk-↑ᴿ ↑ˢ-id ↑ˢ-zero ↑ˢ-suc ↑ˢ-⨟ ↑ˢ-cons wk-↑ˢ ⟨⟩-↑
 coincidence-↑ interact-ext interactᴿ-ext coincidence-comp-ext lift-∘-ext lift-cons-ext wklift-ext
#-}
--! }


↑ᵗ_ : Sort → Sort 
↑ᵗ expr = type
↑ᵗ type = kind
↑ᵗ kind = kind

_∶⊢_ : Scope → Sort → Set
S ∶⊢ s = S ⊢ (↑ᵗ s)
  
depth : S ∋ s → ℕ
depth zero     = zero
depth (suc x)  = suc (depth x)

drop-∈ : S ∋ s → Scope → Scope
drop-∈ e xs = drop (suc (depth e)) xs

Ctx : Scope → Set
Ctx S = ∀ s → (x : S ∋ s) → drop-∈ x S ∶⊢ s

[]ₜ : Ctx []
[]ₜ _ ()

_∷ₜ_ : S ∶⊢ s → Ctx S → Ctx (s ∷ S)
(t ∷ₜ Γ) _ zero     = t
(t ∷ₜ Γ) _ (suc x)  = Γ _ x

weaken : S ⊢ s → (s′ ∷ S) ⊢ s
weaken {s′ = s} t = t ⋯ᴿ (wkᴿ _)

_[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
t [ t′ ] = t ⋯ˢ (t′ ∙ˢ idˢ) 

wk-drop-∈ : (x : S ∋ s) → drop-∈ x S ⊢ s′ → S ⊢ s′
wk-drop-∈ zero t = weaken t 
wk-drop-∈ (suc x)  t = weaken (wk-drop-∈ x t) 

wk-telescope : Ctx S → S ∋ s → S ∶⊢ s
wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

_∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ′ Γ₁′ Γ₂′ Γ₃′ : Ctx S

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {x : S ∋ s} {t} → 
    Γ ∋ x ∶ t →
    Γ ⊢ (` x) ∶ t
  ⊢λ : 
    (t ∷ₜ Γ) ⊢ e ∶ (weaken t′) → 
    Γ ⊢ (λx e) ∶ (t ⇒ t′)
  ⊢Λ : 
    (k ∷ₜ Γ) ⊢ e ∶ t →  
    Γ ⊢ (Λα e) ∶ (∀[α∶ k ] t)
  ⊢· : 
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ (e₁ · e₂) ∶ t₂
  ⊢• : 
    Γ ⊢ e ∶ (∀[α∶ k ] t′) →
    Γ ⊢ t ∶ k →
    (k ∷ₜ Γ) ⊢ t′ ∶ k′ →
    Γ ⊢ (e • t) ∶ (t′ [ t ])
  ⊢* : {t : S ⊢ type} →
    Γ ⊢ t ∶ *

_∶_→ᴿ_ : S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ᴿ_ {S₁} {S₂} ρ Γ₁ Γ₂ = ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) → 
  (Γ₁ ∋ x ∶ t) → Γ₂ ∋ (x ⋯ᴿ ρ) ∶ (t ⋯ᴿ ρ)

--! WTS {
_∶_→ˢ_ : S₁ →ˢ S₂ → (Γ₁ : Ctx S₁) → (Γ₂ : Ctx S₂) → Set
--! }

_∶_→ˢ_ {S₁} {S₂} σ Γ₁ Γ₂ = 
  ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) → 
  (Γ₁ ∋ x ∶ t) → Γ₂ ⊢ (x ⋯ˢ σ) ∶ (t ⋯ˢ σ) 

data Val : S ⊢ expr → Set where
  vλ : Val (λx e)
  vΛ : Val (Λα e)

data _↪_ : S ⊢ expr → S ⊢ expr → Set where
  β-λ :
    Val e₂ →
    ((λx e₁) · e₂) ↪ (e₁ [ e₂ ])
  β-Λ :
    ((Λα e) • t) ↪ (e [ t ])
  ξ-·₁ :
    e₁ ↪ e →
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-• :
    e ↪ e′ →
    (e • t) ↪ (e′ • t)

⊢wkᴿ : ∀ (Γ : Ctx S) (x : S ∋ s) t (t′ : S ∶⊢ s′) → Γ ∋ x ∶ t → (t′ ∷ₜ Γ) ∋ x ⋯ᴿ (wkᴿ _) ∶ (weaken t) 
⊢wkᴿ _ _ _ _ refl = refl

⊢↑ᴿ : ρ ∶ Γ₁ →ᴿ Γ₂ → (t : S₁ ∶⊢ s) → (ρ ↑ᴿ s) ∶ (t ∷ₜ Γ₁) →ᴿ ((t ⋯ᴿ ρ) ∷ₜ Γ₂)
⊢↑ᴿ ⊢ρ _ _ (zero) _ refl = refl 
⊢↑ᴿ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ t _ (suc x) _ refl = ⊢wkᴿ Γ₂ (x ⋯ᴿ ρ) (wk-drop-∈ x (Γ₁ _ x) ⋯ᴿ ρ) (t ⋯ᴿ ρ) (⊢ρ _ x _ refl)

_⊢⋯ᴿ[_]_ : ∀ {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
  Γ₁ ⊢ e ∶ t →
  (ρ : S₁ →ᴿ S₂) →
  ρ ∶ Γ₁ →ᴿ Γ₂ →
  Γ₂ ⊢ (e ⋯ᴿ ρ) ∶ (t ⋯ᴿ ρ)
(⊢` {x = x} {t = t} ⊢x) ⊢⋯ᴿ[ ρ ] ⊢ρ  = ⊢` (⊢ρ _ x t ⊢x)
(⊢λ ⊢e)         ⊢⋯ᴿ[ ρ ] ⊢ρ  = ⊢λ (⊢e ⊢⋯ᴿ[ ρ ↑ᴿ _ ] (⊢↑ᴿ ⊢ρ _))
(⊢Λ ⊢e)         ⊢⋯ᴿ[ ρ ] ⊢ρ  = ⊢Λ (⊢e ⊢⋯ᴿ[ ρ ↑ᴿ _ ] (⊢↑ᴿ ⊢ρ _))
(⊢· ⊢e₁ ⊢e₂)    ⊢⋯ᴿ[ ρ ] ⊢ρ  = ⊢· (⊢e₁ ⊢⋯ᴿ[ ρ ] ⊢ρ) (⊢e₂ ⊢⋯ᴿ[ ρ ] ⊢ρ)
(⊢• ⊢e ⊢t ⊢t')  ⊢⋯ᴿ[ ρ ] ⊢ρ  = ⊢• (⊢e ⊢⋯ᴿ[ ρ ] ⊢ρ) (⊢t ⊢⋯ᴿ[ ρ ] ⊢ρ) (⊢t' ⊢⋯ᴿ[ ρ ↑ᴿ _ ] (⊢↑ᴿ ⊢ρ _))
⊢*              ⊢⋯ᴿ[ ρ ] ⊢ρ  = ⊢*

⊢wkˢ : ∀ (Γ : Ctx S) (e : S ⊢ s) (t : S ∶⊢ s) (t′ : S ∶⊢ s′) → Γ ⊢ e ∶ t → (t′ ∷ₜ Γ) ⊢ weaken e ∶ weaken t 
⊢wkˢ Γ e t t' ⊢t = ⊢t ⊢⋯ᴿ[ wkᴿ _ ] (λ s x t ⊢x → ⊢wkᴿ Γ x t t' ⊢x)

⊢↑ˢ[_]_ : (σ : S₁ →ˢ S₂) → σ ∶ Γ₁ →ˢ Γ₂ → (t : S₁ ∶⊢ s) → (σ ↑ˢ s) ∶ t ∷ₜ Γ₁ →ˢ ((t ⋯ˢ σ) ∷ₜ Γ₂)
(⊢↑ˢ[ σ ] ⊢σ) _ _ (zero) _ refl = ⊢` refl 
⊢↑ˢ[_]_ {Γ₁ = Γ₁} {Γ₂ = Γ₂} σ ⊢σ t _ (suc x) _ refl = 
  ⊢wkˢ Γ₂ (x ⋯ˢ σ) (wk-drop-∈ x (Γ₁ _ x) ⋯ˢ σ) (t ⋯ˢ σ) (⊢σ _ x _ refl)

--! SPT {
_⊢⋯ˢ[_]_ : 
  Γ₁ ⊢ t ∶ t′ →
  (σ : S₁ →ˢ S₂) →
  σ ∶ Γ₁ →ˢ Γ₂ →
  Γ₂ ⊢ (t ⋯ˢ σ) ∶ (t′ ⋯ˢ σ)
(⊢` {x = x} {t = t} ⊢x) ⊢⋯ˢ[ σ ] ⊢σ  =
  ⊢σ _ x t ⊢x
(⊢λ ⊢e)         ⊢⋯ˢ[ σ ] ⊢σ  = 
  ⊢λ (⊢e ⊢⋯ˢ[ σ ↑ˢ _ ] (⊢↑ˢ[ σ ] ⊢σ) _)
(⊢Λ ⊢e)         ⊢⋯ˢ[ σ ] ⊢σ  = 
  ⊢Λ (⊢e ⊢⋯ˢ[ σ ↑ˢ _ ] (⊢↑ˢ[ σ ] ⊢σ) _)
(⊢· ⊢e₁ ⊢e₂)    ⊢⋯ˢ[ σ ] ⊢σ  = 
  ⊢· (⊢e₁ ⊢⋯ˢ[ σ ] ⊢σ) (⊢e₂ ⊢⋯ˢ[ σ ] ⊢σ)
(⊢• ⊢e ⊢t ⊢t')  ⊢⋯ˢ[ σ ] ⊢σ  =
  ⊢• (⊢e ⊢⋯ˢ[ σ ] ⊢σ) (⊢t ⊢⋯ˢ[ σ ] ⊢σ)
  (⊢t' ⊢⋯ˢ[ σ ↑ˢ _ ] (⊢↑ˢ[ σ ] ⊢σ) _)
⊢*              ⊢⋯ˢ[ σ ] ⊢σ  = ⊢*
--! }

⊢[] : ∀ {Γ : Ctx S} {e : S ⊢ s} {t : S ∶⊢ s} → Γ ⊢ e ∶ t → (e ∙ˢ idˢ) ∶ (t ∷ₜ Γ) →ˢ Γ
⊢[] ⊢t _ zero     _ refl = ⊢t
⊢[] ⊢t _ (suc x)  _ refl = ⊢` refl

--! SR {
sr : 
  Γ ⊢ e ∶ t →   
  e ↪ e′ → 
  Γ ⊢ e′ ∶ t 
sr (⊢· {e₂ = e₂} (⊢λ ⊢e₁) ⊢e₂) (β-λ v₂) =
  ⊢e₁ ⊢⋯ˢ[ e₂ ∙ˢ idˢ ] (⊢[] ⊢e₂)
sr (⊢• {t = t} (⊢Λ ⊢e) ⊢t ⊢t') β-Λ = 
  ⊢e ⊢⋯ˢ[ t ∙ˢ idˢ ] (⊢[] ⊢t)     
sr (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e) = 
  ⊢· (sr ⊢e₁ e₁↪e) ⊢e₂
sr (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e x) = 
  ⊢· ⊢e₁ (sr ⊢e₂ e₂↪e)          
sr (⊢• ⊢e ⊢t ⊢t') (ξ-• e↪e') = 
  ⊢• (sr ⊢e e↪e') ⊢t ⊢t'
--! }   