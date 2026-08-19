{-# OPTIONS --rewriting --local-confluence-check --type-in-type #-}
-- ⚠ INCOMPLETE PORT — *EXPECTED TO FAIL* (exit 42) ⚠
-- The Agdasubst2 canonicity prototype, retargeted from `SystemF-fresh`
-- to the CURRENT esop27 `SystemF` (full β, `Normal` instead of `Value`).
-- Ported so far: --type-in-type added (the prototype needs it and its
-- OPTIONS line lacked it); `Neutral` hidden from the import; ξ-· split
-- into ξ-·₁/ξ-·₂; `·-inv` returns a sum; `⟦⟧-exp`'s ⇒-case gains an
-- SN-induction; `sn-λx` takes the body's SN; `Value`→`Normal`;
-- `progress` loses its NoVar argument.
-- STILL BROKEN: the λ- and Λ-cases of `fundamental`, which under full β
-- need the double induction of SystemF-strat §16 (`⟦⟧-β-λ`) plus a
-- substitution-congruence lemma (`sub-⟶*`) that the prototype does not
-- have.  See §3 of REPORT-canonicity-port.md.
-- Nothing imports this file.
-- ════════════════════════════════════════════════════════════════════
-- CANONICITY FOR THE INTRINSICALLY TYPED SYSTEM F OF SystemF-fresh
--
-- Theorem (canonicity):  every CLOSED expression  e : Expr ∅ T
-- reduces to a value.  Since the syntax is intrinsically typed,
-- preservation is definitional, and progress is already proved in
-- SystemF-fresh; canonicity is the remaining half — termination —
-- and it is proved here by a Girard-style logical relation.
--
-- ON --type-in-type.  System F's reducibility argument is IMPREDICATIVE:
-- the interpretation of ∀α.T quantifies over the collection of all
-- semantic types, and then instantiates that quantifier with the
-- interpretation of a type — which is itself a semantic type.  In a
-- predicative hierarchy the quantification lands one universe above the
-- thing it must produce, and no re-indexing repairs it (this is exactly
-- Girard's observation that System F cannot be normalised by a
-- predicative argument).  The proof below is the standard reducibility
-- argument, unchanged; the ONLY thing --type-in-type does is switch off
-- the universe check that this impredicativity trips.  SystemF-fresh
-- itself is not affected: the flag is local to this module.
-- ════════════════════════════════════════════════════════════════════
module SystemF-canonicity where

open import SystemF hiding (Neutral)

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin using (zero; suc) renaming (Fin to Var)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- (the generalizable variables n, T, Γ, η, ζ, … come from SystemF-fresh)

-- ═══ §0  The expression traversal laws, as REWRITE RULES ════════════
-- These are the laws SystemF-fresh cannot certify locally confluent
-- (their LHS carries the computed index T [ η₁ ]ˢ).  Every one of them
-- is a proved THEOREM there, so registering them is SOUND — what is
-- given up is the local-confluence certificate, not consistency.  This
-- module carries no --local-confluence-check, so SystemF-fresh keeps
-- its certificate untouched.
--
-- WHAT THIS BUYS: the semantic substitution lemma was already
-- definitional; with these registered, three of the five transports the
-- proof used disappear as well — the λ- and Λ-redex substitution steps
-- (§12 `go`, `inst`) and the Λ-dimension variable case (§12 `⊨∙*`).
--
-- WHAT IT COSTS, precisely: folding compositionality normalises the
-- SINGLE substitutions `_[_]` and `_[*_*]` away, because each is itself
-- a traversal.  So at a substituted redex the term no longer has the
-- syntactic shape `e₁ [ e₂ ]` that the CONSTRUCTOR β-λ is stated in,
-- and Agda can no longer invert it — `⟶-sub` below must transport to
-- put that shape back.  Those two `rewrite`s are therefore NOT about
-- type indices at all; they re-expose the reduction rule's own form.
-- Making `_[_]` and `_[*_*]` opaque would remove them too, at the price
-- of `_[_]`-typed goals no longer computing.
{-# REWRITE Compositionalityᴿᴿ Compositionalityᴿˢ Compositionalityˢᴿ Compositionalityˢˢ #-}
{-# REWRITE Beta-compᴿ Beta-compˢ #-}
{-# REWRITE Beta-ext-suc*ᴿ Beta-ext-sucˢ* #-}
{-# REWRITE Beta-⇑ˢ-zero Beta-⇑ˢ-suc Beta-⇑ˢ*-suc* #-}

-- ═══ §1  Reduction sequences ════════════════════════════════════════

⟶*-trans : ∀ {n} {Γ : Ctx n} {T} {e₁ e₂ e₃ : Expr Γ T} →
           e₁ ⟶* e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃
⟶*-trans ⟶refl              q = q
⟶*-trans (⟶trans s p)  q = ⟶trans s (⟶*-trans p q)

ξ-·₁* : ∀ {n} {Γ : Ctx n} {T₁ T₂} {e₁ e₁′ : Expr Γ (T₁ ⇒ T₂)} {e₂ : Expr Γ T₁} →
        e₁ ⟶* e₁′ → (e₁ · e₂) ⟶* (e₁′ · e₂)
ξ-·₁* ⟶refl             = ⟶refl
ξ-·₁* (⟶trans s p) = ⟶trans (ξ-·₁ s) (ξ-·₁* p)

ξ-Λ* : ∀ {n} {Γ : Ctx n} {T} {e e′ : Expr (Γ ▷*) T} →
       e ⟶* e′ → (Λα e) ⟶* (Λα e′)
ξ-Λ* ⟶refl             = ⟶refl
ξ-Λ* (⟶trans s p) = ⟶trans (ξ-Λ s) (ξ-Λ* p)

ξ-·*ᵉ : ∀ {n} {Γ : Ctx n} {T} {e e′ : Expr Γ (∀α T)} {T′ : Type n} →
        e ⟶* e′ → (e ·* T′) ⟶* (e′ ·* T′)
ξ-·*ᵉ ⟶refl             = ⟶refl
ξ-·*ᵉ (⟶trans s p) = ⟶trans (ξ-·* s) (ξ-·*ᵉ p)

-- ═══ §2  Halting ════════════════════════════════════════════════════

record Halts {n} {Γ : Ctx n} {T} (e : Expr Γ T) : Set where
  constructor halts
  field
    {result}  : Expr Γ T
    reduction : e ⟶* result
    value     : Normal result

open Halts public

halts-value : ∀ {n} {Γ : Ctx n} {T} {e : Expr Γ T} → Normal e → Halts e
halts-value v = halts ⟶refl v

halts-expand : ∀ {n} {Γ : Ctx n} {T} {e e′ : Expr Γ T} → e ⟶ e′ → Halts e′ → Halts e
halts-expand s (halts p v) = halts (⟶trans s p) v

halts-Λ : ∀ {n} {Γ : Ctx n} {T} {e : Expr (Γ ▷*) T} → Halts e → Halts (Λα e)
halts-Λ (halts p v) = halts (ξ-Λ* p) (Λα v)

-- Strong normalisation, as accessibility.  The logical relation is built
-- on SN rather than on Halts for one reason: SN REFLECTS along a
-- substitution by a one-line argument (§11), whereas Halts would need
-- either an inversion of substitution (blocked: `e ·* A` has a computed
-- type index, so Agda cannot split the head of an application) or
-- determinism of ⟶ (false: (Λα e) ·* A can both β-Λ and reduce under Λ).
-- `progress` turns SN back into Halts at the very end.
data SN {n} {Γ : Ctx n} {T} (e : Expr Γ T) : Set where
  acc : (∀ {e′} → e ⟶ e′ → SN e′) → SN e

sn-step : ∀ {n} {Γ : Ctx n} {T} {e e′ : Expr Γ T} → SN e → e ⟶ e′ → SN e′
sn-step (acc f) s = f s

-- PORTED TO FULL β: `λx e` now steps (ξ-λ), so this needs the body's SN.
sn-λx : ∀ {n} {Γ : Ctx n} {T₁ T₂} {e : Expr (Γ ▷ T₁) T₂} → SN e → SN (λx e)
sn-λx (acc f) = acc λ { (ξ-λ s) → sn-λx (f s) }

sn-Λ : ∀ {n} {Γ : Ctx n} {T} {e : Expr (Γ ▷*) T} → SN e → SN (Λα e)
sn-Λ (acc f) = acc λ { (ξ-Λ s) → sn-Λ (f s) }

-- SN ⇒ Halts, via the artifact's own `progress`
sn-halts : ∀ {n} {Γ : Ctx n} {T} → NoVar Γ → (e : Expr Γ T) → SN e → Halts e
sn-halts nv e (acc f) with progress e
... | done v  = halts ⟶refl v
... | step st = halts-expand st (sn-halts nv _ (f st))

-- neutral = not a value former.  Defined by matching on an expression of
-- GENERAL type, which is why (unlike splitting the head of an
-- application) it costs nothing.
Neutral : ∀ {n} {Γ : Ctx n} {T} → Expr Γ T → Set
Neutral (` _)    = ⊤
Neutral (λx _)   = ⊥
Neutral (Λα _)   = ⊥
Neutral (_ · _)  = ⊤
Neutral (_ ·* _) = ⊤

-- ═══ §3  Semantic types ═════════════════════════════════════════════
-- A candidate is a predicate on CLOSED expressions of a CLOSED type.
-- The closure conditions are Girard's CR1 (reducible ⇒ halting) and
-- backward closure under a step.  There is no CR3/neutral condition:
-- the ambient context is ∅, so by `progress` every closed expression is
-- a value or steps, and neutrals never arise.
-- The CR proof is kept OUT of the semantic type, so that semantic types
-- and environments are proof-free records — which is what lets §4 state
-- their σ-calculus as rewrite rules.

Pred : Type 0 → Set
Pred A = Expr ∅ A → Set

record CR {A : Type 0} (P : Pred A) : Set where
  field
    cr-sn   : ∀ {e} → P e → SN e                                    -- CR1
    cr-fwd  : ∀ {e e′} → e ⟶ e′ → P e → P e′                      -- CR2
    cr-exp  : ∀ {e} → Neutral e → (∀ {e′} → e ⟶ e′ → P e′) → P e  -- CR3

open CR public

-- SN itself is a candidate — used as the dummy semantic type when the
-- Λ-case needs *some* instantiation to reflect halting through.
CR-SN : ∀ {A : Type 0} → CR (SN {Γ = ∅} {T = A})
cr-sn  CR-SN     = λ x → x
cr-fwd CR-SN s x = sn-step x s
cr-exp CR-SN _ h = acc h

SemTy : Set
SemTy = Σ[ A ∈ Type 0 ] Pred A

-- ═══ §4  Semantic environments ══════════════════════════════════════
-- An environment carries its SYNTACTIC part as a genuine `Sub n 0`, so
-- every index below is spelled in the σ-calculus and normalised by the
-- registered rewrite rules.  `sem ρ α` is indexed by `α &ˢ syn ρ`,
-- which is exactly the normal form of `(` α) [ syn ρ ]ˢ`.

record Env (n : Nat) : Set where
  constructor env
  field
    syn : Sub n 0
    sem : (α : Var n) → Pred (α &ˢ syn)

open Env public

Env-ext : {s : Sub n 0} {f g : (α : Var n) → Pred (α &ˢ s)} →
          (∀ α → f α ≡ g α) → env s f ≡ env s g
Env-ext {s = s} p = cong (env s) (fun-ext p)

CREnv : Env n → Set
CREnv ρ = ∀ α → CR (sem ρ α)

-- cons.  Both index equations —
--   zero  &ˢ (A ∙ˢ s) ≡ A         (beta-ext-zero)
--   suc α &ˢ (A ∙ˢ s) ≡ α &ˢ s    (beta-ext-suc)
-- — are registered, so the clauses typecheck with no coercion.
_∷ᴱ_ : SemTy → Env n → Env (1 + n)
syn (S ∷ᴱ ρ)          = proj₁ S ∙ˢ syn ρ
sem (S ∷ᴱ ρ) zero     = proj₂ S
sem (S ∷ᴱ ρ) (suc α)  = sem ρ α

CREnv-∷ : {S : SemTy} {ρ : Env n} → CR (proj₂ S) → CREnv ρ → CREnv (S ∷ᴱ ρ)
CREnv-∷ cr c zero     = cr
CREnv-∷ cr c (suc α)  = c α

-- composition with a RENAMING.  beta-⟨⟩-⨟ makes the index work out.
_⟨_⟩ᴱ : Env n₂ → Ren n₁ n₂ → Env n₁
syn (ρ ⟨ ζ ⟩ᴱ)    = ⟨ ζ ⟩ ⨟ˢ syn ρ
sem (ρ ⟨ ζ ⟩ᴱ) α  = sem ρ (α &ᴿ ζ)

CREnv-⟨⟩ : {ρ : Env n₂} (ζ : Ren n₁ n₂) → CREnv ρ → CREnv (ρ ⟨ ζ ⟩ᴱ)
CREnv-⟨⟩ ζ c α = c (α &ᴿ ζ)

-- ═══ §5  The σ-calculus of semantic environments, ᴿ-fragment ════════
-- Environments form a σ-ALGEBRA: cons is _∷ᴱ_, composition is _⟨_⟩ᴱ /
-- _⟪_⟫ᴱ, and the laws below are the same laws as at the type level.
-- Each of them holds because the corresponding TYPE-level rule already
-- computes on the `syn` component — e.g. ⟨⟩-↑-cons for ∷-⟨⟩↑, interact
-- for ∷-⟨⟩wk, comp-idₗ for ⟨⟩-id — so the proofs are Env-ext of refl.
-- They ARE registrable: every LHS argument (_∷ᴱ_, ↑ᴿ, wkᴿ, idᴿ) is
-- pattern-inert.

∷-⟨⟩↑ : ∀ {S : SemTy} {ρ : Env n₂} (ζ : Ren n₁ n₂) →
        (S ∷ᴱ ρ) ⟨ ζ ↑ᴿ ⟩ᴱ ≡ S ∷ᴱ (ρ ⟨ ζ ⟩ᴱ)          -- ⟨⟩-↑-cons
∷-⟨⟩↑ ζ = Env-ext λ { zero → refl ; (suc α) → refl }

∷-⟨⟩wk : ∀ {S : SemTy} {ρ : Env n} → (S ∷ᴱ ρ) ⟨ wkᴿ ⟩ᴱ ≡ ρ    -- interact
∷-⟨⟩wk = Env-ext λ α → refl

⟨⟩-id : (ρ : Env n) → ρ ⟨ idᴿ ⟩ᴱ ≡ ρ                          -- comp-idₗ
⟨⟩-id ρ = Env-ext λ α → refl

{-# REWRITE ∷-⟨⟩↑ ∷-⟨⟩wk ⟨⟩-id #-}

-- ═══ §6  The logical relation ═══════════════════════════════════════
-- The ∀-clause typechecks with no coercion at all:
--   ((∀α T) [ s ]ˢ) = ∀α (T [ s ↑ˢ ]ˢ)              (traversal clause)
--   (T [ s ↑ˢ ]ˢ) [ A ]*  ≡  T [ A ∙ˢ s ]ˢ
-- the latter by compositionalityˢˢ ▸ lift-cons ▸ comp-idᵣ, all three
-- REGISTERED — so the index of `e ·* A` is already `syn (S ∷ᴱ ρ)`.

⟦_⟧ : (T : Type n) (ρ : Env n) → Pred (T [ syn ρ ]ˢ)
⟦ ` α      ⟧ ρ e = sem ρ α e
⟦ T₁ ⇒ T₂  ⟧ ρ e = SN e × (∀ e′ → ⟦ T₁ ⟧ ρ e′ → ⟦ T₂ ⟧ ρ (e · e′))
⟦ ∀α T     ⟧ ρ e = SN e ×
                   (∀ (S : SemTy) → CR (proj₂ S) → ⟦ T ⟧ (S ∷ᴱ ρ) (e ·* proj₁ S))

⟦⟧-sn : (T : Type n) (ρ : Env n) → CREnv ρ → ∀ {e} → ⟦ T ⟧ ρ e → SN e
⟦⟧-sn (` α)     ρ c = cr-sn (c α)
⟦⟧-sn (T₁ ⇒ T₂) ρ c = proj₁
⟦⟧-sn (∀α T)    ρ c = proj₁

⟦⟧-fwd : (T : Type n) (ρ : Env n) → CREnv ρ →
         ∀ {e e′} → e ⟶ e′ → ⟦ T ⟧ ρ e → ⟦ T ⟧ ρ e′
⟦⟧-fwd (` α)     ρ c s r        = cr-fwd (c α) s r
⟦⟧-fwd (T₁ ⇒ T₂) ρ c s (sn , f) =
  sn-step sn s , λ e″ r → ⟦⟧-fwd T₂ ρ c (ξ-·₁ s) (f e″ r)
⟦⟧-fwd (∀α T)    ρ c s (sn , f) =
  sn-step sn s , λ S cr → ⟦⟧-fwd T (S ∷ᴱ ρ) (CREnv-∷ cr c) (ξ-·* s) (f S cr)

-- inversion of a step out of a neutral application.  Stated with the
-- index in its CANONICAL spelling (T₂ resp. T [ A ]*) so that Agda's
-- unifier can split the step; at the call sites the index is a
-- σ-calculus normal form that is DEFINITIONALLY equal to it.
-- PORTED TO FULL β: the current SystemF has ξ-·₂ as well as ξ-·₁, so a
-- step out of a neutral application can be in the ARGUMENT too.  The
-- conclusion is therefore a sum, not a single Σ.
·-inv : ∀ {n} {Γ : Ctx n} {T₁ T₂} (e₁ : Expr Γ (T₁ ⇒ T₂)) (e₂ : Expr Γ T₁)
          {t : Expr Γ T₂} → Neutral e₁ → (e₁ · e₂) ⟶ t →
        (Σ[ e₁′ ∈ Expr Γ (T₁ ⇒ T₂) ] ((e₁ ⟶ e₁′) × (t ≡ e₁′ · e₂)))
        ⊎ (Σ[ e₂′ ∈ Expr Γ T₁ ] ((e₂ ⟶ e₂′) × (t ≡ e₁ · e₂′)))
·-inv (λx _) e₂ () β-λ
·-inv e₁     e₂ nl (ξ-·₁ s) = inj₁ (_ , s , refl)
·-inv e₁     e₂ nl (ξ-·₂ s) = inj₂ (_ , s , refl)

·*-inv : ∀ {n} {Γ : Ctx n} {T} (e : Expr Γ (∀α T)) (A : Type n)
           {t : Expr Γ (T [ A ]*)} → Neutral e → (e ·* A) ⟶ t →
         Σ[ e′ ∈ Expr Γ (∀α T) ] ((e ⟶ e′) × (t ≡ e′ ·* A))
·*-inv (Λα _) A () β-Λ
·*-inv e      A nl (ξ-·* s) = _ , s , refl

⟦⟧-exp : (T : Type n) (ρ : Env n) → CREnv ρ →
         ∀ {e} → Neutral e → (∀ {e′} → e ⟶ e′ → ⟦ T ⟧ ρ e′) → ⟦ T ⟧ ρ e
⟦⟧-exp (` α)     ρ c nl h = cr-exp (c α) nl h
-- PORTED TO FULL β: the argument can now step, so the ⇒-case runs an
-- inner induction on `SN e″` (the same shape as SystemF-strat §15's `aux`).
⟦⟧-exp (T₁ ⇒ T₂) ρ c {e} nl h =
  acc (λ s → ⟦⟧-sn (T₁ ⇒ T₂) ρ c (h s)) , λ e″ r → aux e″ r (⟦⟧-sn T₁ ρ c r)
  where
    aux : ∀ e″ → ⟦ T₁ ⟧ ρ e″ → SN e″ → ⟦ T₂ ⟧ ρ (e · e″)
    aux e″ r (acc g) = ⟦⟧-exp T₂ ρ c tt go
      where
        go : ∀ {t} → (e · e″) ⟶ t → ⟦ T₂ ⟧ ρ t
        go st with ·-inv e e″ nl st
        ... | inj₁ (e₀ , s , refl) = proj₂ (h s) e″ r
        ... | inj₂ (e₀ , s , refl) = aux e₀ (⟦⟧-fwd T₁ ρ c s r) (g s)
⟦⟧-exp (∀α T)    ρ c {e} nl h =
  acc (λ s → ⟦⟧-sn (∀α T) ρ c (h s)) ,
  λ S cr → ⟦⟧-exp T (S ∷ᴱ ρ) (CREnv-∷ cr c) tt (go S cr)
  where
    go : ∀ S (cr : CR (proj₂ S)) {t} → (e ·* proj₁ S) ⟶ t → ⟦ T ⟧ (S ∷ᴱ ρ) t
    go S cr st with ·*-inv e (proj₁ S) nl st
    ... | e₀ , s , refl = proj₂ (h s) S cr

⟦⟧-CR : (T : Type n) (ρ : Env n) → CREnv ρ → CR (⟦ T ⟧ ρ)
cr-sn  (⟦⟧-CR T ρ c) = ⟦⟧-sn T ρ c
cr-fwd (⟦⟧-CR T ρ c) = ⟦⟧-fwd T ρ c
cr-exp (⟦⟧-CR T ρ c) = ⟦⟧-exp T ρ c

⟦⟧-fwd* : (T : Type n) (ρ : Env n) → CREnv ρ →
          ∀ {e e′} → e ⟶* e′ → ⟦ T ⟧ ρ e → ⟦ T ⟧ ρ e′
⟦⟧-fwd* T ρ c ⟶refl        r = r
⟦⟧-fwd* T ρ c (⟶trans s p) r = ⟦⟧-fwd* T ρ c p (⟦⟧-fwd T ρ c s r)

-- the semantic type carried by a syntactic type under an environment
⟦_⟧ᵀ : (T : Type n) (ρ : Env n) → SemTy
⟦ T ⟧ᵀ ρ = T [ syn ρ ]ˢ , ⟦ T ⟧ ρ

-- ═══ §7  Equality helpers ═══════════════════════════════════════════

Π-≡ : ∀ {A : Set} {P Q : A → Set} → (∀ a → P a ≡ Q a) →
      ((a : A) → P a) ≡ ((a : A) → Q a)
Π-≡ p = cong (λ F → (a : _) → F a) (fun-ext p)

≡→ : ∀ {A : Type 0} {P Q : Pred A} → P ≡ Q → ∀ {e} → P e → Q e
≡→ refl x = x

-- ═══ §8  Semantic compositionality, ᴿ-fragment ══════════════════════
-- Both sides are predicates on Expr ∅ (T [ ⟨ ζ ⟩ ⨟ˢ syn ρ ]ˢ): the two
-- spellings (T [ ζ ]ᴿ) [ syn ρ ]ˢ and T [ ⟨ ζ ⟩ ⨟ˢ syn ρ ]ˢ are
-- identified by the registered compositionalityᴿˢ, so the STATEMENT
-- typechecks as-is.  With §5 registered the ∀-case is just the IH.

⟦⟧-ren : (T : Type n₁) (ζ : Ren n₁ n₂) (ρ : Env n₂) →
         ⟦ T [ ζ ]ᴿ ⟧ ρ ≡ ⟦ T ⟧ (ρ ⟨ ζ ⟩ᴱ)
⟦⟧-ren (` α)     ζ ρ = refl
⟦⟧-ren (T₁ ⇒ T₂) ζ ρ = fun-ext λ e →
  cong₂ (λ P Q → SN e × (∀ e′ → P e′ → Q (e · e′)))
        (⟦⟧-ren T₁ ζ ρ) (⟦⟧-ren T₂ ζ ρ)
⟦⟧-ren (∀α T)    ζ ρ = fun-ext λ e →
  cong (λ X → SN e × X) (Π-≡ λ S → Π-≡ λ cr →
    cong (λ P → P (e ·* proj₁ S)) (⟦⟧-ren T (ζ ↑ᴿ) (S ∷ᴱ ρ)))

{-# REWRITE ⟦⟧-ren #-}

-- ═══ §9  The σ-calculus of environments, ˢ-fragment ═════════════════

_⟪_⟫ᴱ : Env n₂ → Sub n₁ n₂ → Env n₁
syn (ρ ⟪ η ⟫ᴱ)    = η ⨟ˢ syn ρ
sem (ρ ⟪ η ⟫ᴱ) α  = ⟦ α &ˢ η ⟧ ρ

CREnv-⟪⟫ : {ρ : Env n₂} (η : Sub n₁ n₂) → CREnv ρ → CREnv (ρ ⟪ η ⟫ᴱ)
CREnv-⟪⟫ {ρ = ρ} η c α = ⟦⟧-CR (α &ˢ η) ρ c

⟪⟫-⟨⟩ : (ρ : Env n₂) (ζ : Ren n₁ n₂) → ρ ⟪ ⟨ ζ ⟩ ⟫ᴱ ≡ ρ ⟨ ζ ⟩ᴱ    -- coincidence
⟪⟫-⟨⟩ ρ ζ = Env-ext λ α → refl

∷-⟪⟫↑ : ∀ {S : SemTy} {ρ : Env n₂} (η : Sub n₁ n₂) →
        (S ∷ᴱ ρ) ⟪ η ↑ˢ ⟫ᴱ ≡ S ∷ᴱ (ρ ⟪ η ⟫ᴱ)                     -- lift-cons
-- the (suc α) case is the ONE place the ᴿ-fragment has to be invoked by
-- hand: the goal's type has already been normalised by the type-level
-- beta-fold-ˢᴿ from (α &ˢ η) [ wkᴿ ]ᴿ to α &ˢ (η ⨟ˢ ⟨ wkᴿ ⟩), so the
-- registered ⟦⟧-ren no longer matches it — the same index-inertness
-- phenomenon as one level down (see SystemF-fresh, §5.2).
∷-⟪⟫↑ {S = S} {ρ = ρ} η =
  Env-ext λ { zero → refl ; (suc α) → ⟦⟧-ren (α &ˢ η) wkᴿ (S ∷ᴱ ρ) }

⟪⟫-∙ : (ρ : Env n₂) (A : Type n₂) (η : Sub n₁ n₂) →
       ρ ⟪ A ∙ˢ η ⟫ᴱ ≡ (⟦ A ⟧ᵀ ρ) ∷ᴱ (ρ ⟪ η ⟫ᴱ)                  -- distributivity
⟪⟫-∙ ρ A η = Env-ext λ { zero → refl ; (suc α) → refl }

{-# REWRITE ⟪⟫-⟨⟩ ∷-⟪⟫↑ ⟪⟫-∙ #-}

⟦⟧-sub : (T : Type n₁) (η : Sub n₁ n₂) (ρ : Env n₂) →
         ⟦ T [ η ]ˢ ⟧ ρ ≡ ⟦ T ⟧ (ρ ⟪ η ⟫ᴱ)
⟦⟧-sub (` α)     η ρ = refl
⟦⟧-sub (T₁ ⇒ T₂) η ρ = fun-ext λ e →
  cong₂ (λ P Q → SN e × (∀ e′ → P e′ → Q (e · e′)))
        (⟦⟧-sub T₁ η ρ) (⟦⟧-sub T₂ η ρ)
⟦⟧-sub (∀α T)    η ρ = fun-ext λ e →
  cong (λ X → SN e × X) (Π-≡ λ S → Π-≡ λ cr →
    cong (λ P → P (e ·* proj₁ S)) (⟦⟧-sub T (η ↑ˢ) (S ∷ᴱ ρ)))

{-# REWRITE ⟦⟧-sub #-}

-- ═══ §10  Two substitution identities ═══════════════════════════════
-- The instances of the "missing" mirror rules (see the index-inertness
-- discussion in SystemF-fresh) that the fundamental theorem needs.
-- Everything around them is discharged by REGISTERED rules, so each
-- proof is a three-step chain.

-- pointwise extensionality for expression-level maps.  This is the only
-- place that needs the opaque `&ˢ` to unfold; the block holds nothing
-- else, so no registered rule is shadowed inside it.
opaque
  unfolding _∣_&ˢ_
  map-ext : ∀ {n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {η : Sub n₁ n₂}
              {σ₁ σ₂ : η ∣ Γ₁ ⇒ˢ Γ₂} →
            (∀ T (x : Γ₁ ∋ T) → η ∣ x &ˢ σ₁ ≡ η ∣ x &ˢ σ₂) → σ₁ ≡ σ₂
  map-ext p = fun-ext λ T → fun-ext λ x → p T x

-- (σ ⇑ˢ T₁) ⨾ˢ (e′ ∙ˢ Idˢ)  ≡  e′ ∙ˢ σ            [λ-dimension]
⇑-∙ : ∀ {n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {η : Sub n₁ n₂} {T₁ : Type n₁}
        (σ : η ∣ Γ₁ ⇒ˢ Γ₂) (e′ : Expr Γ₂ (T₁ [ η ]ˢ)) →
      (η , ⟨ idᴿ ⟩ ∣ (η ∣ σ ⇑ˢ T₁) ⨾ˢ (⟨ idᴿ ⟩ ∣ e′ ∙ˢ Idˢ)) ≡ (η ∣ e′ ∙ˢ σ)
⇑-∙ {η = η} {T₁ = T₁} σ e′ = map-ext {η = η} λ
  { _ zero →
      trans (sym (Beta-compˢ {η₁ = η} {η₂ = ⟨ idᴿ ⟩} zero
                    (η ∣ σ ⇑ˢ T₁) (⟨ idᴿ ⟩ ∣ e′ ∙ˢ Idˢ)))
            (cong (λ u → ⟨ idᴿ ⟩ ∣ u [ ⟨ idᴿ ⟩ ∣ e′ ∙ˢ Idˢ ]ˢ)
                  (Beta-⇑ˢ-zero {η = η} {T = T₁} σ))
  ; _ (suc x) →
      trans (sym (Beta-compˢ {η₁ = η} {η₂ = ⟨ idᴿ ⟩} (suc x)
                    (η ∣ σ ⇑ˢ T₁) (⟨ idᴿ ⟩ ∣ e′ ∙ˢ Idˢ)))
      (trans (cong (λ u → ⟨ idᴿ ⟩ ∣ u [ ⟨ idᴿ ⟩ ∣ e′ ∙ˢ Idˢ ]ˢ)
                   (Beta-⇑ˢ-suc {η = η} {T = T₁} x σ))
             (Compositionalityᴿˢ (η ∣ x &ˢ σ) idᴿ ⟨ idᴿ ⟩
                                 (Wkᴿ _) (⟨ idᴿ ⟩ ∣ e′ ∙ˢ Idˢ)))
  }

-- (σ ⇑ˢ*) ⨾ˢ (A ∙ˢ* Idˢ)  ≡  A ∙ˢ* σ              [Λ-dimension]
⇑*-∙* : ∀ {n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {η : Sub n₁ n₂}
          (σ : η ∣ Γ₁ ⇒ˢ Γ₂) (A : Type n₂) →
        ((η ↑ˢ) , (A ∙ˢ ⟨ idᴿ ⟩) ∣ (η ∣ σ ⇑ˢ*) ⨾ˢ (⟨ idᴿ ⟩ ∣ A ∙ˢ* Idˢ))
      ≡ (η ∣ A ∙ˢ* σ)
⇑*-∙* {η = η} σ A = map-ext {η = A ∙ˢ η} λ
  { _ (suc* x) →
      trans (sym (Beta-compˢ {η₁ = η ↑ˢ} {η₂ = A ∙ˢ ⟨ idᴿ ⟩} (suc* x)
                    (η ∣ σ ⇑ˢ*) (⟨ idᴿ ⟩ ∣ A ∙ˢ* Idˢ)))
      (trans (cong (λ u → (A ∙ˢ ⟨ idᴿ ⟩) ∣ u [ ⟨ idᴿ ⟩ ∣ A ∙ˢ* Idˢ ]ˢ)
                   (Beta-⇑ˢ*-suc* {η = η} x σ))
      (trans (Weaken*-cons {η = ⟨ idᴿ ⟩} (η ∣ x &ˢ σ) A Idˢ)
             (sym (Beta-ext-sucˢ* {η = η} A x σ))))
  }

{-# REWRITE ⇑-∙ ⇑*-∙* #-}

-- the two redex-substitution laws
β-λ-sub : ∀ {n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {η : Sub n₁ n₂} {T₁ T₂}
            (e₀ : Expr (Γ₁ ▷ T₁) T₂) (e₂ : Expr Γ₁ T₁) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
          (η ∣ e₀ [ η ∣ σ ⇑ˢ T₁ ]ˢ) [ η ∣ e₂ [ σ ]ˢ ] ≡ η ∣ (e₀ [ e₂ ]) [ σ ]ˢ
β-λ-sub {η = η} {T₁ = T₁} e₀ e₂ σ =
  trans (trans (Compositionalityˢˢ e₀ η ⟨ idᴿ ⟩ (η ∣ σ ⇑ˢ T₁)
                  (⟨ idᴿ ⟩ ∣ (η ∣ e₂ [ σ ]ˢ) ∙ˢ Idˢ))
               (cong (λ m → η ∣ e₀ [ m ]ˢ) (⇑-∙ σ (η ∣ e₂ [ σ ]ˢ))))
        (sym (Compositionalityˢˢ e₀ ⟨ idᴿ ⟩ η (⟨ idᴿ ⟩ ∣ e₂ ∙ˢ Idˢ) σ))

β-Λ-sub : ∀ {n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {η : Sub n₁ n₂} {T}
            (e₀ : Expr (Γ₁ ▷*) T) (A : Type n₁) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
          ((η ↑ˢ) ∣ e₀ [ η ∣ σ ⇑ˢ* ]ˢ) [* A [ η ]ˢ *] ≡ η ∣ (e₀ [* A *]) [ σ ]ˢ
β-Λ-sub {η = η} e₀ A σ =
  trans (trans (Compositionalityˢˢ e₀ (η ↑ˢ) ((A [ η ]ˢ) ∙ˢ ⟨ idᴿ ⟩)
                  (η ∣ σ ⇑ˢ*) (⟨ idᴿ ⟩ ∣ (A [ η ]ˢ) ∙ˢ* Idˢ))
               (cong (λ m → ((A [ η ]ˢ) ∙ˢ η) ∣ e₀ [ m ]ˢ) (⇑*-∙* σ (A [ η ]ˢ))))
        (sym (Compositionalityˢˢ e₀ (A ∙ˢ ⟨ idᴿ ⟩) η (⟨ idᴿ ⟩ ∣ A ∙ˢ* Idˢ) σ))

-- ═══ §11  Substitution simulates reduction ═════════════════════════
-- `Λα e` is a VALUE only when e is, and ξ-Λ reduces UNDER Λ, so the
-- fundamental theorem's Λ-case must know the BODY is normalising — not
-- just one of its type instances.  Forward simulation gives that in one
-- line, because SN is an accessibility predicate: every reduction of the
-- body maps to a reduction of the instance.

⟶-sub : ∀ {n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {T} {e e′ : Expr Γ₁ T}
          (η : Sub n₁ n₂) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
        e ⟶ e′ → (η ∣ e [ σ ]ˢ) ⟶ (η ∣ e′ [ σ ]ˢ)
⟶-sub η σ (β-λ {e₁ = a} {e₂ = b}) rewrite sym (β-λ-sub {η = η} a b σ) = β-λ
⟶-sub η σ (β-Λ {e = a} {T′ = A})  rewrite sym (β-Λ-sub {η = η} a A σ) = β-Λ
⟶-sub η σ (ξ-·₁ s) = ξ-·₁ (⟶-sub η σ s)
⟶-sub η σ (ξ-·₂ s) = ξ-·₂ (⟶-sub η σ s)
⟶-sub η σ (ξ-·* s) = ξ-·* (⟶-sub η σ s)
⟶-sub η σ (ξ-Λ s)  = ξ-Λ (⟶-sub (η ↑ˢ) (η ∣ σ ⇑ˢ*) s)

⟶*-sub : ∀ {n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {T} {e e′ : Expr Γ₁ T}
           (η : Sub n₁ n₂) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
         e ⟶* e′ → (η ∣ e [ σ ]ˢ) ⟶* (η ∣ e′ [ σ ]ˢ)
⟶*-sub η σ ⟶refl        = ⟶refl
⟶*-sub η σ (⟶trans s p) = ⟶trans (⟶-sub η σ s) (⟶*-sub η σ p)

-- …hence SN reflects along a substitution.  THE one-liner that decides
-- the whole design: with `Halts` in place of SN this step would need
-- either an inversion of substitution (blocked by the computed index of
-- _·*_) or determinism of ⟶ (false).
sn-sub : ∀ {n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {T}
           (η : Sub n₁ n₂) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) (e : Expr Γ₁ T) →
         SN (η ∣ e [ σ ]ˢ) → SN e
sn-sub η σ e (acc f) = acc λ s → sn-sub η σ _ (f (⟶-sub η σ s))

NoVar-∅ : NoVar ∅
NoVar-∅ ()

-- ═══ §12  The fundamental theorem ══════════════════════════════════

-- a closing substitution is reducible when every variable is
_⊨_ : (ρ : Env n) {Γ : Ctx n} → (syn ρ ∣ Γ ⇒ˢ ∅) → Set
_⊨_ ρ {Γ} σ = ∀ A (x : Γ ∋ A) → ⟦ A ⟧ ρ (syn ρ ∣ x &ˢ σ)

-- the two "compose a lifted map with a cons" laws, in the shape the
-- β-cases need.  Both are the first half of §10's redex laws.
[]-⇑ : ∀ {n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {η : Sub n₁ n₂} {T₁ T₂}
         (e : Expr (Γ₁ ▷ T₁) T₂) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) (e′ : Expr Γ₂ (T₁ [ η ]ˢ)) →
       (η ∣ e [ η ∣ σ ⇑ˢ T₁ ]ˢ) [ e′ ] ≡ η ∣ e [ η ∣ e′ ∙ˢ σ ]ˢ
[]-⇑ {η = η} {T₁ = T₁} e σ e′ =
  trans (Compositionalityˢˢ e η ⟨ idᴿ ⟩ (η ∣ σ ⇑ˢ T₁) (⟨ idᴿ ⟩ ∣ e′ ∙ˢ Idˢ))
        (cong (λ m → η ∣ e [ m ]ˢ) (⇑-∙ σ e′))

[*]-⇑* : ∀ {n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {η : Sub n₁ n₂} {T}
           (e : Expr (Γ₁ ▷*) T) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) (A : Type n₂) →
         ((η ↑ˢ) ∣ e [ η ∣ σ ⇑ˢ* ]ˢ) [* A *] ≡ (A ∙ˢ η) ∣ e [ η ∣ A ∙ˢ* σ ]ˢ
[*]-⇑* {η = η} e σ A =
  trans (Compositionalityˢˢ e (η ↑ˢ) (A ∙ˢ ⟨ idᴿ ⟩)
           (η ∣ σ ⇑ˢ*) (⟨ idᴿ ⟩ ∣ A ∙ˢ* Idˢ))
        (cong (λ m → (A ∙ˢ η) ∣ e [ m ]ˢ) (⇑*-∙* σ A))

-- the dummy semantic type used only to reflect normalisation of a
-- Λ-body through one arbitrary instantiation
SN-Ty : SemTy
SN-Ty = ∀α (` zero) , SN

fundamental : ∀ {n} {Γ : Ctx n} {T} (e : Expr Γ T) (ρ : Env n) (c : CREnv ρ)
                (σ : syn ρ ∣ Γ ⇒ˢ ∅) → ρ ⊨ σ → ⟦ T ⟧ ρ (syn ρ ∣ e [ σ ]ˢ)

fundamental (` x) ρ c σ ⊨σ = ⊨σ _ x

fundamental (e₁ · e₂) ρ c σ ⊨σ =
  proj₂ (fundamental e₁ ρ c σ ⊨σ) _ (fundamental e₂ ρ c σ ⊨σ)

-- the ·*-case needs NO transport: with ⟦⟧-sub, ⟪⟫-∙, ⟪⟫-⟨⟩ and ⟨⟩-id
-- registered, ⟦ T [ T′ ]* ⟧ ρ IS ⟦ T ⟧ (⟦ T′ ⟧ᵀ ρ ∷ᴱ ρ) definitionally.
fundamental (e ·* T′) ρ c σ ⊨σ =
  proj₂ (fundamental e ρ c σ ⊨σ) (⟦ T′ ⟧ᵀ ρ) (⟦⟧-CR T′ ρ c)

fundamental (λx {T₁ = T₁} {T₂ = T₂} e) ρ c σ ⊨σ =
  sn-λx , λ e′ r → ⟦⟧-exp T₂ ρ c tt (go e′ r)
  where
    ⊨∙ : ∀ e′ → ⟦ T₁ ⟧ ρ e′ → ρ ⊨ (syn ρ ∣ e′ ∙ˢ σ)
    ⊨∙ e′ r _ zero    = r
    ⊨∙ e′ r _ (suc x) = ⊨σ _ x
    go : ∀ e′ (r : ⟦ T₁ ⟧ ρ e′) {t} →
         ((λx (syn ρ ∣ e [ syn ρ ∣ σ ⇑ˢ T₁ ]ˢ)) · e′) ⟶ t → ⟦ T₂ ⟧ ρ t
    go e′ r β-λ = fundamental e ρ c (syn ρ ∣ e′ ∙ˢ σ) (⊨∙ e′ r)
    go e′ r (ξ-· ())

fundamental (Λα {T = T} e) ρ c σ ⊨σ =
  sn-Λ (sn-body SN-Ty CR-SN) ,
  λ S cr → aux S cr body (sn-body S cr) ⟶refl
  where
    body : Expr (∅ ▷*) (T [ syn ρ ↑ˢ ]ˢ)
    body = (syn ρ ↑ˢ) ∣ e [ syn ρ ∣ σ ⇑ˢ* ]ˢ

    ⊨∙* : ∀ (S : SemTy) → (S ∷ᴱ ρ) ⊨ (syn ρ ∣ proj₁ S ∙ˢ* σ)
    ⊨∙* S _ (suc* x) = ⊨σ _ x

    -- the IH, at the instantiated environment
    inst : ∀ S (cr : CR (proj₂ S)) → ⟦ T ⟧ (S ∷ᴱ ρ) (body [* proj₁ S *])
    inst S cr =
      fundamental e (S ∷ᴱ ρ) (CREnv-∷ cr c) (syn ρ ∣ proj₁ S ∙ˢ* σ) (⊨∙* S)

    -- SN of the body, reflected through ONE arbitrary instantiation
    sn-body : ∀ S (cr : CR (proj₂ S)) → SN body
    sn-body S cr = sn-sub (proj₁ S ∙ˢ ⟨ idᴿ ⟩) (⟨ idᴿ ⟩ ∣ proj₁ S ∙ˢ* Idˢ)
                     body (⟦⟧-sn T (S ∷ᴱ ρ) (CREnv-∷ cr c) (inst S cr))

    -- expansion under Λ: the redex (Λα b) ·* A does NOT have a unique
    -- reduct (b may step), so this is an induction on SN b.
    aux : ∀ S (cr : CR (proj₂ S)) (b : Expr (∅ ▷*) (T [ syn ρ ↑ˢ ]ˢ)) →
          SN b → body ⟶* b → ⟦ T ⟧ (S ∷ᴱ ρ) ((Λα b) ·* proj₁ S)
    aux S cr b (acc f) r = ⟦⟧-exp T (S ∷ᴱ ρ) (CREnv-∷ cr c) tt red
      where
        red : ∀ {t} → ((Λα b) ·* proj₁ S) ⟶ t → ⟦ T ⟧ (S ∷ᴱ ρ) t
        red β-Λ =
          ⟦⟧-fwd* T (S ∷ᴱ ρ) (CREnv-∷ cr c)
            (⟶*-sub (proj₁ S ∙ˢ ⟨ idᴿ ⟩) (⟨ idᴿ ⟩ ∣ proj₁ S ∙ˢ* Idˢ) r)
            (inst S cr)
        red (ξ-·* (ξ-Λ s)) =
          aux S cr _ (f s) (⟶*-trans r (⟶trans s ⟶refl))

-- ═══ §13  Canonicity ════════════════════════════════════════════════

ρ₀ : Env 0
syn ρ₀ = idˢ
sem ρ₀ ()

CREnv-ρ₀ : CREnv ρ₀
CREnv-ρ₀ ()

-- T [ idˢ ]ˢ ≡ T and ⟨ idᴿ ⟩ ∣ e [ Idˢ ]ˢ ≡ e are both DEFINITIONAL,
-- so the theorem's statement needs no coercion either.
canonicity : (T : Type 0) (e : Expr ∅ T) → Halts e
canonicity T e =
  sn-halts NoVar-∅ e
    (⟦⟧-sn T ρ₀ CREnv-ρ₀ (fundamental e ρ₀ CREnv-ρ₀ Idˢ (λ _ ())))

-- a demo: the polymorphic identity, applied to itself at its own type
private
  id-ty : Type 0
  id-ty = ∀α (` zero ⇒ ` zero)

  idᴱ : Expr ∅ id-ty
  idᴱ = Λα (λx (` zero))

  selfapp : Expr ∅ (id-ty ⇒ id-ty)
  selfapp = (idᴱ ·* id-ty)

  _ : Halts (selfapp · idᴱ)
  _ = canonicity _ _
