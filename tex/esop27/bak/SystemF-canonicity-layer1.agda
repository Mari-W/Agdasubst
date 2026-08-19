{-# OPTIONS --rewriting --local-confluence-check --type-in-type #-}
-- ⚠ MEASUREMENT PROBE — *EXPECTED TO FAIL* (exit 42) ⚠
-- THE DECISIVE MEASUREMENT for Task 1.  As -core, but with the §0
-- layer-0 pragma REMOVED, so Agda actually reaches and checks the
-- layer-(i) environment σ-algebra
--     ∷-⟨⟩↑  ∷-⟨⟩wk  ⟨⟩-id  ⟦⟧-ren  ⟪⟫-⟨⟩  ∷-⟪⟫↑  ⟪⟫-∙  ⟦⟧-sub
-- Measured: 7 non-joinable pairs, NOT 0.
--   Family A (3): rule vs the record's own copattern clause
--     ∷-⟨⟩↑ / ∷-⟪⟫↑ / ⟪⟫-∙  vs  _⟨_⟩ᴱ-clause2 / _⟪_⟫ᴱ-clause2
--   Family B (4): interpretation rule vs type-level σ-rule
--     ⟦⟧-ren vs compositionalityˢᴿ, beta-fold-ˢᴿ
--     ⟦⟧-sub vs compositionalityˢˢ, beta-fold
-- See §2 of REPORT-canonicity-port.md.  Nothing imports this file.
-- ⚠ DECISIVE MEASUREMENT for REPORT-canonicity-port.md, Task 1 ⚠
-- `SystemF-canonicity.agda` truncated immediately after the last
-- layer-(i) REWRITE pragma, with the prototype's §0 LAYER-0 pragma
-- (Compositionality*/Beta-*) removed.  Purpose: measure the layer-(i)
-- environment σ-algebra
--     ∷-⟨⟩↑  ∷-⟨⟩wk  ⟨⟩-id  ⟦⟧-ren  ⟪⟫-⟨⟩  ∷-⟪⟫↑  ⟪⟫-∙  ⟦⟧-sub
-- against --local-confluence-check, in isolation.
-- With §0 left IN, the measurement is 102 non-joinable pairs, ALL
-- attributed to the §0 rules; layer (i) contributes 0 of them.

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
module SystemF-canonicity-layer1 where

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
-- (§0 layer-0 pragma REMOVED for this measurement)
-- (§0 layer-0 pragma REMOVED for this measurement)
-- (§0 layer-0 pragma REMOVED for this measurement)
-- (§0 layer-0 pragma REMOVED for this measurement)

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
