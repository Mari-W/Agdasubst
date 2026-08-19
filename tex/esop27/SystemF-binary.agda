{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════
-- A BINARY (parametricity / Reynolds-style) LOGICAL RELATION for the
-- finitely stratified System F of SystemF-strat.agda.
--
-- RELATION TO SAFFRICH / THIEMANN / WEIDNER.
--   Their TyDe'24 paper "Intrinsically Typed Syntax, a Logical Relation,
--   and the Scourge of the Transfer Lemma" builds a logical relation for
--   exactly this calculus (Leivant's finitely stratified System F,
--   intrinsically typed in Agda), but their two sides are HETEROGENEOUS
--   — a closed syntactic value on the left and its Agda DENOTATION on
--   the right, `REL T = CValue T → ⟦ T ⟧ [] → Set l` — so their theorem
--   is soundness of a denotational semantics, with adequacy as its
--   corollary.  That development is reproduced in SystemF-adequacy.agda.
--
--   THIS FILE keeps their PROOF ARCHITECTURE — relation environments
--   carrying one closed type per type variable plus a relation over it,
--   a renaming action and a substitution action on relation
--   environments (their `Tren-act`/`Tsub-act`, their `LRVren`/`LRVsub`),
--   a relational environment for term variables (their `𝓖⟦_⟧`), and a
--   fundamental theorem quantified over all of them — but instantiates
--   the two sides SYNTAX × SYNTAX, i.e. genuine parametricity, which is
--   what the strat development's full-β and SN infrastructure supports.
--
-- The whole substitution calculus, the reduction relation and the SN
-- infrastructure are reused from SystemF-strat unchanged.  In
-- particular §B0 upgrades that file's UNARY fundamental theorem from
-- closed to open terms, and every SN side condition below is discharged
-- from it; the binary relation itself therefore carries no strong
-- normalisation component at all.
--
-- The only postulate is `fun-ext`, inherited from SystemF-strat.
-- ════════════════════════════════════════════════════════════════════
module SystemF-binary where

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
-- `[_]` (from Reveal) is hidden: it would make `b [ a ]` ambiguous
-- against SystemF-strat's single-variable substitution `_[_]`.
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Level using (Lift; lift; lower)
open import Relation.Nullary using (¬_)

open import SystemF-strat

-- ══════════════ §B0  SN for OPEN terms, from the unary theorem ═════
-- SystemF-strat's `SN-all` covers only CLOSED terms.  The binary
-- relation lives over contexts `Γ : Ctx ∅` that may still contain term
-- variables (reduction is full, so the relation must see under λ), so
-- we first strengthen `SN-all` to those.  Nothing new is proved: the
-- unary fundamental theorem is applied to the *variable* substitution,
-- whose reducibility is exactly the `rsLift` step of its own λ-case.

-- every variable-to-variable substitution is reducible.  `Env ∅ η = ⊤`
-- determines nothing, so the realised substitution `idˢ` and the target
-- context are given EXPLICITLY throughout.
Reds-var-sub : ∀ {Γ Γ′ : Ctx ∅} (f : ∀ l (T : Type ∅ l) → Γ ∋ T → Γ′ ∋ T) →
            Reds Γ {idˢ} ρ∅ {Γ′} (λ l T x → ` (f l T x))
Reds-var-sub {∅}     f = tt
Reds-var-sub {Γ ▷ T} f =
  ( cr-exp (⟦⟧-CR T {idˢ} ρ∅ tt) (ne-var _) (λ ())
  , Reds-var-sub (λ l A x → f l A (suc x)) )

-- STRONG NORMALISATION FOR OPEN TERMS
SN-open : ∀ {Γ : Ctx ∅} {l} {T : Type ∅ l} (e : Expr Γ T) → SN e
SN-open {Γ} {T = T} e =
  sn-sub idˢ (λ l A x → ` x)
    (cr-sn (⟦⟧-CR T {idˢ} ρ∅ tt)
           (fundamental e {idˢ} ρ∅ tt {Γ} (λ l A x → ` x)
                        (Reds-var-sub {Γ} {Γ} (λ _ _ x → x))))

-- …and under a TYPE binder.  A term in `Γ ▷* l` cannot be handed to
-- `SN-open` directly (its level context is `l ∙ ∅`, not `∅`), but SN
-- reflects along type substitution, and `base l` closes the context —
-- this is the same `base l` trick the unary Λ-case uses for `snBody`.
SN-open* : ∀ {Γ : Ctx ∅} {l l′} {T : Type (l ∙ ∅) l′} (b : Expr (Γ ▷* l) T) → SN b
SN-open* {l = l} b =
  sn-sub ((base l) ∙ˢ idˢ) ((idˢ ∣ (base l) ∙ˢ* Idˢ)) (SN-open (b [* base l *]))

-- ══════════════ §B1  Binary predicates and candidates ══════════════
-- `Pred² A B` is the binary analogue of `Pred A`.  Both terms live in the
-- SAME term context Γ, and only ever get weakened in lockstep, so a
-- single Kripke world suffices.  Γ is EXPLICIT, so plain fun-ext
-- applies.
--
-- Level check: `Pred² {l} A B : Set (lsuc l)`, exactly like `Pred`.  The
-- ∀-case of the relation quantifies over `Pred² S₁ S₂` and lands in
-- `Set (lsuc l ⊔ l′)` — precisely the level Agda assigns to `∀α_`.
-- Predicativity is what makes this typecheck with no --type-in-type.
Pred² : ∀ {l} → Type ∅ l → Type ∅ l → Set (lsuc l)
Pred² {l} A B = (Γ : Ctx ∅) → Expr Γ A → Expr Γ B → Set l

-- The BINARY reducibility-candidate conditions.  CR2 (forward closure)
-- and CR3 (neutral expansion) each split into a LEFT and a RIGHT half,
-- and each half leaves the other side completely unconstrained.  That
-- one-sided form is what makes β-expansion work: in the λ-case of the
-- fundamental theorem both sides are redexes, but a step on one side
-- does not come with a matching step on the other, so the expansion has
-- to be performed one side at a time.
--
-- CR1 (`cr-sn`) is ABSENT: §B0 supplies SN for every term of every type
-- in every `Ctx ∅`, so the binary relation never has to carry it.  This
-- is also what makes the one-sided CR3 provable at all: the CR3 proof
-- for `⇒` needs SN of the *argument* to run its inner induction, and a
-- one-sided CR3 cannot extract SN of the unconstrained side from the
-- relation.
record CR² {l} {A B : Type ∅ l} (R : Pred² A B) : Set l where
  field
    cr²-fwd₁ : ∀ {Γ : Ctx ∅} {e₁ e₁′ : Expr Γ A} {e₂ : Expr Γ B} →
               R Γ e₁ e₂ → e₁ ⟶ e₁′ → R Γ e₁′ e₂
    cr²-fwd₂ : ∀ {Γ : Ctx ∅} {e₁ : Expr Γ A} {e₂ e₂′ : Expr Γ B} →
               R Γ e₁ e₂ → e₂ ⟶ e₂′ → R Γ e₁ e₂′
    cr²-exp₁ : ∀ {Γ : Ctx ∅} {e₁ : Expr Γ A} {e₂ : Expr Γ B} → Ne e₁ →
               (∀ {e₁′} → e₁ ⟶ e₁′ → R Γ e₁′ e₂) → R Γ e₁ e₂
    cr²-exp₂ : ∀ {Γ : Ctx ∅} {e₁ : Expr Γ A} {e₂ : Expr Γ B} → Ne e₂ →
               (∀ {e₂′} → e₂ ⟶ e₂′ → R Γ e₁ e₂′) → R Γ e₁ e₂
    cr²-wk   : ∀ {Γ Γ′ : Ctx ∅} {e₁ : Expr Γ A} {e₂ : Expr Γ B} (w : Γ ⊆ Γ′) →
               R Γ e₁ e₂ → R Γ′ (ren⊆ w e₁) (ren⊆ w e₂)
open CR² public

-- multi-step forward closure, both sides
cr²-fwd*₁ : ∀ {l}{A B : Type ∅ l}{R : Pred² A B} → CR² R →
            ∀ {Γ : Ctx ∅}{e₁ e₁′ : Expr Γ A}{e₂ : Expr Γ B} →
            R Γ e₁ e₂ → e₁ ⟶* e₁′ → R Γ e₁′ e₂
cr²-fwd*₁ cr r ⟶refl       = r
cr²-fwd*₁ cr r (⟶step s p) = cr²-fwd*₁ cr (cr²-fwd₁ cr r s) p

cr²-fwd*₂ : ∀ {l}{A B : Type ∅ l}{R : Pred² A B} → CR² R →
            ∀ {Γ : Ctx ∅}{e₁ : Expr Γ A}{e₂ e₂′ : Expr Γ B} →
            R Γ e₁ e₂ → e₂ ⟶* e₂′ → R Γ e₁ e₂′
cr²-fwd*₂ cr r ⟶refl       = r
cr²-fwd*₂ cr r (⟶step s p) = cr²-fwd*₂ cr (cr²-fwd₂ cr r s) p

-- ══════════════ §B2  Two-sided semantic environments ═══════════════
-- The analogue of STW's `RelEnv Δ = ∀ l → l ∈ Δ → Σ (Type [] l) REL`.
-- Here the `Σ (Type ∅ l)` half is pulled out into the INDICES η₁, η₂
-- (their `π₁ ρ`, doubled), following SystemF-strat's `Env`: indexing by
-- the realised substitutions is what makes all the composition
-- bookkeeping definitional rather than propositional.
Env² : (Δ : LCtx) → Sub Δ ∅ → Sub Δ ∅ → Set (maxL Δ)
Env² ∅       η₁ η₂ = ⊤
Env² (l ∙ Δ) η₁ η₂ =
  Pred² (here &ˢ η₁) (here &ˢ η₂) × Env² Δ (⟨ wkᴿ ⟩ ⨟ˢ η₁) (⟨ wkᴿ ⟩ ⨟ˢ η₂)

-- η₁, η₂ EXPLICIT: Env² is a recursive function, so its indices can
-- never be recovered by unification from an environment's type.
semE² : ∀ {Δ l} (α : Δ ∋ˡ l) (η₁ η₂ : Sub Δ ∅) → Env² Δ η₁ η₂ →
       Pred² (α &ˢ η₁) (α &ˢ η₂)
semE² here      η₁ η₂ (R , _) = R
semE² (there α) η₁ η₂ (_ , ρ) = semE² α (⟨ wkᴿ ⟩ ⨟ˢ η₁) (⟨ wkᴿ ⟩ ⨟ˢ η₂) ρ

-- ══════════════ §B3  THE BINARY LOGICAL RELATION ═══════════════════
-- Transport-free.  The ∀-case needs (T [ ηᵢ ↑ˢ ]ˢ) [ Sᵢ ]* ≡ T [ Sᵢ ∙ˢ ηᵢ ]ˢ
-- and (R , ρ) : Env² (l ∙ Δ) (S₁ ∙ˢ η₁) (S₂ ∙ˢ η₂); the registered
-- type-level σ-rewrites make both definitional, on BOTH sides at once.
-- This is exactly the place where STW need their transfer lemmas
-- (`RE-ext∘lift`, `lemma1`) and where their statement of `LRVren-eq′`
-- acquires a `subst₂`.
⟦_⟧² : ∀ {Δ l} (T : Type Δ l) {η₁ η₂ : Sub Δ ∅} → Env² Δ η₁ η₂ →
       Pred² (T [ η₁ ]ˢ) (T [ η₂ ]ˢ)
⟦ ` α ⟧²     {η₁} {η₂} ρ = semE² α η₁ η₂ ρ
⟦ base l ⟧²  ρ Γ e₁ e₂ = Lift l ⊤
⟦ T₁ ⇒ T₂ ⟧² {η₁} {η₂} ρ Γ e₁ e₂ =
  ∀ {Γ′} (w : Γ ⊆ Γ′) (a₁ : Expr Γ′ (T₁ [ η₁ ]ˢ)) (a₂ : Expr Γ′ (T₁ [ η₂ ]ˢ)) →
    ⟦ T₁ ⟧² ρ Γ′ a₁ a₂ → ⟦ T₂ ⟧² ρ Γ′ (ren⊆ w e₁ · a₁) (ren⊆ w e₂ · a₂)
⟦ ∀α_ {l = l} T ⟧² {η₁} {η₂} ρ Γ e₁ e₂ =
  ∀ {Γ′} (w : Γ ⊆ Γ′) (S₁ S₂ : Type ∅ l) (R : Pred² S₁ S₂) → CR² R →
    ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) Γ′ (ren⊆ w e₁ ·* S₁) (ren⊆ w e₂ ·* S₂)

-- every relation in the environment is a candidate
CREnv² : ∀ {Δ} {η₁ η₂ : Sub Δ ∅} → Env² Δ η₁ η₂ → Set (maxL Δ)
CREnv² {∅}     _       = ⊤
CREnv² {l ∙ Δ} (R , ρ) = Lift (lsuc l) (CR² R) × CREnv² ρ

-- ══════════════ §B4  Semantic type substitution, two-sided ═════════
-- Mirror of SystemF-strat §11, and the analogue of STW's `LRVren`
-- and `LRVsub`.  The renaming/substitution
-- being PUSHED is single; it is the two CLOSING substitutions that are
-- doubled.  NO `subst` occurs in any statement below.

⊛² : ∀ {Δ₁ Δ₂} (ζ : Ren Δ₁ Δ₂) (η₁ η₂ : Sub Δ₂ ∅) → Env² Δ₂ η₁ η₂ →
     Env² Δ₁ (⟨ ζ ⟩ ⨟ˢ η₁) (⟨ ζ ⟩ ⨟ˢ η₂)
⊛² {∅}      ζ η₁ η₂ ρ = tt
⊛² {l ∙ Δ₁} ζ η₁ η₂ ρ = semE² (here &ᴿ ζ) η₁ η₂ ρ , ⊛² (wkᴿ ⨟ᴿ ζ) η₁ η₂ ρ

semE²-⊛ : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (ζ : Ren Δ₁ Δ₂) (η₁ η₂ : Sub Δ₂ ∅)
          (ρ : Env² Δ₂ η₁ η₂) →
          semE² α (⟨ ζ ⟩ ⨟ˢ η₁) (⟨ ζ ⟩ ⨟ˢ η₂) (⊛² ζ η₁ η₂ ρ) ≡ semE² (α &ᴿ ζ) η₁ η₂ ρ
semE²-⊛ here      ζ η₁ η₂ ρ = refl
semE²-⊛ (there α) ζ η₁ η₂ ρ = semE²-⊛ α (wkᴿ ⨟ᴿ ζ) η₁ η₂ ρ

⊛²-wk : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (η₁ η₂ : Sub (l ∙ Δ₂) ∅) (ρ : Env² (l ∙ Δ₂) η₁ η₂) →
        ⊛² (ζ ⨟ᴿ wkᴿ) η₁ η₂ ρ
      ≡ ⊛² ζ (⟨ wkᴿ ⟩ ⨟ˢ η₁) (⟨ wkᴿ ⟩ ⨟ˢ η₂) (proj₂ ρ)
⊛²-wk {Δ₁ = ∅}      ζ η₁ η₂ ρ = refl
⊛²-wk {Δ₁ = l ∙ Δ₁} ζ η₁ η₂ ρ =
  cong (semE² (here &ᴿ ζ) (⟨ wkᴿ ⟩ ⨟ˢ η₁) (⟨ wkᴿ ⟩ ⨟ˢ η₂) (proj₂ ρ) ,_)
       (⊛²-wk (wkᴿ ⨟ᴿ ζ) η₁ η₂ ρ)

⊛²-wk₀ : ∀ {Δ l} (η₁ η₂ : Sub (l ∙ Δ) ∅) (ρ : Env² (l ∙ Δ) η₁ η₂) →
         ⊛² wkᴿ η₁ η₂ ρ ≡ proj₂ ρ
⊛²-wk₀ {Δ = ∅}     η₁ η₂ ρ = refl
⊛²-wk₀ {Δ = l ∙ Δ} η₁ η₂ ρ =
  cong (semE² here (⟨ wkᴿ ⟩ ⨟ˢ η₁) (⟨ wkᴿ ⟩ ⨟ˢ η₂) (proj₂ ρ) ,_)
       (trans (⊛²-wk wkᴿ η₁ η₂ ρ) (⊛²-wk₀ (⟨ wkᴿ ⟩ ⨟ˢ η₁) (⟨ wkᴿ ⟩ ⨟ˢ η₂) (proj₂ ρ)))

⊛²-lift : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (η₁ η₂ : Sub (l ∙ Δ₂) ∅) (ρ : Env² (l ∙ Δ₂) η₁ η₂) →
          ⊛² (ζ ↑ᴿ) η₁ η₂ ρ
        ≡ (proj₁ ρ , ⊛² ζ (⟨ wkᴿ ⟩ ⨟ˢ η₁) (⟨ wkᴿ ⟩ ⨟ˢ η₂) (proj₂ ρ))
⊛²-lift ζ η₁ η₂ ρ = cong (proj₁ ρ ,_) (⊛²-wk ζ η₁ η₂ ρ)

-- the binary interpretation commutes with type RENAMING  (their LRVren)
⟦⟧²-ren : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η₁ η₂ : Sub Δ₂ ∅)
          (ρ : Env² Δ₂ η₁ η₂) →
          ⟦ T [ ζ ]ᴿ ⟧² ρ ≡ ⟦ T ⟧² (⊛² ζ η₁ η₂ ρ)
⟦⟧²-ren (` α)     ζ η₁ η₂ ρ = sym (semE²-⊛ α ζ η₁ η₂ ρ)
⟦⟧²-ren (base l)  ζ η₁ η₂ ρ = refl
⟦⟧²-ren (T₁ ⇒ T₂) ζ η₁ η₂ ρ =
  fun-ext λ Γ → fun-ext λ e₁ → fun-ext λ e₂ →
    cong₂ (λ P Q → ∀ {Γ′} (w : Γ ⊆ Γ′) a₁ a₂ → P Γ′ a₁ a₂ →
                     Q Γ′ (ren⊆ w e₁ · a₁) (ren⊆ w e₂ · a₂))
          (⟦⟧²-ren T₁ ζ η₁ η₂ ρ) (⟦⟧²-ren T₂ ζ η₁ η₂ ρ)
⟦⟧²-ren (∀α_ {l = l} T) ζ η₁ η₂ ρ =
  fun-ext λ Γ → fun-ext λ e₁ → fun-ext λ e₂ →
    cong (λ f → ∀ {Γ′} (w : Γ ⊆ Γ′) (S₁ S₂ : Type ∅ l) (R : Pred² S₁ S₂) → CR² R →
                  f S₁ S₂ R Γ′ (ren⊆ w e₁ ·* S₁) (ren⊆ w e₂ ·* S₂))
         (fun-ext λ S₁ → fun-ext λ S₂ → fun-ext λ R → ∀step S₁ S₂ R)
  where
  ∀step : ∀ (S₁ S₂ : Type ∅ l) (R : Pred² S₁ S₂) →
          ⟦ T [ ζ ↑ᴿ ]ᴿ ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ)
        ≡ ⟦ T ⟧² {S₁ ∙ˢ (⟨ ζ ⟩ ⨟ˢ η₁)} {S₂ ∙ˢ (⟨ ζ ⟩ ⨟ˢ η₂)} (R , ⊛² ζ η₁ η₂ ρ)
  ∀step S₁ S₂ R =
    trans (⟦⟧²-ren T (ζ ↑ᴿ) (S₁ ∙ˢ η₁) (S₂ ∙ˢ η₂) (R , ρ))
          (cong (⟦ T ⟧² {S₁ ∙ˢ (⟨ ζ ⟩ ⨟ˢ η₁)} {S₂ ∙ˢ (⟨ ζ ⟩ ⨟ˢ η₂)})
                (⊛²-lift ζ (S₁ ∙ˢ η₁) (S₂ ∙ˢ η₂) (R , ρ)))

-- ── now SUBSTITUTIONS, mirroring the renaming development ──

⊙² : ∀ {Δ₁ Δ₂} (η : Sub Δ₁ Δ₂) (κ₁ κ₂ : Sub Δ₂ ∅) → Env² Δ₂ κ₁ κ₂ →
     Env² Δ₁ (η ⨟ˢ κ₁) (η ⨟ˢ κ₂)
⊙² {∅}      η κ₁ κ₂ ρ = tt
⊙² {l ∙ Δ₁} η κ₁ κ₂ ρ = ⟦ here &ˢ η ⟧² {κ₁} {κ₂} ρ , ⊙² (⟨ wkᴿ ⟩ ⨟ˢ η) κ₁ κ₂ ρ

semE²-⊙ : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (η : Sub Δ₁ Δ₂) (κ₁ κ₂ : Sub Δ₂ ∅)
          (ρ : Env² Δ₂ κ₁ κ₂) →
          semE² α (η ⨟ˢ κ₁) (η ⨟ˢ κ₂) (⊙² η κ₁ κ₂ ρ) ≡ ⟦ α &ˢ η ⟧² {κ₁} {κ₂} ρ
semE²-⊙ here      η κ₁ κ₂ ρ = refl
semE²-⊙ (there α) η κ₁ κ₂ ρ = semE²-⊙ α (⟨ wkᴿ ⟩ ⨟ˢ η) κ₁ κ₂ ρ

⊙²-⟨⟩ : ∀ {Δ₁ Δ₂} (ζ : Ren Δ₁ Δ₂) (κ₁ κ₂ : Sub Δ₂ ∅) (ρ : Env² Δ₂ κ₁ κ₂) →
        ⊙² ⟨ ζ ⟩ κ₁ κ₂ ρ ≡ ⊛² ζ κ₁ κ₂ ρ
⊙²-⟨⟩ {Δ₁ = ∅}      ζ κ₁ κ₂ ρ = refl
⊙²-⟨⟩ {Δ₁ = l ∙ Δ₁} ζ κ₁ κ₂ ρ =
  cong (semE² (here &ᴿ ζ) κ₁ κ₂ ρ ,_) (⊙²-⟨⟩ (wkᴿ ⨟ᴿ ζ) κ₁ κ₂ ρ)

⊙²-wk : ∀ {Δ₁ Δ₂ l} (η : Sub Δ₁ Δ₂) (κ₁ κ₂ : Sub (l ∙ Δ₂) ∅) (ρ : Env² (l ∙ Δ₂) κ₁ κ₂) →
        ⊙² (η ⨟ˢ ⟨ wkᴿ ⟩) κ₁ κ₂ ρ
      ≡ ⊙² η (⟨ wkᴿ ⟩ ⨟ˢ κ₁) (⟨ wkᴿ ⟩ ⨟ˢ κ₂) (proj₂ ρ)
⊙²-wk {Δ₁ = ∅}      η κ₁ κ₂ ρ = refl
⊙²-wk {Δ₁ = l ∙ Δ₁} η κ₁ κ₂ ρ =
  cong₂ _,_
    (trans (⟦⟧²-ren (here &ˢ η) wkᴿ κ₁ κ₂ ρ)
           (cong (⟦ here &ˢ η ⟧² {⟨ wkᴿ ⟩ ⨟ˢ κ₁} {⟨ wkᴿ ⟩ ⨟ˢ κ₂}) (⊛²-wk₀ κ₁ κ₂ ρ)))
    (⊙²-wk (⟨ wkᴿ ⟩ ⨟ˢ η) κ₁ κ₂ ρ)

⊙²-lift : ∀ {Δ₁ Δ₂ l} (η : Sub Δ₁ Δ₂) (κ₁ κ₂ : Sub (l ∙ Δ₂) ∅) (ρ : Env² (l ∙ Δ₂) κ₁ κ₂) →
          ⊙² (η ↑ˢ) κ₁ κ₂ ρ
        ≡ (proj₁ ρ , ⊙² η (⟨ wkᴿ ⟩ ⨟ˢ κ₁) (⟨ wkᴿ ⟩ ⨟ˢ κ₂) (proj₂ ρ))
⊙²-lift η κ₁ κ₂ ρ = cong (proj₁ ρ ,_) (⊙²-wk η κ₁ κ₂ ρ)

⊙²-id : ∀ {Δ} (κ₁ κ₂ : Sub Δ ∅) (ρ : Env² Δ κ₁ κ₂) → ⊙² idˢ κ₁ κ₂ ρ ≡ ρ
⊙²-id {∅}     κ₁ κ₂ ρ = refl
⊙²-id {l ∙ Δ} κ₁ κ₂ ρ =
  cong (semE² here κ₁ κ₂ ρ ,_) (trans (⊙²-⟨⟩ wkᴿ κ₁ κ₂ ρ) (⊛²-wk₀ κ₁ κ₂ ρ))

-- THE BINARY INTERPRETATION COMMUTES WITH TYPE SUBSTITUTION  (their LRVsub)
⟦⟧²-sub : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (η : Sub Δ₁ Δ₂) (κ₁ κ₂ : Sub Δ₂ ∅)
          (ρ : Env² Δ₂ κ₁ κ₂) →
          ⟦ T [ η ]ˢ ⟧² {κ₁} {κ₂} ρ ≡ ⟦ T ⟧² (⊙² η κ₁ κ₂ ρ)
⟦⟧²-sub (` α)     η κ₁ κ₂ ρ = sym (semE²-⊙ α η κ₁ κ₂ ρ)
⟦⟧²-sub (base l)  η κ₁ κ₂ ρ = refl
⟦⟧²-sub (T₁ ⇒ T₂) η κ₁ κ₂ ρ =
  fun-ext λ Γ → fun-ext λ e₁ → fun-ext λ e₂ →
    cong₂ (λ P Q → ∀ {Γ′} (w : Γ ⊆ Γ′) a₁ a₂ → P Γ′ a₁ a₂ →
                     Q Γ′ (ren⊆ w e₁ · a₁) (ren⊆ w e₂ · a₂))
          (⟦⟧²-sub T₁ η κ₁ κ₂ ρ) (⟦⟧²-sub T₂ η κ₁ κ₂ ρ)
⟦⟧²-sub (∀α_ {l = l} T) η κ₁ κ₂ ρ =
  fun-ext λ Γ → fun-ext λ e₁ → fun-ext λ e₂ →
    cong (λ f → ∀ {Γ′} (w : Γ ⊆ Γ′) (S₁ S₂ : Type ∅ l) (R : Pred² S₁ S₂) → CR² R →
                  f S₁ S₂ R Γ′ (ren⊆ w e₁ ·* S₁) (ren⊆ w e₂ ·* S₂))
         (fun-ext λ S₁ → fun-ext λ S₂ → fun-ext λ R → ∀stepˢ S₁ S₂ R)
  where
  ∀stepˢ : ∀ (S₁ S₂ : Type ∅ l) (R : Pred² S₁ S₂) →
           ⟦ T [ η ↑ˢ ]ˢ ⟧² {S₁ ∙ˢ κ₁} {S₂ ∙ˢ κ₂} (R , ρ)
         ≡ ⟦ T ⟧² {S₁ ∙ˢ (η ⨟ˢ κ₁)} {S₂ ∙ˢ (η ⨟ˢ κ₂)} (R , ⊙² η κ₁ κ₂ ρ)
  ∀stepˢ S₁ S₂ R =
    trans (⟦⟧²-sub T (η ↑ˢ) (S₁ ∙ˢ κ₁) (S₂ ∙ˢ κ₂) (R , ρ))
          (cong (⟦ T ⟧² {S₁ ∙ˢ (η ⨟ˢ κ₁)} {S₂ ∙ˢ (η ⨟ˢ κ₂)})
                (⊙²-lift η (S₁ ∙ˢ κ₁) (S₂ ∙ˢ κ₂) (R , ρ)))

-- the single-variable instance the ·*-case of the fundamental theorem needs
⟦⟧²-[]* : ∀ {Δ l l′} (T : Type (l ∙ Δ) l′) (T′ : Type Δ l) (κ₁ κ₂ : Sub Δ ∅)
          (ρ : Env² Δ κ₁ κ₂) →
          ⟦ T [ T′ ]* ⟧² {κ₁} {κ₂} ρ
        ≡ ⟦ T ⟧² {(T′ [ κ₁ ]ˢ) ∙ˢ κ₁} {(T′ [ κ₂ ]ˢ) ∙ˢ κ₂} (⟦ T′ ⟧² {κ₁} {κ₂} ρ , ρ)
⟦⟧²-[]* T T′ κ₁ κ₂ ρ =
  trans (⟦⟧²-sub T (T′ ∙ˢ idˢ) κ₁ κ₂ ρ)
        (cong (⟦ T ⟧² {(T′ [ κ₁ ]ˢ) ∙ˢ κ₁} {(T′ [ κ₂ ]ˢ) ∙ˢ κ₂})
              (cong (⟦ T′ ⟧² {κ₁} {κ₂} ρ ,_) (⊙²-id κ₁ κ₂ ρ)))

-- the weakening instance §B7 needs  (their LRVwk-eq)
⟦⟧²-weaken : ∀ {Δ l l′} (T : Type Δ l′) (κ₁ κ₂ : Sub (l ∙ Δ) ∅) (ρ : Env² (l ∙ Δ) κ₁ κ₂) →
             ⟦ weaken T ⟧² ρ ≡ ⟦ T ⟧² (proj₂ ρ)
⟦⟧²-weaken T κ₁ κ₂ ρ =
  trans (⟦⟧²-ren T wkᴿ κ₁ κ₂ ρ)
        (cong (⟦ T ⟧² {⟨ wkᴿ ⟩ ⨟ˢ κ₁} {⟨ wkᴿ ⟩ ⨟ˢ κ₂}) (⊛²-wk₀ κ₁ κ₂ ρ))

-- ══════════════ §B5  The binary relation is a candidate ════════════
-- Mirror of SystemF-strat §15.  In the ⇒-case both cr²-exp₁ and
-- cr²-exp₂ run an inner induction on the SN of the corresponding
-- ARGUMENT, supplied by §B0.  The ∀-case needs no inner induction: a
-- redex under a type application can only be in the head.
⟦⟧²-CR : ∀ {Δ l} (T : Type Δ l) {η₁ η₂ : Sub Δ ∅} (ρ : Env² Δ η₁ η₂) →
         CREnv² ρ → CR² (⟦ T ⟧² ρ)
⟦⟧²-CR (base l) ρ c = record
  { cr²-fwd₁ = λ p s → lift tt
  ; cr²-fwd₂ = λ p s → lift tt
  ; cr²-exp₁ = λ nu h → lift tt
  ; cr²-exp₂ = λ nu h → lift tt
  ; cr²-wk   = λ w p → lift tt }
⟦⟧²-CR (` here)      (R , ρ) (c , _)  = lower c
⟦⟧²-CR (` (there α)) (_ , ρ) (_ , cs) = ⟦⟧²-CR (` α) ρ cs
⟦⟧²-CR (T₁ ⇒ T₂) {η₁} {η₂} ρ c = record
  { cr²-fwd₁ = λ f s w a₁ a₂ r →
      cr²-fwd₁ (⟦⟧²-CR T₂ ρ c) (f w a₁ a₂ r) (ξ-·₁ (⟶-ren idᴿ (⊆-ren w) s))
  ; cr²-fwd₂ = λ f s w a₁ a₂ r →
      cr²-fwd₂ (⟦⟧²-CR T₂ ρ c) (f w a₁ a₂ r) (ξ-·₁ (⟶-ren idᴿ (⊆-ren w) s))
  ; cr²-exp₁ = λ { {e₁ = e₁} {e₂ = e₂} nu h w a₁ a₂ r →
      aux₁ e₁ e₂ nu h w a₁ a₂ r (SN-open a₁) }
  ; cr²-exp₂ = λ { {e₁ = e₁} {e₂ = e₂} nu h w a₁ a₂ r →
      aux₂ e₁ e₂ nu h w a₁ a₂ r (SN-open a₂) }
  ; cr²-wk   = λ { {e₁ = e₁} {e₂ = e₂} w f w′ a₁ a₂ r →
      subst₂ (λ z₁ z₂ → ⟦ T₂ ⟧² ρ _ (z₁ · a₁) (z₂ · a₂))
             (sym (ren⊆-trans w w′ e₁)) (sym (ren⊆-trans w w′ e₂))
             (f (⊆-trans w w′) a₁ a₂ r) }
  }
  where
  aux₁ : ∀ {Γ : Ctx ∅} (e₁ : Expr Γ ((T₁ ⇒ T₂) [ η₁ ]ˢ)) (e₂ : Expr Γ ((T₁ ⇒ T₂) [ η₂ ]ˢ)) →
         Ne e₁ → (∀ {u} → e₁ ⟶ u → ⟦ T₁ ⇒ T₂ ⟧² ρ Γ u e₂) →
         ∀ {Γ′} (w : Γ ⊆ Γ′) (a₁ : Expr Γ′ (T₁ [ η₁ ]ˢ)) (a₂ : Expr Γ′ (T₁ [ η₂ ]ˢ)) →
         ⟦ T₁ ⟧² ρ Γ′ a₁ a₂ → SN a₁ →
         ⟦ T₂ ⟧² ρ Γ′ (ren⊆ w e₁ · a₁) (ren⊆ w e₂ · a₂)
  aux₁ e₁ e₂ nu h w a₁ a₂ r (acc g) =
    cr²-exp₁ (⟦⟧²-CR T₂ ρ c) (ne-app _ _) hyp
    where
    hyp : ∀ {r′} → (ren⊆ w e₁ · a₁) ⟶ r′ → ⟦ T₂ ⟧² ρ _ r′ (ren⊆ w e₂ · a₂)
    hyp s with ne-app-inv (Ne-ren idᴿ (⊆-ren w) nu) s
    ... | inj₁ (X′ , sX , refl) with ⟶-ren-inv idᴿ (⊆-ren w) e₁ sX
    ...   | (u , su , refl) = h su w a₁ a₂ r
    hyp s | inj₂ (a₁′ , sa , refl) =
      aux₁ e₁ e₂ nu h w a₁′ a₂ (cr²-fwd₁ (⟦⟧²-CR T₁ ρ c) r sa) (g sa)
  aux₂ : ∀ {Γ : Ctx ∅} (e₁ : Expr Γ ((T₁ ⇒ T₂) [ η₁ ]ˢ)) (e₂ : Expr Γ ((T₁ ⇒ T₂) [ η₂ ]ˢ)) →
         Ne e₂ → (∀ {u} → e₂ ⟶ u → ⟦ T₁ ⇒ T₂ ⟧² ρ Γ e₁ u) →
         ∀ {Γ′} (w : Γ ⊆ Γ′) (a₁ : Expr Γ′ (T₁ [ η₁ ]ˢ)) (a₂ : Expr Γ′ (T₁ [ η₂ ]ˢ)) →
         ⟦ T₁ ⟧² ρ Γ′ a₁ a₂ → SN a₂ →
         ⟦ T₂ ⟧² ρ Γ′ (ren⊆ w e₁ · a₁) (ren⊆ w e₂ · a₂)
  aux₂ e₁ e₂ nu h w a₁ a₂ r (acc g) =
    cr²-exp₂ (⟦⟧²-CR T₂ ρ c) (ne-app _ _) hyp
    where
    hyp : ∀ {r′} → (ren⊆ w e₂ · a₂) ⟶ r′ → ⟦ T₂ ⟧² ρ _ (ren⊆ w e₁ · a₁) r′
    hyp s with ne-app-inv (Ne-ren idᴿ (⊆-ren w) nu) s
    ... | inj₁ (X′ , sX , refl) with ⟶-ren-inv idᴿ (⊆-ren w) e₂ sX
    ...   | (u , su , refl) = h su w a₁ a₂ r
    hyp s | inj₂ (a₂′ , sa , refl) =
      aux₂ e₁ e₂ nu h w a₁ a₂′ (cr²-fwd₂ (⟦⟧²-CR T₁ ρ c) r sa) (g sa)
⟦⟧²-CR (∀α_ {l = l} T) {η₁} {η₂} ρ c = record
  { cr²-fwd₁ = λ f s w S₁ S₂ R cr →
      cr²-fwd₁ (⟦⟧²-CR T (R , ρ) (lift cr , c)) (f w S₁ S₂ R cr)
               (ξ-·* (⟶-ren idᴿ (⊆-ren w) s))
  ; cr²-fwd₂ = λ f s w S₁ S₂ R cr →
      cr²-fwd₂ (⟦⟧²-CR T (R , ρ) (lift cr , c)) (f w S₁ S₂ R cr)
               (ξ-·* (⟶-ren idᴿ (⊆-ren w) s))
  ; cr²-exp₁ = λ { {e₁ = e₁} {e₂ = e₂} nu h w S₁ S₂ R cr →
      cr²-exp₁ (⟦⟧²-CR T (R , ρ) (lift cr , c)) (ne-tapp _ _)
               (hyp₁ e₁ e₂ nu h w S₁ S₂ R cr) }
  ; cr²-exp₂ = λ { {e₁ = e₁} {e₂ = e₂} nu h w S₁ S₂ R cr →
      cr²-exp₂ (⟦⟧²-CR T (R , ρ) (lift cr , c)) (ne-tapp _ _)
               (hyp₂ e₁ e₂ nu h w S₁ S₂ R cr) }
  ; cr²-wk   = λ { {e₁ = e₁} {e₂ = e₂} w f w′ S₁ S₂ R cr →
      subst₂ (λ z₁ z₂ → ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) _ (z₁ ·* S₁) (z₂ ·* S₂))
             (sym (ren⊆-trans w w′ e₁)) (sym (ren⊆-trans w w′ e₂))
             (f (⊆-trans w w′) S₁ S₂ R cr) }
  }
  where
  hyp₁ : ∀ {Γ : Ctx ∅} (e₁ : Expr Γ ((∀α T) [ η₁ ]ˢ)) (e₂ : Expr Γ ((∀α T) [ η₂ ]ˢ)) →
         Ne e₁ → (∀ {u} → e₁ ⟶ u → ⟦ ∀α T ⟧² ρ Γ u e₂) →
         ∀ {Γ′} (w : Γ ⊆ Γ′) (S₁ S₂ : Type ∅ l) (R : Pred² S₁ S₂) (cr : CR² R) →
         ∀ {r′} → (ren⊆ w e₁ ·* S₁) ⟶ r′ →
         ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) Γ′ r′ (ren⊆ w e₂ ·* S₂)
  hyp₁ e₁ e₂ nu h w S₁ S₂ R cr s with ne-tapp-inv (Ne-ren idᴿ (⊆-ren w) nu) s
  ... | (X′ , sX , refl) with ⟶-ren-inv idᴿ (⊆-ren w) e₁ sX
  ...   | (u , su , refl) = h su w S₁ S₂ R cr
  hyp₂ : ∀ {Γ : Ctx ∅} (e₁ : Expr Γ ((∀α T) [ η₁ ]ˢ)) (e₂ : Expr Γ ((∀α T) [ η₂ ]ˢ)) →
         Ne e₂ → (∀ {u} → e₂ ⟶ u → ⟦ ∀α T ⟧² ρ Γ e₁ u) →
         ∀ {Γ′} (w : Γ ⊆ Γ′) (S₁ S₂ : Type ∅ l) (R : Pred² S₁ S₂) (cr : CR² R) →
         ∀ {r′} → (ren⊆ w e₂ ·* S₂) ⟶ r′ →
         ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) Γ′ (ren⊆ w e₁ ·* S₁) r′
  hyp₂ e₁ e₂ nu h w S₁ S₂ R cr s with ne-tapp-inv (Ne-ren idᴿ (⊆-ren w) nu) s
  ... | (X′ , sX , refl) with ⟶-ren-inv idᴿ (⊆-ren w) e₂ sX
  ...   | (u , su , refl) = h su w S₁ S₂ R cr

-- ══════════════ §B6  β-expansion, ONE SIDE AT A TIME ═══════════════
-- The genuinely new part relative to the unary proof.  In the λ-case of
-- the fundamental theorem the two sides are the same term under two
-- different substitutions, so both are redexes; but a step on one side
-- does NOT come with a matching step on the other, so the expansion has
-- to be done separately on the left and on the right, with the opposite
-- side held completely abstract.  That is exactly why CR3 above is
-- stated in one-sided form.

⟦⟧²-β-λ-L : ∀ {Δ l₁ l₂} (T₁ : Type Δ l₁) (T₂ : Type Δ l₂) {η₁ η₂ : Sub Δ ∅}
            (ρ : Env² Δ η₁ η₂) (c : CREnv² ρ) {Γ : Ctx ∅}
            (b : Expr (Γ ▷ (T₁ [ η₁ ]ˢ)) (T₂ [ η₁ ]ˢ)) (a : Expr Γ (T₁ [ η₁ ]ˢ))
            (d : Expr Γ (T₂ [ η₂ ]ˢ)) → SN b → SN a →
            ⟦ T₂ ⟧² ρ Γ (b [ a ]) d → ⟦ T₂ ⟧² ρ Γ ((λx b) · a) d
⟦⟧²-β-λ-L T₁ T₂ ρ c b a d (acc fb) (acc fa) h =
  cr²-exp₁ (⟦⟧²-CR T₂ ρ c) (ne-app _ _) hyp
  where
  hyp : ∀ {r} → ((λx b) · a) ⟶ r → ⟦ T₂ ⟧² ρ _ r d
  hyp β-λ            = h
  hyp (ξ-·₁ (ξ-λ s)) =
    ⟦⟧²-β-λ-L T₁ T₂ ρ c _ a d (fb s) (acc fa)
              (cr²-fwd₁ (⟦⟧²-CR T₂ ρ c) h (⟶-sub idˢ ((idˢ ∣ a ∙ˢ Idˢ)) s))
  hyp (ξ-·₂ s)       =
    ⟦⟧²-β-λ-L T₁ T₂ ρ c b _ d (acc fb) (fa s)
              (cr²-fwd*₁ (⟦⟧²-CR T₂ ρ c) h (sub-⟶* b s))

⟦⟧²-β-λ-R : ∀ {Δ l₁ l₂} (T₁ : Type Δ l₁) (T₂ : Type Δ l₂) {η₁ η₂ : Sub Δ ∅}
            (ρ : Env² Δ η₁ η₂) (c : CREnv² ρ) {Γ : Ctx ∅}
            (d : Expr Γ (T₂ [ η₁ ]ˢ))
            (b : Expr (Γ ▷ (T₁ [ η₂ ]ˢ)) (T₂ [ η₂ ]ˢ)) (a : Expr Γ (T₁ [ η₂ ]ˢ)) →
            SN b → SN a →
            ⟦ T₂ ⟧² ρ Γ d (b [ a ]) → ⟦ T₂ ⟧² ρ Γ d ((λx b) · a)
⟦⟧²-β-λ-R T₁ T₂ ρ c d b a (acc fb) (acc fa) h =
  cr²-exp₂ (⟦⟧²-CR T₂ ρ c) (ne-app _ _) hyp
  where
  hyp : ∀ {r} → ((λx b) · a) ⟶ r → ⟦ T₂ ⟧² ρ _ d r
  hyp β-λ            = h
  hyp (ξ-·₁ (ξ-λ s)) =
    ⟦⟧²-β-λ-R T₁ T₂ ρ c d _ a (fb s) (acc fa)
              (cr²-fwd₂ (⟦⟧²-CR T₂ ρ c) h (⟶-sub idˢ ((idˢ ∣ a ∙ˢ Idˢ)) s))
  hyp (ξ-·₂ s)       =
    ⟦⟧²-β-λ-R T₁ T₂ ρ c d b _ (acc fb) (fa s)
              (cr²-fwd*₂ (⟦⟧²-CR T₂ ρ c) h (sub-⟶* b s))

⟦⟧²-β-Λ-L : ∀ {Δ l l′} (T : Type (l ∙ Δ) l′) {η₁ η₂ : Sub Δ ∅}
            (ρ : Env² Δ η₁ η₂) (c : CREnv² ρ)
            (S₁ S₂ : Type ∅ l) (R : Pred² S₁ S₂) (cr : CR² R) {Γ : Ctx ∅}
            (b : Expr (Γ ▷* l) (T [ η₁ ↑ˢ ]ˢ))
            (d : Expr Γ (T [ S₂ ∙ˢ η₂ ]ˢ)) → SN b →
            ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) Γ (b [* S₁ *]) d →
            ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) Γ ((Λα b) ·* S₁) d
⟦⟧²-β-Λ-L T {η₁} {η₂} ρ c S₁ S₂ R cr b d (acc fb) h =
  cr²-exp₁ (⟦⟧²-CR T (R , ρ) (lift cr , c)) (ne-tapp _ _) hyp
  where
  hyp : ∀ {r} → ((Λα b) ·* S₁) ⟶ r →
        ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) _ r d
  hyp β-Λ            = h
  hyp (ξ-·* (ξ-Λ s)) =
    ⟦⟧²-β-Λ-L T ρ c S₁ S₂ R cr _ d (fb s)
              (cr²-fwd₁ (⟦⟧²-CR T (R , ρ) (lift cr , c)) h
                        (⟶-sub (S₁ ∙ˢ idˢ) ((idˢ ∣ S₁ ∙ˢ* Idˢ)) s))

⟦⟧²-β-Λ-R : ∀ {Δ l l′} (T : Type (l ∙ Δ) l′) {η₁ η₂ : Sub Δ ∅}
            (ρ : Env² Δ η₁ η₂) (c : CREnv² ρ)
            (S₁ S₂ : Type ∅ l) (R : Pred² S₁ S₂) (cr : CR² R) {Γ : Ctx ∅}
            (d : Expr Γ (T [ S₁ ∙ˢ η₁ ]ˢ))
            (b : Expr (Γ ▷* l) (T [ η₂ ↑ˢ ]ˢ)) → SN b →
            ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) Γ d (b [* S₂ *]) →
            ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) Γ d ((Λα b) ·* S₂)
⟦⟧²-β-Λ-R T {η₁} {η₂} ρ c S₁ S₂ R cr d b (acc fb) h =
  cr²-exp₂ (⟦⟧²-CR T (R , ρ) (lift cr , c)) (ne-tapp _ _) hyp
  where
  hyp : ∀ {r} → ((Λα b) ·* S₂) ⟶ r →
        ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) _ d r
  hyp β-Λ            = h
  hyp (ξ-·* (ξ-Λ s)) =
    ⟦⟧²-β-Λ-R T ρ c S₁ S₂ R cr d _ (fb s)
              (cr²-fwd₂ (⟦⟧²-CR T (R , ρ) (lift cr , c)) h
                        (⟶-sub (S₂ ∙ˢ idˢ) ((idˢ ∣ S₂ ∙ˢ* Idˢ)) s))

-- ══════════════ §B7  Related substitutions  (their 𝓖⟦_⟧) ═══════════
Reds² : ∀ {Δ} (Γ : Ctx Δ) {η₁ η₂ : Sub Δ ∅} (ρ : Env² Δ η₁ η₂) {Γ′ : Ctx ∅}
        (σ₁ : η₁ ∣ Γ ⇒ˢ Γ′) (σ₂ : η₂ ∣ Γ ⇒ˢ Γ′) → Set (maxC Γ)
Reds² ∅         ρ σ₁ σ₂ = ⊤
Reds² (Γ ▷ T)   ρ {Γ′} σ₁ σ₂ =
  ⟦ T ⟧² ρ Γ′ (σ₁ _ _ zero) (σ₂ _ _ zero) ×
  Reds² Γ ρ (λ l A x → σ₁ l A (suc x)) (λ l A x → σ₂ l A (suc x))
Reds² (Γ ▷* l)  ρ σ₁ σ₂ =
  Reds² Γ (proj₂ ρ) (λ l₀ A x → σ₁ l₀ (weaken A) (suc* x))
                    (λ l₀ A x → σ₂ l₀ (weaken A) (suc* x))

-- their 𝓖-lookup; the suc*-case is where their LRVwk-eq is needed
Reds²-var : ∀ {Δ} {Γ : Ctx Δ} {η₁ η₂ : Sub Δ ∅} (ρ : Env² Δ η₁ η₂) {Γ′ : Ctx ∅}
            (σ₁ : η₁ ∣ Γ ⇒ˢ Γ′) (σ₂ : η₂ ∣ Γ ⇒ˢ Γ′) → Reds² Γ ρ σ₁ σ₂ →
            ∀ {l} {T : Type Δ l} (x : Γ ∋ T) → ⟦ T ⟧² ρ Γ′ (σ₁ _ _ x) (σ₂ _ _ x)
Reds²-var ρ σ₁ σ₂ rs zero    = proj₁ rs
Reds²-var ρ σ₁ σ₂ rs (suc x) =
  Reds²-var ρ (λ l A y → σ₁ l A (suc y)) (λ l A y → σ₂ l A (suc y)) (proj₂ rs) x
Reds²-var {η₁ = η₁} {η₂ = η₂} ρ σ₁ σ₂ rs (suc* {T = T} x) =
  subst (λ Q → Q _ (σ₁ _ _ (suc* x)) (σ₂ _ _ (suc* x)))
        (sym (⟦⟧²-weaken T η₁ η₂ ρ))
        (Reds²-var (proj₂ ρ) (λ l₀ A y → σ₁ l₀ (weaken A) (suc* y))
                             (λ l₀ A y → σ₂ l₀ (weaken A) (suc* y)) rs x)

Reds²-wk : ∀ {Δ} (Γ : Ctx Δ) {η₁ η₂ : Sub Δ ∅} (ρ : Env² Δ η₁ η₂) (c : CREnv² ρ)
           {Γ′ Γ″ : Ctx ∅} (σ₁ : η₁ ∣ Γ ⇒ˢ Γ′) (σ₂ : η₂ ∣ Γ ⇒ˢ Γ′) (w : Γ′ ⊆ Γ″) →
           Reds² Γ ρ σ₁ σ₂ →
           Reds² Γ ρ (λ l A x → ren⊆ w (σ₁ l A x)) (λ l A x → ren⊆ w (σ₂ l A x))
Reds²-wk ∅        ρ c σ₁ σ₂ w rs = tt
Reds²-wk (Γ ▷ T)  ρ c σ₁ σ₂ w rs =
  ( cr²-wk (⟦⟧²-CR T ρ c) w (proj₁ rs)
  , Reds²-wk Γ ρ c (λ l A x → σ₁ l A (suc x)) (λ l A x → σ₂ l A (suc x)) w (proj₂ rs) )
Reds²-wk (Γ ▷* l) ρ c σ₁ σ₂ w rs =
  Reds²-wk Γ (proj₂ ρ) (proj₂ c)
           (λ l₀ A x → σ₁ l₀ (weaken A) (suc* x))
           (λ l₀ A x → σ₂ l₀ (weaken A) (suc* x)) w rs

-- ══════════════ §B8  THE FUNDAMENTAL THEOREM (ABSTRACTION THM) ═════
-- STW's `semantic-soundness` / `fundamental`, in the two-syntax reading:
-- ONE term e, TWO closing type substitutions η₁ η₂ related by ρ, and TWO
-- term substitutions related pointwise by Reds².
fundamental² :
  ∀ {Δ} {Γ : Ctx Δ} {l} {T : Type Δ l} (e : Expr Γ T)
    {η₁ η₂ : Sub Δ ∅} (ρ : Env² Δ η₁ η₂) (c : CREnv² ρ)
    {Γ′ : Ctx ∅} (σ₁ : η₁ ∣ Γ ⇒ˢ Γ′) (σ₂ : η₂ ∣ Γ ⇒ˢ Γ′) → Reds² Γ ρ σ₁ σ₂ →
    ⟦ T ⟧² ρ Γ′ (η₁ ∣ e [ σ₁ ]ˢ) (η₂ ∣ e [ σ₂ ]ˢ)
fundamental² (` x)  ρ c σ₁ σ₂ rs = Reds²-var ρ σ₁ σ₂ rs x
fundamental² true   ρ c σ₁ σ₂ rs = lift tt
fundamental² false  ρ c σ₁ σ₂ rs = lift tt
fundamental² (_·_ {T₂ = T₂} e₁ e₂) {η₁} {η₂} ρ c σ₁ σ₂ rs =
  subst₂ (λ z₁ z₂ → ⟦ T₂ ⟧² ρ _ (z₁ · (η₁ ∣ e₂ [ σ₁ ]ˢ)) (z₂ · (η₂ ∣ e₂ [ σ₂ ]ˢ)))
         (ren⊆-refl (η₁ ∣ e₁ [ σ₁ ]ˢ)) (ren⊆-refl (η₂ ∣ e₁ [ σ₂ ]ˢ))
         (fundamental² e₁ ρ c σ₁ σ₂ rs ⊆-refl _ _ (fundamental² e₂ ρ c σ₁ σ₂ rs))
fundamental² (_·*_ {T = T} e S) {η₁} {η₂} ρ c σ₁ σ₂ rs =
  subst (λ Q → Q _ ((η₁ ∣ e [ σ₁ ]ˢ) ·* (S [ η₁ ]ˢ)) ((η₂ ∣ e [ σ₂ ]ˢ) ·* (S [ η₂ ]ˢ)))
        (sym (⟦⟧²-[]* T S η₁ η₂ ρ))
        (subst₂ (λ z₁ z₂ → ⟦ T ⟧² {(S [ η₁ ]ˢ) ∙ˢ η₁} {(S [ η₂ ]ˢ) ∙ˢ η₂}
                                  (⟦ S ⟧² ρ , ρ) _ (z₁ ·* (S [ η₁ ]ˢ)) (z₂ ·* (S [ η₂ ]ˢ)))
                (ren⊆-refl (η₁ ∣ e [ σ₁ ]ˢ)) (ren⊆-refl (η₂ ∣ e [ σ₂ ]ˢ))
                (fundamental² e ρ c σ₁ σ₂ rs ⊆-refl
                              (S [ η₁ ]ˢ) (S [ η₂ ]ˢ) (⟦ S ⟧² ρ) (⟦⟧²-CR S ρ c)))
fundamental² (λx {T₁ = T₁} {T₂ = T₂} b) {η₁} {η₂} ρ c {Γ′} σ₁ σ₂ rs w a₁ a₂ r =
  ⟦⟧²-β-λ-L T₁ T₂ ρ c _ a₁ _ (SN-open _) (SN-open a₁)
    (⟦⟧²-β-λ-R T₁ T₂ ρ c _ _ a₂ (SN-open _) (SN-open a₂)
      (subst₂ (λ z₁ z₂ → ⟦ T₂ ⟧² ρ _ z₁ z₂)
              (sym (ren-lift-cons η₁ b σ₁ w a₁)) (sym (ren-lift-cons η₂ b σ₂ w a₂))
              (fundamental² b ρ c
                 ((η₁ ∣ a₁ ∙ˢ (λ l A x → ren⊆ w (σ₁ l A x))))
                 ((η₂ ∣ a₂ ∙ˢ (λ l A x → ren⊆ w (σ₂ l A x))))
                 (r , Reds²-wk _ ρ c σ₁ σ₂ w rs))))
fundamental² (Λα {l = l} {T = T} b) {η₁} {η₂} ρ c {Γ′} σ₁ σ₂ rs w S₁ S₂ R cr =
  ⟦⟧²-β-Λ-L T ρ c S₁ S₂ R cr _ _ (SN-open* _)
    (⟦⟧²-β-Λ-R T ρ c S₁ S₂ R cr _ _ (SN-open* _)
      (subst₂ (λ z₁ z₂ → ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) _ z₁ z₂)
              (sym (ren-lift*-cons η₁ b σ₁ w S₁)) (sym (ren-lift*-cons η₂ b σ₂ w S₂))
              (fundamental² b (R , ρ) (lift cr , c)
                 ((η₁ ∣ S₁ ∙ˢ* (λ l₀ A x → ren⊆ w (σ₁ l₀ A x))))
                 ((η₂ ∣ S₂ ∙ˢ* (λ l₀ A x → ren⊆ w (σ₂ l₀ A x))))
                 (Reds²-wk _ ρ c σ₁ σ₂ w rs))))

-- ══════════════ §B9  PARAMETRICITY ═════════════════════════════════

ρ∅² : Env² ∅ idˢ idˢ
ρ∅² = tt

-- REFLEXIVITY / ABSTRACTION THEOREM: every closed term is related to
-- itself at its own type over the empty relation environment.
parametricity : ∀ {l} {T : Type ∅ l} (e : Expr ∅ T) → ⟦ T ⟧² {idˢ} {idˢ} ρ∅² ∅ e e
parametricity {T = T} e =
  subst₂ (λ z₁ z₂ → ⟦ T ⟧² {idˢ} {idˢ} ρ∅² ∅ z₁ z₂) (Identityᵣ e) (Identityᵣ e)
         (fundamental² e {idˢ} {idˢ} ρ∅² tt {∅} Idˢ Idˢ tt)

-- The relation environment is genuinely two-sided, so the theorem also
-- applies to ONE term used at TWO DIFFERENT type instantiations.
-- Instance: the Church booleans 𝔹ᶜ = ∀α. α ⇒ α ⇒ α.  For every closed
-- e : 𝔹ᶜ, every pair of closed types S₁ S₂, every candidate R between
-- them, and every pair of R-related arguments, the two instantiations
-- produce R-related results.  This is Reynolds' abstraction theorem for
-- 𝔹ᶜ, a statement STW's syntax-vs-denotation relation cannot express.
free-theorem-𝔹ᶜ :
  ∀ (e : Expr ∅ 𝔹ᶜ) (S₁ S₂ : Type ∅ lzero) (R : Pred² S₁ S₂) (cr : CR² R)
    (a₁ b₁ : Expr ∅ S₁) (a₂ b₂ : Expr ∅ S₂) →
    R ∅ a₁ a₂ → R ∅ b₁ b₂ →
    R ∅ (((e ·* S₁) · a₁) · b₁) (((e ·* S₂) · a₂) · b₂)
free-theorem-𝔹ᶜ e S₁ S₂ R cr a₁ b₁ a₂ b₂ ra rb =
  subst₂ (λ z₁ z₂ → R ∅ (z₁ · b₁) (z₂ · b₂))
         (ren⊆-refl ((e ·* S₁) · a₁)) (ren⊆-refl ((e ·* S₂) · a₂))
         (step₂ ⊆-refl b₁ b₂ rb)
  where
  step₁ : ⟦ (` here) ⇒ ((` here) ⇒ (` here)) ⟧² {S₁ ∙ˢ idˢ} {S₂ ∙ˢ idˢ} (R , ρ∅²) ∅
            (ren⊆ ⊆-refl e ·* S₁) (ren⊆ ⊆-refl e ·* S₂)
  step₁ = parametricity e ⊆-refl S₁ S₂ R cr
  step₂ : ⟦ (` here) ⇒ (` here) ⟧² {S₁ ∙ˢ idˢ} {S₂ ∙ˢ idˢ} (R , ρ∅²) ∅
            ((e ·* S₁) · a₁) ((e ·* S₂) · a₂)
  step₂ =
    subst₂ (λ z₁ z₂ → ⟦ (` here) ⇒ (` here) ⟧² {S₁ ∙ˢ idˢ} {S₂ ∙ˢ idˢ} (R , ρ∅²) ∅
                        (z₁ · a₁) (z₂ · a₂))
           (ren⊆-refl (e ·* S₁)) (ren⊆-refl (e ·* S₂))
           (subst₂ (λ z₁ z₂ → ⟦ (` here) ⇒ (` here) ⟧² {S₁ ∙ˢ idˢ} {S₂ ∙ˢ idˢ} (R , ρ∅²) ∅
                                (ren⊆ ⊆-refl z₁ · a₁) (ren⊆ ⊆-refl z₂ · a₂))
                   (ren⊆-refl (e ·* S₁)) (ren⊆-refl (e ·* S₂))
                   (step₁ ⊆-refl a₁ a₂ ra))
