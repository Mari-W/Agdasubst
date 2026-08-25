# Design notes recovered from the Agda sources

The Agda modules carried long explanatory headers.  They were trimmed to what a
reader needs at the file, and the removed prose is kept here verbatim so nothing
is lost.  Each section names the file and the line range it came from.

Nothing here is load-bearing: no build step reads this file, and every claim it
makes is either checked in the Agda or recorded more carefully in `trs/TRS.md`
(the rule-by-rule account) or `supplement/README.md` (what the development
costs).  Treat it as the reasoning behind choices the code no longer explains.

# From `supplement/poplmark/`

## POPLmark Reloaded 2a/2b: why intrinsically scoped, not typed

*Reloaded/Normalization.agda, lines 3-59*

```
-- ═══ POPLMark Reloaded, Challenges 2a and 2b ════════════════════════
--   [Abel, Allais, Hameer, Pientka, Momigliano, Schäfer, Stark, JFP 2019]
--
--   2a  properties of the inductive SN:  renaming, ANTI-renaming,
--       extensionality                                 (Lemmas 3.17-3.19)
--   2b  the Kripke logical predicate R, CR1-CR3, semantic substitutions,
--       the Fundamental Lemma, and  ⊢ M : A  ⟹  M ∈ SN
--                                       (Thm 3.3, Def 3.3, Lem 3.20, Cor 3.4)
--
-- The terms are INTRINSICALLY SCOPED, not intrinsically typed:
-- Languages/STLC.agda is the reference development's multi-sorted
-- σ-calculus at the closed sort set {expr}, so `S ⊢ expr` is the set of
-- λ-terms with at most |S| free variables and nothing more.  The simple
-- types are the separate datatype `Ty` below and the object-language
-- typing judgment is the separate inductive family `Γ ⊢ e ∶ A`.
--
-- WHAT THE LOGICAL PREDICATE IS INDEXED BY (the design decision).
-- `R` is a relation between a TYPE and a SCOPED TERM,
--
--     R : Ty → S ⊢ expr → Set
--
-- defined by recursion on the type, exactly as in the paper.  It is NOT
-- indexed by a typing derivation.  Two reasons, both structural:
--
--   * `R` must recurse on the type (it is not strictly positive, so it
--     cannot be an inductive family).  An STLC type is CLOSED — `Ty` is
--     scope-free — so the type is available as a recursion argument on
--     its own, with no well-typedness hypothesis needed to make sense of
--     it.  That is exactly what fails for F<:, where a type is a term of
--     the scoped syntax and a predicate on types would have to be
--     indexed by the scope.
--   * Well-typedness is a hypothesis of the FUNDAMENTAL LEMMA, not of
--     the predicate.  `fund` recurses on the typing derivation
--     `Γ ⊢ e ∶ A` instead of on the term, and the semantic-substitution
--     predicate `Rˢ Γ σ` is what ties the context to the predicate:
--     `Rˢ Γ σ = ∀ x → R (Γ x) (x [ σ ]ˢ)`.  Nothing else in 2a/2b mentions
--     typing at all: SN, SNe, ⟶SN, renaming, anti-renaming,
--     extensionality and CR1-CR3 are statements about raw scoped terms.
--
-- The consequence is that Corollary 3.4 recovers its content.  Under an
-- intrinsically typed encoding it reads `(e : S ⊢ A) → SN e` — every
-- term of the syntax, because that syntax has no ill-typed terms.  Here it
-- reads `Γ ⊢ e ∶ A → SN e`, and the syntax `S ⊢ expr` really does
-- contain the untypable terms (`λx (x · x)` and friends), for which the
-- statement is false and unprovable.
--
-- The price is the challenge's Lemmas 3.1-3.5, which an intrinsically
-- typed encoding gets for free.  They are proved below: `_⊢⋯ᴿ_` (3.2/3.3,
-- weakening and anti-renaming for typing), `_⊢⋯ˢ_` and `⊢[]` (3.4/3.5,
-- substitution) and `preservation` in Reloaded/Soundness.agda (3.1).
-- Each is three or four lines, because every substitution equation they
-- need holds definitionally in the σ-calculus.  Lemma A.15 (SN, SNe and
-- ⟶SN imply well-typedness) has no analogue and needs none: our SN
-- carries no typing premises to be well-formed in the first place.
--
-- Challenges 1a/1b (soundness of SN w.r.t. the accessibility predicate
-- sn) are in Reloaded/Soundness.agda.
```

## Why `[]-as-ren` must be proved by hand (Normalization)

*Reloaded/Normalization.agda, lines 257-283*

```
-- ─── substituting a VARIABLE is a renaming ──────────────────────────
-- THE ONE SUBSTITUTION FACT THIS DEVELOPMENT HAS TO PROVE BY HAND.
-- `t [ ` x ]₀` and `t [ x ∙ᴿ idᴿ ]ᴿ` are two DISTINCT normal forms of
-- the rewrite system.  `t [ ` x ]₀` unfolds to `t [ (` x) ∙ˢ idˢ ]ˢ`, and
-- `idˢ` IS `⟨ idᴿ ⟩` -- but the map is cons-shaped, not `⟨ _ ⟩`-shaped, so
-- `coincidence` (whose left-hand side needs a syntactic `⟨ ξ ⟩`) cannot
-- fire on it.
--
-- The rule that would fix this is `(` x) ∙ˢ ⟨ ξ ⟩ → ⟨ x ∙ᴿ ξ ⟩`: the
-- S -> R orientation that `⟨⟩-comp`, `⟨⟩-lift` and `coincidence` all
-- have, and which `⟨⟩-cons` -- a LEMMA here, not a registered rule --
-- points the other way round.  With it, `t [ ` x ]₀` would collapse into
-- the renaming world and this file's `[]-as-ren` would be a conversion.
--
-- It cannot be registered.  Measured on this rule set: the rule alone
-- costs 4 non-joinable critical pairs; adding the ⨟-continued companions
-- that close two of them costs 5; adding `distᴿ` and `lift-consᴿ` on top
-- costs 4.  The pair that survives every round is
--
--   (x [ ξ ↑ᴿ s ]ᴿ) [ (` y) ∙ˢ ⟨ ξ₁ ⟩ ]ˢ
--
-- whose two reducts meet only if composition at a VARIABLE folds, so that
-- `lift-consᴿ` can fire -- and composition at mode V pushes, because
-- folding there overlaps `def-wkᴿ` unjoinably.  So this is the same
-- obstruction as the push-at-V/fold-at-T decision, seen from the
-- substitution side.  We supply the missing join as an induction on the
-- term.
```

## Why `[]-as-ren` must be proved by hand (SumsNormalization)

*Reloaded/SumsNormalization.agda, lines 304-330*

```
-- ─── substituting a VARIABLE is a renaming ──────────────────────────
-- THE ONE SUBSTITUTION FACT THIS DEVELOPMENT HAS TO PROVE BY HAND.
-- `t [ ` x ]₀` and `t [ x ∙ᴿ idᴿ ]ᴿ` are two DISTINCT normal forms of
-- the rewrite system.  `t [ ` x ]₀` unfolds to `t [ (` x) ∙ˢ idˢ ]ˢ`, and
-- `idˢ` IS `⟨ idᴿ ⟩` -- but the map is cons-shaped, not `⟨ _ ⟩`-shaped, so
-- `coincidence` (whose left-hand side needs a syntactic `⟨ ξ ⟩`) cannot
-- fire on it.
--
-- The rule that would fix this is `(` x) ∙ˢ ⟨ ξ ⟩ → ⟨ x ∙ᴿ ξ ⟩`: the
-- S -> R orientation that `⟨⟩-comp`, `⟨⟩-lift` and `coincidence` all
-- have, and which `⟨⟩-cons` -- a LEMMA here, not a registered rule --
-- points the other way round.  With it, `t [ ` x ]₀` would collapse into
-- the renaming world and this file's `[]-as-ren` would be a conversion.
--
-- It cannot be registered.  Measured on this rule set: the rule alone
-- costs 4 non-joinable critical pairs; adding the ⨟-continued companions
-- that close two of them costs 5; adding `distᴿ` and `lift-consᴿ` on top
-- costs 4.  The pair that survives every round is
--
--   (x [ ξ ↑ᴿ s ]ᴿ) [ (` y) ∙ˢ ⟨ ξ₁ ⟩ ]ˢ
--
-- whose two reducts meet only if composition at a VARIABLE folds, so that
-- `lift-consᴿ` can fire -- and composition at mode V pushes, because
-- folding there overlaps `def-wkᴿ` unjoinably.  So this is the same
-- obstruction as the push-at-V/fold-at-T decision, seen from the
-- substitution side.  We supply the missing join as an induction on the
-- term.
```

## Commuting conversions: the three measurements M1-M3

*Reloaded/SumsCommuting.agda, lines 3-47*

```
-- ═══ POPLmark Reloaded STLC+: the COMMUTING CONVERSIONS, MEASURED ═══
--
-- Reloaded/SumsSoundness.agda and Reloaded/SumsNormalization.agda
-- cover the β-rules for sums and the congruences, but NOT the permutative
-- (commuting) conversions.  This module MEASURES what adding them would
-- cost, rather than estimating it.  Everything here typechecks; nothing
-- here is imported by the metatheory, and nothing here claims the
-- commuting conversions are proved -- they are not.
--
-- Three separate measurements:
--
--   (M1) Can the two permutative rules even be STATED in this
--        σ-calculus, and does RENAMING commute with them definitionally?
--        Measured: YES to both.  The weakenings the rules introduce
--        (`n [ wkᴿ expr ]ᴿ` and `w [ (wkᴿ expr ↑ᴿ expr) ]ᴿ`) are pushed
--        through by the rewrite system, so `ren-↝π` is a bare
--        constructor application — no transport, no new rewrite rule,
--        and the rule set stays at 72 rules and 0 non-joinable pairs.
--
--   (M2) Does the INDUCTIVE characterisation of strong normalisation
--        survive?  Measured: NO.  `SNe`'s `cse` and `app` constructors
--        admit terms that are π-redexes (`SNe-admits-π-redex-c`,
--        `SNe-admits-π-redex-a` below, both machine-checked, and both
--        WELL-TYPED — `⊢bad-c` / `⊢bad-a` give the derivations, which
--        under the scoped encoding is a real obligation rather than a
--        property of the indices), so `neu : SNe e → SN e` asserts that
--        a REDUCIBLE term is normal by fiat.  Soundness `SN ⟹ sn` is
--        exactly what that breaks: `sn` must inspect every reduct and
--        `neu` supplies nothing about the π-reduct.  This is not a
--        missing case; the definition of "neutral" is wrong once π is
--        present.
--
--   (M3) What has to change.  Neutrals must be stratified: an
--        elimination spine may contain at most one `case`, at the
--        outside.  `SNe⁻` (variable head, applications only) and
--        `SNe′ = SNe⁻ ∪ {case SNe⁻ u v}` below is that stratification,
--        and `SNe⁻-no-π·` proves the smaller class is closed
--        under nothing (no π-rule applies to it) — which is the
--        property `neu` needs and the current `SNe` lacks.
--        With it, `SNsum` does need a further closure constructor for
--        `case`-headed terms (`r-cse`), and — measured, see the note at
--        the end — its two parameters must become SCOPE-INDEXED
--        families, because the branches of that `case` live in
--        extended scopes -- which the present `SNsum`, whose parameters
--        are `S ⊢ expr → Set` for one fixed S, cannot express.
```

## Commuting conversions: consequences of a Kripke `R` at sums

*Reloaded/SumsCommuting.agda, lines 269-298*

```
-- The new constructor is well-formed only because `P` and `Q` are
-- Kripke: `u` lives in `expr ∷ S`, not in `S`.  Compare `SNsum` in
-- Reloaded/SumsNormalization.agda, whose parameters are `S ⊢ expr → Set`
-- for ONE fixed `S`; that shape cannot state `r-cse` at all.
--
-- MEASURED CONSEQUENCES of making `R (A +ᵗ B) = SNsum′ (R A) (R B)`:
--   * `R` must become a Kripke family at every type, not only at `⇒`.
--   * `cr1` gains one case (`r-cse`), which needs `SN (case r u v)`
--     from `SNe⁻ r` and SN branches — available from `cse′`.
--   * `R-case` (the fundamental lemma's `case`) gains one case, and it
--     is the one that has to APPLY the permutative conversion: from
--     `R (A +ᵗ B) (case r u v)` by `r-cse` and reducible continuations,
--     `R C (case (case r u v) w₁ w₂)` is obtained by `cr2` on `πc`,
--     which therefore has to be in `_⟶SN_` as well.
--   * `_⟶SN_` gaining π means `confl` in Reloaded/SumsSoundness.agda
--     gains the overlaps (applsn, π·) and (csesn, πc) — 2 new critical
--     cases at the top level, each recursing.
--
-- Every obstruction listed here is about the shape of the SN/SNsum
-- families; none of them is discharged by the object-language types.
-- Because the syntax is intrinsically SCOPED rather than typed, the two
-- counterexample terms carry explicit typing derivations (`⊢bad-c`,
-- `⊢bad-a`), so "SNe accepts a well-typed π-redex" is a proved statement
-- rather than a by-product of intrinsic typing.
--
-- None of this is done here.  What is measured is (i) that the σ-calculus
-- side is FREE — the permutative rules need no new rewrite rule, no
-- transport and no change to the 72-rule core — and (ii) that the
-- obstruction is entirely in the SN characterisation, at a precisely
-- located point: the definition of "neutral".
```

## F<: 1A/2A: the mode-merged single judgment

*Challenge/Subtyping.agda, lines 3-28*

```
-- ═══ POPLmark Challenge, parts 1A and 2A ════════════════════════════
--
--   1A  transitivity and narrowing of algorithmic F<: subtyping
--   2A  preservation and progress for F<:
--
-- built on the σ-calculus rewrite system of Languages/Fsub.agda.
--
-- THE MODE-MERGED, MULTI-SORTED DESIGN, PUSHED ONE STEP FURTHER.
-- F<: has two judgments -- subtyping between types and typing of terms.
-- Here they are ONE inductive family
--
--     _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set
--
-- indexed by the sort s of the subject.  At s = type it is
-- `Γ ⊢ A <: B`; at s = expr it is `Γ ⊢ e ∶ A`.  The payoff is that the
-- typed-map
-- machinery is written ONCE and simultaneously delivers
--
--   * weakening of subtyping AND of typing              (_⊢⋯ᴿ_)
--   * type substitution in subtyping AND in typing,
--     and term substitution in typing                   (_⊢⋯ˢ_)
--   * narrowing of subtyping AND of typing              (narrow)
--
-- and that a "typed substitution" σ ∶ Γ₁ →ˢ Γ₂ automatically means
-- "subtyping-respecting at type variables, typing-respecting at term
-- variables" -- the single condition F<: substitution lemmas need.
```

## POPLmark Part 3: why determinism is needed on top of decidable equality

*Challenge/Animation.agda, lines 3-31*

```
-- ═══ POPLmark Challenge, Part 3 ═════════════════════════════════════
--   "Testing and Animating with Respect to the Semantics"
--
--   1. Given F<: terms t and t′, decide whether t ⟶ t′.
--   2. Given t and t′, decide whether t ⟶* t′ ↛.
--   3. Given t, find t′ such that t ⟶ t′.
--
-- Task 3 is `reduct`.  Task 1 is `_↪?_`, a REAL decision procedure:
-- `Dec (e ↪ e′)` for arbitrary e, e′.  Task 2 is `evalDec`, decidable
-- up to a fuel bound.
--
-- The three ingredients, in order of depth:
--
--   * `stp⁺ : (e : S ⊢ expr) → Dec (Σ[ e′ ] (e ↪ e′))` — a step function
--     that is sound AND complete by construction: its `no` branch is a
--     proof that NOTHING steps.
--   * `_≟_ : (t u : S ⊢ s) → Dec (t ≡ u)` — decidable equality on the
--     intrinsically scoped, multi-sorted syntax, 89 clauses.
--   * `determinism : e ↪ e₁ → e ↪ e₂ → e₁ ≡ e₂`.
--
-- Decidable equality alone is *necessary but not sufficient*: without
-- determinism, `stp⁺ e = yes (e″ , _)` and `e″ ≢ e′` would not refute
-- `e ↪ e′`.  Determinism is what makes `stp⁺` complete for the whole
-- relation rather than for one reduction strategy.
--
-- The other question Part 3 asks is whether a term can COMPUTE at all:
-- `_[_]₀` unfolds to `_[ _ ∙ˢ idˢ ]ˢ` whose symbols are all `opaque`, so
-- no β-contraction can happen by unfolding — every one is performed by
-- the REWRITE SYSTEM.  Each `refl` below is Agda running the semantics.
```

---

# From `systemf.agda`

Removed from the rule block.  `trs/TRS.md` carries the full rule-by-rule
account; these were the in-file notes.

## Why compositionality must split by mode (push at V, fold at T)

```
  -- (Clos) at the renaming level.  It must be SPLIT by mode, and the
  -- two halves point in OPPOSITE directions — the one place where the
  -- V/T merge does not pay.  Reason: renaming preserves the mode, so
  -- x [ ξ₁ ]ᴿ is itself a variable and hence again a subject for the
  -- applied rules; a fold at mode V therefore overlaps def-wkᴿ
  -- unjoinably ((x [ ξ₁ ]ᴿ) [ wkᴿ s ]ᴿ reduces to suc (x [ ξ₁ ]ᴿ) on one
  -- side and to the stuck x [ ξ₁ ⨟ᴿ wkᴿ s ]ᴿ on the other).  So
  -- composition at a variable PUSHES and composition on a term FOLDS.
  -- (In the σ-world the question does not arise: a substituted variable
  -- is a term, which no applied rule can match.)
```

## Which sigma-up completion families push at V makes unnecessary

```
  -- with push at variables the VarShift2/FVarLift2/RVarLift2 family is
  -- unnecessary: push exposes the factors, so the applied rules fire on
  -- them directly.  What remains is the variable-level lift-dist-compˢˢ (the
  -- join of push with lift-dist-compᴿᴿ) and interact under a continuation.
```

## Why compositionality-RS is T-only

```
  -- T-ONLY.  Its V-instance would be compositionalityᴿˢ-⨟-var read backwards, and
  -- registering both LOOPS: compositionalityᴿˢ folds (x [ ξ) ]ᴿ [ σ ]ˢ into
  -- x [ (⟨ξ⟩ ]ˢ ⨟ˢ σ) and compositionalityᴿˢ-⨟-var pushes it straight back.  The systematic
  -- rule for the two-world system is: at mode V everything PUSHES, at
  -- mode T everything FOLDS (cf. compositionalityᴿᴿ-var vs compositionalityᴿᴿ).
```

## The one completion image that cannot be taken

```
  -- ⟨⟩-comp needs a C2 continuation image, because assoc right-nests ⨟
  -- and ⟨ξ₁⟩ ⨟ˢ ⟨ξ₂⟩ is then not a subterm of ⟨ξ₁⟩ ⨟ˢ (⟨ξ₂⟩ ⨟ˢ τ).  The
  -- GENERAL image ⟨ξ₁⟩ ⨟ˢ (⟨ξ₂⟩ ⨟ˢ τ) → ⟨ξ₁ ⨟ᴿ ξ₂⟩ ⨟ˢ τ is the exact
  -- inverse of ⟨⟩-split-⨟ and LOOPS with it -- the one completion image
  -- in the whole system that cannot be taken.  What survives is that
  -- image restricted to the prefixes on which the ᴿ world can make
  -- progress, i.e. where folding immediately fires a ᴿ-rule and so does
  -- not hand the result straight back to ⟨⟩-split-⨟.  Those prefixes are
  -- exactly the three ᴿ-rules that themselves needed C2 images --- the
  -- same set, twice --- and each rule is named for the one it fires.
```

## Why there is no ⟨⟩-split-tail-⨟

```
  -- the TAIL companion of ⟨⟩-split-⨟: same split, but where the coerced
  -- composite is the right operand and so has no continuation for
  -- ⟨⟩-split-⨟ to match.  With a continuation present it is derivable
  -- (⟨⟩-split-⨟ then lift-dist-compˢᴿ-⨟), which is why there is no
  -- ⟨⟩-split-tail-⨟ -- see closure.agda.
```

## What first-class renamings buy in the preservation lemma

```
-- TYPED RENAMINGS: phase 1 of the preservation lemma.  With renamings
-- first class this is a plain judgment on ᴿ-maps, and the payoff is
-- immediate.  _[_]ᴿ preserves the mode, so a typed renaming sends a
-- variable to a VARIABLE by construction, and the ⊢`-case below is a
-- direct application.  The one-world file cannot say this: there phase
-- 1 must be a Σ-PREDICATE on substitutions,
--
--   σ ∶ᵥ Γ₁ →ˢ Γ₂ = ∀ x t → Γ₁ ∋ x ∶ t → Σ y ((x [ σ) ]ˢ ≡ ` y) × …
--
-- and extracting that y costs a transport (its ⊢ᵥ-var, "the one
-- unavoidable transport", with a `rewrite` to dodge UnificationStuck).
-- HERE THE TRANSPORT DISAPPEARS — that is the clearest single win of
-- first-class renamings.
```

---

# From the remaining `Reloaded/` headers

## Reloaded/Soundness.agda header, lines 3-26

```
-- ═══ POPLMark Reloaded, Challenges 1a and 1b ════════════════════════
--
--   1a  properties of the accessibility predicate `sn`: subterm and
--       expansion closure, closure of neutrals, confluence ("weak
--       standardisation") and backward closure   (Lemmas 3.8-3.13)
--   1b  soundness of the inductive characterisation:
--       SN ⟹ sn,  SNe ⟹ sn,  ⟶SN ⟹ ⟶sn        (Lemma 3.14, Thm 3.1)
--
-- Together with Reloaded/Normalization.agda (2a/2b) this closes the STLC
-- half of the challenge:  every well-typed term is strongly normalising
-- in the classical, accessibility sense.
--
-- The syntax is intrinsically scoped (Languages/STLC.agda), so `_↝_`,
-- `sn`, `ne` and `_⟶sn_` are relations on raw λ-terms and every lemma
-- of 1a is a statement about arbitrary terms, typed or not.  Typing
-- enters in exactly two places: `preservation` (the challenge's Lemma
-- 3.1, which the intrinsically typed encoding got for free and which is
-- proved below in four lines) and `corollary-3-4-sn`.
--
-- The σ-calculus contribution here is Lemma 3.7 (`sub-↝`, `ren-↝`):
-- reduction is closed under substitution because
--   (b [ n ]₀) [ σ ]ˢ ≡ (b [ (σ ↑ˢ expr) ]ˢ) [ n [ σ ]ˢ ]₀
-- holds definitionally, so the β case of each of those lemmas is a bare
-- constructor.  Everything else is ordinary induction on derivations.
```

## Reloaded/SumsSoundness.agda header, lines 3-24

```
-- ═══ POPLMark Reloaded STLC+, Challenges 1a and 1b (with sums) ══════
--
--   1a  properties of the accessibility predicate `sn`: subterm and
--       expansion closure, closure of neutrals, confluence ("weak
--       standardisation") and backward closure   (Lemmas 3.8-3.13)
--   1b  soundness of the inductive characterisation:
--       SN ⟹ sn,  SNe ⟹ sn,  ⟶SN ⟹ ⟶sn        (Lemma 3.14, Thm 3.1)
--
-- Together with Reloaded/SumsNormalization.agda (2a/2b) this closes the
-- STLC+ half of the challenge:  every well-typed term is strongly
-- normalising in the classical, accessibility sense.
--
-- The syntax is intrinsically scoped (Languages/STLCSums.agda), so
-- `_↝_`, `sn`, `ne` and `_⟶sn_` are relations on raw terms.  Typing
-- enters only at `preservation` (the challenge's Lemma 3.1) and at
-- `corollary-3-4-sn`.
--
-- The σ-calculus contribution here is Lemma 3.7 (`sub-↝`, `ren-↝`):
-- reduction is closed under substitution because
--   (b [ n ]₀) [ σ ]ˢ ≡ (b [ (σ ↑ˢ expr) ]ˢ) [ n [ σ ]ˢ ]₀
-- holds definitionally, so the β case of each of those lemmas is a bare
-- constructor.  Everything else is ordinary induction on derivations.
```

## Reloaded/SumsNormalization.agda header, lines 3-26

```
-- ═══ POPLMark Reloaded STLC+, Challenges 2a and 2b (with sums) ══════
--   [Abel, Allais, Hameer, Pientka, Momigliano, Schäfer, Stark, JFP 2019]
--
--   2a  properties of the inductive SN:  renaming, anti-renaming,
--       extensionality                                 (Lemmas 3.17-3.19)
--   2b  the Kripke logical predicate R, CR1-CR3, semantic substitutions,
--       the Fundamental Lemma, and  ⊢ M : A  ⟹  M ∈ SN
--                                       (Thm 3.3, Def 3.3, Lem 3.20, Cor 3.4)
--
-- The terms are intrinsically scoped, not intrinsically typed:
-- Languages/STLCSums.agda is the reference development's multi-sorted
-- σ-calculus at the closed sort set {expr}.  The simple types (now with
-- `_+ᵗ_`) are the separate datatype `Ty` below, and the typing judgment
-- `Γ ⊢ e ∶ A` is a separate inductive family.  See the header of
-- Reloaded/Normalization.agda for why the logical predicate is indexed by a
-- type and a scoped term rather than by a typing derivation; with sums
-- the argument is the same, and `SNsum` below inherits it.
--
-- Challenges 1a/1b are in Reloaded/SumsSoundness.agda.
--
-- the answer to the structural question is at `R` below: the arrow case
-- stays a Π-type defined by recursion on the type, but the sum case
-- cannot -- it has to be an inductive closure (`SNsum`).  So the
-- logical predicate needed restructuring, not just more cases.
```
