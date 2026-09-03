# Supplementary material

Agda 2.8.0, agda-stdlib 2.3. Every module carries its own
`{-# OPTIONS --rewriting --local-confluence-check #-}`, so nothing depends on
how you invoke `agda`.

    systemf.agda        the development the paper is about, maps as functions
    systemf-vec.agda    the same, maps as inductive vectors (§3.4)
    mltt.agda           Martin-Löf type theory on the same machinery, functions
    mltt-vec.agda       the same, vectors
    examples.agda       the small examples of §2
    poplmark/           the POPLmark Challenge and POPLmark Reloaded
    generator/          agdasubst.py, which emits poplmark/Languages/

## Checking it

    agda systemf.agda
    agda systemf-vec.agda
    agda mltt.agda
    agda mltt-vec.agda
    cd poplmark && ./check.sh

`check.sh` typechecks every module and tabulates lines, exit status, error
classes, non-joinable critical pairs and wall time. Every module reports 0
errors and 0 non-joinable pairs. Each module takes about 70 seconds, so the run
is about 15 minutes.

## What is assumed

`systemf.agda`, `mltt.agda` and every `poplmark/Languages/*.agda` model a map as
a function from variables and postulate function extensionality.
`systemf-vec.agda` and `mltt-vec.agda` model it as an inductive vector and
assume nothing.

## What is not checked in Agda

Agda's `--local-confluence-check` checks local confluence, not confluence, and
does not check termination of rewrite rules at all. The system was exported as a
first-order term rewriting system and given to AProVE, which proves termination
in 23.9 s and confluence in 24.9 s. That export and the two proof texts are not
part of this supplement; §4.3 of the paper reports them.

## POPLmark Challenge

Every module names its results at the end of the file, under the challenge's own
numbering.

| part | proved | where | gap |
|---|---|---|---|
| 1A | Lemma 3.1 transitivity, Lemma 3.2 narrowing with the trailing ∆ | `Challenge/Subtyping.agda` | none |
| 2A | Theorem 3.3 preservation, Theorem 3.4 progress | `Challenge/Subtyping.agda` | none |
| 1B | Lemma 3.1 with record types, Lemma 3.2 | `Challenge/Records.agda`, `Challenge/Patterns.agda` | the relation carries a primitive reflexivity rule, eliminated below |
| 2B | Theorem 3.3, Theorem 3.4, Lemma A.17, for records, projection, patterns and `let` | `Challenge/Patterns.agda` | reduction is given by congruence rules, not related to the challenge's evaluation contexts for this language |
| 3 | not attempted | none | the three tasks are not proved anywhere in this development |

Gaps, in full:

* **Part 3 is not attempted.** None of the three tasks is proved in this
  development: deciding `t ⟶ t′`, deciding `t ⟶* t′ ↛`, and finding a reduct.
  Neither are the challenge's own graded test terms.
* **Part 2B and evaluation contexts.** Footnote 5 of the challenge sanctions the
  congruence-rule presentation of reduction, which `Challenge/Patterns.agda`
  uses. The equivalence with the challenge's `E-Ctx` presentation is proved for
  pure F<: (`Challenge/Subtyping.agda`) and for records and projection
  (`Challenge/Records.agda`, `congruence≡evaluation-contexts`, where Theorems
  3.3 and 3.4 are then stated for `_⟶_` itself), but not for the language with
  `let`.
* **Record subtyping carries a primitive reflexivity rule.** The multi-sorted
  syntax admits a record body that is a variable, a form F<: does not have, and
  at such a body the structural proof of reflexivity has no case, so `_⊢_<:ᴿ_`
  takes reflexivity as a rule. `Challenge/Records.agda` gives the challenge's
  system verbatim, with no reflexivity rule anywhere (`_⊢_<:ᶜ_` / `_⊢_<:ᴿᶜ_`),
  proves the two agree on well-formed types, and transfers transitivity to it
  (`lemma-3-1-transitivity-challenge`). `Challenge/Patterns.agda` does the same
  at the record level only (`transitivityᴿ°`).
* **Representation.** Terms are intrinsically scoped de Bruijn terms, so
  well-scopedness holds by construction rather than by a well-formedness
  judgment, and α-equivalence is syntactic equality. Progress is stated for the
  empty context. The syntax has a variable at every sort, so it admits a record
  body, a record term and a pattern that are variables, which F<: does not have,
  and `Challenge/Patterns.agda` gives each of those a typing rule so that the
  judgment is total. The `Wf` premises of `lemma-3-1-transitivity-challenge`
  rule such bodies out and require the labels of a record type to be pairwise
  distinct, which is the challenge's own side condition.

## POPLmark Reloaded

| part | proved | where | gap |
|---|---|---|---|
| 1a | Lemmas 3.9–3.13 | `Reloaded/Soundness.agda` | none |
| 1b | Lemma 3.14, Theorem 3.1 | `Reloaded/Soundness.agda` | the optional evaluation-context variant is not proved |
| 2a | Lemmas 3.17–3.19 | `Reloaded/Normalization.agda` | none |
| 2b | Theorem 3.3, Definition 3.3, Lemma 3.20, Corollary 3.4 | `Reloaded/Normalization.agda` | none |
| 1a, 1b with sums (§3.7) | the same, plus Lemmas 3.21–3.25 | `Reloaded/SumsSoundness.agda` | none |
| 2a, 2b with sums (§3.7) | the same, with the §3.7 closure of the logical predicate | `Reloaded/SumsNormalization.agda` | none |

The §3.2 lemmas the two challenges rest on are proved as well: 3.1 in the two
`Soundness` modules, 3.2 and 3.3 in the two `Normalization` modules, and 3.6,
3.7 and 3.8 in the two `Soundness` modules, with 3.4 and 3.5 as the
single-binder special cases of 3.7. The substitution lemma for typing, which the
challenge uses silently, is `typed-substitution`.

Gaps, in full:

* **The judgments are not type-directed.** The challenge writes reduction, `sn`
  and `SN` as typed judgments `Γ ⊢ M −→ N : A`. Here they are relations on raw
  intrinsically scoped terms, typing is a separate judgment, and Lemma 3.1
  (reduction preserves typing) is proved rather than being true by construction.
  Nothing in 1a, 1b, 2a or 2b uses the dropped typing premises.
* **Section 3.4's "additional twist" is not proved.** That is soundness of `SN`
  via evaluation contexts, Lemmas 3.15 and 3.16 and Theorem 3.2. The challenge
  presents it as an alternative to Theorem 3.1, which is proved.
* **`Reloaded/SumsCommuting.agda` is not a challenge part.** The permutative
  (commuting) conversions are outside what Reloaded asks for and strong
  normalisation for the extended reduction relation is not proved anywhere in
  this development. That module states the two permutative rules, shows renaming
  commutes with them definitionally, exhibits two well-typed terms the current
  `SNe` wrongly calls neutral, and states the stratification that would repair
  it, of which only that it excludes those two terms is proved. Nothing imports
  it.

## What the development costs

Across 4,788 lines of metatheory, **one substitution fact is proved by hand**.
`traversals` counts applications of `_[_]ᴿ` or `_[_]ˢ` outside comments;
`appeals` counts lines invoking `ren-as-sub` or its corollary `[]-as-ren`.

| module | lines | traversals | appeals |
|---|---:|---:|---:|
| `Challenge/Subtyping.agda` | 605 | 12 | **0** |
| `Challenge/Records.agda` | 1032 | 28 | **0** |
| `Challenge/Patterns.agda` | 1139 | 65 | **0** |
| `Reloaded/Soundness.agda` | 351 | 13 | **0** |
| `Reloaded/SumsSoundness.agda` | 550 | 13 | **0** |
| `Reloaded/SumsCommuting.agda` | 257 | 20 | **0** |
| `Reloaded/Normalization.agda` | 362 | 31 | 8 |
| `Reloaded/SumsNormalization.agda` | 492 | 38 | 13 |

The two non-zero rows are `ren-as-sub` — substituting a variable is a
renaming — its corollary `[]-as-ren`, and their clauses. `ren-as-sub` is an
induction on the term, and it has exactly one call site in each module:
`ext-SN`'s β case, where the redex contracts to ``b [ ` x ]₀`` and
anti-renaming needs to see that as a renaming.

It cannot be a rule. `idˢ` is `⟨ idᴿ ⟩`, so ``t [ ` x ]₀`` is
``t [ (` x) ∙ˢ ⟨ idᴿ ⟩ ]ˢ``, which is cons-shaped, and `coincidence` needs a
syntactic `⟨ ξ ⟩`. The repair is ``(` x) ∙ˢ ⟨ ξ ⟩ → ⟨ x ∙ᴿ ξ ⟩``. Registering it
costs 4 non-joinable pairs; completing it gives 5, then 4 again. The pair that survives
every round joins only if composition at a **variable** folds so that
`lift-consᴿ` can fire, and at mode V composition pushes, because folding there
overlaps `def-wkᴿ` unjoinably. It is the same obstruction as **push at V, fold
at T**, met from the substitution side.

## The two models

`systemf.agda` models a map as a function from variables to terms and needs
function extensionality. `systemf-vec.agda` models it as an inductive vector, so
equality of maps is equality of data and the module assumes nothing. Both
register the same 73 rules and prove the same subject reduction; 59 of the rule
names coincide, and the 14 traversal names differ because each file names them
after its own constructors.

## The generator

`poplmark/Languages/*.agda` is **generated**: each of the five cores is emitted
by `generator/agdasubst.py` from the matching signature in
`poplmark/Languages/signatures/`. The σ-calculus infrastructure is generated;
the metatheory on top of it is hand-written.

    python3 generator/agdasubst.py --model=fun \
        poplmark/Languages/signatures/STLC.sg poplmark/Languages/STLC.agda

All five were emitted with `--model=fun`, which models a map as a function;
`--model=vectors` (the default) models it as an inductive vector. `--no-star`
drops the 15-rule iterated-lifting family, which only a signature with a
variable-arity binder needs; it is honoured by `--model=vectors` only.

Of the rules emitted, 57 are signature-independent and 15 more are the iterated
lifting; the rest are `2 × (constructors + 1)` traversal rules. That gives 78
rules for `STLC`, 84 for `STLCSums`, 88 for `Fsub`, 102 for `FsubRecords` and
112 for `FsubPatterns`.

`generator/signatures/` holds fifteen stand-alone example signatures (untyped
λ, CBPV, CPS, π-calculus, …) that exercise the generator on syntaxes this
development does not otherwise use. Most are the HOAS descriptions shipped with
Autosubst 2 and keep that project's `.sig` extension; signatures written for
this development use `.sg`.

A signature declares sorts and constructors; a parenthesised argument is a
binder, a quoted one an external parameter:

    ty : Type
    tm : Type
    arr : ty -> ty -> ty
    all : (ty -> ty) -> ty          -- (s -> t) binds s in t
    lam : ty -> (tm -> tm) -> tm

A binder may bind several variables at once, `(tm -> tm -> tm)`, or a variable
number, `(tm ^ n -> tm)`. `%%module`, `%%var`, `%%funext`, `%%epilogue` and
`%`-prefixed preamble lines control the emitted module's name, its variable
constructor, its extensionality lemma, trailing verbatim text and imports.

## Notation

| written | is |
|---|---|
| `t [ ξ ]ᴿ` | renaming `t` by `ξ` |
| `t [ σ ]ˢ` | substituting `σ` in `t` |
| `t [ u ]₀` | single substitution, `t [ u ∙ˢ idˢ ]ˢ` |
| `ξ₁ ⨟ᴿ ξ₂`, `σ₁ ⨟ σ₂` | composition of renamings, of substitutions |
| `⟨ ξ ⟩` | the coercion of a renaming into a substitution |
| `ξ ↑ᴿ s`, `x ∙ᴿ ξ` | lifting under a binder, and cons |
| `S₁ →ᴿ S₂`, `S₁ →ˢ S₂` | the two map spaces |
| `S ⊢[ m ] s` | the syntax at mode `m` — `S ∋ s` at `V`, `S ⊢ s` at `T` |

The preservation lemmas are `ren-pres` and `sub-pres` in `systemf.agda`. The
POPLmark modules keep the older infix spelling `_⊢⋯ᴿ_` / `_⊢⋯ˢ_` for the same
two statements.

## A dependently typed object language

`mltt.agda` and `mltt-vec.agda` apply the same construction to Martin-Löf type
theory. The signature is `generator/signatures/mltt.sig`: one syntactic sort, so
types are terms, with `Pi`, `lam`, `app`, a universe, and `Nat` with a `natrec`
whose successor branch binds two variables at once. The generator accepted it
unchanged and emitted 90 rules in each model.

Subject reduction and progress are proved with **zero** substitution lemmas
applied by hand, the same count as `systemf.agda`. Church-Rosser for the untyped
β/ι calculus is proved in both files by Takahashi's method, in 380 lines that are
identical in the two models; Π-injectivity follows from it, and in MLTT it is
needed for subject reduction itself rather than only for progress, because a
lambda may reach its Π-type by conversion.

`mltt.agda` assumes only function extensionality. **`mltt-vec.agda` assumes
nothing at all.**
