# Supplementary material

Agda 2.8.0, agda-stdlib 2.3. Every module carries its own
`{-# OPTIONS --rewriting --local-confluence-check #-}`, so nothing depends on
how you invoke `agda`.

    systemf.agda        the development the paper is about, maps as functions
    systemf-vec.agda    the same, maps as inductive vectors (§3.4)
    examples.agda       the small examples of §2
    poplmark/           the POPLmark Challenge and POPLmark Reloaded
    generator/          agdasubst.py, which emits poplmark/Languages/

## Checking it

    agda systemf.agda
    agda systemf-vec.agda
    cd poplmark && ./check.sh

`check.sh` typechecks every module and tabulates lines, exit status, error
classes, non-joinable critical pairs and wall time. Every module reports 0
errors and 0 non-joinable pairs.

Not included: the Part-3 test harness (`Challenge/Test1..7.agda`, `Suite`,
`Timing`), which runs `Animation`'s evaluator against the challenge's own
`step.poplmark`. It carries no substitution reasoning and needs ~76 minutes to
check. `Animation.agda`, which is what Part 3 actually asks for, is here.

## The two models

`systemf.agda` models a map as a function from variables to terms and needs
function extensionality. `systemf-vec.agda` models it as an inductive vector,
so equality of maps is equality of data and the module assumes nothing.

Both register the same 72 rules and prove the same subject reduction. 61 of the
rule names coincide; the 11 traversal rules differ, because the generator names
them after their constructor (`inst-λx_`) where the hand-written file
abbreviates (`inst-λ`).

## What is checked where

The paper's claim has two halves, and two different machines check them.

**Inside Agda**, here. The σ-calculus is installed as a `{-# REWRITE #-}`
system that passes `--local-confluence-check` with 0 non-joinable critical
pairs. That makes the substitution laws hold *definitionally*: a proof that
would otherwise have to `rewrite` by them is a bare constructor application.

**Outside Agda**, not here. Local confluence is not confluence, and Agda does
not check termination of rewrite rules at all. The system was therefore
exported as a first-order term rewriting system and given to AProVE, which
proves termination in 23.9 s and confluence in 24.9 s. That export and the two
proof texts are not part of this supplement; §4.3 of the paper reports them.

## What the development costs

Across 5,293 lines of metatheory, **one substitution fact is proved by hand**.
`traversals` counts applications of `_[_]ᴿ` or `_[_]ˢ` outside comments;
`appeals` counts lines invoking `ren-as-sub` or its corollary `[]-as-ren`.

| module | lines | traversals | appeals |
|---|---:|---:|---:|
| `Challenge/Subtyping.agda` | 635 | 12 | **0** |
| `Challenge/Records.agda` | 884 | 28 | **0** |
| `Challenge/Patterns.agda` | 1161 | 66 | **0** |
| `Challenge/Animation.agda` | 678 | 0 | **0** |
| `Reloaded/Soundness.agda` | 322 | 12 | **0** |
| `Reloaded/SumsSoundness.agda` | 481 | 12 | **0** |
| `Reloaded/SumsCommuting.agda` | 254 | 20 | **0** |
| `Reloaded/Normalization.agda` | 377 | 29 | 8 |
| `Reloaded/SumsNormalization.agda` | 501 | 36 | 13 |

The two non-zero rows are `ren-as-sub` — substituting a variable is a
renaming — its corollary `[]-as-ren`, and their clauses. `ren-as-sub` is an
induction on the term, and it has exactly one call site in each module:
`ext-SN`'s β case, where the redex contracts to ``b [ ` x ]₀`` and
anti-renaming needs to see that as a renaming.

Why it cannot be a rule is worth stating precisely, because it is not an
independent limitation. `idˢ` is `⟨ idᴿ ⟩`, so ``t [ ` x ]₀`` is
``t [ (` x) ∙ˢ ⟨ idᴿ ⟩ ]ˢ`` — cons-shaped, and `coincidence` needs a
syntactic `⟨ ξ ⟩`. The repair is ``(` x) ∙ˢ ⟨ ξ ⟩ → ⟨ x ∙ᴿ ξ ⟩``, which is the
S → R direction `⟨⟩-comp`, `⟨⟩-lift` and `coincidence` already have.
Registering it costs 4 non-joinable pairs; completing it (the two ⨟-continued
companions, then `distᴿ` and `lift-consᴿ`) gives 5, then 4 again. The pair
that survives every round joins only if composition at a **variable** folds so
that `lift-consᴿ` can fire — and at mode V composition pushes, because folding
there overlaps `def-wkᴿ` unjoinably. It is the *same* obstruction as
**push at V, fold at T**, met from the substitution side.

## Which parts of the challenges are solved

| | |
|---|---|
| POPLmark 1A, 2A | `Challenge/Subtyping.agda` |
| POPLmark 1B | `Challenge/Records.agda` |
| POPLmark 2B | `Challenge/Patterns.agda` |
| POPLmark 3 | `Challenge/Animation.agda` |
| Reloaded 1a, 1b | `Reloaded/Soundness.agda`, `Reloaded/SumsSoundness.agda` |
| Reloaded 2a, 2b | `Reloaded/Normalization.agda`, `Reloaded/SumsNormalization.agda` |

`Reloaded/SumsCommuting.agda` is not a challenge part. The permutative
(commuting) conversions are outside what Reloaded asks for, and that module
measures what adding them would cost rather than estimating it.

Each `Challenge/` and `Reloaded/` module sits on exactly one `Languages/`
module, named in its `open import`.

## The generator

`poplmark/Languages/*.agda` is **generated**: each of the five cores is emitted
by `generator/agdasubst.py` from the matching signature in
`poplmark/Languages/signatures/`. The σ-calculus infrastructure is generated;
the metatheory on top of it is hand-written.

    python3 generator/agdasubst.py poplmark/Languages/signatures/STLC.sg \
        poplmark/Languages/STLC.agda

`--model=vectors` (the default) emits maps as inductive vectors, `--model=fun`
as functions; `--no-star` drops the 15-rule iterated-lifting family, which only
a signature with a variable-arity binder needs.

`generator/signatures/` holds fifteen stand-alone example signatures (untyped
λ, CBPV, CPS, π-calculus, …) that exercise the generator on syntaxes this
development does not otherwise use. Most are the HOAS descriptions shipped
with Autosubst 2 and keep that project's `.sig` extension; signatures written
for this development use `.sg`.

A signature declares sorts and constructors; a parenthesised argument is a
binder, a quoted one an external parameter:

    ty : Type
    tm : Type
    arr : ty -> ty -> ty
    all : (ty -> ty) -> ty          -- (s -> t) binds s in t
    lam : ty -> (tm -> tm) -> tm

A binder may bind several variables at once, `(tm -> tm -> tm)`, or a
variable number, `(tm ^ n -> tm)`.

`%%module`, `%%var`, `%%epilogue` and `%`-prefixed preamble lines control the
emitted module's name, its variable constructor, trailing verbatim text and
imports. 72 of the rules are signature-independent, plus 15 more with `↑*`;
the rest are `2 × (constructors + 1)` traversal rules.

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
