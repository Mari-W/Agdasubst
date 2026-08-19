# The canonicity prototype's layer-(i) σ-calculus: does it certify?

Self-contained report. It answers three questions about
`Agdasubst2/fresh/SystemF-canonicity.agda` — the 595-line prototype that proves
canonicity for the non-stratified intrinsic System F and registers its
**logical-relation-environment** σ-calculus as `REWRITE` rules.

**Headline: no.** Repaired and measured, the layer-(i) rule set reports **7 non-joinable
critical pairs**, not 0. The prototype could never have reported 0, because as archived it
does not typecheck at all and Agda never reaches its pragmas.

Nothing in `Agdasubst2/` was modified; the prototype was copied out.

---

## 0. The two layers, kept apart

* **layer (i) — the logical-relation environment.** `Env` / `REnv` / `𝓓⟦_⟧`: the thing
  assigning a predicate (or relation, or `REL`) to each type variable. In the prototype
  this is the `Env` record and its σ-algebra `_∷ᴱ_`, `_⟨_⟩ᴱ`, `_⟪_⟫ᴱ`, together with the
  logical relation `⟦_⟧` itself.
* **layer (ii) — the denotational interpretation of types.** `⟦_⟧ᵀ` and its environment
  actions. This is what `REPORT-adequacy.md` §6 is about; that result stands and is not
  re-opened here.
* **layer 0 — the expression traversal laws.** `Compositionalityᴿᴿ`, `Beta-comp*`, etc.
  The prototype registers these too, in its §0. They are neither (i) nor (ii), and they
  turn out to dominate the measurement.

---

## 1. The prototype as archived never typechecked

Three independent reasons, each verified:

1. **Scope error.** It is written against `SystemF-fresh`, whose reduction had a single
   application congruence `ξ-·`. The current development has full β, where that became
   `ξ-·₁` and `ξ-·₂`. Six sites break. Agda's scope checker rejects them *before* type
   checking, so the `{-# REWRITE #-}` pragmas are never reached.
2. **Universe error.** It declares `Pred : Type 0 → Set` with body `Expr ∅ A → Set`, which
   is `Set₁`. Its header comment discusses `--type-in-type` at length, but its `OPTIONS`
   line does not contain it: `{-# OPTIONS --rewriting  --local-confluence-check #-}`.
3. **The file contradicts itself.** Its §0 comment says

   > "This module carries no `--local-confluence-check`, so `SystemF-fresh` keeps its
   > certificate untouched."

   while its `OPTIONS` line does carry `--local-confluence-check`. The §0 rules are
   described there as "the laws `SystemF-fresh` cannot certify locally confluent (their
   LHS carries the computed index `T [ η₁ ]ˢ`)" — i.e. the author knew they were not
   certifiable and intended the flag off.

So the prototype's apparent "0 non-joinable" was an artifact of the file failing early.
Establishing the real number required repairing it.

---

## 2. The repair, and the measurement

`esop27/SystemF-canonicity.agda` is the prototype retargeted to the current `SystemF`
(full β, `Normal` instead of `Value`, `progress` without a `NoVar` argument). Changes:

| change | why |
|---|---|
| `--type-in-type` added | reason 2 above; the reducibility argument is impredicative |
| `open import SystemF hiding (Neutral)` | the prototype defines its own Girard-neutral `Neutral` as a *function*, shadowing `SystemF`'s data type |
| `ξ-·` → `ξ-·₁` (2 sites) | full β |
| `·-inv` now returns a **sum** | under full β a step out of `e₁ · e₂` can be in the argument |
| `⟦⟧-exp`'s ⇒-case gains an **SN-induction** | same reason; this is `SystemF-strat` §15's `aux` |
| `sn-λx` now takes the body's `SN` | `λx e` steps via `ξ-λ` under full β |
| `Value` → `Normal`, `progress nv e` → `progress e` | the current `SystemF` uses normal forms |

Two truncated variants were then built to isolate the question, each cut immediately after
the last layer-(i) pragma so that no later error can pre-empt the check:

| file | §0 layer-0 pragma | non-joinable pairs |
|---|---|---:|
| `SystemF-canonicity-core.agda` | left **in** | **102** — *all* attributed to §0 |
| `SystemF-canonicity-layer1.agda` | **removed** | **7** — all in layer (i) |

Breakdown of the 102 (all layer 0, none layer (i)): `Compositionalityˢˢ` 14,
`Compositionalityˢᴿ` 13, `Compositionalityᴿˢ` 13, `Compositionalityᴿᴿ` 13,
`Beta-⇑ˢ*-suc*` 8, `Beta-compᴿ` 8, `Beta-⇑ˢ-zero` 7, `Beta-⇑ˢ-suc` 7, `Beta-compˢ` 7,
`Beta-ext-sucˢ*` 6, `Beta-ext-suc*ᴿ` 6.

### The answer to Task 1

> **Does the layer-(i) rule set report 0 non-joinable pairs? No. It reports 7.**

| # | pair | family |
|---|---|---|
| 1 | `∷-⟨⟩↑` vs `_⟨_⟩ᴱ-clause2` | A |
| 2 | `∷-⟪⟫↑` vs `_⟪_⟫ᴱ-clause2` | A |
| 3 | `⟪⟫-∙` vs `_⟪_⟫ᴱ-clause2` | A |
| 4 | `⟦⟧-ren` vs `compositionalityˢᴿ` | B |
| 5 | `⟦⟧-ren` vs `beta-fold-ˢᴿ` | B |
| 6 | `⟦⟧-sub` vs `compositionalityˢˢ` | B |
| 7 | `⟦⟧-sub` vs `beta-fold` | B |

**Family A (3) — rule vs the record's own copattern clause.** `_⟨_⟩ᴱ` and `_⟪_⟫ᴱ` are
defined by copatterns (`syn (ρ ⟨ ζ ⟩ᴱ) = …`, `sem (ρ ⟨ ζ ⟩ᴱ) α = …`), so projecting out of
them *computes*, and that competes with a rewrite rule that rewrites the whole
environment. Agda's output shows it directly:

```
sem (env (proj₁ S ∙ˢ syn ρ) ((S ∷ᴱ ρ) .sem) ⟨ ζ ↑ᴿ ⟩ᴱ) α
reduces to both  sem (S ∷ᴱ (ρ ⟨ ζ ⟩ᴱ)) α           [rule ∷-⟨⟩↑]
            and  (S ∷ᴱ ρ) .sem (α &ᴿ (ζ ↑ᴿ))       [_⟨_⟩ᴱ-clause2]
```

This is the same mechanism that produced `⊛ᵀ ζ η .proj₁` in the layer-(ii) measurements
(`REPORT-adequacy.md` §6): a projection competing with a whole-object rewrite. Its known
fix there was `opaque` on the operations.

**Family B (4) — interpretation rule vs type-level σ-rule.** These are, name for name, the
*same* pairs as layer (ii)'s P3/P4/P9/P10. The mechanism is what the prototype's own
comment on `∷-⟪⟫↑` calls index-inertness:

> "the goal's type has already been normalised by the type-level `beta-fold-ˢᴿ` from
> `(α &ˢ η) [ wkᴿ ]ᴿ` to `α &ˢ (η ⨟ˢ ⟨ wkᴿ ⟩)`, so the registered `⟦⟧-ren` no longer
> matches it"

The author documented this at the *proof* level and worked around it by hand. It also
blocks *confluence*, which the file never got far enough to discover.

### What the record design does buy — measured

`⟦⟧-ren` vs `compositionalityᴿᴿ` does **not** appear among the failures, and neither does
any pure-renaming composition pair. Bundling `syn` as a field means two environments with
definitionally equal `syn` and `sem` are themselves definitionally equal, so the renaming
composition laws hold by computation. The failures are confined to exactly the places
where the type-level rule set is **asymmetric** — the `ˢᴿ`, `ˢˢ` and `beta-fold`
directions. That is a real and non-obvious benefit of the design, and it is why layer (i)
fails with 7 pairs rather than the ~27 that the analogous unbundled layer-(ii)
formulation produced at the comparable stage.

---

## 3. State of the port

`esop27/SystemF-canonicity.agda` is banner-marked and **does not typecheck** (exit 42).
Ported: everything up to and including the logical relation, its candidate conditions,
and all four layer-(i) pragmas. Still broken: the λ- and Λ-cases of `fundamental`. Under
full β those need the double induction of `SystemF-strat` §16 (`⟦⟧-β-λ`) together with a
substitution-congruence lemma (`sub-⟶*`: `a ⟶ a′ → b [ a ] ⟶* b [ a′ ]`) that the
prototype does not contain, because its object language had neither `ξ-λ` nor `ξ-·₂`.

This is a port cost, not a defect of the prototype: full β genuinely changes the proof.

---

## 4. Task 2 — porting the record to the stratified setting

**Attempt (a), "index the record by the level": rejected.** Measured in
`EnvRecordProbe.agda`:

```agda
record EnvR (Δ : LCtx) : Set (maxL Δ) where
  field syn : Sub Δ ∅
        sem : ∀ {l} (α : Δ ∋ˡ l) → Pred (α &ˢ syn)
```
```
error: [ConstructorDoesNotFitInData]
Constructor EnvR.constructor of inferred sort Setω
does not fit into record type of sort Set (maxL Δ).
(Reason: Setω is not less or equal than Set (maxL Δ))
```

This is precisely the objection recorded at `SystemF-strat.agda:815`. Moving the level to
a parameter does not rescue it: a single environment for `Δ` must supply a predicate at
*every* level occurring in `Δ`, so the level cannot be lifted out. The `sem` field's Π
over `Level` is unavoidable, and it lands in `Setω`.

**Attempt (b), "recursive function with a `no-eta-equality` carrier": not separately built
for layer (i); assessed as unable to deliver the record's benefit.** Stated precisely, so
the epistemic status is not overclaimed:

* **Measured** (in layer (ii), `REPORT-adequacy.md` §6, rounds 3c onward): a
  `no-eta-equality` + `pattern` carrier does typecheck, and does remove the η-caused
  critical pairs — 3 → 1 in the isolated setting.
* **Not measured**: a layer-(i) environment built this way. No such file was constructed.
* **Reasoned**: it cannot reproduce the prototype's leverage. That leverage comes from
  `syn` being a **field** of one bundled object, which is what makes every law
  `Env-ext λ α → refl` and, per §2, what makes the pure-renaming composition pairs vanish.
  An environment defined by recursion on `Δ` has no such field — `SystemF-strat`'s
  `Env Δ η` carries the substitution as an *index* instead — so its laws are inductions
  on `Δ`, exactly as the layer-(ii) `⊛ᵀ-*` lemmas turned out to be. Design (b) is
  therefore the one strat already uses, and adopting it is not a port of the prototype but
  a return to the status quo.

Per the agreed scope, no third variation was attempted.

**Conclusion for Task 2: the record design does not port.** Not for want of a trick — the
obstruction is that `Pred` is level-indexed and one environment must serve all levels.

---

## 5. Task 3 — the A/B

Task 3 was conditional on layer (i) closing in the stratified setting. It does not close
even in the prototype's own impredicative, non-stratified setting (7 pairs, §2), and the
record design does not reach the stratified setting at all (§4). **No A/B was measured,
and `SystemF-adequacy.agda` was not modified.**

---

## 6. What this changes

The premise that "layer (i) is where a working prototype already exists" is not borne out.
Measured, layer (i) fails in the *same two ways* as layer (ii):

| failure mode | layer (i) | layer (ii) |
|---|---|---|
| projection/η competing with a whole-object rewrite | 3 pairs (Family A) | measured as `.proj₁`/`.proj₂` pairs; fixed by `no-eta-equality` |
| interpretation rule vs `compositionalityˢᴿ`/`ˢˢ`/`beta-fold` | 4 pairs (Family B) | the same pairs, P3/P4/P9/P10 |

Both families have known closers from the layer-(ii) work — `opaque` on the environment
operations for A, and semantic associativity plus a refolded lookup rule for B. Neither
was applied here; that would be a fresh completion campaign of the kind
`REPORT-adequacy.md` §6 documents, and it was not started.

The one genuinely new and positive finding is in §2: **bundling the substitution as a
record field makes the pure-renaming composition laws hold definitionally**, which removes
a whole family of critical pairs that the unbundled formulation has to close by hand. That
is worth carrying into any future attempt, in whatever form survives the level problem.

---

## 7. Files

| file | status |
|---|---|
| `SystemF-canonicity.agda` | incomplete port, banner-marked, exit 42 |
| `SystemF-canonicity-core.agda` | probe, exit 42 — 102 pairs, all layer 0 |
| `SystemF-canonicity-layer1.agda` | probe, exit 42 — **7 pairs, layer (i)**; the decisive measurement |
| `EnvRecordProbe.agda` | probe, exit 42 — Task 2(a) rejected by the universe check |

All four carry a banner stating that they are probes, that they are expected to fail, their
measured result, and that nothing imports them. `--local-confluence-check` is on in all of
them. No holes and no postulates were introduced; `--type-in-type` is present in the three
canonicity files because the prototype's reducibility argument is impredicative, and is
local to those modules.
