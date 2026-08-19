# Reproducing Saffrich–Thiemann–Weidner's adequacy proof on a rewrite-based σ-calculus

This report is self-contained. It describes what was built, how it compares
like-for-like against the original development, an experiment that was attempted and
not completed, and every claim made along the way that turned out to be wrong.

---

## 0. Deliverables and exit status

| file | lines | `agda <file>` | clean-build wall clock |
|---|---:|---|---|
| `SystemF-adequacy.agda` | 840 (506 non-comment) | **exit 0** | **71.3 s** (from scratch, incl. `SystemF-strat`) |
| `SystemF-binary.agda` | 630 | **exit 0** | (see file; unrelated parametricity development) |
| `SemRewriteProbe{M,O,O2,N,E,G,H,I,J,K}.agda` | — | **exit 42, by design** | 10 measurement probes, §6 |

Options throughout: `--rewriting --local-confluence-check`. The confluence check was
never disabled or weakened.

`SystemF-adequacy.agda`: **no holes, no postulates** beyond `fun-ext`, which is inherited
from `SystemF-strat.agda` (that file's only postulate). No `--type-in-type`, no
`{-# TERMINATING #-}`, no `trustMe`.

No pre-existing file was modified. `SystemF-strat.agda`, `SystemF.agda`, `STLC.agda`,
`main.tex`, `runagdatex` are byte-identical to their state before this work.

The ten probe files are measurement artifacts. Each carries a banner saying it is
expected to fail, its measured critical-pair count, and that nothing imports it. They
exist so that §6 is reproducible.

---

## 1. What was built and proved

The reference is Hannes Saffrich, Peter Thiemann and Marius Weidner, *"Intrinsically
Typed Syntax, a Logical Relation, and the Scourge of the Transfer Lemma"*, TyDe 2024,
doi:10.1145/3678000.3678201, artifact at <https://github.com/proglang/SystemF>
(`src/StratF/`). Their construction — not a parametricity variant — was reproduced on
top of the rewrite-based σ-calculus of `SystemF-strat.agda`:

* **big-step CBV** `_⇓_ : CExpr T → CValue T → Set`, with `isValue`, `CValue`, `Value-⇓`.
  This had to be *added*: `SystemF-strat` has full β-reduction, not big-step CBV.
* **tagless denotational semantics** `⟦_⟧ᵀ : Type Δ l → Env* Δ → Set l` and
  `E⟦_⟧ : Expr Γ T → (η : Env* Δ) → Envᵥ Γ η → ⟦ T ⟧ᵀ η`.
* **their logical relation**, `REL {l} T = CValue T → ⟦ T ⟧ᵀ [] → Set l`, verbatim; then
  `𝓥⟦_⟧`, `𝓔⟦_⟧`, `𝓖⟦_⟧`, `CSub`, `Csub`, `Cextend`, `Cdrop-t`, `Cextt`.
* **`𝓥⟦⟧-ren` / `𝓥⟦⟧-sub`** — their `LRVren-eq′` / `LRVsub`.
* **`semantic-soundness`** — their `fundamental`.
* **`adequacy`**:
  ```agda
  adequacy : ∀ (e : CExpr 𝔹) (b : Bool) → E⟦ e ⟧ [] tt ≡ lift b → e ⇓ 𝔹val b
  ```
  plus a `canonicity-⇓` corollary: every closed boolean expression evaluates to a literal.

### Declared deviations from the original

| id | deviation | why | attributed to |
|---|---|---|---|
| D1 | `𝓥⟦ T ⟧ ρ` relates `CValue (T [ η ]ˢ)` to `⟦ T [ η ]ˢ ⟧ᵀ []`; theirs relates `CValue (Tsub (π₁ ρ) T)` to `⟦ T ⟧ (⟦ π₁ ρ ⟧* [])` | the substituted-type form is what the σ-rewrites normalise | **reformulation** — quantified in §3 |
| D2 | base type is `base l` (booleans at level 0); theirs is `ℕ` | strat's object language | object language |
| D3 | `𝓓⟦ Δ ⟧ : Sub Δ ∅ → Set (maxL Δ)` by recursion; theirs is `Setω` | avoids `Setω` equality | `Setω` handling |
| D4 | base clause is "u's denotation is z", not "u is a literal denoting z" | `base l` at `l ≠ 0` has no literals, so the latter is not uniform in `l` | object language |
| D5 | `Envᵥ Γ η : Set (maxC Γ)` by recursion on Γ; theirs is `Setω` | avoids `Setω` equality | `Setω` handling |

Only D1 touches the subject of the comparison. §3 quantifies exactly what it buys and
what it costs.

---

## 2. Module-for-module correspondence

STW line counts are from their artifact; "live" means reachable from
`StratF/Everything.agda` (9725 lines across 33 modules; a further 1163 lines are dead:
`Util/SubstPropertiesHeq.agda` 817, `Misc/SubstExamples.agda` 346).

| THEIR module | lines | OUR section | lines |
|---|---:|---|---:|
| `Types.agda` (`Env*`, `⟦_⟧`) | 63 | §A2 | 22 |
| `TypeSubstitution.agda` | 104 | — | 0 |
| `TypeSubstProperties.agda` | 314 | — | 0 |
| `TypeSubstPropertiesSem.agda` | 146 | §A3 | 91 |
| `Expressions.agda` (`Env`, `E⟦_⟧`) | 89 | §A4 | 46 |
| `ExprSubstitution.agda` | 147 | — | 0 |
| `ExprSubstProperties.agda` | 659 | — | 0 |
| `ExprSubstPropertiesSem.agda` | 435 | — | 0 |
| `ExprSubstFusion.agda` + `ExprSubstFusion/*` | 1300 | — | 0 |
| `Util/SubstProperties.agda` | 398 | §A7 coercion helpers | 40 |
| `Util/PropositionalSetOmegaEquality.agda` | 128 | — | 0 |
| `Util/HeterogeneousSetOmegaEquality.agda` | 128 | — | 0 |
| `Util/HeterogeneousEqualityLemmas.agda` | 67 | — | 0 |
| `Util/Extensionality.agda` | 53 | — | 0 |
| `Evaluation.agda` + `BigStep.agda` | 97 | §A1 | 52 |
| `SmallStep*`, `BigSmallEq`, `BigStepSoundness` | 267 | — | 0 |
| `LogicalPrelim.agda` | 215 | §A5 top + §A7 | 76 |
| `Logical.agda` | 100 | §A5 + §A7 (`𝓖⟦_⟧`) | 60 |
| `LogicalVariation.agda` | 75 | — | 0 |
| **`LRVren.agda`** | **2013** | **§A6, renaming half** | **≈45** |
| **`LRVsub.agda`** | **2296** | **§A6, substitution half** | **≈50** |
| `Fundamental.agda` | 607 | §A8 + §A9 | 168 |
| **live total** | **9725** | | **840 (506 non-comment)** |

The bottom-line ratio is **not** a like-for-like figure: roughly 2900 of their lines are
the substitution infrastructure that this development *imports* from `SystemF-strat.agda`
(1786 lines, itself doing considerably more than adequacy needs). The defensible
comparison is per-module, and above all the two `LRV*` rows, which §3 treats properly.

---

## 3. `LRVren` / `LRVsub`: the headline, and the attribution

### Their statements, from the artifact

`LRVren.agda:31–40`:

```agda
LRVren-eq′ :
  ∀ (T : Type Δ₁ l) (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) →
  let ρ* = π₁ ρ in  (v : Value (Tsub (τ* ∘ᵣₛ ρ*) T)) →
                    (z : ⟦ T ⟧ (⟦ π₁ (Tren-act τ* ρ) ⟧* [])) →
  let S = subst₂  (λ vv zz → Value vv → zz → Set l)
                  (fusion-Tsub-Tren T τ* ρ*)                       -- SYNTACTIC
                  (Tren*-preserves-semantics … T) in               -- SEMANTIC
  𝓥⟦ T ⟧ (Tren-act τ* ρ) v z ≡ S (𝓥⟦ Tren τ* T ⟧ ρ) v z
```

`LRVsub.agda:134–153` carries a `subst Value (sym (fusion-Tsub-Tsub …))` and a
`subst id (sym (…))` whose proof is an `≡-Reasoning` chain containing `congωl` — a
`Setω`-eliminating congruence — **inlined into the type signature**.

### Ours

```agda
𝓥⟦⟧-ren : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η : Sub Δ₂ ∅) (ρ : 𝓓⟦ Δ₂ ⟧ η) →
          𝓥⟦ T [ ζ ]ᴿ ⟧ ρ ≡ 𝓥⟦ T ⟧ (⊛𝓓 ζ η ρ)

𝓥⟦⟧-sub : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (σ : Sub Δ₁ Δ₂) (κ : Sub Δ₂ ∅) (ρ : 𝓓⟦ Δ₂ ⟧ κ) →
          𝓥⟦ T [ σ ]ˢ ⟧ {κ} ρ ≡ 𝓥⟦ T ⟧ (⊙𝓓 σ κ ρ)
```

**The statements are plain `_≡_` between two applications of `𝓥⟦_⟧`: no `subst`, no
`subst₂`, no `congωl`, no reasoning chain in the type.** The two declarations together
with their supporting `⊛𝓓`/`⊙𝓓` lemmas occupy **95 lines** (lines 399–493) and contain
**2 `subst`s in the proofs** — the same `subst id (sym (⟦⟧ᵀ-single …))` in each `∀`-case,
carried through the `cong` motive. `subst₂` and `congωl` are 0.

### The attribution split

Their `subst₂` transports along two coherences, and the two vanish for different reasons.
This distinction is the substance of the comparison:

| half of their `subst₂` | why it vanishes here | credit |
|---|---|---|
| `fusion-Tsub-Tren` / `fusion-Tsub-Tsub` (the **value** index) | `(T [ ζ ]ᴿ) [ η ]ˢ ≡ T [ ⟨ ζ ⟩ ⨟ˢ η ]ˢ` and `(T [ σ ]ˢ) [ κ ]ˢ ≡ T [ σ ⨟ˢ κ ]ˢ` are registered σ-rewrites, hence definitional | **the rewrite-based σ-calculus** |
| `Tren*-preserves-semantics` / the `congωl` chain (the **denotation** index) | the denotation side is `⟦ T [ η ]ˢ ⟧ᵀ []`, not `⟦ T ⟧ᵀ (envOf η)` (deviation **D1**), so both sides are the same type by the same σ-rewrites | **D1, a reformulation** |

**The rewrite system removes the syntactic half outright. The semantic half is removed by
a change of formulation whose cost is relocated, not eliminated** — it reappears as one
`coeᵀ` (= `subst id (sym (⟦⟧ᵀ-closing …))`) in the statements of `semantic-soundness` and
`𝓖-lookup`.

---

## 4. Transport counts

Counts over non-comment lines. `subst` totals count every occurrence of the string,
including `subst₂`, `substᴮ`, `subst-sym-subst`, `subst-subst-sym`.

| | STW `LRVren` + `LRVsub` | ours (whole file) |
|---|---:|---:|
| lines | 4309 | 840 (506 non-comment) |
| all occurrences of `subst` | 689 | **56** |
| …of which the bare token `subst` | — | 46 |
| `subst₂` | 24 | **3** |
| `cong` family | 704 (incl. 130 `congωl`/`conglω`/`congωω`) | **40** |
| `trans` | 345 (incl. 15 `transω`) | **20** |
| `≡ω` | 2 | **0** |
| heterogeneous `≅` | 0 live | **0** |
| postulates (whole development) | 5 (`fun-ext`, `fun-extω`, `fun-extω₂`, `fun-ext-llω-ω`, `relenv-ext`) | **1**, inherited (`fun-ext`) |

### Transports appearing in a lemma's STATEMENT

**Theirs — 5 declarations:** `LRVren-eq′` (`subst₂`), `LRVren-eq` (`subst₂`), `LRVwk-eq`
(`subst` ×2), `Cdrop-t-Cextt≡id` (`subst`), `LRVsub` (`subst` ×2 + inlined `congωl`
chain). Plus `Gdrop-t-ext≡id` and `Tsub-act-REext` stated with `≡ω`.

**Ours — 2 declarations**, both carrying the same single `coeᵀ`: `𝓖-lookup` and
`semantic-soundness`.

| theirs | ours | transport in statement? |
|---|---|---|
| `LRVren-eq′`, `LRVren-eq` | `𝓥⟦⟧-ren` | **none** |
| `LRVsub` | `𝓥⟦⟧-sub` | **none** |
| `LRVwk-eq` | `𝓥⟦⟧-weaken` | **none** |
| `Cdrop-t-Cextt≡id` | — (holds by η: `Cdrop-t (T′ ∙ˢ η) (Cextt η T′ χ)` *is* `χ`) | n/a |
| `Gdrop-t-ext≡id` (`≡ω`) | — (`Gdrop-t` is the identity, by D5) | n/a |
| `𝓖-lookup` | `𝓖-lookup` | `coeᵀ` (D1) |
| `Γ ⊨ e ⦂ T` | `semantic-soundness` | `coeᵀ` (D1) |

### What forces each of our 56 `subst` occurrences

| cause | count |
|---|---:|
| `coeᵀ`/`coeᵀ⁻` — the `⟦ T [ η ]ˢ ⟧ᵀ [] ↔ ⟦ T ⟧ᵀ (envOf η)` interface (D1) | 25 |
| `⟦⟧ᵀ-single` in `E⟦ e ·* T′ ⟧` and in `𝓥⟦ ∀α T ⟧` | 2 |
| `⟦⟧ᵀ-ren` in `lookupᵥ`'s `suc*` clause | 1 |
| `uip`-based coherence (`coe¹ coe² coe³`) | 11 |
| `𝓥⟦⟧-weaken` / `𝓥⟦⟧-[]*` rewriting the relation itself | 3 |
| `value-ƛ` / `value-Λ` canonical-forms transports in `⇓-·` / `⇓-∙` | 4 |
| `subst₂`/`substᴮ`/`subst-*-subst` variants, and 2 occurrences inside comments | 10 |

**Every transport in this file is on the denotational side. Not one is caused by type or
expression substitution.** That is the sharpest statement of what the method buys.

---

## 5. Their reported pain points, scored

| STW pain point | verdict | evidence |
|---|---|---|
| the "scourge" — `subst` in the *statement* of lemmas about the logical relation | **removed** for the syntactic half; the semantic half is **relocated** | `𝓥⟦⟧-ren`/`𝓥⟦⟧-sub`/`𝓥⟦⟧-weaken` statements are transport-free; the semantic coherence reappears as one `coeᵀ` in two places |
| `Esub` fusion, the type-application case | **removed** | strat's `Compositionalityˢˢ` is a 6-line transport-free induction; we import it and never state a fusion lemma |
| `RE-ext∘lift` / `lemma1` — `subst CValue` inside the definition of `𝓥⟦ ∀α ⟧` | **removed** | `(T [ η ↑ˢ ]ˢ) [ T′ ]* ≡ T [ T′ ∙ˢ η ]ˢ` is definitional |
| `subst-var-preserves` — `subst id` inside `𝓥⟦ ` α ⟧` | **removed** | our variable clause is `π₂ α η ρ v z` |
| `Cdrop-t`, `Cextt` carry `subst CValue (…)` | **removed** | both are plain projections here |
| `Cextt-Eextₛ-l` — needs `dist-subst'` and a 3-deep `trans` chain | **removed** | ours is `fun-ext … λ { (suc* x) → refl }` |
| `Cdrop-t-Cextt≡id` — stated with a `subst` | **removed** | holds by η-equality of functions |
| `Setω` handling — 2 utility modules (256 lines) and 4 extensionality/`relenv` postulates | **removed, but by D3/D5, not by rewriting** | making `𝓓⟦_⟧` and `Envᵥ` level-computing recursive functions removes every `≡ω`; 0 `≡ω`, 0 `Setω` postulates |
| `Tren*-preserves-semantics` / `Tsingle-subst-preserves` — the denotational transfer lemmas | **not helped** | `⟦_⟧ᵀ` is a semantic function; strat's rule set says nothing about it, so §A3 is a genuine 91-line induction. §6 is the attempt to change that |

### Attribution summary

| difference | attributable to |
|---|---|
| all syntactic transports gone | **the rewrite-based σ-calculus** |
| `𝓥⟦⟧-ren`/`𝓥⟦⟧-sub` statements transport-free | **half rewriting, half D1** |
| no `≡ω`, no `Setω` postulates; `Gdrop-t` and `Cdrop-t-Cextt≡id` vanish | **D3/D5**, orthogonal to substitution |
| adequacy for booleans not numerals | **object language (D2/D4)** |
| big-step CBV had to be added (52 lines) | a **cost**, not a saving |

---

## 6. The semantic-REWRITE experiment

**Question.** The σ-calculus-as-`REWRITE` method removes every *syntactic* transport.
Can the *denotational* laws — how `⟦_⟧ᵀ` interacts with type substitution — also be
registered, so that the 25 `coeᵀ` uses and the `uip`/`coe¹²³` coherence block disappear?

**Answer: not established.** Eleven measured rounds got a 21-rule semantic σ-calculus to
8 non-joinable critical pairs, with each residual naming the rule that would close it.
The work was stopped there. `SystemF-adequacy-rw.agda` does not exist.

### 6.1 Method

Rounds 1–5 varied whole configurations and read only a total pair count. That is a poor
instrument: the total conceals which pairs died and which appeared, so it cannot
distinguish progress from regress. Those rounds are retained only where they carry
distinct evidence:

| round | file | configuration | pairs |
|---|---|---|---:|
| 1 | — (superseded, not retained) | `Env*` in `Setω`; single-variable law only | 4 |
| 2 | `SemRewriteProbeM` | `Env*` a real `Set`; operations transparent | 2 + 1 `RewriteLHSReduces` |
| 3 | `SemRewriteProbeO` | `⊛ᵀ` `opaque`; record η on | 7 |
| 3b | `SemRewriteProbeO2` | + `lookupᵀ` opaque; isolated | 3 |
| 3c | `SemRewriteProbeN` | 3b + `no-eta-equality` | **1** |
| 3e | `SemRewriteProbeE` | no-eta + λσ⇑ orientation | 4 |
| 5 | `SemRewriteProbeH` | outward orientation | 6, and `probe-weaken` fails |

Two further intermediate configurations (a full rule set with unfold-oriented composition,
and a variant adding `⊛ᵀ-wk₀`) were measured at 9 and 5 pairs respectively; their probes
are not retained, being superseded by rounds 6–7, which measure the same rules under the
fixed configuration.

Rounds 6–7 used a better one. Fix the configuration — **inward** orientation
(`⟦ T [ ζ ]ᴿ ⟧ᵀ η ↦ ⟦ T ⟧ᵀ (⊛ᵀ ζ η)`), which is the orientation that makes weakening,
single-substitution and closing definitional, i.e. the one that actually deletes
coercions. Then enumerate the residual pairs individually, and for each, find the rule
that closes the corresponding overlap in strat's syntactic set — it is already there,
since strat is confluent — and construct its semantic analogue.

Setup common to rounds 3c onward: the environment carrier is a `no-eta-equality` record
with the `pattern` directive (`pattern` is required: disabling η also disables pattern
matching on the record by default). The carrier is *parameterised*, not indexed, so its
sort still computes and no inductive family is needed. Operations `ext`, `lookupᵀ`, `⊛ᵀ`,
`⊙ᵀ` are `opaque`, exactly as strat wraps its syntactic maps.

### 6.2 Trajectory under the fixed configuration

| round | file | rules | pairs |
|---|---|---:|---:|
| 4 | `SemRewriteProbeG` | 14 | **9** |
| 6 | `SemRewriteProbeI` | 16 | **27** |
| 7 | `SemRewriteProbeJ` | 21 | **8** |

Round 6's rise to 27 is not regress: adding associativity exposes strat's whole `-⨟`
companion family at once. Round 7 supplied those companions: **27 → 8 in a single pass.**

### 6.3 The per-pair table

| # | pair | strat's closer | semantic analogue | resolved |
|---|---|---|---|---|
| P1 | `lkp-lift-ext` vs `` `beta-lift-fusion `` | `` `associativity `` | `⊛ᵀ-assoc` | yes |
| P2 | `⟦⟧ᵀ-ren` vs `compositionalityᴿᴿ` | `` `associativity `` | `⊛ᵀ-assoc` | yes |
| P3 | `⟦⟧ᵀ-ren` vs `compositionalityˢᴿ` | `associativity` + `coincidence` | `⊙ᵀ-assoc` + `⊙ᵀ-⟨⟩` | yes |
| P4 | `⟦⟧ᵀ-ren` vs `beta-fold-ˢᴿ` | `beta-fold` (fold, not push) | reorient `lkp-⊙` to fold | yes |
| P5 | `lkp-⊙` vs `lkp-⊛` (undecidable overlap) | — | dissolves once `lkp-⊙` folds | yes |
| P6 | `lkp-lift-ext-ˢ` vs `beta-lift-ren-↑` | `associativity` + `coincidence` | `⊙ᵀ-assoc` + `⊙ᵀ-⟨⟩` | yes |
| P7 | `lkp-lift-ext-ˢ` vs `beta-lift-suc` | `interact` | `⊛ᵀ-interact` | yes |
| P8 | `⟦⟧ᵀ-sub` vs `compositionalityᴿˢ` | `associativity` | `⊙ᵀ-assoc` | yes |
| P9 | `⟦⟧ᵀ-sub` vs `compositionalityˢˢ` | `associativity` | `⊙ᵀ-assoc` | yes |
| P10 | `⟦⟧ᵀ-sub` vs `beta-fold` | `beta-fold` | `⊙ᵀ-assoc` + folded `lkp-⊙` | yes |
| P11 | `probe-single` did not fire | `distributivity` | `⊙ᵀ-cons` | yes |
| P12 | `⊛ᵀ-assoc` vs `` `interact ``, `` `interact-⨟ `` | `` `interact `` | `⊛ᵀ-cons` — **rejected**, see §6.5 | no |
| P13 | `⊛ᵀ-assoc` vs `` `lift-wk ``, `` `lift-wk-⨟ `` | `` `lift-wk `` | `⊛ᵀ-lift-wk` | yes |
| P14 | `⊛ᵀ-assoc` vs `` `lift-fusion ``, `` -⨟ `` | `` `lift-fusion `` | `⊛ᵀ-lift-fusion` | yes |
| P15 | `lkp-⊙` vs `beta-lift-{zero,suc}` and `-⨟` forms | those rules | `⊙ᵀ-lift-{zero,suc}` | yes |
| P16 | `lkp-⊙` vs `beta-lift-ren-↑` | that rule | `⊙ᵀ-lift-ren` | yes |

15 of 16 resolved. The residuals after round 7:

| # | residual pair | named closer, not yet written |
|---|---|---|
| R1 | `lkp-⊛` vs `⊛ᵀ-cons` | replace `⊛ᵀ-cons` with the shape-specific `⊛ᵀ wkᴿ (⊛ᵀ (α ∙ᴿ ζ) η) ≡ ⊛ᵀ ζ η` |
| R2–R8 | `⊙ᵀ-assoc` vs `⟨⟩-lift-SR-⨟`, `⟨⟩-lift-SR-comp`, `⟨⟩-lift-RS…` | semantic mirrors of strat's mixed `⟨⟩-lift-*` family (≈10 rules) |

**No residual pair lacks a syntactic counterpart to copy.** The stopping condition — "a
pair with demonstrably no syntactic counterpart" — was never reached. Work stopped for
budget reasons, not because the method ran out.

### 6.4 Why no proper subset works

A weaker goal was tried: register the largest *subset* of the semantic laws that is
confluent and still shortens the proof. The result is that **no such subset exists.**

The minimal payoff-bearing rule is `⟦⟧ᵀ-wk : ⟦ weaken T ⟧ᵀ (A ∷ η) ↦ ⟦ T ⟧ᵀ η`, the
semantic mirror of `interact`, chosen because it is the smallest rule that deletes any
coercion at all. Measured alone (`SemRewriteProbeK.agda`): **4 non-joinable pairs**,
against `compositionalityᴿᴿ`, `compositionalityˢᴿ`, `beta-fold-ˢᴿ` and `_[_]ᴿ`-clause3.

The reason generalises to the whole family. Any semantic law that deletes a coercion must
mention `⟦ T [ ζ ]ᴿ ⟧ᵀ …` or `⟦ T [ σ ]ˢ ⟧ᵀ …` on its left-hand side — that is, must
carry a **computed argument** — and every such left-hand side overlaps strat's
composition and traversal rules. Conversely, the semantic rules that *are* confluent in
isolation (`lkp-ext-zero`, `lkp-ext-suc`, the `ext`/`lookupᵀ` laws) mention no type
substitution and therefore delete nothing.

| candidate subset | confluent | coercions removed |
|---|---|---:|
| `{}` | yes | 0 |
| `{lkp-ext-zero, lkp-ext-suc}` | yes | **0** |
| `{⟦⟧ᵀ-wk}` | **no** — 4 pairs | (would be ≈5) |
| `{⟦⟧ᵀ-single}` | **no** — 4 pairs | (would be 2) |
| full 21-rule set | **no** — 8 pairs | (would be ≈50) |

**The semantic laws form one connected component under critical-pair closure.** They are
all-or-nothing: there is no useful proper subset. This is a sharper result than "the full
set was not closed", and it is why the fallback was abandoned rather than shipped.

### 6.5 `⊛ᵀ-cons`, and why its failure is evidence *for* the discipline

Every closer in §6.3 is strat's own rule transplanted one layer up — not a new
device. The one member that *broke* confluence, `⊛ᵀ-cons` (the semantic image of renaming
`distributivity`, `⊛ᵀ (α ∙ᴿ ζ) η ≡ ext (lookupᵀ α η) (⊛ᵀ ζ η)`), broke it precisely
because **strat deliberately does not register syntactic renaming `distributivity`**: it
is proved in `SystemF-strat.agda` §4 but is absent from the `{-# REWRITE #-}` block.

Copying strat's rule set faithfully means copying its *omissions* as well as its
inclusions. A discipline that predicts which rules must be left out is a principled one;
ad-hoc patching would not have flagged `⊛ᵀ-cons` as suspect in advance, and would not
explain why the shape-specific interaction rule (R1) is the right replacement.

Two further observations support the same reading. The orientation that is
confluence-friendly (outward, matching strat's fold discipline) was measured in
`SemRewriteProbeH.agda` to be the one that **cannot serve the development**: its
`probe-weaken` fails, so weakening is not definitional. And strat's own set is not
uniform either — it pushes at the variable for renamings, folds for substitutions, and
carries shape-specific interaction rules. Mixed shapes are the norm, not a symptom.

### 6.6 The one asymmetry between the layers

The semantic layer has an interpreter above it that the syntactic layer does not:
`⟦_⟧ᵀ` pattern-matches on the type. Consequently a semantic law's left-hand side either
carries a computed argument (inward) or overlaps the interpreter's own defining clauses
(outward). strat's syntactic maps have no such interpreter to contend with. This is why
the rule counts do not correspond one-to-one, and why "mirror strat" is the right
instinct but not a complete recipe.

---

## 7. Corrections and retractions

Every claim made during this work that turned out to be wrong, in one place.

1. **"The type-application case of expression-substitution fusion carries eight nested
   `subst`s."** Repeated from the paper without checking. That code is
   `StratF/Misc/SubstExamples.agda:255–288`, a file whose own header says it is *"only
   used to generate examples for the paper, and is not part of the actual
   formalization"*. It is unimported and **does not typecheck** — it contains
   `E₈ = {!!}`, `p₂ = {!!}`, `p₃ = {!!}` and a `{!!}` catch-all. The substs are eight in
   *number*, maximum nesting depth **three**. The live proof,
   `ExprSubstFusion/SubSub.agda:220–243`, is stated in heterogeneous equality with
   **3 substs at depth 1**. Honest form: *homogeneous formulation → 8 substs, depth 3,
   never closed; heterogeneous formulation → 3 substs, depth 1, closed.*

2. **"LRVren/LRVsub are ≈30× ours."** The 4309 figure is right but the ratio was not
   like-for-like: it compared their syntax×denotation relation against a syntax×syntax
   one from a different development. Replaced by §2–§4.

3. **"Our `𝓥⟦⟧-ren`/`𝓥⟦⟧-sub` region is ≈125 lines with no `subst`."** Wrong on both
   counts. It is **95 lines** and contains **4 occurrences of the string `subst`**, of
   which two are in comments — one of them literally the words "NO subst", which is how
   the grep was fooled — and **two are code**. The defensible claim, made in §3, is that
   the *statements* are transport-free with 0 `subst₂` and 0 `congωl`.

4. **"Total `subst` in the file is 46."** 46 is the bare token; **56** is the count of all
   occurrences. 56 is the figure quoted in §4.

5. **"The semantic layer is structurally closed to rewriting — Agda's record η makes it
   impossible."** Wrong. `no-eta-equality` (with `pattern`) disables exactly that η rule,
   and removes exactly the pairs η caused: **3 → 1** in the isolated setting
   (`SemRewriteProbeO2` → `SemRewriteProbeN`). The carrier being parameterised rather
   than indexed also disposes of the accompanying "the sort depends on the index"
   objection. What survives of that account is only the mechanism — `--rewriting` matches
   up to η, cf. Agda issue [#5961](https://github.com/agda/agda/issues/5961) — which
   explained 2 of 3 pairs, not impossibility.

6. **"Round 1 showed `⟦⟧ᵀ-wk` registers confluently."** Wrong, and caught only by
   building the fallback. Round 1 registered `⟦⟧ᵀ-wk` and `⟦⟧ᵀ-single` in one pragma and
   Agda attributed all 4 errors to `⟦⟧ᵀ-single`; that was misread as the first rule
   passing. Measured alone, `⟦⟧ᵀ-wk` has **4 non-joinable pairs** (§6.4).

7. **Method error, not a factual one.** Rounds 1–5 varied whole configurations and tracked
   a total pair count. That is a random walk over configurations and cannot distinguish
   progress from regress. Rounds 6–7 fixed the configuration and closed pairs
   individually; the same effort then produced 27 → 8 in one pass.

---

## 8. Open / not done

* **`SystemF-adequacy-rw.agda` was not built.** No variant of the development with
  semantic rewrite rules typechecks. The file is not present in the directory; the
  attempt is preserved as `SemRewriteProbeK.agda`, which fails.
* **The A/B is unmeasured.** No numbers are reported for it. For the record, a successful
  build would have deleted `coeᵀ` (21 uses), `coeᵀ⁻` (4), `coeᵀ-inv`, `coeᵀ-idˢ`, `uip`
  (5), `coe¹` (3), `coe²` (5), `coe³` (3), `coe-⇒` (4), `coe-Π` (4), `substᴮ` (3), `dapp`
  (3) — essentially all of §A7 — and would have added a `no-eta-equality` carrier, ≈90
  lines of semantic σ-calculus replacing §A3's 91, and the η-lemmas. Of the additions,
  exactly two were measured: `⊛ᵀ-wk₀` and `⊛ᵀ-id` require explicit pattern matching once
  pair-η is gone. **Whether the deletions outweigh the additions is unmeasured.**
* **8 residual critical pairs**, listed as R1–R8 in §6.3, each with its named closer.
  None is blocking.
* **The denotational transfer lemmas remain ordinary lemmas.** §A3 is 91 lines of genuine
  induction, and `⟦⟧ᵀ-single`, `⟦⟧ᵀ-ren`, `⟦⟧ᵀ-closing` are applied explicitly.

---

## 9. Verdict

1. **STW's adequacy theorem reproduces on the rewrite-based σ-calculus**, in 840 lines,
   exit 0, no holes, no new postulates, with `--local-confluence-check` on throughout.
2. **`LRVren.agda` (2013) + `LRVsub.agda` (2296) become 95 lines with 2 `subst`s**, and —
   the claim that matters — the *statements* of `𝓥⟦⟧-ren`, `𝓥⟦⟧-sub` and `𝓥⟦⟧-weaken`
   are transport-free where all three of their counterparts are not. Half of that saving
   is the σ-rewrites; half is deviation D1, whose cost is relocated to one `coeᵀ` in two
   statements rather than eliminated.
3. **All 56 `subst` occurrences in the file are denotational.** Zero are caused by type or
   expression substitution.
4. **Several of their pain points are removed by something other than rewriting** — the
   entire `Setω`/`≡ω` apparatus (2 utility modules, 4 postulates) goes away because the
   environments are level-computing recursive functions, which is orthogonal to the
   substitution infrastructure and should be reported as such.
5. **Extending the method to the denotational layer is open.** It is not blocked: the
   discipline is principled (§6.5), the trajectory is 9 → 27 → 8 under a fixed
   configuration, and every residual names its closer. It is also not done, and no proper
   subset of the semantic laws is usable (§6.4), so there is no partial version to ship.
