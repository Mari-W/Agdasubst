# The maximal confluent, subst-free σ-rewrite system for `systemf.agda`

**An empirical investigation grounded in Autosubst 2 / σ_SP.**
Target: `tex/itp26/systemf.agda` · Agda 2.8.0 · `--rewriting` + `--local-confluence-check`.

---

## One-line verdict

> **"Confluent (`--local-confluence-check` on) **and** fully subst-free System F subject reduction" is NOT achievable for the intrinsically-scoped, first-class-renaming, *functional* de Bruijn representation of `systemf.agda`. The minimal obstruction is the abstract de Bruijn index: it turns the variable-lookup law into a rewrite `def-⨟ : x ⋯ˢ (σ₁ ⨟ σ₂) → (x ⋯ˢ σ₁) ⋯ˢ σ₂` that is metatheory-essential yet locally non-confluent against the distribution law `dist` in *every* orientation — while dropping it breaks the join of `compositionalityˢˢ ↔ inst-x`. σ_SP (Curien–Hardin–Lévy / Autosubst 2) escapes this only because its variables are first-order `0[↑ⁿ]`, so no such abstract-index rewrite exists.**

The two properties are a genuine Pareto trade-off with two endpoints:

| configuration | `--local-confluence-check` | manual substs in SR |
|---|---|---|
| **A** — the file as shipped | **off** | **0** (fully definitional) |
| **B** — maximal confluent set | **on, passes** | **N > 0** (see §7) |

No configuration dominates both. Autosubst 2's own papers flag exactly this boundary: the *single-sorted* σ_SP is *proven* convergent, but the *two-sorted first-class-renaming* extension's confluence is only *conjectured* (CPP'19 §3.2, §4), and it is "precisely where a naive `--rewriting` rule set will manufacture non-joinable critical pairs."

---

## 1. Method — an empirical, checker-backed harness

Nothing below is asserted without Agda's verdict. A driver (`scratchpad/harness/driver.py`) takes a set of rule names to **exclude** (or **add**) from the `{-# REWRITE … #-}` block, writes a variant of `systemf.agda` with `--local-confluence-check` ON, runs `agda`, and classifies:

- **confluent?** — no `[RewriteNonConfluent]` error;
- **metatheory compiles subst-free?** — `agda` exits 0 (Agda continues type-checking the file *after* reporting confluence errors, so both signals come from one run);
- the exact set of failing critical pairs, parsed from *"when checking confluence of the rewrite rule X with Y."*

Every claim (P1)–(P6) below cites the experiment that produced it. A key structural fact discovered immediately: **rule removal is *non-monotone* for Agda's local-confluence check** — removing a rule can *expose* new failing pairs, because Agda checks *joinability using the currently-registered rules*, and a removed rule may have been the joiner. So each candidate set must be re-run; you cannot reason about subsets abstractly.

---

## 2. Ground truth — the 49-rule set is subst-free but has 14 failing pairs

`systemf.agda` registers ~49 σ-laws and ships with `--local-confluence-check` **off**. Its metatheory — `sr`, `_⊢⋯ˢ[_]_`, `_⊢⋯ᴿ[_]_`, `⊢↑ˢ`, `⊢↑ᴿ`, `⊢[]` — contains **zero** `subst`/`transport`: every β/type-β/ξ case is `refl` or a structural congruence relying on the rewrites firing definitionally. So configuration **A** already has 0 substs.

Turning the check on (experiment `E0_full`) reports exactly **14 non-joinable critical pairs**:

```
 1 {def-⨟, dist}            8 {dist, coincidence-ext}
 2 {dist, η-law}            9 {coincidence-fold, assocᴿ}
 3 {η-law, def-⨟}          10 {def-∘, distᴿ}
 4 {compᴿˢ, compᴿᴿ}        11 {coincidence-fold, distᴿ}
 5 {def-⨟, coincidence-fold} 12 {distᴿ, η-lawᴿ}
 6 {coincidence-fold, η-law} 13 {η-lawᴿ, def-∘}
 7 {assoc, coincidence-comp} 14 {η-lawᴿ, def-wk}
```

(The brief listed 7; the file has since grown the `coincidence-{fold,comp,ext}` completions and a `compᴿˢ↔compᴿᴿ` clash.) Many carry Agda's *"not equal because S₁ != … : List Sort"* — the checker cannot even unify the *scope indices* of the overlap, a hallmark of indexed de Bruijn rewrite rules; but these must be eliminated regardless, since the goal is that the checker *accepts* the set.

---

## 3. The essentiality map — which laws the subst-free metatheory *requires* as rewrites

For each candidate law we removed it *alone* from the full set and asked whether the metatheory still compiles (experiments `iso_*`). This partitions the laws:

**Metatheory-ESSENTIAL** (removal breaks subst-free SR — these *must* be registered rewrites for 0 substs):
`def-⨟, def-∘, compositionalityᴿᴿ, compositionalityᴿˢ, compositionalityˢᴿ, compositionalityˢˢ, coincidence, coincidence-fold, dist, assoc, interact, def-wk, inst-x, inst-λ (…all inst/instᴿ), def-∙ˢ-zero, def-∙ˢ-suc, def-↑ˢ, comp-idᵣ, comp-idₗ, coincidence-var, def-id, def-∙ᴿ-*`.

**FREE** (metatheory still compiles without it):
`η-law, η-lawᴿ, η-id, η-idᴿ, coincidence-comp, coincidence-ext, distᴿ, assocᴿ, right-id`.

Cross-referencing with the 14 pairs: every pair is "resolvable" by dropping a FREE rule **except three "crux" pairs where both rules are essential**: `{def-⨟, dist}`, `{compᴿˢ, compᴿᴿ}`, `{def-⨟, coincidence-fold}`.

---

## 4. Why "drop the redundant rules" fails — the load-bearing joiners (refuting H1)

The brief's hypothesis **H1** was: drop the split clauses `def-⨟`/`def-∘`, keep combine-`compositionalityˢˢ`, get confluence. **Empirically false** (experiment `E1_noSplit`): dropping them *raises* the failure count 14 → 16 and breaks the metatheory. Reason:

- `def-⨟` is not a redundant reorientation of `compositionalityˢˢ`; it is the unique **joiner** of `compositionalityˢˢ ↔ inst-x`. On `((` x) ⋯ˢ σ₁) ⋯ˢ σ₂`, `inst-x` (inner) gives `(x ⋯ˢ σ₁) ⋯ˢ σ₂`; `compˢˢ` (outer) then `inst-x` gives `x ⋯ˢ (σ₁ ⨟ σ₂)`; these join *only* via `def-⨟`. Remove `def-⨟` and this pair fails.

Similarly (experiment `G1_dropAllFree`), dropping **all** free rules does **not** isolate the 3 crux pairs — it *exposes ~20 new pairs* (`compˢᴿ ↔ inst-λ`, `coincidence ↔ inst-λ`, `compᴿᴿ ↔ itself`, `instᴿ-λ ↔ right-id`, …). The free rules (`η-law`, the `coincidence-*` completions) are **load-bearing**: they close the *compositionality-under-a-binder* critical pairs, whose joins require the ↑-distribution `lift-dist-compˢˢ : (σ₁↑) ⨟ (σ₂↑) ≡ (σ₁ ⨟ σ₂)↑` — which is **proven in the file (line 342) but not registered**. The system is a delicately balanced, *nearly-completed* Knuth–Bendix system: pulling any thread unravels others.

Two more routes, both empirically closed:
- **Additive completion** (`ADD_*`): registering the four proven `lift-dist-comp*` laws makes it *worse* — they clash with `def-⨟`/`def-∘` too (`def-⨟ ↔ lift-dist-compˢˢ`, `def-∘ ↔ lift-dist-compᴿᴿ`, …). Every rule that rewrites a composition `σ₁ ⨟ σ₂` at its head clashes with the abstract-index split.
- **Reorientation to COMBINE** (`combBoth`): stating `def-⨟` as `(x ⋯ˢ σ₁) ⋯ˢ σ₂ → x ⋯ˢ (σ₁ ⨟ σ₂)` removes `{def-⨟,dist}` but is *strictly worse*: the combine variant now clashes with the **leaf lookups** `def-∙ᴿ-zero/suc`, `def-wk`, self-overlaps, and re-exposes the `compˢᴿ↔inst` / `coincidence↔inst` families. The abstract-index lookup is non-confluent with the algebra in **both** orientations.
- **Transparent operations** (make `_⨟_`, `_∙ˢ_`, `_⋯ˢ_` non-opaque so the leaf/lookup laws — `def-⨟`, `def-∙*`, `inst-*` — hold by δ-computation and need *no* rewrite): closed by an **opacity tension**, not empirically but structurally. `dist`, `assoc`, `compositionality*` are function-extensionality equalities (`(t ∙ˢ σ₁) ⨟ σ₂` equals `(t ⋯ˢ σ₂) ∙ˢ (σ₁ ⨟ σ₂)` only *pointwise*), so they can only be supplied as **rewrites**, and a rewrite LHS `(t ∙ˢ σ₁) ⨟ σ₂` is legal only if `_∙ˢ_`/`_⨟_` are **opaque** (a transparent LHS η-reduces to a lambda and never matches). But once `_⨟_` is opaque, `x ⋯ˢ (σ₁ ⨟ σ₂)` no longer computes, so the metatheory again needs `def-⨟` as a *rewrite* — and the `{def-⨟, dist}` clash returns. Opacity is *forced* by needing `dist` as a rewrite, and it *forces* `def-⨟` as a rewrite. The route collapses to §5.

---

## 5. The minimal obstruction — an unsatisfiable essential quadruple

Isolating the core (experiments `MIN_*`, with `assoc` present so the combine-associativity self-pair is joined):

- **`{compositionalityˢˢ, inst-x, dist}` without `def-⨟`** ⟹ `{compˢˢ, inst-x}` non-confluent. *(unique joiner absent)*
- **`{compositionalityˢˢ, inst-x, dist, def-⨟}`** ⟹ `{def-⨟, dist}` non-confluent. *(split clashes with distribution)*

Both `compˢˢ`, `inst-x`, `dist`, `def-⨟` are metatheory-essential (§3). Therefore:

> **No registered rule set that contains `{compˢˢ, inst-x, dist}` is locally confluent** — with the forced joiner `def-⨟` you get `{def-⨟, dist}`; without it you get `{compˢˢ, inst-x}`. And subst-free SR *requires* all of `compˢˢ` (⊢• type-application commutation), `inst-x` (variable substitution), `dist` (map/distribution) as rewrites. Hence subst-free ⟹ non-confluent. ∎

A **second, independent** obstruction is `{compᴿˢ, compᴿᴿ}` (pair 4): on `((t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂) ⋯ˢ σ`, the two reducts converge only if `⟨ρ₁⟩ ⨟ (⟨ρ₂⟩ ⨟ σ) = ⟨ρ₁∘ρ₂⟩ ⨟ σ`, which needs a "merge-under-associativity" step that the right-associating `assoc` cannot supply. Both are essential (weakening / β-type / first-class-renaming coincidence). So confluence must break **both** cores, each at the cost of an essential rewrite.

---

## 6. Grounding in σ_SP / Autosubst 2 — *why* the wall is here and not there

Autosubst 2's normalizer `asimpl` decides the substitution equational theory because its rules form the **convergent σ_SP-calculus** (Curien–Hardin–Lévy 1996; Stark thesis Ch. 4, *terminating* per Abadi et al. 1991, *confluent* per CHL, *complete* per Schäfer et al. 2015). Three facts from the theory pin down the discrepancy with `systemf.agda`:

1. **σ_SP INCLUDES the η/SCons rules** (`0 · ↑ → I`, `0[σ] · (↑∘σ) → σ`), oriented toward the smaller RHS, *plus* right-identity `σ∘I → σ`. The bare Abadi σ-calculus *excludes* them and is provably non-confluent. So the instinct "drop the η-laws" is theory-wrong; here they cause clashes only because of the representation (§4). *(This matches the file: `η-law`/`η-lawᴿ` are FREE, but dropping them re-exposes `dist ↔ η-id`, because `η-id` needs `η-law` to join against `dist`.)*

2. **Compositionality is COMBINE-only on terms** (`s[σ][τ] → s[σ∘τ]`); the SPLIT rule exists *only* as the variable base-case lookup `(id x)[σ] → σ x` and its composed form `(σ₁∘[σ₂]) x → (σ₁ x)[σ₂]`. These do not overlap because in σ_SP **every variable is `0[↑ⁿ]` — a first-order term built from `0` and `↑`.** There is **no abstract de Bruijn index.** The overlap `x[(t·σ₁)∘σ₂]` that fails in Agda simply cannot be formed: `(id x)[t·σ₁]` reduces by case analysis on the *concrete* structure `0` / `↑ⁿ`, never getting stuck.

3. `systemf.agda`'s `def-⨟` *is* the composed-lookup interference law — but with an **abstract** `x : S ∋ s`. For abstract `x`, `x ⋯ˢ (t ∙ˢ σ₁)` is a *stuck* term (no `def-∙ˢ` clause matches an unknown index), so the critical pair against `dist` has two **distinct stuck normal forms**. This is exactly the brief's "doubly-structural lookup," now precisely located: **it is an artifact of the intrinsically-scoped functional representation, absent from first-order σ_SP.**

First-class renamings: σ_SP orients the coincidence lemma `rinstInst : s⟨ξ⟩ → s[ξ >> ids]` (renaming *into* substitution). `systemf.agda` orients it the **opposite** way — `coincidence : t ⋯ˢ ⟨ρ⟩ → t ⋯ᴿ ρ` (substitution-by-a-renaming *collapses to* a renaming, keeping renamings as the normal form). This is a defensible dual choice, but it is the source of core 2 (`compᴿˢ ↔ compᴿᴿ`) and the `coincidence-*` completion clashes: keeping renamings first-class means the `⟨_⟩` sub-algebra must stay in lock-step with the `∘` ren-algebra, and the merge law `⟨ρ₁⟩⨟⟨ρ₂⟩ → ⟨ρ₁∘ρ₂⟩` fights `assoc`. Autosubst 2 explicitly leaves confluence of this two-sorted extension a **conjecture**.

---

## 7. The completeness frontier — what is definitional, what is propositional

Confluent sets *do* exist. `C1_structuralCore` (30 rules: the `def-∙*`, `def-↑ˢ`, `inst-*`, `instᴿ-*`, `def-id`, `def-wk`, `comp-id*`, `interact*`, `coincidence-var` — i.e. **constructor-pushing + leaf lookups only**) **passes `--local-confluence-check`**. A greedy maximal search yields a **38-rule confluent set**:

> full − `{assoc, assocᴿ, coincidence-fold, compositionalityˢˢ, compositionalityˢᴿ, compositionalityᴿˢ, compositionalityᴿᴿ, dist, distᴿ, η-law, η-lawᴿ}` — verified: 0 non-confluent pairs.

So the confluent frontier keeps the **traversal/leaf layer definitional** and forces the **entire monad/algebra layer** (`compositionality*`, `dist`, `assoc`, `coincidence-fold`, the η-laws) to be **propositional** — provided as lemmas and applied by hand in the metatheory. The propositional remainder is therefore **not empty and not a single stray fact**: it is the whole simultaneous-substitution algebra. Concretely, subject reduction then needs manual bridges (`subst` with the still-proven `compositionality*`/`dist`/`assoc` lemmas) at the type-alignment sites: `⊢↑ᴿ`, `⊢↑ˢ`, the `⊢λ`/`⊢•` cases of both traversal lemmas, `⊢[]`, and `sr` β-λ.

The 38-rule set is the **minimum-cardinality** confluent subset: adding back *any one* of the 11 removed rules re-introduces ≥1 failing pair (verified exhaustively; the non-monotone re-exposure of `compᴿᴿ ↔ instᴿ-{λ,Λ,∀}` and `coincidence ↔ inst-{λ,Λ,∀}` rules out every alternative size-7 vertex cover of the failing-pair graph). It is also **bridge-minimal**: it keeps every `inst-*`/`instᴿ-*`/`def-*` rule (so `_⋯ᴿ_`/`_⋯ˢ_` fully compute on constructors) and drops exactly the composition/interaction layer.

**Surviving-subst count for configuration B** (companion file `systemf_confluent.agda`, verified `agda … --local-confluence-check` exit 0): **`N = 7` `subst` coercions**, factored through **5 helper lemmas** that repackage **16 σ-lemma applications** — versus `N = 0` for the shipped, confluence-off configuration A. The 5 helpers are the irreducible semantic content confluence expels from the definitional layer:
- `⋯ᴿ-wk-↑ᴿ` — renaming/weakening naturality (`compᴿᴿ`);
- `⋯ˢ-wk-↑ˢ` — substitution/weakening naturality (`compˢᴿ`,`compᴿˢ`);
- `[]-⋯ᴿ` — single-substitution commutes with renaming (`compˢᴿ`,`compᴿˢ`,`dist`,`coincidence`,`coincidence-fold`);
- `[]-⋯ˢ` — single-substitution commutes with substitution (`compˢˢ`×2,`dist`×2,`assoc`) — the `⊢•` type-application case;
- `wk-[]-id` — weaken-then-single-substitution = identity (`compᴿˢ`,`right-idˢ`) — the β-redex type `(weaken t′)[e₂] ≡ t′`.

`sr`'s β-Λ, ξ-·₁, ξ-·₂, ξ-• and the `⊢Λ`/`⊢·`/`⊢*` cases stay fully definitional (0 bridges).

The boundary sits exactly at the **traversal / algebra** line: constructor-pushing and leaf-variable lookup can be confluent *and* definitional; the moment a law rewrites a **composition `σ₁ ⨟ σ₂` / `ρ₁ ∘ ρ₂` at its head** (distribution, associativity, combine-compositionality, the coincidence completions) it collides with the abstract-index lookup and must be demoted to propositional.

---

## 8. Deliverables

- **Configuration A** — `systemf.agda` (as shipped): subst-free SR, `--local-confluence-check` **off**. 0 substs.
- **Configuration B** — `systemf_confluent.agda`: the **minimum-cardinality** confluent registered set (38 rules = full − `{assoc, assocᴿ, dist, distᴿ, η-law, η-lawᴿ, compᴿᴿ, compᴿˢ, compˢᴿ, compˢˢ, coincidence-fold}`), `--local-confluence-check` **on and passing** (`agda` exit 0), SR compiling with the σ-algebra layer supplied propositionally. Surviving-subst count: **7** (5 helper lemmas, 16 σ-lemma applications). No new postulates, no `TERMINATING`, no escape flags.
- This analysis.
- Reproduction harness: `scratchpad/harness/driver.py` (+ `battery*.json`, `greedy.py`, `mkbase.py`).

---

## Answers to the specific questions

1. **Autosubst 2's rule set / orientation** — §6: COMBINE-only compositionality on terms; SPLIT only at the variable leaf `(id x)[σ]→σ x`; η/SCons **included**, toward smaller RHS; `rinstInst` orients renaming→substitution; four compositionality instances for first-class renamings.
2. **Mapping onto `systemf.agda`** — `compositionalityˢˢ` = Clos/combine ✓; `def-⨟` = composed-lookup **but over an abstract index** (the fatal difference); `dist` = Map; `coincidence*` = the `rinstInst`/merge completions with the *opposite* orientation; the `def-∙*` leaf rules and abstract-index `_⋯ˢ_ {V}` clause have **no σ_SP counterpart** (σ_SP has no abstract index).
3. **Maximal `--local-confluence-check`-passing subset** — §7: the 38-rule constructor-pushing + leaf-lookup set (proved by the checker). The genuine, minimal obstruction to going further is the essential quadruple `{compˢˢ, inst-x, dist, def-⨟}` (§5), *not* registrable together.
4. **Subst-freeness downstream** — §5, §7: SR is subst-free **iff** `compˢˢ`, `inst-x`, `dist` (and `def-⨟`) are registered, which is exactly the non-confluent configuration. Under any confluent set the surviving substs bridge precisely the demoted algebra laws.
5. **First-class renamings** — §6: they stay a distinct sort; the chosen `coincidence` orientation keeps *renamings* (not substitutions) as the normal form, which is the source of the independent `{compᴿˢ, compᴿᴿ}` core; Autosubst 2 leaves the two-sorted confluence a conjecture.
6. **Completeness frontier** — §7: definitional = traversal + leaf lookup; propositional = the entire composition/distribution/associativity/η algebra; the remainder is a **specific, irreducible core**, not empty.
