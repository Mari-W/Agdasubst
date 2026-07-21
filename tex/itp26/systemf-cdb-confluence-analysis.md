# Confluent, near-subst-free System F via co-de-Bruijn first-order variables

**Follow-up to `systemf-confluence-analysis.md`.** The functional verdict was: `--local-confluence-check` + subst-free SR are mutually exclusive for abstract-index de Bruijn, with the root cause being the **abstract variable** (σ_SP escapes because its variables are first-order `0[↑ⁿ]`). Co-de-Bruijn gives first-order variables natively (a variable is the thinning `os oe` shifted by `o'`). This document reports what that escape buys — empirically, `--local-confluence-check` ON throughout, 0 postulates.

Artifacts (all `agda … --local-confluence-check`, exit 0): baseline `FOp/`, H1 re-representation `FOpH1/`.

---

## ⚠️ Scope caveat — this is NOT yet the multi-sorted setting

The impossibility (`systemf-confluence-analysis.md`) was proven in the genuinely **multi-sorted** `systemf.agda`: `Scope = List Sort`, `Sort = expr | type | kind`, one *unified intrinsic* `_⋯ˢ_`/`_⋯ᴿ_` algebra across all three sorts. **FOp/FOpH1 are not that setting.** Verified: `Scope = List ⊤` (co-de-Bruijn thinnings over a *single* sort = type variables only), and terms are **extrinsic** — `var : ℕ → Tm Θ` (raw ℕ-indexed term variables), typing a relation, term substitution a separate ℕ-indexed mechanism. So FOp *decomposes* the multi-sorted problem into **(single-sorted co-de-Bruijn types) + (extrinsic ℕ-indexed terms)** — two single-sort mechanisms, not one multi-sorted algebra.

Consequences for the claims below:
- The σ-algebra escape (first-order variables kill the abstract-index `def-⨟ ↔ dist` clash) is verified **per-sort**, for the one type sort. It does **not** establish the escape for a *unified multi-sorted* co-de-Bruijn substitution acting on several sorts at once.
- That unified case is exactly Autosubst 2's **vector substitutions** (CPP'19 §3.2, §5), whose confluence is only **conjectured** and whose completeness is stated to **break** in the multi-sorted case — i.e. the harder, open regime where new coherences may reappear.
- Part of FOp's low subst count is attributable to the **extrinsic** design (substs land on type-classifiers/derivations, not on a unified term algebra), independent of co-de-Bruijn.

So the comparison below is **co-de-Bruijn-single-sorted-types + extrinsic-terms vs. functional-multi-sorted-intrinsic** — informative about the σ-algebra escape, but **not apples-to-apples**. The faithful multi-sorted co-de-Bruijn (thinnings/covers over `List Sort`, unified vector substitution) is the correct next target.

### Multi-sorted verification (`FOpMS/`) — the gap closed

Built the faithful multi-sorted development: `FOpMS/ThinRw.agda` (thinnings/covers/`cop`/`Fac`/`Pos` over `List Sort`, sorts threaded through `os`/`o'`/`bb`/`ll`/`rr`, never inspected) and `FOpMS/Tm.agda` (genuinely **unified** multi-sorted syntax — ONE scope `List Sort` holding expr+type variables, ONE vector substitution acting on all sorts, cross-sort binders `Λ`/`App` via a sorted `Bind`). Both compile `--local-confluence-check` ON, 0 postulates. Findings:

- **The thinning/cover foundation stays confluent** — sorts ride along inertly; `⨾`/`Fac` unchanged.
- **`FOpMS/ObsTest.agda`**: registering `↾-⨾` on a *sorted* substitution-vector yields the **identical 3 critical pairs** as single-sorted `FOp`. The residual obstruction is **sort-agnostic** (`↾`-elimination vs `↾`-composition).
- **H1 works identically multi-sorted**: in `FOpMS/Tm.agda`, `⟪⟫-⇒↑`, `⟪⟫-app↑`, `⟪⟫-App↑` and every binder **use**-case (`⟪⟫-∀↑/lam↑/Lam↑-use`) are `refl`; only the binder **drop**-cases need `sub'-drop` (= `sub-ren`, weakening naturality) — the same residual, now uniform across all three binders ∀/λ/Λ.

**Full unified build** (`FOpMS/Typing.agda` + `FOpMS/SR.agda`, both compile `--local-confluence-check` ON, 0 postulates): extrinsic typing over a full telescope `Cx`, and the **single unified substitution-preservation lemma** `sub-pres : WtSub Ψ σ Φ → Φ ⊢[θ] e ∶ A → Ψ ⊢↑ (e⟪σ⟫) ∶ (A⟪σ⟫)` — which is *simultaneously* type-substitution- and term-substitution-preservation (β and type-β are both instances `v ∙ ids` / `A ∙ ids` of the ONE `Sub`), proven in `SR.agda` as `⊢-inst`/`⊢-instTy`. Because `sub'` threads θ and restricts σ once at the leaf, σ is **never peeled**: it threads unchanged (subst-free) through `app`/`App` since `⟪⟫-⇒↑`/`⟪⟫-app↑`/`⟪⟫-App↑` are `refl`, and is only lifted under binders.

**The cross-sort question — answered: NO new coherence.** `Λ` binds a *type* var in an *expr* (`Bind type (Tm expr)`), `App` pairs an *expr* with a *type*, `∀` binds a *type* var in a *type* — all reuse the same `Bind`/`lift`/`cop` machinery with the sort threaded and never inspected. The only binder residual is the single sort-generic `sub'-drop` (weakening naturality), fired identically for λ, Λ, ∀; the type-application coherence `App-comm` factors through `Clos` + the `⨟`-identities, none mentioning a sort; H1 composes cover thinnings through the confluent `⨾`, so a cross-sort binder yields the exact same `thinL/thinR cv ⨾ θ` shape as a same-sort one and `Fac-L/Fac-R` fire uniformly. **No new critical pair.**

Residual substs (Typing 32 + SR 2) are all the same sort-agnostic families as single-sorted FOp: `sub'-drop`/weakening naturality (∀/λ/Λ drop-cases), `wk-⟪⟫`/`wkSub-⟪⟫`/`wk-cancel`, `App-comm`, `lookup-ren`/telescope coherence, and the thinning-analog `⟨⟩-*`/`⨾⨾` bookkeeping in `⊢-ren` (larger only because this typing uses co-de-Bruijn context *renaming*, which FOp's simpler `Cx` avoided). The one honest gap: the top-level `preserve : Γ⊢t∶A → t⟶t′ → Γ⊢t′∶A` *dispatch* is not completed — the smart constructors `app↑`/`App↑` are not unification-invertible at the `⇑`-carrier level (the arrow domain / cover thinnings sit under `cop`); FOp closes this with `domOf`/`codOf`/`bodyOf` inversion, which was not ported. The *substitution content* such a `preserve` consumes (the two β corollaries) is proven.

**Conclusion: multi-sortedness is orthogonal to the confluence ⊻ subst-free question.** The obstruction is neither the σ-algebra (first-order *sorted* variables still escape it) nor multi-sortedness (rides along) — it is the sort-agnostic thinning/cover coherence (`↾-⨾`/`sub-ren`). Multi-sorted co-de-Bruijn lands on the **same frontier** as single-sorted (`FOpH1`); per Autosubst 2 (CPP'19) vector-substitution completeness even *breaks*, so it is never better. The single-sorted analysis below therefore transfers verbatim.

---

## One-line verdict

> **The co-de-Bruijn escape is real but partial. First-order variables eliminate the functional σ-algebra obstruction `{compˢˢ, inst-x, dist, def-⨟}` entirely — the whole substitution algebra is confluent *and* definitional. Re-representing `sub` to thread the type's thinning through the confluent thinning-composition `⨾` (H1) additionally makes the *form-distribution* laws `⟪⟫-⇒↑` (arrow) and `⟪⟫-∀↑`-`use` DEFINITIONAL (`refl`), with no new rewrite rules — dropping the typing/SR substs 11 → 8. But 0-subst is NOT reached: two strictly-smaller, binder-confined obstructions survive — (a) weakening naturality `sub'-ren ↔ mapWk-↾` (a genuine A-vs-B, `sub`-elimination vs naturality-pull, verified non-confluent-registrable, confined to the ∀-binder), and (b) context-list coherence (`App-comm`, `subCx-inst`) whose underlying laws `Clos`/`⟪⟫-id` are not legal rewrite LHSs (they reduce). Co-de-Bruijn moves the obstruction from the *core σ-algebra* (functional: unavoidable, every substitution) to *binder/target-weakening coherence* (co-de-Bruijn: only ∀) — strictly weaker, but nonzero.**

---

## 1. The σ-algebra obstruction is eliminated (the escape confirmed)

`FOp/Ty.agda` proves **every** σ-law — `Clos` (`(u⟪σ⟫)⟪τ⟫ ≡ u⟪σ⨟τ⟫`), `⟪⟫-id`, `sub-⨟`, `⨟-idₗ/ᵣ`, `VarCons`, `Map` — with 0 postulates, and the whole `FOp/SR.agda` System F subject-reduction chain type-checks with `--local-confluence-check` ON. The functional deadlock `{compˢˢ, inst-x, dist, def-⨟}` simply cannot form: there is no abstract index `x : S ∋ s`, so no `def-⨟ : x ⋯ˢ (σ₁⨟σ₂) → (x⋯σ₁)⋯σ₂` rewrite to clash with distribution. A variable is `tvar ⇑ (o'ⁿ (os oe))` — first-order data — and lookup is structural recursion on the thinning. The confluent registered core is tiny: `Fac-L Fac-R` (cover factorisation), `mapWk-↾`, and the four `⨾`-elimination clauses. Everything else is definitional or a propositional lemma applied by hand.

So the co-de-Bruijn baseline already occupies a point the functional representation proved *impossible*: **confluent AND definitional σ-algebra**. The residual substs live only in the typing/SR layer and bridge cover coherence — not lookup.

## 2. The obstruction relocated — two A-vs-B cores, reproduced

The residual is the **type-former distribution** at the classifier level. Registering the missing laws to make distribution `refl` fails confluence — the same elimination-vs-composition duality as the functional `def-⨟ ↔ dist`, now on the cover operators:

| core | law | clashes with | pairs (verified) | blocks |
|---|---|---|---|---|
| **(a)** restriction-composition | `↾-⨾ : (σ↾θ)↾φ ≡ σ↾(φ⨾θ)` | `↾`-elimination + itself | **3** | `⟪⟫-⇒↑`, `⟪⟫-∀↑`-use |
| **(b)** weakening-naturality | `sub-ren : sub t (mapWk σ r) ≡ (sub t σ)⟨r⟩↑` | `mapWk-↾` | **1** | `⟪⟫-∀↑`-drop, `wk-ty` |

Both are genuine (checker output reproduced: `{-# REWRITE ↾-⨾ #-}` → 3 `RewriteNonConfluent`; `{-# REWRITE sub-ren #-}` → 1). Each is *structurally* the functional duality (an operator's defining clauses vs. its composition/naturality law), but **strictly weaker**: confined to the type classifier at the arrow/∀ formers, not every substitution.

## 3. H1 — routing distribution through the confluent `⨾` (the load-bearing result)

Core (a) is **avoidable** — not by registering `↾-⨾` (non-confluent), but by *eliminating the double restriction* that needs it. Baseline `_⟪_⟫ (t ⇑ θ) σ = sub t (σ ↾ θ)` and `sub (pair l r cv) σ = sub l (σ↾thinL cv) ⇒↑ …` produce `(σ↾out)↾thinL cv` — two `↾`s. Re-represent `sub` to thread the thinning and restrict **once**, at the leaf, composing cover thinnings through the *already-confluent* `⨾` (`FOpH1/Ty.agda`):

```agda
sub' : Ty Θ → Θ ⊑ Δ → Sub Ξ Δ → Ty ↑ Ξ
sub' tvar                θ σ = look θ σ                                   -- the single ↾, at the leaf
sub' (_⇒_ (pair l r cv)) θ σ = sub' l (thinL cv ⨾ θ) σ ⇒↑ sub' r (thinR cv ⨾ θ) σ
sub' (∀' (use t))        θ σ = ∀↑ (sub' t (os θ) (lift σ))
sub' (∀' (drop t))       θ σ = ∀' <$> (drop <$> sub' t θ σ)
(t ⇑ θ) ⟪ σ ⟫ = sub' t θ σ
```

Now `(A ⇒↑ B) ⟪ τ ⟫ = sub' a (thinL cv ⨾ out) τ ⇒↑ sub' b (thinR cv ⨾ out) τ`, and the **registered** `Fac-L`/`Fac-R` fire on the *thinning argument* (`thinL cv ⨾ out → α`) before `sub'` inspects the subterm, giving `sub' a α τ ⇒↑ sub' b β τ = (A⟪τ⟫) ⇒↑ (B⟪τ⟫)` — **definitionally**. Verified:

- `⟪⟫-⇒↑ (a ⇑ α)(b ⇑ β) τ = refl` (`FOpH1/Ty.agda:132`).
- `⟪⟫-∀↑ (y ⇑ os ξ) τ = refl` (∀-`use`).
- **No new REWRITE rules** — the confluent set is unchanged, so `--local-confluence-check` still passes on the whole `FOpH1/SR.agda` chain (exit 0, 0 postulates, no `TERMINATING`).
- Typing-layer substs **6 → 4** (both arrow substs gone); SR **5 → 4** (`bodyOf-∀↑` gone by splitting `B`'s thinning head). **Total 11 → 8.**

This is the payoff of first-order variables applied *one level up*: the same trick that makes the σ-algebra confluent (compose thinnings via `⨾`, factor via `Fac`) makes form-distribution definitional — because the coherence is now carried by first-order thinning data, not a stuck restriction.

## 4. The residual 8 substs — why 0 is not reached

**(a) Weakening naturality — the genuine second obstruction (binder-confined).** `⟪⟫-∀↑`-drop, `subCx-wk`, `wk-ty`, `subCx-wkids` all reduce to `sub'-ren : sub' t θ (mapWk σ r) ≡ (sub' t θ σ)⟨r⟩↑`. Registering it fails `--local-confluence-check`: the critical pair on `sub' (pair l r cv) θ (mapWk σ r₁)` forks into `sub' (…) θ σ ⟨r₁⟩↑` (naturality-pull) vs `sub' l (thinL cv ⨾ θ)(mapWk σ r₁) ⇒↑ …` (`sub'`-elimination) and does not join (target scopes differ). This is the exact A-vs-B analogue of the functional `compᴿᴿ` naturality clash — `sub`-elimination vs the renaming-pull — but here it only fires where a binder introduces weakening (`lift`/`wkSub`), i.e. **only at ∀**. H2 (represent target weakening as a first-order shift so `sub-ren` becomes `⨾`-associativity) is the candidate to clear it; the direct registration is provably non-confluent.

**(b) Context-list coherence — not a form-distribution law.** `App-comm` (needs `Clos` + `inst-lift`) and `subCx-inst ×2` (need `wk-cancel` + `⟪⟫-id`, folded over `Cx = List (Ty ↑ Θ)`) are `map`-over-context equalities, irreducibly inductive over the context list. The underlying σ-laws here are not even legal rewrite LHSs — `Clos`'s LHS `(u⟪σ⟫)⟪τ⟫`, `⟪⟫-id`'s `t⟪ids⟫` **reduce** (`RewriteLHSReduces`), so they can only ever be propositional. This is orthogonal to confluence; it is a consequence of typing being *extrinsic* over a `List` context.

## 5. Frontier comparison — functional vs co-de-Bruijn

| | functional (`systemf.agda`) | co-de-Bruijn (`FOpH1/`) |
|---|---|---|
| σ-algebra (`compˢˢ`,`dist`,`assoc`,`Clos`) | **non-confluent** if registered ⇒ must be propositional (config B: 7 substs) or drop confluence (config A) | **confluent AND definitional** (0 substs, always) |
| form-distribution (`⟪⟫-⇒↑`, `⟪⟫-∀↑`-use) | propositional (subst) | **definitional (`refl`)** via H1 |
| residual obstruction | σ-**algebra** lookup vs distribution — *every* substitution | weakening-**naturality** + context-list — *only* the ∀-binder |
| `--local-confluence-check` + subst-free | **impossible** (proven) | **not reached**, residual = 8 substs, all binder/context coherence |
| Pareto endpoints | A: 0 subst/conf-off · B: 7 subst/conf-on | single point: 8 subst/conf-on (no conf-off tradeoff needed) |

**Does co-de-Bruijn dominate?** On *definitional-algebra richness* — decisively yes: the entire σ-algebra plus arrow/∀-use distribution is confluent-and-definitional, which the functional representation proved impossible for the algebra. On *raw residual-subst count* — no: 8 (co-de-Bruijn) vs 7 (functional config B), comparable. But the 8 are a **different and weaker kind**: target-weakening naturality and extrinsic-context list coherence at the ∀-binder, versus the functional 7 which repaired the demoted core algebra. Crucially, co-de-Bruijn has **no impossibility** — there is no `{compˢˢ, inst-x, dist, def-⨟}` deadlock; the residual is a *naturality* obstruction that H2 (first-order shift) may yet close, whereas the functional deadlock is final.

## Answers to the specific questions

1. **Can the typing substs → 0 while confluent, by routing through `⨾`?** Partially: the arrow `⟪⟫-⇒↑` and ∀-`use` are driven to `refl` by H1 (`FOpH1/`, verified), eliminating 3 substs (11 → 8). The remaining 8 cannot be driven to 0 by any `↾`/`⨾` re-representation because they are weakening-naturality (`sub'-ren`) and context-list, not restriction-composition.
2. **Exact minimal obstruction, and is it smaller than functional?** Yes, strictly smaller: it is the `sub-ren ↔ mapWk-↾` weakening-naturality A-vs-B (1 critical pair), confined to the ∀-binder — versus the functional `{compˢˢ, inst-x, dist, def-⨟}` that hit every substitution. The arrow is fully closable; only the ∀/weakening survives.
3. **Fully subst-free SR?** No — a residual cover/weakening-coherence subst survives at the binder (`⟪⟫-∀↑`-drop → `sub'-ren`), pinned to the single critical pair `sub'-ren ↔ mapWk-↾`.
4. **Completeness frontier.** Definitional & confluent: the whole σ-algebra + arrow/∀-use distribution. Propositional: weakening naturality (`sub-ren` and its consequents) + extrinsic context-list coherence. There is **no** co-de-Bruijn point that reaches (0 subst / conf-on) with the current `sub'`; H2 (first-order target-shift) is the open route to eliminate the naturality residual.
