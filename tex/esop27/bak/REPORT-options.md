# Is there a way out? Options for the rewriting method, ranked

Self-contained. The rewriting method is blocked at two ends of the same development, with
the one thing that works — the type-level σ-calculus, certified locally confluent —
sitting between them. This report gives a structural diagnosis, a ranked list of escape
routes with the cheapest falsifier for each, and the results of the two falsifiers that
were run.

**Bottom line: the boundary is real, and it now has a precise characterisation (§2). Two
of the most promising escapes were tested and both bit (§3, §4). The recommended move is
to stop treating this as all-or-nothing and adopt the layering principle in §5, which the
working development already instantiates.**

---

## 1. The situation being diagnosed

| site | status |
|---|---|
| expression-level σ-calculus | 105 non-joinable pairs at the β/lookup stage, 191 with traversal laws; ≈77% are expression-rule × TYPE-rule |
| **type-level σ-calculus** | **certified locally confluent — the thing that works** |
| layer (i), the LR environment | 7 pairs |
| layer (ii), `⟦_⟧ᵀ`/`⊛ᵀ`/`⊙ᵀ` | 8 pairs after a completion campaign that went 9 → 27 → 8 |

Layers (i) and (ii) fail the *same two ways*:

* **Family (A)** — a rule competing with a record projection or copattern clause
  (`.proj₁`, `.sem`).
* **Family (B)** — `⟦⟧-ren`/`⟦⟧-sub` against `compositionalityˢᴿ`, `beta-fold-ˢᴿ`,
  `compositionalityˢˢ`, `beta-fold`.

---

## 2. Diagnosis: a non-disjoint union of two rewrite systems

There are two rewrite systems that share symbols:

* **R_type** — the type-level σ-calculus, ~40 rules, confluent.
* **R_sem** — the semantic laws, whose left-hand sides *contain R_type-defined symbols in
  matchable positions*: `⟦ T [ σ ]ˢ ⟧ η`, `⟦ T [ ζ ]ᴿ ⟧ η`.

Confluence is **not modular for non-disjoint unions**. For R_type ∪ R_sem to be locally
confluent, R_sem must be closed under every R_type rule that can fire inside an R_sem
left-hand side. Since `T [ σ ]ˢ` is exactly what R_type rewrites, essentially every R_type
rule overlaps, and each closer added to R_sem itself mentions type-level terms and so
opens fresh overlaps. That is the treadmill, and its size is combinatorial in
|R_type| × |R_sem|.

This single mechanism explains all three measured sites:

* the expression level's ≈77% expression × type pairs — the same thing one layer down;
* family (B) at both semantic layers — verbatim the same pairs, by name;
* the "matching limit" already noted separately (a rule whose stored index is `T [ η₁ ]ˢ`
  fires only at a rigid type) is the *same* fact seen from the matching side rather than
  the confluence side.

**Family (B) is not a curation shortfall. It is what a non-disjoint union of rewrite
systems costs.** Family (A) is a different and much smaller problem: it is local to the
carrier, and `no-eta-equality` was measured to remove exactly the η-caused pairs.

---

## 3. Falsifier 1 — RUN. "Drop to a single-sorted σ-calculus." **Killed.**

**Mechanism attacked.** strat's R_type is two-sorted — renamings *and* substitutions,
joined by `coincidence` — which generates the mixed `⟨⟩-lift-RS/SR/…` family (≈10 rules).
Rounds 6–7 of the layer-(ii) campaign died against exactly that family. If the base were a
single-sorted λσ⇑, that family would not exist, and R_sem might close. Call this H2
(the blocker is the *size* of R_type), against H1 (the blocker is the *shape* of the laws).

**Result: neither. The design does not exist.** `OneSortedProbe.agda` fails before the
confluence check is reached:

```
Syntax.DisallowedInterleavedMutual: _[_] declared but not defined.
Since `opaque` blocks can not participate in mutual recursion,
their definition must be given before this point.
```

A single-sorted λσ⇑ must define lifting through the traversal,
`(σ ↑) (suc α) = (σ α) [ wkₛ ]`, so `_↑` and `_[_]` are mutually recursive. Agda's
`opaque` cannot participate in mutual recursion. Therefore `_↑` cannot be opaque,
therefore `σ ↑` is not rigid, therefore no rule may match on it — and rigidity of the map
formers is the precondition for the whole method.

**SystemF-strat escapes this by being two-sorted**: `_↑ˢ` is defined via the *renaming*
traversal `_[_]ᴿ`, which is already complete when `_↑ˢ` is declared, so `_↑ˢ` can be
opaque and `_[_]ˢ` comes afterwards.

**Consequence.** The two-sorted structure is **forced, not chosen**. The mixed
`⟨⟩-lift-*` family that killed rounds 6–7 is a consequence of the very device that makes
the map formers opaque-able. "Use a smaller R_type" is not an available move. H2 is
downgraded to: the size of R_type is real, but it is not separable from the design.

---

## 4. Falsifier 2 — RUN. "Make composition a constructor." **Severely damaged.**

**Mechanism attacked.** Family (B) is "a law whose LHS carries a computed type argument".
If the map formers are *constructors* of an inductive `Sub` rather than opaque defined
symbols, then `σ ⨟ τ` and `σ ↑` are rigid by construction — and, unlike `opaque`,
constructors have no trouble with mutual recursion, so §3's obstruction does not apply.

**Result: termination fails.** `InductiveSubProbe.agda`:

```
error: [TerminationIssue] Termination checking failed for: _&_, _[_]
Problematic calls: α & σ ; (α & σ) [ τ ] ; α & σ ; T [ σ ↑ ]
```

With `_⨟_` a constructor, lookup must read `α & (σ ⨟ τ) = (α & σ) [ τ ]`, and the
traversal must read `(var α) [ σ ] = α & σ`. The two are mutually recursive with neither
argument structurally decreasing: `α & σ` is an arbitrary `Ty`.

**Cost, and why this is close to fatal rather than merely expensive.** The escape is
standard — well-founded recursion on the size of the `Sub`. But a well-founded `_&_`/`_[_]`
computes only as far as its accessibility proof reduces, and *the entire method depends on
these two functions computing definitionally*. Trading definitional computation for
rigidity is trading away the thing being bought. Not formally killed — a sized-types or
fuel-indexed formulation might preserve enough computation — but it is no longer a cheap
idea, and the burden of proof has moved onto it.

---

## 5. The live option: state the boundary as a layering principle

**Mechanism.** Stop asking for a globally definitional σ-calculus. Rewrite exactly the
layer whose equations are between terms of a **single sort with no computed indices**, and
transport across layer boundaries.

**Why it works.** It is what the working development already does, and the numbers support
it rather than merely tolerating it:

* the type-level σ-calculus satisfies the criterion (its equations are between `Type`s and
  maps, and its LHSs contain only opaque map formers) — and it is certified confluent;
* `SystemF-adequacy.agda` has 56 `subst` occurrences and **every one of them is
  denotational**; not one is caused by type or expression substitution;
* the statements of `𝓥⟦⟧-ren`, `𝓥⟦⟧-sub` and `𝓥⟦⟧-weaken` are transport-free, where
  their counterparts in the original development all carry transports.

**Why this is a principle and not a compromise.** It makes a falsifiable prediction: *any
layer whose laws mention a computed index of a lower layer will require transports, in
proportion to the overlap between the two rule sets.* That prediction is confirmed at
three independent sites with no fitting — the expression level (≈77% cross-layer pairs),
layer (i) (4 of 7 pairs are family B), layer (ii) (the same four pairs by name). A
compromise has no predictive content; this does.

**Cost.** None in code. It costs the claim "the method eliminates all transports", which
was never true anyway.

---

## 6. Ranked list

| # | option | attacks | status | cheapest falsifier |
|---|---|---|---|---|
| 1 | **Layering principle** (§5) | reframes the goal | **LIVE — recommended** | already confirmed at 3 sites |
| 2 | **Mechanised Knuth–Bendix completion** | family (B), by grinding | **LIVE, pragmatic** | partially done by hand: 27 → 8 in one pass; script the loop that reads Agda's pair reports and proposes closers |
| 3 | **Family (A) via `opaque` + `no-eta-equality`** | projection-vs-rewrite | **LIVE, cheap, partial** | apply to layer (i)'s 3 family-(A) pairs; measured to work in layer (ii) (3 → 1) |
| 4 | Inductive `Sub`, composition as constructor | family (B), by rigidity | **damaged (§4)** | run: does a well-founded `_&_`/`_[_]` still compute enough for the type-level rules to fire? |
| 5 | Single-sorted λσ⇑ | family (B), by shrinking R_type | **KILLED (§3)** | — |
| 6 | Extrinsic typing / fused sort | the expression level only | **KILLED** | — |
| 7 | Global `--confluence-check` | — | **KILLED** | — |
| 8 | Cubical + HITs | family (A) | **KILLED** | — |
| 9 | `opaque` interpreter + outward orientation | family (B) at layer (ii) | **parked, payoff-free** | — |

### The kills, with reasons

**(6) Extrinsic typing.** Dissolves the *expression*-level problem by construction —
expression laws would mention no types, so the ≈77% cross-layer pairs vanish. But it does
**not** touch layers (i) or (ii): `⟦ T [ σ ]ˢ ⟧ᵀ η` mentions type substitution regardless
of how expressions are typed. So it fixes the site that is arguably least central and
leaves the semantic boundary exactly where it is — while giving up intrinsic typing, which
is the setting's premise. Wrong target, high cost.

**(7) Global `--confluence-check`.** Strictly stronger than the local check: it requires
local confluence *and* termination. It can only report at least as many problems, never
fewer. There is no sense in which switching to it helps.

**(8) Cubical + HITs.** Family (A) is unaffected — the existing notes record that both
η-rules survive in the `sized-hit*` prototypes. Family (B) is a *pattern-matching*
limitation, not an equality-proof limitation: HITs supply new equalities, not new matchable
forms, so the offending LHS `⟦ T [ σ ]ˢ ⟧` is no more stable under cubical. Wrong
mechanism, total rewrite.

**(9) `opaque` interpreter.** Untested, and would plausibly close round 5's residual
(`⟦⟧ᵀ-ren⁻` vs `⟦_⟧ᵀ`-clause3) by turning a rule-vs-clause overlap into rule-vs-rule. But
round 5 also measured that the outward orientation **fails `probe-weaken`** — weakening is
not definitional there — so even a fully confluent outward system deletes no coercions.
Confluence-improving and payoff-free. Not worth the run.

---

## 7. Honest conclusion

The boundary is real, and it is not where I previously said it was. It is not record η
(that was retracted and is genuinely fixable), and it is not a shortfall of curation
effort. It is this:

> **A rewrite rule whose left-hand side contains, in a matchable position, a term built by
> a defined symbol of another confluent rewrite system, inherits a critical pair for every
> rule of that system which can fire there. When the two systems are the type-level
> σ-calculus and any semantics defined over it, that is essentially all of them.**

The two structural escapes — shrink the lower system, or make its operators constructors —
were tested. The first does not exist as a design (§3, `opaque` cannot be mutually
recursive, so two-sortedness is forced). The second costs well-founded recursion and
therefore the definitional computation the method is built on (§4).

What remains is not a compromise but a scope statement: **rewrite the layer that satisfies
the single-sort/no-computed-index criterion, and transport across the boundary.** The
existing development is already the best instance of that principle, and its transport
profile — 56, all denotational, none substitutional — is the evidence.

---

## 8. Files

| file | status |
|---|---|
| `OneSortedProbe.agda` | probe, exit 42 — falsifier 1; single-sorted design does not exist |
| `InductiveSubProbe.agda` | probe, exit 42 — falsifier 2; termination fails as predicted |

Both carry a banner stating that they are probes, that they are expected to fail, their
measured outcome, and that nothing imports them. `--local-confluence-check` is on in both.
No file outside this report and these two probes was created or modified.

---

## 9. Falsifier 3 — RUN. "Declare the semantic rules in a parametrised module." **Killed, decisively.**

**The idea.** Agda checks confluence at the point of *rule declaration*. So declare the
semantic rewrite rules inside a module parametrised over an abstract type-substitution
structure — the operations as module parameters, their laws as propositional parameters,
no rewrite rules registered for them. Inside that module the type operations are rigid
variables, so there is nothing for the semantic rules to overlap: R_type does not exist
there. Then instantiate the module with the concrete `SystemF-strat` layer.

This is the one escape that attacks the diagnosis in §2 head-on. §2 says the trouble is
that R_sem's left-hand sides contain R_type-*defined* symbols; a parametrised module makes
them *variables* instead.

**Anticipated outcomes.** (1) rules register and still fire after instantiation → the
obstacle dissolves; (2) register but do not fire → the matching limit, localised; (3) Agda
rejects the instantiation, or accepts it without re-checking confluence → an Agda-level
observation.

**Measured outcome: none of the three.** The rules are rejected *at declaration*, inside
the parametrised module, before instantiation is ever reached
(`ParamModuleProbe.agda`, exit 42):

```
warning: -W[no]RewriteVariablesNotBoundByLHS
⟦⟧-sub  is not a legal rewrite rule, since the following variables are not
bound by the left hand side:  σ, T, Δ₁
⊙-assoc … not bound by the left hand side:  τ, σ, Δ₂
```

and the in-module probe then fails with a type error, because the rule never fired.

**Why, and why it generalises.** A rewrite rule's left-hand side must determine all of its
variables by **first-order matching**. The LHS here is `⟦ app T σ ⟧ η`, where `app` is a
module parameter — a variable. Matching a goal against a variable-headed application
determines nothing, so `T`, `σ` and `Δ₁` are unbound and the rule is not legal.

That is not an accident of this encoding. It is a dichotomy:

| the type operations are… | overlap with R_type? | matchable in an LHS? |
|---|---|---|
| **concrete** (defined symbols with rewrite rules) | **yes** — critical pairs, §2 | yes |
| **abstract** (module parameters, record fields) | no | **no** — not a legal rule |

**The very property that makes abstraction attractive — the operations are opaque, so
nothing can overlap them — is the property that makes them non-matchable.** You cannot
have rigidity-by-abstraction and matchability at once; they are the same property seen
from the two sides.

One variant is worth naming and dismissing in the same breath: *postulating* the abstract
operations instead of parametrising over them would make them matchable (postulates are
defined symbols), and the rules would register. But postulates cannot afterwards be
instantiated with the real operations — and instantiation is exactly the move the
parametrised module was introduced to enable. Agda's module system offers substitution of
parameters, not re-checking of rules at the instantiation site, so there is no version of
this that both registers and connects to `SystemF-strat`.

**Where this leaves §2.** The diagnosis is strengthened, not weakened. §2 said the semantic
laws cannot avoid mentioning R_type-defined symbols in matchable positions. §9 shows the
one syntactic device that could have removed those symbols removes matchability with them.
The obstruction is therefore not "R_type happens to have 40 rules" and not "we have not
curated enough" — it is that *a rewrite rule needs a concrete head to match on, and any
concrete head in this development belongs to a rewrite system of its own.*

### Ranked list, updated

Insert as #10, killed:

| # | option | attacks | status | measured cause |
|---|---|---|---|---|
| 10 | **Parametrised module over an abstract type layer** | family (B), by removing R_type from the declaration context | **KILLED (§9)** | `RewriteVariablesNotBoundByLHS` — abstraction and matchability are the same property |

Options 1–3 (layering principle, mechanised completion, family-(A) fix) are unaffected and
remain the live set. §7's conclusion stands unchanged, and now rests on three independent
falsifiers rather than two.

### Files, updated

| file | status |
|---|---|
| `OneSortedProbe.agda` | probe, exit 42 — falsifier 1; single-sorted design does not exist |
| `InductiveSubProbe.agda` | probe, exit 42 — falsifier 2; termination fails as predicted |
| `ParamModuleProbe.agda` | probe, exit 42 — falsifier 3; rules illegal at declaration. **Postulates used, named:** `SEnv`, `⟦_⟧`, `⊙`, `⟦⟧-sub`, `⊙-assoc` — they stand in for the semantic layer, and postulating it makes the question sharper rather than weaker: if the technique cannot work for an abstract semantics it cannot work for a concrete one |
