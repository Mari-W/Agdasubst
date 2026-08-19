# The two-world σ-calculus: a principled rule-by-rule account

Source of truth: [`systemf.agda`](systemf.agda) — declarations in the `opaque`
block (lines 185–581), registration in the `{-# REWRITE #-}` block (lines 586–602).

**72 rules registered.** Nine further rule-shaped facts are proved but
deliberately *not* registered (§7). Of the 72, 16 are one-per-constructor
(`instᴿ-*`, `inst-*`); the schema-level system is **56 rules + 2·|constructors|**.

The *absences* — the places where a completion operator does not need an image
— are checked in [`closure.agda`](closure.agda): eight `refl` assertions, each
saying that the redex a missing rule would have handled already reduces without
it. They are stated outside `systemf.agda`'s `opaque` block on purpose, since
inside it the definitions unfold and the rules stop matching.

Agda verifies **local confluence** (`--local-confluence-check`: every critical
pair joinable). Termination is *not* machine-checked — see [`coco/`](coco/) for
the export to external tools.

---

## 1. Provenance legend

| Tag | Source |
|---|---|
| **σw** | Curien, Hardin & Lévy, *Confluence properties of weak and strong calculi of explicit substitutions*, JACM 43(2) 1996 — weak fragment, as tabulated in Hardin, Maranget & Pagano, JFP 8(2) 1998, **fig. 1** |
| **σ⇑** | same, **strong** calculus with first-class lifting — HMP JFP 8(2) 1998, **fig. 2** |
| **σ_SP** | Stark, *Mechanising Syntax with Binders in Coq*, 2020, **fig. 4.1** (the surjective-pairing corner; Schäfer–Smolka–Tebbi CPP 2015) |
| **Abadi** | Abadi, Cardelli, Curien & Lévy, *Explicit substitutions*, POPL'90 / JFP 1(4) 1991, `10.1145/96709.96712` |
| **AS2** | Stark, Schäfer & Kaiser, *Autosubst 2*, CPP'19 |
| **new** | this work — no counterpart in the above |

Two systematic sources of *new* rules, neither present in σ⇑:

* the **V/T mode split** — σ⇑ has no variables, so it cannot distinguish them;
* the **coercion `⟨_⟩`** — first-class renamings (the AS2 §4 axis) give a second
  spelling for every renaming-shaped substitution, and the rules that reconcile
  the two spellings are ours.

Notation: `x` variable, `t` term, `x/t` mode-generic; `ξ` renaming,
`σ τ` substitutions; `[_]ᴿ`/`[_]ˢ` application, `⨟ᴿ`/`⨟` composition, `∙ᴿ`/`∙ˢ` cons,
`↑ᴿ`/`↑ˢ` lift, `wkᴿ` shift, `⟨_⟩` the renaming→substitution coercion.

---

## 2. The four decisions that fix the system

1. **`⇑` is primitive, not defined.** σ⇑'s choice. Abadi and both Autosubst
   versions instead *define* `⇑σ = 0 · (σ ⨟ᴿ ↑)` (AS2 fig. 2(b)); we keep it a
   constructor, and `def-↑ᴿ`/`def-↑ˢ` demote that definition to a lemma (§7).
2. **No η.** σ_SP keeps both η-laws (`0 · S → I`, `0[σ] · S∘σ → σ`); AS2 keeps
   them as *interference laws* (fig. 2(a)). We cannot: with **native inductive
   variables**, `def-wkᴿ` (σ⇑'s VarShift1) identifies `suc x` with `x [ wkᴿ ]ᴿ`,
   and that is exactly what breaks the non-left-linear η LHS. σ_SP can afford η
   only because it has no numerals — variable *n* *is* `0[S]ⁿ`. **Native
   inductive variables and surjective pairing cannot coexist in one rewrite
   system**: σ_SP drops the variables, σ⇑ drops η, and we follow σ⇑.
3. **Push at mode V, fold at mode T.** Renaming preserves the mode, so `x [ ξ ]ᴿ`
   is itself a variable and hence again a subject for the applied rules. A *fold*
   at V would overlap `def-wkᴿ` unjoinably. So composition at a variable
   **pushes** and composition on a term **folds** (`compositionalityᴿᴿ-var` vs
   `compositionalityᴿᴿ`). In the σ-world the question does not arise: a
   substituted variable is a term, which no applied rule can match.
4. **Coincidence oriented ˢ→ᴿ.** `t [ ⟨ ξ ⟩ ]ˢ → t [ ξ ]ᴿ`: the renaming world is
   the normal form, so the ᴿ-copy is not redundant duplication but the *target*.

### Retired and subsumed rules (2026-08-19)

Three rules were removed after measurement: `⟨⟩-wk-lift`, `⟨⟩-wk-cons` and
`⟨⟩-lift-lift` (numbers 70, 72 and 74; the numbering keeps its gaps, so every
other rule's number is stable). Each is derivable from `⟨⟩-comp` together with
its ᴿ-original, and dropping all three keeps the system at **0 non-joinable
critical pairs**. Their `-⨟` continuation forms are *not* derivable and stay:
dropping `⟨⟩-comp-⨟-lift-wkᴿ`, `⟨⟩-comp-⨟-interactᴿ` or `⟨⟩-comp-⨟-lift-dist-compᴿᴿ` costs 6, 3 and 5
pairs respectively.

`⟨⟩-split-⨟` looks like the same kind of rule — it un-collapses `⟨ ξ₁ ⨟ᴿ ξ₂ ⟩`
into two coercions, the only registered rule that moves work *out* of the
renaming world — but it is load-bearing: dropping it costs 11 pairs.

A fourth rule, `lift-id` (number 46, σ⇑'s **LiftId**), is not retired but
**subsumed**: its left-hand side `⟨ idᴿ ⟩ ↑ˢ s` is a strict instance of
`⟨⟩-lift`'s `⟨ ξ ⟩ ↑ˢ s`, which sends it to `⟨ idᴿ ↑ᴿ s ⟩`, where `lift-idᴿ`
finishes under the coercion. A base rule subsumed by its own coercion image is
redundant, and the 72-rule system checks at **0 non-joinable critical pairs**.
Nothing definitional is lost: `⟨ idᴿ ⟩ ↑ˢ s ≡ ⟨ idᴿ ⟩` still holds by `refl`
for user code (verified outside the `opaque` block, where the rules apply).

The exported TRS shrinks from 79 to 75 first-order rules. Every one of the 75
appears verbatim in the archived termination and confluence proofs, so the
shipped system is a subset of a system proved SN; with Agda's 0 non-joinable
pairs, Newman's lemma gives confluence without re-running the provers. This is
checked mechanically by `check_archives.py` (in [`coco/`](coco/) here, and
shipped next to this file in the supplement), not asserted from memory.

### 2.1 A load-bearing asymmetry: MapEnv

`dist` (σ⇑'s **MapEnv**) is a rule in the substitution world; `distᴿ` is **not**
a rule in the renaming world — decision 3 forbids it, since its pair with
`assocᴿ` demands the variable-level fold that push exists to avoid.

That single choice explains the shape of the completion in both worlds:

| | MapEnv/LiftEnv as rules? | companions needed |
|---|---|---|
| substitution world | yes (`dist`, `lift-cons`) | **exactly σ⇑'s five 2-rules** |
| renaming world | no (`distᴿ`, `lift-consᴿ` are lemmas) | σ⇑'s ShiftLift2 + Lift2, **plus** `interactᴿ-⨟ᴿ` and `lift-dist-compᴿᴿ-var` |

Why: in σ⇑ the term `↑∘((M·s)∘t)` is joinable *because MapEnv fires on the inner
composition* — `(M·s)∘t → M[t]·(s∘t)`, then ShiftCons. That is why σ⇑ needs no
"ShiftCons2". Withdraw MapEnv and the join disappears, so the ᴿ-world must post
`interactᴿ-⨟ᴿ` in its place. **The companion set is a function of which algebra
rules you keep**, not an arbitrary list.

---

## 3. Renaming world — 27 rules

### Iᴿ. Applied rules (variable meets map) — 5

| # | Agda | Rule | Origin | Purpose |
|---|---|---|---|---|
| 1 | `def-wkᴿ` | `x [ wkᴿ ]ᴿ s′ → suc x` | σ⇑ **VarShift1** | shift is successor; the rule that makes de Bruijn indices *native* — and thereby rules out η (§2.2) |
| 2 | `def-∙ᴿ-zero` | `zero [ (x ∙ᴿ ξ) ]ᴿ → x` | σw **FVar** | cons at the head |
| 3 | `def-∙ᴿ-suc` | `suc x′ [ (x ∙ᴿ ξ) ]ᴿ → x′ [ ξ ]ᴿ` | σw **RVar** | cons under a successor |
| 4 | `def-↑ᴿ-zero` | `zero [ (ξ ↑ᴿ s) ]ᴿ → zero` | σ⇑ **FVarLift1** | lift fixes the bound variable |
| 5 | `def-↑ᴿ-suc` | `suc x [ (ξ ↑ᴿ s) ]ᴿ → suc (x [ ξ ]ᴿ)` | σ⇑ **RVarLift1**, *strengthened* | σ⇑ gives `n+1[⇑s] → n[s∘↑]`; because renaming preserves the mode, `x [ ξ ]ᴿ` is already a variable, so we may apply VarShift1 on the spot and land in a strictly smaller normal form |

### IIᴿ. Traversal — 8 (one per constructor)

| # | Agda | Rule | Origin | Purpose |
|---|---|---|---|---|
| 6 | `instᴿ-x` | `(` x) [ ξ ]ᴿ → ` (x [ ξ ]ᴿ)` | σ⇑ — | the V/T injection commutes |
| 7 | `instᴿ-λ` | `(λx e) [ ξ ]ᴿ → λx (e [ (ξ ↑ᴿ _) ]ᴿ)` | σ⇑ **Lambda** | binder: push under a lift |
| 8 | `instᴿ-Λ` | `(Λα e) [ ξ ]ᴿ → Λα (e [ (ξ ↑ᴿ _) ]ᴿ)` | σ⇑ **Lambda** | binder |
| 9 | `instᴿ-∀` | `(∀[α∶ k ] t) [ ξ ]ᴿ → ∀[α∶ k [ ξ ]ᴿ ] (t [ (ξ ↑ᴿ _) ]ᴿ)` | σ⇑ **App+Lambda** | mixed: one non-binding, one binding position |
| 10 | `instᴿ-·` | `(e₁ · e₂) [ ξ ]ᴿ → (e₁ [ ξ ]ᴿ) · (e₂ [ ξ ]ᴿ)` | σw **App** | non-binding node |
| 11 | `instᴿ-•` | `(e • t) [ ξ ]ᴿ → (e [ ξ ]ᴿ) • (t [ ξ ]ᴿ)` | σw **App** | non-binding, cross-sort |
| 12 | `instᴿ-⇒` | `(t₁ ⇒ t₂) [ ξ ]ᴿ → (t₁ [ ξ ]ᴿ) ⇒ (t₂ [ ξ ]ᴿ)` | σw **App** | non-binding |
| 13 | `instᴿ-*` | `* [ ξ ]ᴿ → *` | σw **App** (nullary) | closed leaf |

*Schematic*: one rule per constructor, `↑ᴿ` inserted at each binding position.
This is the only part of the system that depends on the object signature, and the
only part the generator must read the `.sg` file for.

### IIIᴿ. Map algebra — 4

| # | Agda | Rule | Origin | Purpose |
|---|---|---|---|---|
| 14 | `assocᴿ` | `(ξ₁ ⨟ᴿ ξ₂) ⨟ᴿ ξ₃ → ξ₁ ⨟ᴿ (ξ₂ ⨟ᴿ ξ₃)` | σw **AssEnv** | right-nest compositions; fixes the shape all `-⨟ᴿ` companions must anticipate |
| 15 | `comp-idₗᴿ` | `idᴿ ⨟ᴿ ξ → ξ` | σw **IdL** | left unit |
| 16 | `comp-idᵣᴿ` | `ξ ⨟ᴿ idᴿ → ξ` | σ⇑ **IdR** | right unit |
| 17 | `interactᴿ` | `wkᴿ s ⨟ᴿ (x ∙ᴿ ξ) → ξ` | σw **ShiftCons** | shift cancels a cons |
| — | *`distᴿ`* | *(MapEnv)* | σw **MapEnv** | **demoted to a lemma** — see §2.1 |

### IVᴿ. Lifting — 3

| # | Agda | Rule | Origin | Purpose |
|---|---|---|---|---|
| 18 | `lift-idᴿ` | `idᴿ ↑ᴿ s → idᴿ` | σ⇑ **LiftId** | lifting the identity |
| 19 | `lift-dist-compᴿᴿ` | `(ξ₁ ↑ᴿ s) ⨟ᴿ (ξ₂ ↑ᴿ s) → (ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s` | σ⇑ **Lift1** | lift is functorial — the rule that lets nested binders collapse |
| 20 | `lift-wkᴿ` | `wkᴿ s ⨟ᴿ (ξ ↑ᴿ s) → ξ ⨟ᴿ wkᴿ s` | σ⇑ **ShiftLift1** | shift commutes past a lift |
| — | *`lift-consᴿ`* | *(LiftEnv)* | σ⇑ **LiftEnv** | **demoted to a lemma** — §2.1 |

### Vᴿ. Monad laws — 3

| # | Agda | Rule | Origin | Purpose |
|---|---|---|---|---|
| 21 | `right-idᴿ` | `x/t [ idᴿ ]ᴿ → x/t` | σ⇑ **Id** | right identity. **Mode-generic**: renaming preserves the mode, so this one rule is simultaneously σ⇑'s law on terms and its variable instance |
| 22 | `compositionalityᴿᴿ-var` | `x [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ → (x [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ` | **new** (Clos at V, *reversed*) | **push**. Must point this way: a fold at V would leave `(x [ ξ₁ ]ᴿ) [ wkᴿ ]ᴿ s` reducible to `suc (x [ ξ₁ ]ᴿ)` on one side and stuck as `x [ (ξ₁ ⨟ᴿ wkᴿ s) ]ᴿ` on the other |
| 23 | `compositionalityᴿᴿ` | `(t [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ → t [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ` | σ⇑ **Clos** (at T) | **fold**. The one place the V/T merge does not pay: the two halves point in opposite directions |

### VIᴿ. Completion companions — 4

Composition is right-nested by `assocᴿ`, so any rule whose LHS ends in a
composition needs a variant that sees through a continuation `ξ′`.

| # | Agda | Rule | Origin | Purpose |
|---|---|---|---|---|
| 24 | `lift-dist-compᴿᴿ-var` | `(x [ (ξ₁ ↑ᴿ s) ]ᴿ) [ (ξ₂ ↑ᴿ s) ]ᴿ → x [ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s) ]ᴿ` | **new** | join of *push* (22) with Lift1 (19) at an abstract variable — neither side can case-split |
| 25 | `interactᴿ-⨟ᴿ` | `wkᴿ s ⨟ᴿ ((x ∙ᴿ ξ) ⨟ᴿ ξ′) → ξ ⨟ᴿ ξ′` | **new** (a "ShiftCons2") | σ⇑ needs no such rule because MapEnv rescues the pair; we withdrew MapEnv, so we must post this — see §2.1 |
| 26 | `lift-wkᴿ-⨟ᴿ` | `wkᴿ s ⨟ᴿ ((ξ ↑ᴿ s) ⨟ᴿ ξ′) → ξ ⨟ᴿ (wkᴿ s ⨟ᴿ ξ′)` | σ⇑ **ShiftLift2** | continuation form of 20 |
| 27 | `lift-dist-compᴿᴿ-⨟ᴿ` | `(ξ₁ ↑ᴿ s) ⨟ᴿ ((ξ₂ ↑ᴿ s) ⨟ᴿ ξ′) → ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s) ⨟ᴿ ξ′` | σ⇑ **Lift2** | continuation form of 19 |

---

## 4. Substitution world — 27 rules

### Iˢ. Applied rules — 5

There is no `def-idˢ` and no `def-wkˢ`: `idˢ = ⟨ idᴿ ⟩` and `wkˢ = ⟨ wkᴿ ⟩` are
*embedded renamings*, so their applied rules are instances of `coincidence-var`.
Likewise σ⇑'s **Id** on terms is covered by `coincidence` then `right-idᴿ`.

| # | Agda | Rule | Origin | Purpose |
|---|---|---|---|---|
| 28 | `coincidence-var` | `x [ ⟨ ξ ⟩ ]ˢ → ` (x [ ξ ]ᴿ)` | **new** | the coercion's applied rule; subsumes σ⇑'s VarShift1 and Id at variables |
| 29 | `def-∙ˢ-zero` | `zero [ (t ∙ˢ σ) ]ˢ → t` | σw **FVar** | cons at the head |
| 30 | `def-∙ˢ-suc` | `suc x [ (t ∙ˢ σ) ]ˢ → x [ σ ]ˢ` | σw **RVar** | cons under a successor |
| 31 | `def-↑ˢ-zero` | `zero [ (σ ↑ˢ s) ]ˢ → ` zero` | σ⇑ **FVarLift1** | lift fixes the bound variable |
| 32 | `def-↑ˢ-suc` | `suc x [ (σ ↑ˢ s) ]ˢ → x [ (σ ⨟ ⟨ wkᴿ s ⟩) ]ˢ` | σ⇑ **RVarLift1** | exact match — here the mode *does* change (a substituted variable is a term), so no strengthening is available, unlike rule 5 |

### IIˢ. Traversal — 8

| # | Agda | Rule | Origin |
|---|---|---|---|
| 33 | `inst-x` | `(` x) [ σ ]ˢ → x [ σ ]ˢ` | σ⇑ — (V/T injection *absorbed*, not commuted: substitution takes a variable to a term) |
| 34 | `inst-λ` | `(λx e) [ σ ]ˢ → λx (e [ (σ ↑ˢ _) ]ˢ)` | σ⇑ **Lambda** |
| 35 | `inst-Λ` | `(Λα e) [ σ ]ˢ → Λα (e [ (σ ↑ˢ _) ]ˢ)` | σ⇑ **Lambda** |
| 36 | `inst-∀` | `(∀[α∶ k ] t) [ σ ]ˢ → ∀[α∶ k [ σ ]ˢ ] (t [ (σ ↑ˢ _) ]ˢ)` | σ⇑ **App+Lambda** |
| 37 | `inst-·` | `(e₁ · e₂) [ σ ]ˢ → (e₁ [ σ ]ˢ) · (e₂ [ σ ]ˢ)` | σw **App** |
| 38 | `inst-•` | `(e • t) [ σ ]ˢ → (e [ σ ]ˢ) • (t [ σ ]ˢ)` | σw **App** |
| 39 | `inst-⇒` | `(t₁ ⇒ t₂) [ σ ]ˢ → (t₁ [ σ ]ˢ) ⇒ (t₂ [ σ ]ˢ)` | σw **App** |
| 40 | `inst-*` | `* [ σ ]ˢ → *` | σw **App** |

### IIIˢ/IVˢ. Map algebra and lifting — 8

| # | Agda | Rule | Origin | Purpose |
|---|---|---|---|---|
| 41 | `assoc` | `(σ₁ ⨟ σ₂) ⨟ σ₃ → σ₁ ⨟ (σ₂ ⨟ σ₃)` | σw **AssEnv** | right-nesting |
| 42 | `dist` | `(t ∙ˢ σ₁) ⨟ σ₂ → (t [ σ₂ ]ˢ) ∙ˢ (σ₁ ⨟ σ₂)` | σw **MapEnv** | **kept** here (contrast `distᴿ`, §2.1) |
| 43 | `interact` | `⟨ wkᴿ s ⟩ ⨟ (t ∙ˢ σ) → σ` | σw **ShiftCons** | shift cancels a cons |
| 44 | `comp-idₗ` | `⟨ idᴿ ⟩ ⨟ σ → σ` | σw **IdL** | left unit |
| 45 | `comp-idᵣ` | `σ ⨟ ⟨ idᴿ ⟩ → σ` | σ⇑ **IdR** | right unit |
| 47 | `lift-wk` | `⟨ wkᴿ s ⟩ ⨟ (σ ↑ˢ s) → σ ⨟ ⟨ wkᴿ s ⟩` | σ⇑ **ShiftLift1** | shift past a lift |
| 48 | `lift-cons` | `(σ ↑ˢ s) ⨟ (t ∙ˢ τ) → t ∙ˢ (σ ⨟ τ)` | σ⇑ **LiftEnv** | cons absorbs a lift — this is what makes β definitional |
| 49 | `lift-dist-compˢˢ` | `(σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s) → (σ₁ ⨟ σ₂) ↑ˢ s` | σ⇑ **Lift1** | lift is functorial |

### Vˢ. Monad law — 1

| # | Agda | Rule | Origin | Purpose |
|---|---|---|---|---|
| 50 | `compositionalityˢˢ` | `(x/t [ σ₁ ]ˢ) [ σ₂ ]ˢ → x/t [ (σ₁ ⨟ σ₂) ]ˢ` | σ⇑ **Clos** | **mode-generic and always folds.** No V/T split needed: a substituted variable is a *term*, which no applied rule can match, so the obstruction behind rules 22/23 simply does not arise |

### VIˢ. Completion companions — 5

Exactly σ⇑'s five 2-suffixed rules, and no more — because the substitution world
keeps MapEnv (§2.1). The criterion is sharp: *a companion is needed exactly for
the `⨟`-stuck formers `⟨_⟩`, `↑ˢ`* — which is why the cons rules have no
2-variants.

| # | Agda | Rule | Origin |
|---|---|---|---|
| 51 | `compositionalityᴿˢ-⨟-var` | `x [ (⟨ ξ ⟩ ⨟ σ) ]ˢ → (x [ ξ ]ᴿ) [ σ ]ˢ` | σ⇑ **VarShift2**, generalised from `↑` to an arbitrary embedded renaming |
| 52 | `def-↑ˢ-zero-⨟` | `zero [ ((σ ↑ˢ s) ⨟ τ) ]ˢ → zero [ τ ]ˢ` | σ⇑ **FVarLift2** |
| 53 | `def-↑ˢ-suc-⨟` | `suc x [ ((σ ↑ˢ s) ⨟ τ) ]ˢ → x [ (σ ⨟ (⟨ wkᴿ s ⟩ ⨟ τ)) ]ˢ` | σ⇑ **RVarLift2** |
| 54 | `lift-wk-⨟` | `⟨ wkᴿ s ⟩ ⨟ ((σ ↑ˢ s) ⨟ τ) → σ ⨟ (⟨ wkᴿ s ⟩ ⨟ τ)` | σ⇑ **ShiftLift2** |
| 55 | `lift-dist-compˢˢ-⨟` | `(σ₁ ↑ˢ s) ⨟ ((σ₂ ↑ˢ s) ⨟ τ) → ((σ₁ ⨟ σ₂) ↑ˢ s) ⨟ τ` | σ⇑ **Lift2** |

---

## 5. Cross-world rules — 10 (all new)

These have **no σ⇑ counterpart**: σ⇑ has one map sort. They are the price of
first-class renamings, i.e. of the AS2 §4 axis, and they are what makes
context-morphism lemmas and anti-renaming statable at all.

| # | Agda | Rule | Purpose |
|---|---|---|---|
| 56 | `compositionalityᴿˢ` | `(t [ ξ₁ ]ᴿ) [ σ₂ ]ˢ → t [ (⟨ ξ₁ ⟩ ⨟ σ₂) ]ˢ` | Autosubst's `compRenSubst`. **T-only**: its V-instance is `compositionalityᴿˢ-⨟-var` read backwards, and registering both **loops** — 56 folds `(x [ ξ ]ᴿ) [ σ ]ˢ` into `x [ (⟨ξ⟩ ⨟ σ) ]ˢ` and 51 pushes it straight back |
| 57 | `compositionalityˢᴿ` | `(x/t [ σ₁ ]ˢ) [ ξ₂ ]ᴿ → x/t [ (σ₁ ⨟ ⟨ ξ₂ ⟩) ]ˢ` | Autosubst's `compSubstRen`. Mode-generic (the result of `_[_]ˢ` is a term either way) |
| 58 | `lift-dist-compᴿˢ` | `⟨ ξ ↑ᴿ s ⟩ ⨟ (σ ↑ˢ s) → (⟨ ξ ⟩ ⨟ σ) ↑ˢ s` | mixed **Lift1**, RS direction |
| 59 | `lift-dist-compˢᴿ` | `(σ ↑ˢ s) ⨟ ⟨ ξ ↑ᴿ s ⟩ → (σ ⨟ ⟨ ξ ⟩) ↑ˢ s` | mixed **Lift1**, SR direction |
| 60 | `lift-dist-compᴿˢ-⨟` | `⟨ ξ ↑ᴿ s ⟩ ⨟ ((σ ↑ˢ s) ⨟ τ) → ((⟨ ξ ⟩ ⨟ σ) ↑ˢ s) ⨟ τ` | mixed **Lift2** — same completion pattern as 55, one level up |
| 61 | `lift-dist-compˢᴿ-⨟` | `(σ ↑ˢ s) ⨟ (⟨ ξ ↑ᴿ s ⟩ ⨟ τ) → ((σ ⨟ ⟨ ξ ⟩) ↑ˢ s) ⨟ τ` | mixed **Lift2** |
| 62 | `lift-dist-compᴿˢ-var` | `(x [ (ξ ↑ᴿ s) ]ᴿ) [ (σ ↑ˢ s) ]ˢ → x [ ((⟨ ξ ⟩ ⨟ σ) ↑ˢ s) ]ˢ` | variable-level mixed fusion: the join of 51 with 58 at an abstract variable |
| 63 | `lift-dist-compᴿˢ-⨟-var` | `(x [ (ξ ↑ᴿ s) ]ᴿ) [ ((σ ↑ˢ s) ⨟ τ) ]ˢ → x [ (((⟨ ξ ⟩ ⨟ σ) ↑ˢ s) ⨟ τ) ]ˢ` | continuation form of 62 |
| 64 | `⟨⟩-lift-cons-var` | `(x [ (ξ ↑ᴿ s) ]ᴿ) [ (t ∙ˢ σ) ]ˢ → x [ (t ∙ˢ (⟨ ξ ⟩ ⨟ σ)) ]ˢ` | variable-level LiftEnv against a lifted embedded renaming |
| 65 | `⟨⟩-lift-cons` | `⟨ ξ ↑ᴿ s ⟩ ⨟ (t ∙ˢ σ) → t ∙ˢ (⟨ ξ ⟩ ⨟ σ)` | σ⇑'s **LiftEnv**, `⟨_⟩`-flavoured |

---

## 6. The `⟨_⟩`-collapse family — 8 (all new)

`⟨_⟩` gives a *second spelling* for every renaming-shaped substitution. Left
alone, the bare forms would compete with the ᴿ-forms as normal forms. These
rules say that an embedded renaming interacts with the σ-operations exactly as
its ᴿ-original does, and push it back into the ᴿ world.

| # | Agda | Rule | Purpose |
|---|---|---|---|
| 66 | `coincidence` | `t [ ⟨ ξ ⟩ ]ˢ → t [ ξ ]ᴿ` | **the orientation decision (§2.4)**: the renaming world is the normal form. Also discharges σ⇑'s **Id** on terms, via `right-idᴿ` |
| 67 | `⟨⟩-comp` | `⟨ ξ₁ ⟩ ⨟ ⟨ ξ₂ ⟩ → ⟨ ξ₁ ⨟ᴿ ξ₂ ⟩` | the coercion is a homomorphism for composition |
| 68 | `⟨⟩-split-⨟` | `⟨ ξ₁ ⨟ᴿ ξ₂ ⟩ ⨟ σ → ⟨ ξ₁ ⟩ ⨟ (⟨ ξ₂ ⟩ ⨟ σ)` | re-splits under a continuation, where 67 cannot see |
| 69 | `⟨⟩-lift` | `⟨ ξ ⟩ ↑ˢ s → ⟨ ξ ↑ᴿ s ⟩` | homomorphism for lifting |
| 71 | `⟨⟩-comp-⨟-lift-wkᴿ` | `⟨ wkᴿ s ⟩ ⨟ (⟨ ξ ↑ᴿ s ⟩ ⨟ τ) → ⟨ ξ ⟩ ⨟ (⟨ wkᴿ s ⟩ ⨟ τ)` | continuation form; **not** derivable from 67, which cannot see through an abstract `τ` |
| 73 | `⟨⟩-comp-⨟-interactᴿ` | `⟨ wkᴿ s ⟩ ⨟ (⟨ x ∙ᴿ ξ ⟩ ⨟ τ) → ⟨ ξ ⟩ ⨟ τ` | continuation form |
| 75 | `⟨⟩-comp-⨟-lift-dist-compᴿᴿ` | `⟨ ξ₁ ↑ᴿ s ⟩ ⨟ (⟨ ξ₂ ↑ᴿ s ⟩ ⨟ τ) → ⟨ (ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s ⟩ ⨟ τ` | continuation form |
| 76 | `⟨⟩-split-tail` | `(σ ↑ˢ s) ⨟ ⟨ (ξ ↑ᴿ s) ⨟ᴿ ξ′ ⟩ → ((σ ⨟ ⟨ ξ ⟩) ↑ˢ s) ⨟ ⟨ ξ′ ⟩` | the SR-fusion against a *continued* embedded renaming: the join of 61 with 67 |

The bare forms (70, 72, 74) are mostly derivable via `⟨⟩-comp`; the
`⨟`-continued ones (71, 73, 75) are **not** — an abstract continuation is opaque
to 67. This is the same phenomenon as σ⇑'s 2-rules, transposed to the coercion.

---

## 7. Proved but *not* registered — 9

(Ten rows below; `⟨⟩-cons` was retired outright and is no longer in the file.)

Every one of these is a **theorem** of the development; none is a rewrite rule.
Their absence is the design, not a gap.

| Agda | Statement | Source | Why not a rule |
|---|---|---|---|
| `distᴿ` | `(x ∙ᴿ ξ₁) ⨟ᴿ ξ₂ ≡ (x [ ξ₂ ]ᴿ) ∙ᴿ (ξ₁ ⨟ᴿ ξ₂)` | σw **MapEnv** | its pair with `assocᴿ` demands a variable-level fold, which *push* exists to avoid (§2.3, §2.1) |
| `lift-consᴿ` | `(ξ ↑ᴿ s) ⨟ᴿ (x ∙ᴿ ξ′) ≡ x ∙ᴿ (ξ ⨟ᴿ ξ′)` | σ⇑ **LiftEnv** | same reason: push already decomposes `∙ᴿ`-headed maps at variables |
| `⟨⟩-cons` | *(removed)* | **new** | the one member of the collapse family oriented ᴿ→ˢ; never registered and never used, so it was retired outright. Its ˢ→ᴿ mirror is the rule that would make `[]-as-ren` definitional — see §7.1 |
| `η-idᴿ` | `zero ∙ᴿ wkᴿ s ≡ idᴿ` | σ_SP fig. 4.1; AS2 fig. 2(a) `0 , ↑ ≡ id` | **surjective pairing.** Non-left-linear LHS conflicts with `def-wkᴿ` (§2.2) |
| `η-lawᴿ` | `(zero [ ξ ]ᴿ) ∙ᴿ (wkᴿ s ⨟ᴿ ξ) ≡ ξ` | σ_SP; AS2 `σ 0 , ↑ ⨟ᴿ σ ≡ σ` | as above |
| `η-id` | `(` zero) ∙ˢ wkˢ s ≡ idˢ` | σ_SP; AS2 | as above |
| `η-law` | `(zero [ σ ]ˢ) ∙ˢ (wkˢ s ⨟ σ) ≡ σ` | σ_SP; AS2 | as above |
| `def-↑ᴿ` | `ξ ↑ᴿ s ≡ zero ∙ᴿ (ξ ⨟ᴿ wkᴿ s)` | Abadi; AS2 fig. 2(b) | we keep `⇑` **primitive** (§2.1); this is the *definition* others use, demoted to a lemma |
| `def-↑ˢ` | `σ ↑ˢ s ≡ (` zero) ∙ˢ (σ ⨟ wkˢ s)` | Abadi; AS2 fig. 2(b) | as above |
| `lift-id` | `⟨ idᴿ ⟩ ↑ˢ s ≡ ⟨ idᴿ ⟩` | σ⇑ **LiftId** | **subsumed**, not excluded: `⟨⟩-lift` plus `lift-idᴿ` already reach the same normal form, so registering it adds nothing (§2, *Retired and subsumed*) |

Measured consequence: across the ~8700 lines of POPLmark metatheory built on this
system, **none of these nine is ever applied by hand**, and no `subst` transports
along a σ-law.

---

## 8. Counts

| Group | Registered | of which new |
|---|---|---|
| Iᴿ–VIᴿ renaming world | 27 | 3 (`compositionalityᴿᴿ-var`, `lift-dist-compᴿᴿ-var`, `interactᴿ-⨟ᴿ`) |
| Iˢ–VIˢ substitution world | 27 | 1 (`coincidence-var`) + 1 generalised (`compositionalityᴿˢ-⨟-var`) |
| cross-world | 10 | 10 |
| `⟨⟩`-collapse | 8 | 8 |
| **total** | **72** | **22** |
| stated as lemmas only | 9 | — |

Signature-dependent: 16 of the 72 (`instᴿ-*`, `inst-*`), i.e. two per
constructor. Everything else is schematic — which is why
[`poplmark/gen/agdasubst.py`](poplmark/gen/agdasubst.py) needs only the
constructor list from a `.sg` file.

**50 of 72 rules are σw/σ⇑ rules or their exact two-world duplicates.** The
system is not a new calculus: it is σ⇑ instantiated twice — once erased, once
not — plus 19 rules that reconcile the two copies (10 cross-world, 8 collapse,
and `coincidence-var`), plus 3 forced by native inductive variables and the
resulting V/T mode split (`compositionalityᴿᴿ-var`, `lift-dist-compᴿᴿ-var`,
`interactᴿ-⨟ᴿ`).
