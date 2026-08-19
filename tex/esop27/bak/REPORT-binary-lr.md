# A binary logical relation on top of `SystemF-strat.agda`

**File:** `esop27/SystemF-binary.agda` — 630 lines.
**Status:** `agda SystemF-binary.agda` → **exit 0**, clean rebuild (both `SystemF-strat`
and `SystemF-binary` from scratch, `--rewriting --local-confluence-check`) in **77 s**.
No warnings, no unsolved metas.
**Holes: none. Postulates: none** beyond `fun-ext`, which is inherited from
`SystemF-strat` (that file's only postulate).
No existing file was modified. `SystemF-strat.agda`, `SystemF.agda`, `STLC.agda`,
`main.tex`, `runagdatex` are byte-identical; the paper still builds.

---

## 1. What Saffrich / Thiemann / Weidner actually do

Two papers are relevant, and the first one has **no logical relation at all**:

* Thiemann & Weidner, *Towards Tagless Interpretation of Stratified System F*,
  TyDe'23 extended abstract, <https://tydeworkshop.org/2023-abstracts/paper15.pdf>.
  This is a purely denotational tagless interpreter for Leivant's finitely stratified
  System F. Object levels map onto Agda universe levels; `⟦_⟧ : Type Δ l → Env* Δ → Set l`;
  the domain environment `DEnv` lives in `Setω`. Its "Future Work" says a small-step
  semantics and an adequacy theorem are still to come. *(Caveat: an automated summariser
  claimed this abstract contains a binary logical relation. It does not — I read the PDF.)*

* Saffrich, Thiemann & Weidner, *Intrinsically Typed Syntax, a Logical Relation, and the
  Scourge of the Transfer Lemma*, TyDe'24, DOI
  [10.1145/3678000.3678201](https://dl.acm.org/doi/10.1145/3678000.3678201).
  ACM DL is paywalled, but the **paper source and full Agda artifact are public**:
  <https://github.com/proglang/SystemF> (LaTeX at `tex-2024-05/main-tyde24.tex`,
  Agda at `src/StratF/`). ~7.8 kLoC of Agda.

### Their construction, precisely

Their relation **is binary, but not parametricity**. They say so explicitly (§5):

> "Our relation is not the 'standard' binary logical relation that relates two expressions
> with the goal of proving contextual equivalence or parametricity under a small-step
> operational semantics. We rather follow Benton et al. and relate an expression under
> big-step semantics to its denotational semantics."

So the two sides are **heterogeneous — syntax × denotation**:

```agda
REL : Type [] l → Set (suc l)
REL {l} T = CValue T → ⟦ T ⟧ [] → Set l        -- StratF/LogicalPrelim.agda
```

with clauses (`StratF/Logical.agda`):

```agda
𝓥⟦ `ℕ ⟧ ρ u z         = ∃[ n ] (exp u ≡ # n) ∧ (n ≡ z)
𝓥⟦ T₁ ⇒ T₂ ⟧ ρ u f    = ∃[ e ] (exp u ≡ ƛ e) ∧
                          ∀ w z → 𝓥⟦ T₁ ⟧ ρ w z → 𝓔⟦ T₂ ⟧ ρ (e [ exp w ]E) (f z)
𝓥⟦ ` α ⟧ ρ v z        = π₂ ρ _ α v (subst id (subst-var-preserves α (π₁ ρ) []) z)
𝓥⟦ `∀α l , T ⟧ ρ u F  = ∃[ e ] (exp u ≡ Λ l ⇒ e) ∧ ∀ T′ R → ∃[ v ] (e [ T′ ]ET ⇓ v) ∧
                          𝓥⟦ T ⟧ (REext ρ (T′ , R))
                            (subst CValue (RE-ext∘lift ρ T T′ R) v) (F (⟦ T′ ⟧ []))
𝓔⟦ T ⟧ ρ e z          = ∃[ v ] (e ⇓ v) ∧ 𝓥⟦ T ⟧ ρ v z
```

Relation environments and term environments:

```agda
𝓓⟦ Δ ⟧ = ∀ l → l ∈ Δ → Σ (Type [] l) REL          -- in Setω
π₁ ρ l x = proj₁ (ρ l x)                           -- the closing type substitution
Tren-act : TRen Δ₁ Δ₂ → 𝓓⟦ Δ₂ ⟧ → 𝓓⟦ Δ₁ ⟧         -- renaming acts on relation envs
𝓖⟦ Γ ⟧ ρ χ γ                                       -- related closing value substitutions
```

Main theorem (`StratF/Fundamental.agda`) plus its corollary:

```agda
Γ ⊨ e ⦂ T = (ρ : 𝓓⟦ Δ ⟧) (χ : CSub (π₁ ρ) Γ) (γ : Env Δ Γ ⟦ π₁ ρ ⟧*[]) →
            𝓖⟦ Γ ⟧ ρ χ γ → 𝓔⟦ T ⟧ ρ (Csub χ e) (E⟦ e ⟧ η γ)
fundamental : ∀ Γ T (e : Expr Δ Γ T) → Γ ⊨ e ⦂ T
adequacy    : ∀ (e : CExpr `ℕ) n → E⟦ e ⟧ [] γ₀ ≡ n → e ⇓ (# n , V-♯)
```

Semantics is **big-step CBV**, and `⇓` relates a closed expression to a `CValue`
(an expression paired with a value proof), *not* to another expression — they report
that relating two expressions "works almost all the way" but fails in the variable case,
because a variable's type can itself be a type variable and its value shape is then unknown.

The **"scourge"** is their name for `subst` appearing in *statements*, not just proofs.
Because expression substitutions are indexed by a type substitution, the fusion lemma
`Esub σ₂ (Esub σ₁ e) ≡ Esub (σ₁ ∘ₛₛ σ₂) (σ₁ >>SS σ₂)` only typechecks under a `subst`,
and the type-application case of that proof carries **eight nested `subst`s**. The pain
propagates all the way into the logical relation itself: their `LRVren-eq′` has a
`subst₂` **in the statement of a lemma about the relation**, transporting `𝓥⟦_⟧` along
both a type equality and a semantic-environment equality. `LRVren.agda` is 2013 lines and
`LRVsub.agda` is 2296 lines, almost entirely this bookkeeping.

### Consequence for this task

The brief asked for the *parametricity-style* binary relation. That is **not** what STW
built. I therefore kept their **proof architecture** (relation environments carrying a
closed type + a relation per type variable; renaming and substitution actions on relation
environments; a relational environment for term variables; a fundamental theorem
quantified over all of them) and instantiated the two sides **syntax × syntax**, which is
what the strat file's full-β + SN infrastructure actually supports. The correspondence is
noted at every section boundary in the Agda file.

---

## 2. What I built

`esop27/SystemF-binary.agda`, structured to shadow `SystemF-strat`'s §8–§19 and STW's
module map:

| § | Contents | mirrors strat | mirrors STW |
|---|---|---|---|
| B0 | `Reds-vars`, `SN-open`, `SN-open*` | (new) | — |
| B1 | `Rel`, `CR²`, `cr²-fwd*₁/₂` | `Pred`, `CR` | `REL` |
| B2 | `REnv`, `semR` | `Env`, `semE` | `𝓓⟦_⟧`, `π₁`/`π₂` |
| B3 | `⟦_⟧²`, `CREnv²` | `⟦_⟧`, `CREnv` | `𝓥⟦_⟧` |
| B4 | `⊛²`, `⊙²`, `⟦⟧²-ren`, `⟦⟧²-sub`, `⟦⟧²-[]*`, `⟦⟧²-weaken` | §11 | `Tren-act`/`Tsub-act`, `LRVren`, `LRVsub`, `LRVwk-eq` |
| B5 | `⟦⟧²-CR` | §15 | — |
| B6 | `⟦⟧²-β-λ-L/R`, `⟦⟧²-β-Λ-L/R` | §16 | — |
| B7 | `Reds²`, `Reds²-var`, `Reds²-wk` | §17 | `𝓖⟦_⟧`, `𝓖-lookup` |
| B8 | `fundamental²` | §18 | `fundamental`/`semantic-soundness` |
| B9 | `parametricity`, `free-theorem-𝔹ᶜ` | §19 | `adequacy` |

The relation itself:

```agda
Rel : ∀ {l} → Type ∅ l → Type ∅ l → Set (lsuc l)
Rel {l} A B = (Γ : Ctx ∅) → Expr Γ A → Expr Γ B → Set l

⟦_⟧² : ∀ {Δ l} (T : Type Δ l) {η₁ η₂ : Sub Δ ∅} → REnv Δ η₁ η₂ → Rel (T [ η₁ ]ˢ) (T [ η₂ ]ˢ)
⟦ ` α ⟧²     {η₁} {η₂} ρ = semR α η₁ η₂ ρ
⟦ base l ⟧²  ρ Γ e₁ e₂ = Lift l ⊤
⟦ T₁ ⇒ T₂ ⟧² {η₁} {η₂} ρ Γ e₁ e₂ =
  ∀ {Γ′} (w : Γ ⊆ Γ′) a₁ a₂ → ⟦ T₁ ⟧² ρ Γ′ a₁ a₂ →
    ⟦ T₂ ⟧² ρ Γ′ (ren⊆ w e₁ · a₁) (ren⊆ w e₂ · a₂)
⟦ ∀α_ {l = l} T ⟧² {η₁} {η₂} ρ Γ e₁ e₂ =
  ∀ {Γ′} (w : Γ ⊆ Γ′) (S₁ S₂ : Type ∅ l) (R : Rel S₁ S₂) → CR² R →
    ⟦ T ⟧² {S₁ ∙ˢ η₁} {S₂ ∙ˢ η₂} (R , ρ) Γ′ (ren⊆ w e₁ ·* S₁) (ren⊆ w e₂ ·* S₂)
```

---

## 3. How far I got

**All the way to the fundamental theorem, and past it to a parametricity corollary.**

```agda
fundamental² :
  ∀ {Δ} {Γ : Ctx Δ} {l} {T : Type Δ l} (e : Expr Γ T)
    {η₁ η₂ : Sub Δ ∅} (ρ : REnv Δ η₁ η₂) (c : CREnv² ρ)
    {Γ′ : Ctx ∅} (σ₁ : η₁ ∣ Γ ⇒ˢ Γ′) (σ₂ : η₂ ∣ Γ ⇒ˢ Γ′) → Reds² Γ ρ σ₁ σ₂ →
    ⟦ T ⟧² ρ Γ′ (η₁ ∣ e [ σ₁ ]ˢ) (η₂ ∣ e [ σ₂ ]ˢ)

parametricity : ∀ {l} {T : Type ∅ l} (e : Expr ∅ T) → ⟦ T ⟧² {idˢ} {idˢ} ρ∅² ∅ e e

free-theorem-𝔹ᶜ :
  ∀ (e : Expr ∅ 𝔹ᶜ) (S₁ S₂ : Type ∅ lzero) (R : Rel S₁ S₂) (cr : CR² R)
    (a₁ b₁ : Expr ∅ S₁) (a₂ b₂ : Expr ∅ S₂) →
    R ∅ a₁ a₂ → R ∅ b₁ b₂ →
    R ∅ (((e ·* S₁) · a₁) · b₁) (((e ·* S₂) · a₂) · b₂)
```

`free-theorem-𝔹ᶜ` is Reynolds' abstraction theorem for `𝔹ᶜ = ∀α. α ⇒ α ⇒ α`, at **two
different type instantiations** — a statement STW's syntax-vs-denotation relation cannot
even express.

**Remaining holes: none. Remaining postulates: none.**
(Inherited: `SystemF-strat`'s `fun-ext : Extensionality`. Nothing else. No `--type-in-type`,
no `TERMINATING`, no `trustMe`.)

### What I deliberately did *not* attempt

`⟦ base l ⟧²` is `Lift l ⊤` — the top candidate, mirroring the unary `⟦ base l ⟧ = SN`,
which is equally uninformative. Making it finer (e.g. "both sides reduce to the same
Church boolean") is not possible with the current strat file: forward closure of such a
relation needs **confluence** of full β, and standardisation for the converse. Neither is
proved in `SystemF-strat`. So the honest ceiling here is the abstraction theorem plus
free theorems *relative to a user-supplied candidate*, which is what `free-theorem-𝔹ᶜ`
delivers. Deriving `e ·* S · a · b ⟶* a` or `⟶* b` from it would need that missing
confluence result.

---

## 4. Where stratification helped, and where it hurt

**Helped — decisively, and this is the whole point.** `Rel {l} A B : Set (lsuc l)`, so
the ∀-clause quantifies over `Rel S₁ S₂ : Set (lsuc l)` and `CR² R : Set l` and lands in
`Set (lsuc l ⊔ l′)` — *exactly* the level Agda assigns to `∀α_ : Type Δ (lsuc l ⊔ l′)`.
The binary relation is definable **by the same arithmetic that makes the unary one work**,
with zero extra slack and no `--type-in-type`. Going binary costs nothing in level budget,
because both sides sit at the same object level `l`: `Expr Γ A → Expr Γ B → Set l` has the
same level as `Expr Γ A → Set l`. I did not have to touch a single level annotation
relative to the unary development.

Two smaller wins:

* `base l` at *every* level is what makes `SN-open*` possible (§B0): to reflect SN through
  a `▷*` binder I instantiate the type variable with `base l`. Without an inhabited closed
  type at every level, that trick is unavailable. This is the same reason the unary
  Λ-case needs `base l` for its `snBody`.
* `CREnv²` needs `Lift (lsuc l) (CR² R)` to sit in `maxL (l ∙ Δ) = lsuc l ⊔ maxL Δ`,
  which the strat file had already established as the right recursion.

**Hurt — mildly, and in exactly the places STW complain about.** `REnv` and `Env` are
*functions* defined by recursion on `Δ`, not records, because a `∀ {l : Level}` field
would land in `Setω`. (STW pay this in full: their `𝓓⟦_⟧`, `Env*` and `Env` are all
`Setω`, and they had to re-implement `cong`/`subst`/`trans`/equational reasoning at
`Setω` in `StratF/Util/PropositionalSetOmegaEquality.agda`. This development sidesteps
that entirely by making the environment level-computing rather than level-polymorphic.)
The cost is that `REnv Δ ?η₁ ?η₂` is not an injective unification problem, so **both**
realised substitutions must be passed explicitly at every call site of `semR`, `⊛²`,
`⊙²` — twice the boilerplate of the unary version, mechanically. And because
`REnv ∅ η₁ η₂ = ⊤`, the indices are genuinely undetermined at the base case; that
produced two rounds of "unsolved metavariable" errors, fixed by writing `{idˢ} {idˢ}`
explicitly in `SN-open`, `Reds-vars`, `parametricity` and `free-theorem-𝔹ᶜ`.

---

## 5. Reuse: what carried over unchanged, what had to be rebuilt

### Carried over verbatim, zero modification (imported from `SystemF-strat`)

The entire lower two-thirds of the development, which is the expensive part:

* the whole type-level σ-calculus and its `REWRITE` set (this is what buys transport-freeness);
* expression renaming/substitution, `Identityᵣ`, all four `Compositionality*`, `Coincidence`;
* `_⟶_`, `_⟶*_`, `SN`, `sn-fwd`, `progress`, `Normal`/`Neutral`, `Ne`;
* **the Kripke plumbing in full**: `_⊆_`, `⊆-var`, `⊆-ren`, `ren⊆`, `⊆-trans`,
  `⊆-var-trans`, `ren⊆-refl`, `ren⊆-trans`. Not one line changed. The binary relation
  weakens both sides in lockstep along a single `w : Γ ⊆ Γ′`, so a single Kripke world
  suffices and the unary plumbing is exactly right;
* **`⟶-ren-inv` and everything feeding it** — `LamView`/`lamView`, `ne-app-inv`,
  `ne-tapp-inv`, `ren-inv-·`, `ren-inv-·*`, `β-λ-ren`, `β-Λ-ren`, `Ne-ren`, `⟶-ren`,
  `sn-ren`, `sn-ren⊆`. This is the single most valuable import: it is ~120 lines of
  delicate coverage-dodging, it is used four times in `⟦⟧²-CR`, and it needed **no**
  generalisation for the binary case (each side is inverted independently);
* `⟶-sub`, `sn-sub`, `sub-⟶*`, `sub-cong`, `lift*-cons-sub`;
* `ren-lift-cons` and `ren-lift*-cons` — the two ugliest substitution lemmas in the file,
  reused **as-is**, just applied twice (once per side);
* and, crucially, **the unary fundamental theorem and `⟦⟧-CR` themselves**, used in §B0.

### Rebuilt

* `Pred → Rel`, `Env → REnv`, `semE → semR`, `⟦_⟧ → ⟦_⟧²`, `CREnv → CREnv²`: mechanical
  doubling, ~55 lines.
* `⊛/⊙` and `⟦⟧-ren`/`⟦⟧-sub` → `⊛²/⊙²`, `⟦⟧²-ren`/`⟦⟧²-sub` (§B4, 143 lines): also
  mechanical — the *pushed* renaming/substitution stays single, only the two *closing*
  substitutions double. Every proof is line-for-line the unary one with `η` replaced by
  `η₁ η₂`.
* `Reds → Reds²`, `Reds-var → Reds²-var`, `Reds-wk → Reds²-wk`: mechanical.
* `⟦⟧-CR → ⟦⟧²-CR` (§B5): **genuinely rebuilt**, see below.
* `⟦⟧-β-λ`/`⟦⟧-β-Λ` → four one-sided lemmas (§B6): **genuinely rebuilt**, see below.
* `SN-open`, `SN-open*` (§B0): new, 25 lines, but only assembles existing pieces.

### The two places where the binary case is not a mechanical doubling

**(a) `CR` → `CR²`.** The naive doubling — a symmetric `cr²-exp` requiring *both* sides
neutral and closure under stepping either side — is **not usable**. The λ-case of the
fundamental theorem produces two redexes `(λx b₁)·a₁` and `(λx b₂)·a₂` that reduce
*independently*: absorbing the left β-step needs `R (b₁[a₁]) ((λx b₂)·a₂)`, i.e. the left
side already contracted and the right side not. So CR3 must be **one-sided**, with the
opposite side entirely unconstrained.

But a one-sided CR3 cannot prove CR1: from `Ne e₁` and "all reducts of `e₁` are related to
`e₂`" one cannot extract `SN e₂` when `e₁` has no reducts. The fix is to **drop CR1 from
`CR²` altogether** and get SN from outside:

```agda
SN-open  : ∀ {Γ : Ctx ∅} {l} {T : Type ∅ l} (e : Expr Γ T) → SN e
SN-open* : ∀ {Γ : Ctx ∅} {l l′} {T : Type (l ∙ ∅) l′} (b : Expr (Γ ▷* l) T) → SN b
```

`SN-open` is the unary fundamental theorem applied to the *variable* substitution (whose
reducibility is exactly the `rsLift` step of the unary λ-case); `SN-open*` reflects SN
through a type binder by instantiating with `base l`. With those two lemmas the binary
relation carries **no SN component at all** — it is strictly *simpler* than the unary one,
and correspondingly `fundamental²` has no `snBody` obligation in its λ- or Λ-cases.

This is the one real design insight of the exercise: **once SN is a theorem, the binary
relation should not re-prove it.** The unary development is a genuine prerequisite of the
binary one, not a parallel track.

**(b) β-expansion.** For the same reason, `⟦⟧-β-λ` splits into `⟦⟧²-β-λ-L` and
`⟦⟧²-β-λ-R` (and likewise for Λ), each expanding one side with the other held abstract;
`fundamental²`'s λ-case composes them (`-R` first, then `-L`). Each half is the unary
proof with the opposite side threaded through as a dead parameter, so the code is not
harder — there is just twice as much of it, and it needs `cr²-fwd*₁`/`cr²-fwd*₂`
(multi-step forward closure) on the correct side.

One minor mechanical annoyance: `⟦ T₁ ⇒ T₂ ⟧²` unfolds to a Π-type, so the implicit `e₂`
in a hypothesis `∀ {u} → e₁ ⟶ u → ⟦ T₁ ⇒ T₂ ⟧² ρ Γ u e₂` is not recoverable by
unification. The four inner helpers `aux₁/aux₂/hyp₁/hyp₂` therefore take both terms
**explicitly**. Same phenomenon the strat file already documents for `Env`.

---

## 6. Transport count

**12 transports in the whole file** (`subst` ×2, `subst₂` ×10), against **12** in
`SystemF-strat.agda`. Restricting to the comparable region (the logical-relation part,
strat §15–§19 vs. binary §B5–§B9) it is **8 vs 8** in the core plus 4 in the corollary.

| line | form | what forces it |
|---|---|---|
| 360 | `subst₂` | `cr²-wk` at `⇒`: `ren⊆-trans`, composing two Kripke weakenings — both sides |
| 407 | `subst₂` | `cr²-wk` at `∀`: same |
| 528 | `subst` | `Reds²-var`, `suc*` case: `⟦⟧²-weaken`. **This is STW's `LRVwk-eq`** |
| 559 | `subst₂` | `fundamental²` `·`-case: `ren⊆-refl` (the relation is Kripke, application is not) |
| 563 | `subst` | `fundamental²` `·*`-case: `⟦⟧²-[]*`, i.e. `⟦T[S]*⟧² = ⟦T⟧²(⟦S⟧², ρ)` |
| 565 | `subst₂` | `fundamental²` `·*`-case: `ren⊆-refl` |
| 573 | `subst₂` | `fundamental²` λ-case: `ren-lift-cons` (weaken-then-extend = extend-with-weakened) |
| 582 | `subst₂` | `fundamental²` Λ-case: `ren-lift*-cons` |
| 598 | `subst₂` | `parametricity`: `Identityᵣ`, `idˢ ∣ e [ Idˢ ]ˢ ≡ e` |
| 614, 624, 627 | `subst₂` ×3 | `free-theorem-𝔹ᶜ`: `ren⊆-refl` bookkeeping in the corollary |

Every one of these is *exactly* a unary transport with a second component bolted on
(`subst → subst₂`). **Going binary introduced no new class of transport.**

Two things carry no transport at all and are worth naming:

* **`⟦_⟧²` itself is transport-free.** The ∀-clause needs
  `(T [ ηᵢ ↑ˢ ]ˢ) [ Sᵢ ]* ≡ T [ Sᵢ ∙ˢ ηᵢ ]ˢ` and `(R , ρ) : REnv (l ∙ Δ) (S₁ ∙ˢ η₁) (S₂ ∙ˢ η₂)`,
  on *both* sides simultaneously. The registered type-level σ-rewrites make all of it
  definitional. **This is precisely where STW need `RE-ext∘lift` / `lemma1`.**
* **§B4 contains zero `subst`s, in statements or proofs.** `⟦⟧²-ren` and `⟦⟧²-sub` are
  bare `≡` between two applications of `⟦_⟧²`. Their counterparts `LRVren-eq′` and
  `LRVsub` carry a `subst₂` **in the statement**, and are 2013 + 2296 lines.
  Here they are **143 lines together**, transport-free. That ~30× is the σ-calculus-as-
  `REWRITE` design paying for itself, and it is the sharpest measurement this exercise
  produced.

---

## 7. Verdict: is the binary relation a natural fit for this infrastructure?

**Yes, and more comfortably than I expected — with two caveats.**

What works well:

1. **Predicativity is free.** Doubling the relation costs nothing in universe budget, and
   the `lsuc l ⊔ l′` arithmetic that the stratified `∀α_` already forces is *exactly*
   right for `Rel` and `CR²`. This is the strongest evidence I have that stratification is
   the right base for relational metatheory in Agda: the binary case is where impredicative
   formulations usually break, and here it simply did not come up.
2. **The transport story is the headline.** The type-level σ-calculus registered as
   confluent `REWRITE` rules kills the scourge STW report. Their two hardest modules —
   4.3 kLoC of `subst`-shuffling around `LRVren`/`LRVsub` — become 143 transport-free
   lines here. The doubling that makes those lemmas painful for them (two type
   substitutions, two semantic environments) is absorbed entirely by the rewrite system.
3. **The Kripke layer and `⟶-ren-inv` transferred with literally no change.** That was
   the part I expected to have to generalise, and I did not touch it.

The two caveats:

4. **The binary case forces a design change that is invisible in the unary case:** CR3 must
   be one-sided, which forces CR1 out of the candidate record, which makes the binary
   relation *depend on* the unary SN theorem rather than being independent of it. That is a
   real structural fact, not an artefact — it would show up in any full-β binary
   development. It is a happy dependency here (the unary theorem exists), but it means the
   binary file is genuinely a *layer on top of* the unary one, not a sibling.
5. **Under-determined indices are the recurring friction.** `REnv Δ η₁ η₂` with
   `REnv ∅ _ _ = ⊤` forces explicit `{idˢ} {idˢ}` annotations, and Π-typed unfoldings force
   explicit term arguments in four helpers. This is the price of the level-computing
   function-valued environment that avoids `Setω`; STW pay the `Setω` price instead and
   need a whole bespoke equality library for it. Given the choice, this side of the
   trade-off is clearly better, but it is not free.

Overall: the strat development is a *better* substrate for a binary logical relation than
for a unary one, because the binary case is where the transport burden would normally
explode and where the rewrite-based substitution calculus has the most to offer.
