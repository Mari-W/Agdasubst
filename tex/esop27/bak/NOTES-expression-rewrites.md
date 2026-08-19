# The expression rewrite set — why it is deregistered

Extracted verbatim from the header block of `SystemF.agda` (§5.2), which
now carries only a short pointer. Section 2 below is a later addendum
with measured numbers.

## 1. The original record (verbatim)

Every law in §5.2 is the exact mirror of a type-level law under the
dictionary Ren↦⇒ᴿ, Sub↦⇒ˢ, ⟨⟩↦⟪⟫, ↑↦⇑ (λ-dim) / ⇑* (Λ-dim), wkᴿ↦Wkᴿ/wkᴿ*,
weaken↦weaken*, and every one of them is an Agda THEOREM. As an
EQUATIONAL theory the mirror is therefore exact. As a REWRITE system it
cannot be, and the obstruction is intrinsic to the two-level structure
rather than an accident of curation:

> at the type level a rule rewrites TERMS;
> at the expression level it rewrites terms whose TYPE INDICES are
> themselves rewritten by the type-level system.

The obstruction is one of MATCHING, not of confluence. Agda matches
rewrite LHSs syntactically and first-order, over ALL arguments,
including the implicit type index. The outer traversal of
`Compositionality` carries the index `T [ η₁ ]ˢ`, and `_[_]ˢ` is defined
by exhaustive pattern matching on its first argument. So `T [ η₁ ]ˢ` is
a redex whenever `T` is in constructor form, and the head `_[_]ˢ`
survives normalisation ONLY when `T` is rigid-neutral, i.e. a variable.
Hence:

> a rewrite rule whose stored index is `T [ η₁ ]ˢ` fires exactly on
> those terms whose type is a VARIABLE, and on no others.

This is verified directly, by refl probes at abstract scopes. With
`Compositionalityˢˢ` registered, the probe at an abstract type `A`
joins; the probes at `A ⇒ B`, `∀α A`, and every deeper shape do NOT —
while the LEMMA applies at all of them. The equation holds; only the
rule fails to fire.

**Completion by instantiation does not converge.** Adding one instance
per type CONSTRUCTOR (`Comp-var`, `Comp-arr`, `Comp-fa`) makes the
depth-1 probes join and leaves the depth-2 ones stuck; adding the
depth-2 instances fixes those and leaves depth 3 stuck. Each instance
covers exactly one type shape, and there are infinitely many, so no
FINITE rewrite system covers the law. Notably this regress is not a
confluence phenomenon: none of these instance families introduces a
non-joinable pair that the base rule did not already have.

**Nor can `opaque` rescue it**, though it does solve the matching
problem outright. Wrapping the index in an opaque alias
`App T η ≔ T [ η ]ˢ` makes the stored pattern inert, and then ONE rule
fires at every type shape and every depth. But an opaque index is no
longer recognisable as an arrow, so `App (T₁ ⇒ T₂) η` cannot be
eliminated by `_·_` and intrinsic typing breaks; and restoring the
eliminator with a rule
`App (T₁ ⇒ T₂) η ≡ (App T₁ η) ⇒ (App T₂ η)` makes `App` compute again
and the pattern dies exactly as before. **The index must be INERT to be
matched and COMPUTING to be usable, and it is the same symbol.** That
trade-off, not curation, is what bounds the mirror.

Types escape all of this because a type-level rule's arguments are
SCOPES (naturals), which no rule rewrites; the recursion bottoms out at
`` `beta-fold ``, whose index is inert. The expression-level leaf case
carries the variable's TYPE instead, and that is arbitrary.

### The laws this excludes, with the offending computed index

| law | offending index |
|---|---|
| `Compositionality{ᴿᴿ,ᴿˢ,ˢᴿ,ˢˢ}` | `T [ η₁ ]ˢ` of the outer traversal |
| `Lift-Dist-Comp{ᴿᴿ,ᴿˢ,ˢᴿ,ˢˢ}` | ditto, inside `⇑ˢ (T [ η₁ ]ˢ)` |
| `Lift*-Dist-Comp{…}` | index `ζ₁ ↑ᴿ` / `η₁ ↑ˢ` |
| `Associativity{ᴿ,ˢ}` | explicit argument `η₁ ⨟ˢ η₂` |
| `Beta-comp{ᴿ,ˢ}` | index `T [ ζ₁ ]ᴿ` |
| `Beta-⇑{ᴿ,ˢ}-zero/suc` | hidden context `Γ₂ ▷ (T [ ζ ]ᴿ)` |

(`Associativity{ᴿ,ˢ}` is the one genuine confluence casualty rather than
a matching one: registered alone it reports 25 non-joinable pairs
against the type-level composition rules.)

Two remarks keep the mirror honest. FIRST, the Λ-dimension analogues of
the last family — `Beta-↑ᴿ*-suc*`, `Beta-⇑ˢ*-suc*` — ARE registrable:
`▷*` extends the context without computing an index, which is exactly
why the Λ-dimension survives where the λ-dimension does not. SECOND,
`Identityᵣ` needs no rule at all: with `Identityᵣᴿ` and `Coincidence`
registered its LHS `⟨idᴿ⟩ ∣ e [ Idˢ ]ˢ` already REDUCES to `e` (Agda
rejects the pragma for precisely that reason) — mirroring the type
level, where `identityᵣˢ` is likewise derived and unregistered.

**DEREGISTERED.** None of the expression-level laws is a REWRITE rule.
The set is not a usable rewrite system: as established, a rule whose
stored index is `T [ η₁ ]ˢ` fires only when `T` is a variable, so the
set is radically incomplete, and `Associativity{ᴿ,ˢ}` is genuinely
non-confluent besides. A rewrite system we cannot certify is one we do
not use. Every law remains an Agda THEOREM and is applied EXPLICITLY, by
`subst`/`cong`, at its use sites. That is Transfer Hell, stated honestly
rather than papered over.

## 2. Addendum — measured numbers

Later measurement of the claims above. Control: type-level rules only
= 0 non-joinable pairs, so the checker is live in every run.

**The curated mirror IS non-confluent**, staged registration of the §5.2
laws:

| registered | non-joinable pairs |
|---|---|
| β/lookup family (24 laws) | 105 |
| + algebra (Assoc / Distrib / Interact / Comp-id, 13) | 135 |
| + traversal laws (6) | 191 |

So the "obstruction is one of MATCHING, not of confluence" framing in §1
is too strong — confluence fails independently, and `Associativity` is
not the only casualty. Classifying the 105:

- **24 expr × expr** — all `Beta-comp{ᴿ,ˢ}` against the other β rules.
  These are §4-shaped and curable by the `-⨟` shifted-variant recipe.
- **81 expr × type-layer** — 30 against `_[_]ᴿ`'s own clauses, the rest
  against `beta-fold-ˢᴿ`, `compositionality{ᴿᴿ,ᴿˢ,ˢᴿ,ˢˢ}`, `identityᵣ`,
  `beta-fold`. Not curable by adding expression rules.

**Opacity on the type traversal changes nothing.** Making `_[_]ᴿ`/`_[_]ˢ`
opaque and re-installing their clauses as rewrite rules gives identical
counts (105 / 135 / 191). Withholding the `⇒`/`∀` clause rules instead
makes the index inert but kills the eliminator — the same
inert-vs-usable dilemma as §1's `App` alias, now on the real symbols.

**Paying transports instead trades down.** Keeping `Sub-⇒`/`Sub-∀` as
theorems rather than rules costs 8 transports just to define the two
traversals, +2 in the logical relation, and then forces all ~24
constructor clauses of `Compositionality*`/`Identityᵣ*` to reason under
`subst`. Against 9 σ-transports in the current design. Transports in a
DEFINITION are worse than in a proof: they stop the traversal computing,
so every downstream `refl` breaks.

**The positive half.** With the expression MAPS made opaque, all 19
traversal/lifting laws become registrable (vs 11/19 transparent — the 8
rejects are `RewriteLHSReduces` on η-reducing `compˢ`). And the traversal
laws DO fire on concrete terms, because the traversal computes
structurally into constructors and bottoms out at variables where the
map laws take over: `λx e` and `λx (Λα e)` at concrete arrow types join;
with transparent maps they do not. So "radically incomplete" overstates
it — the residual gap is exactly one shape: **an eliminator (`·`, `·*`)
whose head is an abstract term at a concrete type.**
