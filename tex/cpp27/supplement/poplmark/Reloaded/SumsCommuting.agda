{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLmark Reloaded STLC+: the COMMUTING CONVERSIONS, MEASURED ═══
--
-- Reloaded/SumsSoundness.agda and Reloaded/SumsNormalization.agda
-- cover the β-rules for sums and the congruences, but NOT the permutative
-- (commuting) conversions.  This module MEASURES what adding them would
-- cost, rather than estimating it.  Everything here typechecks; nothing
-- here is imported by the metatheory, and nothing here claims the
-- commuting conversions are proved -- they are not.
--
-- Three separate measurements:
--
--   (M1) Can the two permutative rules even be STATED in this
--        σ-calculus, and does RENAMING commute with them definitionally?
--        Measured: YES to both.  The weakenings the rules introduce
--        (`n [ wkᴿ expr ]ᴿ` and `w [ (wkᴿ expr ↑ᴿ expr) ]ᴿ`) are pushed
--        through by the rewrite system, so `ren-↝π` is a bare
--        constructor application — no transport, no new rewrite rule,
--        and the rule set stays at 72 rules and 0 non-joinable pairs.
--
--   (M2) Does the INDUCTIVE characterisation of strong normalisation
--        survive?  Measured: NO.  `SNe`'s `cse` and `app` constructors
--        admit terms that are π-redexes (`SNe-admits-π-redex-c`,
--        `SNe-admits-π-redex-a` below, both machine-checked, and both
--        WELL-TYPED — `⊢bad-c` / `⊢bad-a` give the derivations, which
--        under the scoped encoding is a real obligation rather than a
--        property of the indices), so `neu : SNe e → SN e` asserts that
--        a REDUCIBLE term is normal by fiat.  Soundness `SN ⟹ sn` is
--        exactly what that breaks: `sn` must inspect every reduct and
--        `neu` supplies nothing about the π-reduct.  This is not a
--        missing case; the definition of "neutral" is wrong once π is
--        present.
--
--   (M3) What has to change.  Neutrals must be stratified: an
--        elimination spine may contain at most one `case`, at the
--        outside.  `SNe⁻` (variable head, applications only) and
--        `SNe′ = SNe⁻ ∪ {case SNe⁻ u v}` below is that stratification,
--        and `SNe⁻-no-π·` proves the smaller class is closed
--        under nothing (no π-rule applies to it) — which is the
--        property `neu` needs and the current `SNe` lacks.
--        With it, `SNsum` does need a further closure constructor for
--        `case`-headed terms (`r-cse`), and — measured, see the note at
--        the end — its two parameters must become SCOPE-INDEXED
--        families, because the branches of that `case` live in
--        extended scopes -- which the present `SNsum`, whose parameters
--        are `S ⊢ expr → Set` for one fixed S, cannot express.

module Reloaded.SumsCommuting where

open import Languages.STLCSums
open import Reloaded.SumsNormalization
  using (SNe; SN; _⟶SN_; var; app; cse; abs; inlS; inrS; neu; red;
         βSN; applSN; βinl; βinr; cseSN;
         Ty; ★; _⇒ᵗ_; _+ᵗ_; Ctx; _∷ₜ_; _⊢_∶_; ⊢`; ⊢λ; ⊢·; ⊢inl; ⊢inr; ⊢case)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

-- ═══ (M1) the two permutative rules ═════════════════════════════════
-- π· pushes an application into the branches of a case;
-- πc pushes a case into the branches of an inner case.
-- Both weaken the OUTER material into the INNER scope, which is the
-- part the σ-calculus has to absorb.

infix 3 _↝π_

data _↝π_ : ∀ {S} → S ⊢ expr → S ⊢ expr → Set where

  -- the β and congruence rules, verbatim from Reloaded.SumsSoundness's `_↝_`
  β↝    : ∀ {S} {b : (expr ∷ S) ⊢ expr} {n : S ⊢ expr} → ((λx b) · n) ↝π (b [ n ]₀)
  ξλ    : ∀ {S} {b b′ : (expr ∷ S) ⊢ expr} → b ↝π b′ → (λx b) ↝π (λx b′)
  ξ·₁   : ∀ {S} {e e′ n : S ⊢ expr} → e ↝π e′ → (e · n) ↝π (e′ · n)
  ξ·₂   : ∀ {S} {e n n′ : S ⊢ expr} → n ↝π n′ → (e · n) ↝π (e · n′)
  βinl↝ : ∀ {S} {m : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
          (case (inl m) u v) ↝π (u [ m ]₀)
  βinr↝ : ∀ {S} {m : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
          (case (inr m) u v) ↝π (v [ m ]₀)
  ξinl  : ∀ {S} {e e′ : S ⊢ expr} → e ↝π e′ → inl e ↝π inl e′
  ξinr  : ∀ {S} {e e′ : S ⊢ expr} → e ↝π e′ → inr e ↝π inr e′
  ξc₀   : ∀ {S} {e e′ : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
          e ↝π e′ → (case e u v) ↝π (case e′ u v)
  ξc₁   : ∀ {S} {e : S ⊢ expr} {u u′ v : (expr ∷ S) ⊢ expr} →
          u ↝π u′ → (case e u v) ↝π (case e u′ v)
  ξc₂   : ∀ {S} {e : S ⊢ expr} {u v v′ : (expr ∷ S) ⊢ expr} →
          v ↝π v′ → (case e u v) ↝π (case e u v′)

  -- THE PERMUTATIVE CONVERSIONS
  --   (case r u v) n  ↝  case r (u n↑) (v n↑)
  π· : ∀ {S} {r n : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
       ((case r u v) · n) ↝π
       (case r (u · (n [ wkᴿ expr ]ᴿ)) (v · (n [ wkᴿ expr ]ᴿ)))

  --   case (case r u v) w₁ w₂  ↝  case r (case u w₁↑ w₂↑) (case v w₁↑ w₂↑)
  πc : ∀ {S} {r : S ⊢ expr} {u v w₁ w₂ : (expr ∷ S) ⊢ expr} →
       (case (case r u v) w₁ w₂) ↝π
       (case r (case u (w₁ [ (wkᴿ expr ↑ᴿ expr) ]ᴿ) (w₂ [ (wkᴿ expr ↑ᴿ expr) ]ᴿ))
               (case v (w₁ [ (wkᴿ expr ↑ᴿ expr) ]ᴿ) (w₂ [ (wkᴿ expr ↑ᴿ expr) ]ᴿ)))

-- ─── the measurement: renaming commutes with π DEFINITIONALLY ───────
-- The interesting obligations are the two π cases.  For π· the goal is
--   ((case r u v) · n) [ ξ ]ᴿ  ↝π  (case r (u · n↑) (v · n↑)) [ ξ ]ᴿ
-- and the right-hand side must be convertible with the π· instance at
-- the renamed arguments, i.e. Agda must see
--   (n [ wkᴿ expr ]ᴿ) [ (ξ ↑ᴿ expr) ]ᴿ  ≡  (n [ ξ ]ᴿ) [ wkᴿ expr ]ᴿ
-- and its two-level analogue for πc.  Both hold by the rewrite system.

ren-↝π : ∀ {S₁ S₂} {e e′ : S₁ ⊢ expr} → e ↝π e′ → (ξ : S₁ →ᴿ S₂) →
  (e [ ξ ]ᴿ) ↝π (e′ [ ξ ]ᴿ)
ren-↝π β↝        ξ = β↝
ren-↝π (ξλ st)   ξ = ξλ  (ren-↝π st (ξ ↑ᴿ _))
ren-↝π (ξ·₁ st)  ξ = ξ·₁ (ren-↝π st ξ)
ren-↝π (ξ·₂ st)  ξ = ξ·₂ (ren-↝π st ξ)
ren-↝π βinl↝     ξ = βinl↝
ren-↝π βinr↝     ξ = βinr↝
ren-↝π (ξinl st) ξ = ξinl (ren-↝π st ξ)
ren-↝π (ξinr st) ξ = ξinr (ren-↝π st ξ)
ren-↝π (ξc₀ st)  ξ = ξc₀ (ren-↝π st ξ)
ren-↝π (ξc₁ st)  ξ = ξc₁ (ren-↝π st (ξ ↑ᴿ _))
ren-↝π (ξc₂ st)  ξ = ξc₂ (ren-↝π st (ξ ↑ᴿ _))
ren-↝π π·        ξ = π·        -- ← no transport
ren-↝π πc        ξ = πc        -- ← no transport

-- The same two facts, stated on their own so that the measurement is
-- legible without reading the proof above.
π·-weakening-commutes : ∀ {S₁ S₂} (n : S₁ ⊢ expr) (ξ : S₁ →ᴿ S₂) →
  (n [ wkᴿ expr ]ᴿ) [ (ξ ↑ᴿ expr) ]ᴿ ≡ (n [ ξ ]ᴿ) [ wkᴿ expr ]ᴿ
π·-weakening-commutes n ξ = refl

πc-weakening-commutes : ∀ {S₁ S₂} (w : (expr ∷ S₁) ⊢ expr) (ξ : S₁ →ᴿ S₂) →
  (w [ (wkᴿ expr ↑ᴿ expr) ]ᴿ) [ ((ξ ↑ᴿ expr) ↑ᴿ expr) ]ᴿ
    ≡ (w [ (ξ ↑ᴿ expr) ]ᴿ) [ (wkᴿ expr ↑ᴿ expr) ]ᴿ
πc-weakening-commutes w ξ = refl

-- Substitution likewise: the σ-world analogue, also by conversion.
π·-sub-commutes : ∀ {S₁ S₂} (n : S₁ ⊢ expr) (σ : S₁ →ˢ S₂) →
  (n [ wkᴿ expr ]ᴿ) [ (σ ↑ˢ expr) ]ˢ ≡ (n [ σ ]ˢ) [ wkᴿ expr ]ᴿ
π·-sub-commutes n σ = refl

-- ═══ (M2) the inductive characterisation does NOT survive ═══════════
-- Two concrete, closed-under-two-variables witnesses.  Each is a term
-- the CURRENT `SNe` accepts, which the permutative rules reduce, and
-- which is WELL TYPED.

Sx : Scope
Sx = expr ∷ expr ∷ []

Γ₀ : Ctx []
Γ₀ ()

-- x₁ : ★ ,  x₀ : ★ + ★
Γx : Ctx Sx
Γx = ★ ∷ₜ ((★ +ᵗ ★) ∷ₜ Γ₀)

x₀ : Sx ∋ expr
x₀ = suc zero

-- case x (inl z) (inr z)  :  a neutral term of SUM type
ne-sum : Sx ⊢ expr
ne-sum = case (` x₀) (inl (` zero)) (inr (` zero))

⊢ne-sum : Γx ⊢ ne-sum ∶ (★ +ᵗ ★)
⊢ne-sum = ⊢case (⊢` refl) (⊢inl (⊢` refl)) (⊢inr (⊢` refl))

SNe-ne-sum : SNe ne-sum
SNe-ne-sum = cse (var x₀) (inlS (neu (var zero))) (inrS (neu (var zero)))

-- eliminating it AGAIN is still `SNe` by the current rules …
bad-c : Sx ⊢ expr
bad-c = case ne-sum (` zero) (` zero)

⊢bad-c : Γx ⊢ bad-c ∶ ★
⊢bad-c = ⊢case ⊢ne-sum (⊢` refl) (⊢` refl)

SNe-bad-c : SNe bad-c
SNe-bad-c = cse SNe-ne-sum (neu (var zero)) (neu (var zero))

-- … and it is a π-redex.
SNe-admits-π-redex-c : Σ[ e′ ∈ Sx ⊢ expr ] (bad-c ↝π e′)
SNe-admits-π-redex-c = _ , πc

-- the same for the application spine
ne-fun : Sx ⊢ expr
ne-fun = case (` x₀) (λx (` zero)) (λx (` zero))

⊢ne-fun : Γx ⊢ ne-fun ∶ (★ ⇒ᵗ ★)
⊢ne-fun = ⊢case (⊢` refl) (⊢λ (⊢` refl)) (⊢λ (⊢` refl))

SNe-ne-fun : SNe ne-fun
SNe-ne-fun = cse (var x₀) (abs (neu (var zero))) (abs (neu (var zero)))

bad-a : Sx ⊢ expr
bad-a = ne-fun · (` zero)

⊢bad-a : Γx ⊢ bad-a ∶ ★
⊢bad-a = ⊢· ⊢ne-fun (⊢` refl)

SNe-bad-a : SNe bad-a
SNe-bad-a = app SNe-ne-fun (neu (var zero))

SNe-admits-π-redex-a : Σ[ e′ ∈ Sx ⊢ expr ] (bad-a ↝π e′)
SNe-admits-π-redex-a = _ , π·

-- Why that is fatal and not merely untidy: `neu : SNe e → SN e` is the
-- ONLY SN-rule with no premise about reducts, so soundness
-- `SN ⟹ sn` (theorem-3-1-soundness in Reloaded/SumsSoundness.agda) discharges
-- `neu ne` by "a neutral term has no reduct at the head".  Here it has
-- one.  Concretely, the `sn` proof obligation left open at `bad-c` is
-- `sn` of its πc-reduct, about which `SNe-bad-c` says nothing.

-- ═══ (M3) the stratification that repairs it ════════════════════════
-- An elimination spine may contain at most one `case`, outermost.

data SNe⁻ : ∀ {S} → S ⊢ expr → Set                 -- variable head, apps only
data SNe′ : ∀ {S} → S ⊢ expr → Set                 -- SNe⁻, or one case on top

data SNe⁻ where
  var⁻ : ∀ {S} (x : S ∋ expr) → SNe⁻ (` x)
  app⁻ : ∀ {S} {r n : S ⊢ expr} → SNe⁻ r → SN n → SNe⁻ (r · n)

data SNe′ where
  emb  : ∀ {S} {e : S ⊢ expr} → SNe⁻ e → SNe′ e
  cse′ : ∀ {S} {r : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
         SNe⁻ r → SN u → SN v → SNe′ (case r u v)

-- the property the current `SNe` lacks: no π-rule applies at the head
-- of an `SNe⁻` term.  (`π·` needs a `case` under the application and
-- `πc` a `case` under the scrutinee; `SNe⁻` has neither.)
SNe⁻-no-π· : ∀ {S} {r : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
  ¬ SNe⁻ (case r u v)
SNe⁻-no-π· ()

SNe⁻-embeds : ∀ {S} {e : S ⊢ expr} → SNe⁻ e → SNe′ e
SNe⁻-embeds = emb

-- and the old `SNe` is strictly larger: `ne-sum` is `SNe` but its
-- elimination is not `SNe′`
bad-c-not-SNe′ : ¬ SNe′ bad-c
bad-c-not-SNe′ (emb ())
bad-c-not-SNe′ (cse′ () _ _)

bad-a-not-SNe′ : ¬ SNe′ bad-a
bad-a-not-SNe′ (emb (app⁻ () _))

-- ─── the further closure constructor SNsum needs ────────────────────
-- With π present, `case r u v` at SUM type is no longer covered by any
-- of `r-inl` / `r-inr` / `r-ne` / `r-red`: it is not an injection, it is
-- not `SNe′` unless r is `SNe⁻` (and then the outer eliminator would
-- permute into it), and it does not ⟶SN-reduce at the head.  It has to
-- be a constructor, and its premises are the two BRANCHES, which live
-- in EXTENDED scopes.  So the predicate's two parameters can no longer
-- be `S ⊢ expr → Set` for a fixed S: they must be scope-indexed.

Fam : Set₁
Fam = ∀ {S} → S ⊢ expr → Set

data SNsum′ (P : Fam) (Q : Fam) : ∀ {S} → S ⊢ expr → Set where
  r-inl : ∀ {S} {m : S ⊢ expr} → P m → SNsum′ P Q (inl m)
  r-inr : ∀ {S} {m : S ⊢ expr} → Q m → SNsum′ P Q (inr m)
  r-ne  : ∀ {S} {e : S ⊢ expr} → SNe′ e → SNsum′ P Q e
  r-red : ∀ {S} {e e′ : S ⊢ expr} → e ⟶SN e′ → SNsum′ P Q e′ → SNsum′ P Q e
  -- THE NEW ONE
  r-cse : ∀ {S} {r : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
          SNe⁻ r → SNsum′ P Q u → SNsum′ P Q v → SNsum′ P Q (case r u v)

-- The new constructor is well-formed only because `P` and `Q` are
-- Kripke: `u` lives in `expr ∷ S`, not in `S`.  Compare `SNsum` in
-- Reloaded/SumsNormalization.agda, whose parameters are `S ⊢ expr → Set`
-- for ONE fixed `S`; that shape cannot state `r-cse` at all.
--
-- MEASURED CONSEQUENCES of making `R (A +ᵗ B) = SNsum′ (R A) (R B)`:
--   * `R` must become a Kripke family at every type, not only at `⇒`.
--   * `cr1` gains one case (`r-cse`), which needs `SN (case r u v)`
--     from `SNe⁻ r` and SN branches — available from `cse′`.
--   * `R-case` (the fundamental lemma's `case`) gains one case, and it
--     is the one that has to APPLY the permutative conversion: from
--     `R (A +ᵗ B) (case r u v)` by `r-cse` and reducible continuations,
--     `R C (case (case r u v) w₁ w₂)` is obtained by `cr2` on `πc`,
--     which therefore has to be in `_⟶SN_` as well.
--   * `_⟶SN_` gaining π means `confl` in Reloaded/SumsSoundness.agda
--     gains the overlaps (applsn, π·) and (csesn, πc) — 2 new critical
--     cases at the top level, each recursing.
--
-- Every obstruction listed here is about the shape of the SN/SNsum
-- families; none of them is discharged by the object-language types.
-- Because the syntax is intrinsically SCOPED rather than typed, the two
-- counterexample terms carry explicit typing derivations (`⊢bad-c`,
-- `⊢bad-a`), so "SNe accepts a well-typed π-redex" is a proved statement
-- rather than a by-product of intrinsic typing.
--
-- None of this is done here.  What is measured is (i) that the σ-calculus
-- side is FREE — the permutative rules need no new rewrite rule, no
-- transport and no change to the 72-rule core — and (ii) that the
-- obstruction is entirely in the SN characterisation, at a precisely
-- located point: the definition of "neutral".
