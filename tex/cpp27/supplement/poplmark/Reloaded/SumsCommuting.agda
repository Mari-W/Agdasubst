{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ NOT A CHALLENGE RESULT ═════════════════════════════════════════
--
-- This module proves NO part of POPLmark Reloaded.  The permutative
-- (commuting) conversions are not part of the challenge, and strong
-- normalisation for the reduction relation with them, `_↝π_`, is NOT
-- proved here or anywhere else in this development.  Nothing in this
-- module is imported by any other module.
--
-- What it does contain is a measurement of what adding them would cost.
--
--   (M1) The two permutative rules can be stated and renaming commutes
--        with them definitionally: `ren-↝π` is a bare constructor
--        application in both π cases.
--
--   (M2) The inductive characterisation of SN does not survive.
--        `SNe`'s `cse` and `app` admit well-typed π-redexes
--        (`SNe-admits-π-redex-c` and `-a`, with derivations `⊢bad-c`
--        and `⊢bad-a`), so `neu : SNe e → SN e` calls a reducible term
--        normal.  The definition of "neutral" is wrong once π is there.
--
--   (M3) A stratification that would repair it: neutrals so that an
--        elimination spine holds at most one outermost `case`.  `SNe⁻`,
--        `SNe′` and `SNsum′` below are that stratification.  Of it only
--        that it excludes the two π-redexes of (M2) is proved
--        (`bad-c-not-SNe′`, `bad-a-not-SNe′`); no normalisation result
--        is proved for it, and it is used nowhere.

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
-- Both weaken the outer material into the inner scope, which is the
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

  -- the permutative conversions
  --   (case r u v) n  ↝  case r (u n↑) (v n↑)
  π· : ∀ {S} {r n : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
       ((case r u v) · n) ↝π
       (case r (u · (n [ wkᴿ expr ]ᴿ)) (v · (n [ wkᴿ expr ]ᴿ)))

  --   case (case r u v) w₁ w₂  ↝  case r (case u w₁↑ w₂↑) (case v w₁↑ w₂↑)
  πc : ∀ {S} {r : S ⊢ expr} {u v w₁ w₂ : (expr ∷ S) ⊢ expr} →
       (case (case r u v) w₁ w₂) ↝π
       (case r (case u (w₁ [ (wkᴿ expr ↑ᴿ expr) ]ᴿ) (w₂ [ (wkᴿ expr ↑ᴿ expr) ]ᴿ))
               (case v (w₁ [ (wkᴿ expr ↑ᴿ expr) ]ᴿ) (w₂ [ (wkᴿ expr ↑ᴿ expr) ]ᴿ)))

-- ─── (M1) renaming commutes with π definitionally ───────────────────
-- The two π cases need
--   (n [ wkᴿ expr ]ᴿ) [ (ξ ↑ᴿ expr) ]ᴿ  ≡  (n [ ξ ]ᴿ) [ wkᴿ expr ]ᴿ
-- and its two-level analogue, both stated separately below.

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

-- ═══ (M2) the inductive characterisation does not survive ═══════════
-- Two concrete, closed-under-two-variables witnesses.  Each is a term
-- the current `SNe` accepts, which the permutative rules reduce, and
-- which is well typed.

Sx : Scope
Sx = expr ∷ expr ∷ []

Γ₀ : Ctx []
Γ₀ ()

-- x₁ : ★ ,  x₀ : ★ + ★
Γx : Ctx Sx
Γx = ★ ∷ₜ ((★ +ᵗ ★) ∷ₜ Γ₀)

x₀ : Sx ∋ expr
x₀ = suc zero

-- case x (inl z) (inr z)  :  a neutral term of sum type
ne-sum : Sx ⊢ expr
ne-sum = case (` x₀) (inl (` zero)) (inr (` zero))

⊢ne-sum : Γx ⊢ ne-sum ∶ (★ +ᵗ ★)
⊢ne-sum = ⊢case (⊢` refl) (⊢inl (⊢` refl)) (⊢inr (⊢` refl))

SNe-ne-sum : SNe ne-sum
SNe-ne-sum = cse (var x₀) (inlS (neu (var zero))) (inrS (neu (var zero)))

-- eliminating it again is still `SNe` by the current rules …
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
-- only SN-rule with no premise about reducts, so soundness
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
-- With π present, `case r u v` at sum type is no longer covered by any
-- of `r-inl` / `r-inr` / `r-ne` / `r-red`: it is not an injection, it is
-- not `SNe′` unless r is `SNe⁻` (and then the outer eliminator would
-- permute into it), and it does not ⟶SN-reduce at the head.  It has to
-- be a constructor, and its premises are the two branches, which live
-- in extended scopes.  So the predicate's two parameters can no longer
-- be `S ⊢ expr → Set` for a fixed S: they must be scope-indexed.

Fam : Set₁
Fam = ∀ {S} → S ⊢ expr → Set

data SNsum′ (P : Fam) (Q : Fam) : ∀ {S} → S ⊢ expr → Set where
  r-inl : ∀ {S} {m : S ⊢ expr} → P m → SNsum′ P Q (inl m)
  r-inr : ∀ {S} {m : S ⊢ expr} → Q m → SNsum′ P Q (inr m)
  r-ne  : ∀ {S} {e : S ⊢ expr} → SNe′ e → SNsum′ P Q e
  r-red : ∀ {S} {e e′ : S ⊢ expr} → e ⟶SN e′ → SNsum′ P Q e′ → SNsum′ P Q e
  -- the new one
  r-cse : ∀ {S} {r : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
          SNe⁻ r → SNsum′ P Q u → SNsum′ P Q v → SNsum′ P Q (case r u v)

-- `r-cse` is well-formed only because `P` and `Q` are Kripke: `u` lives
-- in `expr ∷ S`.  `SNsum` in Reloaded/SumsNormalization.agda, whose
-- parameters are `S ⊢ expr → Set` for one fixed `S`, cannot state it.
--
-- Measured consequences of `R (A +ᵗ B) = SNsum′ (R A) (R B)`: `R`
-- becomes Kripke at every type; `cr1` and `R-case` each gain a case;
-- `_⟶sn_` gains π, which gives `confl` two new critical overlaps.
--
-- None of this is done here.  What is measured is that the σ-calculus
-- side is free and that the obstruction is entirely in the definition
-- of "neutral".  This module claims no challenge result.
