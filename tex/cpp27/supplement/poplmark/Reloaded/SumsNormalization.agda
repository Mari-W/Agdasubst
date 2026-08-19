{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLMark Reloaded STLC+, Challenges 2a and 2b (WITH SUMS) ══════
--   [Abel, Allais, Hameer, Pientka, Momigliano, Schäfer, Stark, JFP 2019]
--
--   2a  properties of the inductive SN:  renaming, ANTI-renaming,
--       extensionality                                 (Lemmas 3.17-3.19)
--   2b  the Kripke logical predicate R, CR1-CR3, semantic substitutions,
--       the Fundamental Lemma, and  ⊢ M : A  ⟹  M ∈ SN
--                                       (Thm 3.3, Def 3.3, Lem 3.20, Cor 3.4)
--
-- The terms are INTRINSICALLY SCOPED, not intrinsically typed:
-- Languages/STLCSums.agda is the reference development's multi-sorted
-- σ-calculus at the closed sort set {expr}.  The simple types (now with
-- `_+ᵗ_`) are the separate datatype `Ty` below, and the typing judgment
-- `Γ ⊢ e ∶ A` is a separate inductive family.  See the header of
-- Reloaded/Normalization.agda for why the logical predicate is indexed by a
-- TYPE and a scoped term rather than by a typing derivation; with sums
-- the argument is the same, and `SNsum` below inherits it.
--
-- Challenges 1a/1b are in Reloaded/SumsSoundness.agda.
--
-- THE ANSWER TO THE STRUCTURAL QUESTION is at `R` below: the arrow case
-- stays a Π-type defined by recursion on the type, but the SUM case
-- CANNOT -- it has to be an inductive closure (`SNsum`).  So the
-- logical predicate needed RESTRUCTURING, not just more cases.

module Reloaded.SumsNormalization where

open import Languages.STLCSums

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)

-- ─── the language-specific layer this metatheory sits on ────────────
-- Moved out of Languages.STLCSums: none of it is σ-calculus.  It is contexts,
-- generalizable variables and congruences for THIS language, so it
-- belongs with the proofs and not in generated output.

-- the three-argument congruence the metatheory of `case` uses
cong-case : ∀ {S} {e e′ : S ⊢ expr} {u u′ v v′ : (expr ∷ S) ⊢ expr} →
  e ≡ e′ → u ≡ u′ → v ≡ v′ → case e u v ≡ case e′ u′ v′
cong-case refl refl refl = refl


-- ═══ THE OBJECT LANGUAGE'S TYPES AND TYPING JUDGMENT ════════════════

infixr 6 _⇒ᵗ_
infixr 6 _+ᵗ_

data Ty : Set where
  ★    : Ty                     -- the base type
  _⇒ᵗ_ : Ty → Ty → Ty
  _+ᵗ_ : Ty → Ty → Ty           -- disjoint sum

Ctx : Scope → Set
Ctx S = S ∋ expr → Ty

infixr 5 _∷ₜ_
_∷ₜ_ : ∀ {S} → Ty → Ctx S → Ctx (expr ∷ S)
(A ∷ₜ Γ) zero    = A
(A ∷ₜ Γ) (suc x) = Γ x

_∋_∶_ : ∀ {S} → Ctx S → S ∋ expr → Ty → Set
Γ ∋ x ∶ A = Γ x ≡ A

infix 3 _⊢_∶_
data _⊢_∶_ : ∀ {S} → Ctx S → S ⊢ expr → Ty → Set where
  ⊢`    : ∀ {S} {Γ : Ctx S} {x : S ∋ expr} {A} →
          Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  ⊢λ    : ∀ {S} {Γ : Ctx S} {e : (expr ∷ S) ⊢ expr} {A B} →
          (A ∷ₜ Γ) ⊢ e ∶ B → Γ ⊢ (λx e) ∶ (A ⇒ᵗ B)
  ⊢·    : ∀ {S} {Γ : Ctx S} {e₁ e₂ : S ⊢ expr} {A B} →
          Γ ⊢ e₁ ∶ (A ⇒ᵗ B) → Γ ⊢ e₂ ∶ A → Γ ⊢ (e₁ · e₂) ∶ B
  ⊢inl  : ∀ {S} {Γ : Ctx S} {e : S ⊢ expr} {A B} →
          Γ ⊢ e ∶ A → Γ ⊢ (inl e) ∶ (A +ᵗ B)
  ⊢inr  : ∀ {S} {Γ : Ctx S} {e : S ⊢ expr} {A B} →
          Γ ⊢ e ∶ B → Γ ⊢ (inr e) ∶ (A +ᵗ B)
  ⊢case : ∀ {S} {Γ : Ctx S} {e : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} {A B C} →
          Γ ⊢ e ∶ (A +ᵗ B) → (A ∷ₜ Γ) ⊢ u ∶ C → (B ∷ₜ Γ) ⊢ v ∶ C →
          Γ ⊢ (case e u v) ∶ C

-- ─── Lemmas 3.2/3.3: typed renamings ────────────────────────────────

_∶_→ᴿ_ : ∀ {S₁ S₂} → S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ᴿ_ {S₁} ξ Γ₁ Γ₂ = ∀ (x : S₁ ∋ expr) → Γ₂ (x [ ξ ]ᴿ) ≡ Γ₁ x

⊢wkᴿ : ∀ {S} {Γ : Ctx S} (A : Ty) → wkᴿ expr ∶ Γ →ᴿ (A ∷ₜ Γ)
⊢wkᴿ A x = refl

⊢↑ᴿ : ∀ {S₁ S₂} {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} →
  ξ ∶ Γ₁ →ᴿ Γ₂ → (A : Ty) → (ξ ↑ᴿ expr) ∶ (A ∷ₜ Γ₁) →ᴿ (A ∷ₜ Γ₂)
⊢↑ᴿ ⊢ξ A zero    = refl
⊢↑ᴿ ⊢ξ A (suc x) = ⊢ξ x

infixl 5 _⊢⋯ᴿ_
_⊢⋯ᴿ_ : ∀ {S₁ S₂} {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {e : S₁ ⊢ expr} {A} → Γ₁ ⊢ e ∶ A → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (e [ ξ ]ᴿ) ∶ A
-- (the implicit maps are passed explicitly at every recursive call:
-- `ξ` occurs in the type of `⊢ξ` only under `_[_]ᴿ`, which is not a
-- pattern, so Agda cannot invert it)
_⊢⋯ᴿ_ (⊢` {x = x} refl) ⊢ξ = ⊢` (⊢ξ x)
_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢λ {A = A} d) ⊢ξ =
  ⊢λ (_⊢⋯ᴿ_ {ξ = ξ ↑ᴿ expr} {Γ₁ = A ∷ₜ Γ₁} {Γ₂ = A ∷ₜ Γ₂} d
             (⊢↑ᴿ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ξ A))
_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢· d₁ d₂) ⊢ξ =
  ⊢· (_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d₁ ⊢ξ)
     (_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d₂ ⊢ξ)
_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢inl d) ⊢ξ =
  ⊢inl (_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢ξ)
_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢inr d) ⊢ξ =
  ⊢inr (_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢ξ)
_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢case {A = A} {B = B} d du dv) ⊢ξ =
  ⊢case (_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢ξ)
        (_⊢⋯ᴿ_ {ξ = ξ ↑ᴿ expr} {Γ₁ = A ∷ₜ Γ₁} {Γ₂ = A ∷ₜ Γ₂} du
               (⊢↑ᴿ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ξ A))
        (_⊢⋯ᴿ_ {ξ = ξ ↑ᴿ expr} {Γ₁ = B ∷ₜ Γ₁} {Γ₂ = B ∷ₜ Γ₂} dv
               (⊢↑ᴿ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ξ B))

⊢weaken : ∀ {S} {Γ : Ctx S} {e : S ⊢ expr} {B} (A : Ty) →
  Γ ⊢ e ∶ B → (A ∷ₜ Γ) ⊢ (e [ wkᴿ expr ]ᴿ) ∶ B
⊢weaken {Γ = Γ} A d = _⊢⋯ᴿ_ {ξ = wkᴿ expr} {Γ₁ = Γ} {Γ₂ = A ∷ₜ Γ} d (⊢wkᴿ A)

-- ─── Lemmas 3.4/3.5: typed substitutions ────────────────────────────

_∶_→ˢ_ : ∀ {S₁ S₂} → S₁ →ˢ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ˢ_ {S₁} σ Γ₁ Γ₂ = ∀ (x : S₁ ∋ expr) → Γ₂ ⊢ (x [ σ ]ˢ) ∶ Γ₁ x

⊢↑ˢ : ∀ {S₁ S₂} {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} →
  σ ∶ Γ₁ →ˢ Γ₂ → (A : Ty) → (σ ↑ˢ expr) ∶ (A ∷ₜ Γ₁) →ˢ (A ∷ₜ Γ₂)
⊢↑ˢ ⊢σ A zero    = ⊢` refl
⊢↑ˢ {Γ₂ = Γ₂} ⊢σ A (suc x) =
  _⊢⋯ᴿ_ {ξ = wkᴿ expr} {Γ₁ = Γ₂} {Γ₂ = A ∷ₜ Γ₂} (⊢σ x) (⊢wkᴿ A)

infixl 5 _⊢⋯ˢ_
_⊢⋯ˢ_ : ∀ {S₁ S₂} {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {e : S₁ ⊢ expr} {A} → Γ₁ ⊢ e ∶ A → σ ∶ Γ₁ →ˢ Γ₂ → Γ₂ ⊢ (e [ σ ]ˢ) ∶ A
_⊢⋯ˢ_ (⊢` {x = x} refl) ⊢σ = ⊢σ x
_⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢λ {A = A} d) ⊢σ =
  ⊢λ (_⊢⋯ˢ_ {σ = σ ↑ˢ expr} {Γ₁ = A ∷ₜ Γ₁} {Γ₂ = A ∷ₜ Γ₂} d
             (⊢↑ˢ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢σ A))
_⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢· d₁ d₂) ⊢σ =
  ⊢· (_⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d₁ ⊢σ)
     (_⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d₂ ⊢σ)
_⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢inl d) ⊢σ =
  ⊢inl (_⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢σ)
_⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢inr d) ⊢σ =
  ⊢inr (_⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢σ)
_⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢case {A = A} {B = B} d du dv) ⊢σ =
  ⊢case (_⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢σ)
        (_⊢⋯ˢ_ {σ = σ ↑ˢ expr} {Γ₁ = A ∷ₜ Γ₁} {Γ₂ = A ∷ₜ Γ₂} du
               (⊢↑ˢ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢σ A))
        (_⊢⋯ˢ_ {σ = σ ↑ˢ expr} {Γ₁ = B ∷ₜ Γ₁} {Γ₂ = B ∷ₜ Γ₂} dv
               (⊢↑ˢ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢σ B))

⊢∙ˢ : ∀ {S} {Γ : Ctx S} {n : S ⊢ expr} {A} →
  Γ ⊢ n ∶ A → (n ∙ˢ idˢ) ∶ (A ∷ₜ Γ) →ˢ Γ
⊢∙ˢ dn zero    = dn
⊢∙ˢ dn (suc x) = ⊢` refl

⊢[] : ∀ {S} {Γ : Ctx S} {e : (expr ∷ S) ⊢ expr} {n : S ⊢ expr} {A B} →
  (A ∷ₜ Γ) ⊢ e ∶ B → Γ ⊢ n ∶ A → Γ ⊢ (e [ n ]₀) ∶ B
⊢[] {Γ = Γ} {n = n} {A = A} d dn =
  _⊢⋯ˢ_ {σ = n ∙ˢ idˢ} {Γ₁ = A ∷ₜ Γ} {Γ₂ = Γ} d (⊢∙ˢ dn)

-- ─── the inductive characterisation of strong normalisation ─────────
-- Fig. 3 of the challenge, transcribed rule for rule, plus the sum
-- rules.  The paper's typing premises are DROPPED, not hidden in the
-- indices: SN is a predicate on raw scoped terms.

data SNe    : ∀ {S} → S ⊢ expr → Set
data SN     : ∀ {S} → S ⊢ expr → Set
data _⟶SN_ : ∀ {S} → S ⊢ expr → S ⊢ expr → Set

infix 3 _⟶SN_

data SNe where
  var : ∀ {S} (x : S ∋ expr) → SNe (` x)
  app : ∀ {S} {r n : S ⊢ expr} → SNe r → SN n → SNe (r · n)
  cse : ∀ {S} {r : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
        SNe r → SN u → SN v → SNe (case r u v)

data SN where
  abs : ∀ {S} {e : (expr ∷ S) ⊢ expr} → SN e → SN (λx e)
  inlS : ∀ {S} {e : S ⊢ expr} → SN e → SN (inl e)
  inrS : ∀ {S} {e : S ⊢ expr} → SN e → SN (inr e)
  neu : ∀ {S} {r : S ⊢ expr} → SNe r → SN r
  red : ∀ {S} {e e′ : S ⊢ expr} → e ⟶SN e′ → SN e′ → SN e

data _⟶SN_ where
  βSN   : ∀ {S} {e : (expr ∷ S) ⊢ expr} {n : S ⊢ expr} →
          SN n → ((λx e) · n) ⟶SN (e [ n ]₀)
  applSN : ∀ {S} {e e′ n : S ⊢ expr} →
          e ⟶SN e′ → (e · n) ⟶SN (e′ · n)
  βinl  : ∀ {S} {m : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
          SN m → SN v → (case (inl m) u v) ⟶SN (u [ m ]₀)
  βinr  : ∀ {S} {m : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
          SN m → SN u → (case (inr m) u v) ⟶SN (v [ m ]₀)
  cseSN : ∀ {S} {e e′ : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
          e ⟶SN e′ → (case e u v) ⟶SN (case e′ u v)

-- ═══ CHALLENGE 2a ═══════════════════════════════════════════════════

-- ─── Lemma 3.17: renaming ───────────────────────────────────────────
-- The βSN case needs  (e [ n ]₀) [ ξ ]ᴿ ≡ (e [ (ξ ↑ᴿ expr) ]ᴿ) [ n [ ξ ]ᴿ ]₀.
-- Under the rewrite system both sides have the same normal form, so the
-- case is a bare constructor application.

ren-SNe : ∀ {S₁ S₂} {e : S₁ ⊢ expr} → SNe e → (ξ : S₁ →ᴿ S₂) → SNe (e [ ξ ]ᴿ)
ren-SN  : ∀ {S₁ S₂} {e : S₁ ⊢ expr} → SN e → (ξ : S₁ →ᴿ S₂) → SN (e [ ξ ]ᴿ)
ren-⟶SN : ∀ {S₁ S₂} {e e′ : S₁ ⊢ expr} → e ⟶SN e′ → (ξ : S₁ →ᴿ S₂) →
          (e [ ξ ]ᴿ) ⟶SN (e′ [ ξ ]ᴿ)

ren-SNe (var x)   ξ = var (x [ ξ ]ᴿ)
ren-SNe (app r n) ξ = app (ren-SNe r ξ) (ren-SN n ξ)
ren-SNe (cse r u v) ξ = cse (ren-SNe r ξ) (ren-SN u (ξ ↑ᴿ _)) (ren-SN v (ξ ↑ᴿ _))

ren-SN (abs d)    ξ = abs (ren-SN d (ξ ↑ᴿ _))
ren-SN (inlS d)   ξ = inlS (ren-SN d ξ)
ren-SN (inrS d)   ξ = inrS (ren-SN d ξ)
ren-SN (neu r)    ξ = neu (ren-SNe r ξ)
ren-SN (red st d) ξ = red (ren-⟶SN st ξ) (ren-SN d ξ)

ren-⟶SN (βSN n)    ξ = βSN (ren-SN n ξ)      -- no transport
ren-⟶SN (applSN st) ξ = applSN (ren-⟶SN st ξ)
ren-⟶SN (βinl m v) ξ = βinl (ren-SN m ξ) (ren-SN v (ξ ↑ᴿ _))
ren-⟶SN (βinr m u) ξ = βinr (ren-SN m ξ) (ren-SN u (ξ ↑ᴿ _))
ren-⟶SN (cseSN st) ξ = cseSN (ren-⟶SN st ξ)

-- ─── Lemma 3.18: ANTI-renaming ──────────────────────────────────────
-- The paper's flagged pain point: it must invert through `e [ ξ ]ᴿ`, so
-- it holds for renamings only.  Here the term is scrutinised FIRST --
-- for a constructor term the rewrite rules make `e [ ξ ]ᴿ` reduce to a
-- constructor form, and the SN/SNe/⟶SN derivation can then be matched
-- directly.  That is "pattern matching modulo the equational theory of
-- renamings" obtained for free from conversion.
--
-- NOTE: every absurd pattern below is absurd for a SYNTACTIC reason (no
-- constructor of the inductive family matches the head of the term),
-- never because two object-language types differ.  That is why dropping
-- intrinsic typing costs this proof nothing.

anti-SNe : ∀ {S₁ S₂} (e : S₁ ⊢ expr) {ξ : S₁ →ᴿ S₂} → SNe (e [ ξ ]ᴿ) → SNe e
anti-SN  : ∀ {S₁ S₂} (e : S₁ ⊢ expr) {ξ : S₁ →ᴿ S₂} → SN (e [ ξ ]ᴿ) → SN e
anti-⟶SN : ∀ {S₁ S₂} (e : S₁ ⊢ expr) {ξ : S₁ →ᴿ S₂} {n : S₂ ⊢ expr} →
  (e [ ξ ]ᴿ) ⟶SN n → Σ[ e′ ∈ S₁ ⊢ expr ] ((e ⟶SN e′) × (e′ [ ξ ]ᴿ ≡ n))

anti-SNe (` x)     (var _)   = var x
anti-SNe (λx e)    ()
anti-SNe (inl e)   ()
anti-SNe (inr e)   ()
anti-SNe (case e u v) {ξ = ξ} (cse r su sv) =
  cse (anti-SNe e {ξ = ξ} r) (anti-SN u {ξ = ξ ↑ᴿ _} su) (anti-SN v {ξ = ξ ↑ᴿ _} sv)
anti-SNe (e₁ · e₂) {ξ = ξ} (app r n) =
  app (anti-SNe e₁ {ξ = ξ} r) (anti-SN e₂ {ξ = ξ} n)

anti-SN (` x)  {ξ = ξ} (neu ne) = neu (anti-SNe (` x) {ξ = ξ} ne)
anti-SN (` x)  (red () d)
anti-SN (λx e) {ξ = ξ} (abs d)  = abs (anti-SN e {ξ = ξ ↑ᴿ _} d)
anti-SN (λx e) (neu ())
anti-SN (λx e) (red () d)
anti-SN (inl e) {ξ = ξ} (inlS d) = inlS (anti-SN e {ξ = ξ} d)
anti-SN (inl e) (neu ())
anti-SN (inl e) (red () d)
anti-SN (inr e) {ξ = ξ} (inrS d) = inrS (anti-SN e {ξ = ξ} d)
anti-SN (inr e) (neu ())
anti-SN (inr e) (red () d)
anti-SN (case e u v) {ξ = ξ} (neu ne) = neu (anti-SNe (case e u v) {ξ = ξ} ne)
anti-SN (case e u v) {ξ = ξ} (red st d) with anti-⟶SN (case e u v) {ξ = ξ} st
... | (e′ , st′ , refl) = red st′ (anti-SN e′ {ξ = ξ} d)
anti-SN (e₁ · e₂) {ξ = ξ} (neu ne) = neu (anti-SNe (e₁ · e₂) {ξ = ξ} ne)
anti-SN (e₁ · e₂) {ξ = ξ} (red st d) with anti-⟶SN (e₁ · e₂) {ξ = ξ} st
... | (e′ , st′ , refl) = red st′ (anti-SN e′ {ξ = ξ} d)

anti-⟶SN (` x)  ()
anti-⟶SN (λx e) ()
-- the β case: `(e [ n ]₀) [ ξ ]ᴿ ≡ (e [ (ξ ↑ᴿ expr) ]ᴿ) [ n [ ξ ]ᴿ ]₀` is refl
anti-⟶SN ((λx b) · e₂) {ξ = ξ} (βSN n) =
  (b [ e₂ ]₀) , βSN (anti-SN e₂ {ξ = ξ} n) , refl
anti-⟶SN ((λx b) · e₂)   (applSN ())
anti-⟶SN ((` x) · e₂)    (applSN ())
anti-⟶SN ((f · a) · e₂) {ξ = ξ} (applSN st) with anti-⟶SN (f · a) {ξ = ξ} st
... | (e′ , st′ , refl) = (e′ · e₂) , applSN st′ , refl
anti-⟶SN ((inl c) · e₂)  (applSN ())
anti-⟶SN ((inr c) · e₂)  (applSN ())
anti-⟶SN ((case c w z) · e₂) {ξ = ξ} (applSN st) with anti-⟶SN (case c w z) {ξ = ξ} st
... | (e′ , st′ , refl) = (e′ · e₂) , applSN st′ , refl
anti-⟶SN (inl e) ()
anti-⟶SN (inr e) ()
anti-⟶SN (case (inl m) u v) {ξ = ξ} (βinl sm sv) =
  (u [ m ]₀) , βinl (anti-SN m {ξ = ξ} sm) (anti-SN v {ξ = ξ ↑ᴿ _} sv) , refl
anti-⟶SN (case (inl m) u v) (cseSN ())
anti-⟶SN (case (inr m) u v) {ξ = ξ} (βinr sm su) =
  (v [ m ]₀) , βinr (anti-SN m {ξ = ξ} sm) (anti-SN u {ξ = ξ ↑ᴿ _} su) , refl
anti-⟶SN (case (inr m) u v) (cseSN ())
anti-⟶SN (case (` x) u v) (cseSN ())
anti-⟶SN (case (λx b) u v) (cseSN ())
anti-⟶SN (case (f · a) u v) {ξ = ξ} (cseSN st) with anti-⟶SN (f · a) {ξ = ξ} st
... | (e′ , st′ , refl) = case e′ u v , cseSN st′ , refl
anti-⟶SN (case (case c w z) u v) {ξ = ξ} (cseSN st) with anti-⟶SN (case c w z) {ξ = ξ} st
... | (e′ , st′ , refl) = case e′ u v , cseSN st′ , refl

-- ─── substituting a VARIABLE is a renaming ──────────────────────────
-- THE ONE SUBSTITUTION FACT THIS DEVELOPMENT HAS TO PROVE BY HAND.
-- `t [ ` x ]₀` and `t [ x ∙ᴿ idᴿ ]ᴿ` are two DISTINCT normal forms of
-- the rewrite system.  `t [ ` x ]₀` unfolds to `t [ (` x) ∙ˢ idˢ ]ˢ`, and
-- `idˢ` IS `⟨ idᴿ ⟩` -- but the map is cons-shaped, not `⟨ _ ⟩`-shaped, so
-- `coincidence` (whose left-hand side needs a syntactic `⟨ ξ ⟩`) cannot
-- fire on it.
--
-- The rule that would fix this is `(` x) ∙ˢ ⟨ ξ ⟩ → ⟨ x ∙ᴿ ξ ⟩`: the
-- S -> R orientation that `⟨⟩-comp`, `⟨⟩-lift` and `coincidence` all
-- have, and which `⟨⟩-cons` -- a LEMMA here, not a registered rule --
-- points the other way round.  With it, `t [ ` x ]₀` would collapse into
-- the renaming world and this file's `[]-as-ren` would be a conversion.
--
-- It cannot be registered.  Measured on this rule set: the rule alone
-- costs 4 non-joinable critical pairs; adding the ⨟-continued companions
-- that close two of them costs 5; adding `distᴿ` and `lift-consᴿ` on top
-- costs 4.  The pair that survives every round is
--
--   (x [ ξ ↑ᴿ s ]ᴿ) [ (` y) ∙ˢ ⟨ ξ₁ ⟩ ]ˢ
--
-- whose two reducts meet only if composition at a VARIABLE folds, so that
-- `lift-consᴿ` can fire -- and composition at mode V pushes, because
-- folding there overlaps `def-wkᴿ` unjoinably.  So this is the same
-- obstruction as the push-at-V/fold-at-T decision, seen from the
-- substitution side.  We supply the missing join as an induction on the
-- term.

ren-as-sub : ∀ {S₁ S₂ s} (t : S₁ ⊢ s) (σ : S₁ →ˢ S₂) (ξ : S₁ →ᴿ S₂) →
  (∀ {s′} (y : S₁ ∋ s′) → y [ σ ]ˢ ≡ ` (y [ ξ ]ᴿ)) → t [ σ ]ˢ ≡ t [ ξ ]ᴿ
ren-as-sub (` y)     σ ξ h = h y
ren-as-sub (λx e)    σ ξ h = cong λx_ (ren-as-sub e (σ ↑ˢ _) (ξ ↑ᴿ _)
  λ { zero → refl ; (suc y) → cong (_[ wkᴿ _ ]ᴿ) (h y) })
ren-as-sub (e₁ · e₂) σ ξ h =
  cong₂ _·_ (ren-as-sub e₁ σ ξ h) (ren-as-sub e₂ σ ξ h)
ren-as-sub (inl e) σ ξ h = cong inl (ren-as-sub e σ ξ h)
ren-as-sub (inr e) σ ξ h = cong inr (ren-as-sub e σ ξ h)
ren-as-sub (case e u v) σ ξ h = cong-case (ren-as-sub e σ ξ h)
  (ren-as-sub u (σ ↑ˢ _) (ξ ↑ᴿ _) λ { zero → refl ; (suc y) → cong (_[ wkᴿ _ ]ᴿ) (h y) })
  (ren-as-sub v (σ ↑ˢ _) (ξ ↑ᴿ _) λ { zero → refl ; (suc y) → cong (_[ wkᴿ _ ]ᴿ) (h y) })

[]-as-ren : ∀ {S} (t : (expr ∷ S) ⊢ expr) (x : S ∋ expr) →
  t [ ` x ]₀ ≡ t [ (x ∙ᴿ idᴿ) ]ᴿ
[]-as-ren t x = ren-as-sub t ((` x) ∙ˢ idˢ) (x ∙ᴿ idᴿ)
  λ { zero → refl ; (suc y) → refl }

-- ─── Lemma 3.19: extensionality of SN ───────────────────────────────
-- In the β case the redex contracts to `b [ ` x ]₀`, which by the lemma
-- above is a RENAMING, so anti-renaming (3.18) applies.

ext-SN : ∀ {S} {e : S ⊢ expr} {x : S ∋ expr} → SN (e · (` x)) → SN e
ext-SN (neu (app r n))     = neu r
ext-SN (red (applSN st) d) = red st (ext-SN d)
ext-SN {x = x} (red (βSN {e = b} _) d) =
  abs (anti-SN b {ξ = x ∙ᴿ idᴿ} (subst SN ([]-as-ren b x) d))

-- ═══ CHALLENGE 2b: the Kripke logical predicate ═════════════════════

-- THE RESTRUCTURING.  For ⇒ the predicate is a Π-type produced by
-- recursion on the type.  For + that is impossible: the set of
-- reducible terms at A + B must contain the injections of reducible
-- terms, but ALSO every neutral term (CR3) and be closed under
-- ⟶SN-expansion (CR2), and those closure conditions cannot be written
-- as a Π-type over the injections.  So the sum case is an INDUCTIVE
-- CLOSURE, parameterised by the two recursive calls:

data SNsum {S} (P : S ⊢ expr → Set) (Q : S ⊢ expr → Set) : S ⊢ expr → Set where
  r-inl : ∀ {m} → P m → SNsum P Q (inl m)
  r-inr : ∀ {m} → Q m → SNsum P Q (inr m)
  r-ne  : ∀ {e} → SNe e → SNsum P Q e
  r-red : ∀ {e e′} → e ⟶SN e′ → SNsum P Q e′ → SNsum P Q e

R : ∀ {S} (A : Ty) → S ⊢ expr → Set
R ★ e = SN e
R {S} (A ⇒ᵗ B) e =
  ∀ {S₂} (ξ : S →ᴿ S₂) (n : S₂ ⊢ expr) → R A n → R B ((e [ ξ ]ᴿ) · n)
R (A +ᵗ B) e = SNsum (R A) (R B) e

SNsum-map : ∀ {S₁ S₂} {P Q : S₁ ⊢ expr → Set} {P′ Q′ : S₂ ⊢ expr → Set}
  (ξ : S₁ →ᴿ S₂) →
  (∀ {m} → P m → P′ (m [ ξ ]ᴿ)) → (∀ {m} → Q m → Q′ (m [ ξ ]ᴿ)) →
  ∀ {e} → SNsum P Q e → SNsum P′ Q′ (e [ ξ ]ᴿ)
SNsum-map ξ f g (r-inl p)    = r-inl (f p)
SNsum-map ξ f g (r-inr q)    = r-inr (g q)
SNsum-map ξ f g (r-ne ne)    = r-ne (ren-SNe ne ξ)
SNsum-map ξ f g (r-red st d) = r-red (ren-⟶SN st ξ) (SNsum-map ξ f g d)

R-ren : ∀ {S₁ S₂} (A : Ty) {e : S₁ ⊢ expr} → R A e → (ξ : S₁ →ᴿ S₂) → R A (e [ ξ ]ᴿ)
R-ren ★         d ξ = ren-SN d ξ
R-ren (A ⇒ᵗ B)  f ξ = λ ξ′ n rn → f (ξ ⨟ᴿ ξ′) n rn
R-ren (A +ᵗ B)  d ξ = SNsum-map ξ (λ p → R-ren A p ξ) (λ q → R-ren B q ξ) d

-- ─── Theorem 3.3: the reducibility candidate conditions ─────────────
-- At `+ᵗ`, CR2 and CR3 are the CONSTRUCTORS of SNsum.
cr1 : ∀ {S} (A : Ty) {e : S ⊢ expr} → R A e → SN e
cr2 : ∀ {S} (A : Ty) {e e′ : S ⊢ expr} → e ⟶SN e′ → R A e′ → R A e
cr3 : ∀ {S} (A : Ty) {e : S ⊢ expr} → SNe e → R A e

cr1 ★ d = d
cr1 (A ⇒ᵗ B) {e = e} f =
  anti-SN e (ext-SN (cr1 B (f (wkᴿ expr) (` zero) (cr3 A (var zero)))))
cr1 (A +ᵗ B) (r-inl p)    = inlS (cr1 A p)
cr1 (A +ᵗ B) (r-inr q)    = inrS (cr1 B q)
cr1 (A +ᵗ B) (r-ne ne)    = neu ne
cr1 (A +ᵗ B) (r-red st d) = red st (cr1 (A +ᵗ B) d)
cr2 ★ st d         = red st d
cr2 (A ⇒ᵗ B) st f  = λ ξ n rn → cr2 B (applSN (ren-⟶SN st ξ)) (f ξ n rn)
cr2 (A +ᵗ B) st d  = r-red st d
cr3 ★ ne           = neu ne
cr3 (A ⇒ᵗ B) ne    = λ ξ n rn → cr3 B (app (ren-SNe ne ξ) (cr1 A rn))
cr3 (A +ᵗ B) ne    = r-ne ne

-- ─── Definition 3.3: semantic substitutions ─────────────────────────
-- THIS is where the typing context enters.
Rˢ : ∀ {S₁ S₂} → Ctx S₁ → S₁ →ˢ S₂ → Set
Rˢ {S₁} Γ σ = ∀ (x : S₁ ∋ expr) → R (Γ x) (x [ σ ]ˢ)

Rˢ-ren : ∀ {S₁ S₂ S₃} {Γ : Ctx S₁} (σ : S₁ →ˢ S₂) → Rˢ Γ σ → (ξ : S₂ →ᴿ S₃) →
  Rˢ Γ (σ ⨟ ⟨ ξ ⟩)
Rˢ-ren σ rσ ξ x = R-ren _ (rσ x) ξ

Rˢ-ext : ∀ {S₁ S₂} {Γ : Ctx S₁} (σ : S₁ →ˢ S₂) {A} (n : S₂ ⊢ expr) →
  R A n → Rˢ Γ σ → Rˢ (A ∷ₜ Γ) (n ∙ˢ σ)
Rˢ-ext σ n rn rσ zero    = rn
Rˢ-ext σ n rn rσ (suc x) = rσ x

-- lifting a semantic substitution under a binder: needed for the two
-- BRANCHES of a case, which must be shown SN as OPEN terms
Rˢ-↑ : ∀ {S₁ S₂} {Γ : Ctx S₁} (σ : S₁ →ˢ S₂) (A : Ty) → Rˢ Γ σ →
  Rˢ (A ∷ₜ Γ) (σ ↑ˢ expr)
Rˢ-↑ σ A rσ zero    = cr3 A (var zero)
Rˢ-↑ σ A rσ (suc x) = R-ren _ (rσ x) (wkᴿ _)

-- ─── the case analysis, by induction on the SNsum derivation ────────
R-case : ∀ {S} {e : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} {A B C} →
  R (A +ᵗ B) e →
  (∀ (m : S ⊢ expr) → R A m → R C (u [ (m ∙ˢ idˢ) ]ˢ)) →
  (∀ (m : S ⊢ expr) → R B m → R C (v [ (m ∙ˢ idˢ) ]ˢ)) →
  SN u → SN v → R C (case e u v)
R-case {A = A} {C = C} (r-inl p)    hu hv su sv =
  cr2 C (βinl (cr1 A p) sv) (hu _ p)
R-case {B = B} {C = C} (r-inr q)    hu hv su sv =
  cr2 C (βinr (cr1 B q) su) (hv _ q)
R-case {C = C}         (r-ne ne)    hu hv su sv = cr3 C (cse ne su sv)
R-case {C = C}         (r-red st d) hu hv su sv =
  cr2 C (cseSN st) (R-case d hu hv su sv)

-- ─── Lemma 3.20: the fundamental lemma ──────────────────────────────
-- INDUCTION ON THE TYPING DERIVATION.
fund : ∀ {S₁ S₂} {Γ : Ctx S₁} {e : S₁ ⊢ expr} {A} {σ : S₁ →ˢ S₂} →
  Γ ⊢ e ∶ A → Rˢ Γ σ → R A (e [ σ ]ˢ)
fund (⊢` {x = x} refl) rσ = rσ x
fund {σ = σ} (⊢λ d) rσ = λ ξ n rn →
  cr2 _ (βSN (cr1 _ rn))
        (fund {σ = n ∙ˢ (σ ⨟ ⟨ ξ ⟩)} d
              (Rˢ-ext (σ ⨟ ⟨ ξ ⟩) n rn (Rˢ-ren σ rσ ξ)))
fund {σ = σ} (⊢· d₁ d₂) rσ =
  fund {σ = σ} d₁ rσ idᴿ _ (fund {σ = σ} d₂ rσ)
fund {σ = σ} (⊢inl d) rσ = r-inl (fund {σ = σ} d rσ)
fund {σ = σ} (⊢inr d) rσ = r-inr (fund {σ = σ} d rσ)
fund {σ = σ} (⊢case {A = A} {B = B} d du dv) rσ =
  R-case (fund {σ = σ} d rσ)
    (λ m rm → fund {σ = m ∙ˢ σ} du (Rˢ-ext σ m rm rσ))
    (λ m rm → fund {σ = m ∙ˢ σ} dv (Rˢ-ext σ m rm rσ))
    (cr1 _ (fund {σ = σ ↑ˢ expr} du (Rˢ-↑ σ A rσ)))
    (cr1 _ (fund {σ = σ ↑ˢ expr} dv (Rˢ-↑ σ B rσ)))

Rˢ-id : ∀ {S} (Γ : Ctx S) → Rˢ Γ (idˢ {S})
Rˢ-id Γ x = cr3 (Γ x) (var x)

-- ─── Corollary 3.4 ──────────────────────────────────────────────────
strong-normalisation : ∀ {S} {Γ : Ctx S} {e : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → SN e
strong-normalisation {Γ = Γ} {A = A} d = cr1 A (fund {σ = idˢ} d (Rˢ-id Γ))

-- ─── the syntax really does contain untypable terms ─────────────────
-- (so Corollary 3.4 is not the vacuous "every term is SN" that the
-- intrinsically typed encoding gives; Reloaded/SumsSoundness.agda
-- proves `¬ sn Ω`)

self-app : (expr ∷ []) ⊢ expr
self-app = (` zero) · (` zero)

Ω : [] ⊢ expr
Ω = (λx self-app) · (λx self-app)

-- ═══ CHALLENGE-REFERENCING NAMES ════════════════════════════════════

-- Lemma 3.2/3.3 [Weakening and anti-renaming for typing]
lemma-3-2-typed-renaming : ∀ {S₁ S₂} {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {e : S₁ ⊢ expr} {A} → Γ₁ ⊢ e ∶ A → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (e [ ξ ]ᴿ) ∶ A
lemma-3-2-typed-renaming {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢ξ =
  _⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢ξ

-- Lemma 3.4/3.5 [Substitution for typing]
lemma-3-4-typed-substitution : ∀ {S₁ S₂} {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {e : S₁ ⊢ expr} {A} → Γ₁ ⊢ e ∶ A → σ ∶ Γ₁ →ˢ Γ₂ → Γ₂ ⊢ (e [ σ ]ˢ) ∶ A
lemma-3-4-typed-substitution {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢σ =
  _⊢⋯ˢ_ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢σ

-- Lemma 3.17 [Renaming for SN]
lemma-3-17-renaming : ∀ {S₁ S₂} {e : S₁ ⊢ expr} → SN e → (ξ : S₁ →ᴿ S₂) → SN (e [ ξ ]ᴿ)
lemma-3-17-renaming = ren-SN

-- Lemma 3.18 [Anti-renaming for SN]
lemma-3-18-anti-renaming : ∀ {S₁ S₂} (e : S₁ ⊢ expr) {ξ : S₁ →ᴿ S₂} →
  SN (e [ ξ ]ᴿ) → SN e
lemma-3-18-anti-renaming = anti-SN

-- Lemma 3.19 [Extensionality of SN]
lemma-3-19-extensionality : ∀ {S} {e : S ⊢ expr} {x : S ∋ expr} →
  SN (e · (` x)) → SN e
lemma-3-19-extensionality = ext-SN

-- Theorem 3.3 [CR1 / CR2 / CR3]
theorem-3-3-CR1 : ∀ {S} (A : Ty) {e : S ⊢ expr} → R A e → SN e
theorem-3-3-CR1 = cr1
theorem-3-3-CR2 : ∀ {S} (A : Ty) {e e′ : S ⊢ expr} → e ⟶SN e′ → R A e′ → R A e
theorem-3-3-CR2 = cr2
theorem-3-3-CR3 : ∀ {S} (A : Ty) {e : S ⊢ expr} → SNe e → R A e
theorem-3-3-CR3 = cr3

-- Lemma 3.20 [Fundamental Lemma]
lemma-3-20-fundamental : ∀ {S₁ S₂} {Γ : Ctx S₁} {e : S₁ ⊢ expr} {A} {σ : S₁ →ˢ S₂} →
  Γ ⊢ e ∶ A → Rˢ Γ σ → R A (e [ σ ]ˢ)
lemma-3-20-fundamental {σ = σ} d rσ = fund {σ = σ} d rσ

-- Corollary 3.4 [every well-typed term is in SN]
corollary-3-4 : ∀ {S} {Γ : Ctx S} {e : S ⊢ expr} {A} → Γ ⊢ e ∶ A → SN e
corollary-3-4 = strong-normalisation
