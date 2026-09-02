{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLmark Reloaded, Challenges 2a and 2b, for STLC ══════════════
--   [Abel, Allais, Hameer, Pientka, Momigliano, Schäfer, Stark, JFP 2019]
--
--   2a  Lemma 3.17  renaming of SN / SNe / ⟶SN
--       Lemma 3.18  anti-renaming of SN / SNe / ⟶SN
--       Lemma 3.19  extensionality of SN
--   2b  Theorem 3.3   CR1, CR2, CR3 for the Kripke logical predicate R
--       Definition 3.3  semantic substitutions
--       Lemma 3.20   the Fundamental Lemma
--       Corollary 3.4  ⊢ M : A ⟹ M ∈ SN
--
-- Also proved here, as prerequisites: Lemma 3.2 (weakening and
-- exchange for typing), Lemma 3.3 (anti-renaming of typing), and the
-- substitution lemma for typing, which the challenge uses silently.
--
-- Challenges 1a and 1b are in Reloaded/Soundness.agda.
--
-- The terms are intrinsically SCOPED, not intrinsically typed, so
-- `S ⊢ expr` contains untypable terms and Corollary 3.4 has content.
--
-- The statements are collected at the end of this file.

module Reloaded.Normalization where

open import Languages.STLC

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst) renaming (trans to ≡-trans)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)

-- ═══ the object language's types and typing judgment ════════════════
-- Separate from the syntax, which is scoped only.

infixr 6 _⇒ᵗ_

data Ty : Set where
  ★    : Ty                     -- the base type
  _⇒ᵗ_ : Ty → Ty → Ty

-- An STLC type is closed, so a context needs no telescope: it assigns a
-- type to every variable in scope.
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
  ⊢`  : ∀ {S} {Γ : Ctx S} {x : S ∋ expr} {A} →
        Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  ⊢λ  : ∀ {S} {Γ : Ctx S} {e : (expr ∷ S) ⊢ expr} {A B} →
        (A ∷ₜ Γ) ⊢ e ∶ B → Γ ⊢ (λx e) ∶ (A ⇒ᵗ B)
  ⊢·  : ∀ {S} {Γ : Ctx S} {e₁ e₂ : S ⊢ expr} {A B} →
        Γ ⊢ e₁ ∶ (A ⇒ᵗ B) → Γ ⊢ e₂ ∶ A → Γ ⊢ (e₁ · e₂) ∶ B

-- ─── Lemmas 3.2 and 3.3: typed renamings ────────────────────────────

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
_⊢⋯ᴿ_ (⊢` {x = x} refl) ⊢ξ = ⊢` (⊢ξ x)
_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢λ {A = A} d) ⊢ξ =
  ⊢λ (_⊢⋯ᴿ_ {ξ = ξ ↑ᴿ expr} {Γ₁ = A ∷ₜ Γ₁} {Γ₂ = A ∷ₜ Γ₂} d
             (⊢↑ᴿ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ξ A))
_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢· d₁ d₂) ⊢ξ =
  ⊢· (_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d₁ ⊢ξ)
     (_⊢⋯ᴿ_ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d₂ ⊢ξ)

⊢weaken : ∀ {S} {Γ : Ctx S} {e : S ⊢ expr} {B} (A : Ty) →
  Γ ⊢ e ∶ B → (A ∷ₜ Γ) ⊢ (e [ wkᴿ expr ]ᴿ) ∶ B
⊢weaken {Γ = Γ} A d = _⊢⋯ᴿ_ {ξ = wkᴿ expr} {Γ₁ = Γ} {Γ₂ = A ∷ₜ Γ} d (⊢wkᴿ A)

-- Lemma 3.3: anti-renaming of typing.  The term is scrutinised first, so
-- that `e [ ξ ]ᴿ` reduces to a constructor form.
anti-ren-⊢ : ∀ {S₁ S₂} {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  (e : S₁ ⊢ expr) {A} → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (e [ ξ ]ᴿ) ∶ A → Γ₁ ⊢ e ∶ A
anti-ren-⊢ (` x) ⊢ξ (⊢` eq) = ⊢` (≡-trans (sym (⊢ξ x)) eq)
anti-ren-⊢ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (λx e) ⊢ξ (⊢λ {A = A} d) =
  ⊢λ (anti-ren-⊢ {ξ = ξ ↑ᴿ expr} {Γ₁ = A ∷ₜ Γ₁} {Γ₂ = A ∷ₜ Γ₂} e
                 (⊢↑ᴿ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ξ A) d)
anti-ren-⊢ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (e₁ · e₂) ⊢ξ (⊢· d₁ d₂) =
  ⊢· (anti-ren-⊢ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} e₁ ⊢ξ d₁)
     (anti-ren-⊢ {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} e₂ ⊢ξ d₂)

-- ─── typed substitutions ────────────────────────────────────────────

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

⊢∙ˢ : ∀ {S} {Γ : Ctx S} {n : S ⊢ expr} {A} →
  Γ ⊢ n ∶ A → (n ∙ˢ idˢ) ∶ (A ∷ₜ Γ) →ˢ Γ
⊢∙ˢ dn zero    = dn
⊢∙ˢ dn (suc x) = ⊢` refl

-- the substitution lemma
⊢[] : ∀ {S} {Γ : Ctx S} {e : (expr ∷ S) ⊢ expr} {n : S ⊢ expr} {A B} →
  (A ∷ₜ Γ) ⊢ e ∶ B → Γ ⊢ n ∶ A → Γ ⊢ (e [ n ]₀) ∶ B
⊢[] {Γ = Γ} {n = n} {A = A} d dn =
  _⊢⋯ˢ_ {σ = n ∙ˢ idˢ} {Γ₁ = A ∷ₜ Γ} {Γ₂ = Γ} d (⊢∙ˢ dn)

-- ─── the inductive characterisation of strong normalisation ─────────
-- Fig. 3 of the challenge, transcribed rule for rule.  The paper's
-- typing premises (in the β rule of ⟶SN and in its congruence rule) are
-- dropped, not hidden in the indices: SN is a predicate on raw scoped
-- terms.  Nothing in 2a/2b needs them.

data SNe    : ∀ {S} → S ⊢ expr → Set
data SN     : ∀ {S} → S ⊢ expr → Set
data _⟶SN_ : ∀ {S} → S ⊢ expr → S ⊢ expr → Set

infix 3 _⟶SN_

data SNe where
  var : ∀ {S} (x : S ∋ expr) → SNe (` x)
  app : ∀ {S} {r n : S ⊢ expr} → SNe r → SN n → SNe (r · n)

data SN where
  abs : ∀ {S} {e : (expr ∷ S) ⊢ expr} → SN e → SN (λx e)
  neu : ∀ {S} {r : S ⊢ expr} → SNe r → SN r
  red : ∀ {S} {e e′ : S ⊢ expr} → e ⟶SN e′ → SN e′ → SN e

data _⟶SN_ where
  βSN   : ∀ {S} {e : (expr ∷ S) ⊢ expr} {n : S ⊢ expr} →
          SN n → ((λx e) · n) ⟶SN (e [ n ]₀)
  applSN : ∀ {S} {e e′ n : S ⊢ expr} →
          e ⟶SN e′ → (e · n) ⟶SN (e′ · n)

-- ═══ challenge 2a ═══════════════════════════════════════════════════

-- ─── Lemma 3.17: renaming ───────────────────────────────────────────

ren-SNe : ∀ {S₁ S₂} {e : S₁ ⊢ expr} → SNe e → (ξ : S₁ →ᴿ S₂) → SNe (e [ ξ ]ᴿ)
ren-SN  : ∀ {S₁ S₂} {e : S₁ ⊢ expr} → SN e → (ξ : S₁ →ᴿ S₂) → SN (e [ ξ ]ᴿ)
ren-⟶SN : ∀ {S₁ S₂} {e e′ : S₁ ⊢ expr} → e ⟶SN e′ → (ξ : S₁ →ᴿ S₂) →
          (e [ ξ ]ᴿ) ⟶SN (e′ [ ξ ]ᴿ)

ren-SNe (var x)   ξ = var (x [ ξ ]ᴿ)
ren-SNe (app r n) ξ = app (ren-SNe r ξ) (ren-SN n ξ)

ren-SN (abs d)    ξ = abs (ren-SN d (ξ ↑ᴿ _))
ren-SN (neu r)    ξ = neu (ren-SNe r ξ)
ren-SN (red st d) ξ = red (ren-⟶SN st ξ) (ren-SN d ξ)

ren-⟶SN (βSN n)    ξ = βSN (ren-SN n ξ)      -- no transport
ren-⟶SN (applSN st) ξ = applSN (ren-⟶SN st ξ)

-- ─── Lemma 3.18: anti-renaming ──────────────────────────────────────
-- It must invert through `e [ ξ ]ᴿ`, so it holds for renamings only.
-- The term is scrutinised first, so that `e [ ξ ]ᴿ` reduces to a
-- constructor form and the derivation can be matched directly.

anti-SNe : ∀ {S₁ S₂} (e : S₁ ⊢ expr) {ξ : S₁ →ᴿ S₂} → SNe (e [ ξ ]ᴿ) → SNe e
anti-SN  : ∀ {S₁ S₂} (e : S₁ ⊢ expr) {ξ : S₁ →ᴿ S₂} → SN (e [ ξ ]ᴿ) → SN e
anti-⟶SN : ∀ {S₁ S₂} (e : S₁ ⊢ expr) {ξ : S₁ →ᴿ S₂} {n : S₂ ⊢ expr} →
  (e [ ξ ]ᴿ) ⟶SN n → Σ[ e′ ∈ S₁ ⊢ expr ] ((e ⟶SN e′) × (e′ [ ξ ]ᴿ ≡ n))

anti-SNe (` x)     (var _)   = var x
anti-SNe (λx e)    ()
anti-SNe (e₁ · e₂) {ξ = ξ} (app r n) =
  app (anti-SNe e₁ {ξ = ξ} r) (anti-SN e₂ {ξ = ξ} n)

anti-SN (` x)  {ξ = ξ} (neu ne) = neu (anti-SNe (` x) {ξ = ξ} ne)
anti-SN (` x)  (red () d)
anti-SN (λx e) {ξ = ξ} (abs d)  = abs (anti-SN e {ξ = ξ ↑ᴿ _} d)
anti-SN (λx e) (neu ())
anti-SN (λx e) (red () d)
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

-- ─── substituting a variable is a renaming ──────────────────────────
-- The one substitution fact this module proves by hand; ext-SN below is
-- its only call site.

ren-as-sub : ∀ {S₁ S₂ s} (t : S₁ ⊢ s) (σ : S₁ →ˢ S₂) (ξ : S₁ →ᴿ S₂) →
  (∀ {s′} (y : S₁ ∋ s′) → y [ σ ]ˢ ≡ ` (y [ ξ ]ᴿ)) → t [ σ ]ˢ ≡ t [ ξ ]ᴿ
ren-as-sub (` y)     σ ξ h = h y
ren-as-sub (λx e)    σ ξ h = cong λx_ (ren-as-sub e (σ ↑ˢ _) (ξ ↑ᴿ _)
  λ { zero → refl ; (suc y) → cong (_[ wkᴿ _ ]ᴿ) (h y) })
ren-as-sub (e₁ · e₂) σ ξ h =
  cong₂ _·_ (ren-as-sub e₁ σ ξ h) (ren-as-sub e₂ σ ξ h)

[]-as-ren : ∀ {S} (t : (expr ∷ S) ⊢ expr) (x : S ∋ expr) →
  t [ ` x ]₀ ≡ t [ (x ∙ᴿ idᴿ) ]ᴿ
[]-as-ren t x = ren-as-sub t ((` x) ∙ˢ idˢ) (x ∙ᴿ idᴿ)
  λ { zero → refl ; (suc y) → refl }

-- ─── Lemma 3.19: extensionality of SN ───────────────────────────────
-- In the β case the redex contracts to `b [ ` x ]₀`, a renaming by the
-- lemma above, so anti-renaming (3.18) applies.

ext-SN : ∀ {S} {e : S ⊢ expr} {x : S ∋ expr} → SN (e · (` x)) → SN e
ext-SN (neu (app r n))     = neu r
ext-SN (red (applSN st) d) = red st (ext-SN d)
ext-SN {x = x} (red (βSN {e = b} _) d) =
  abs (anti-SN b {ξ = x ∙ᴿ idᴿ} (subst SN ([]-as-ren b x) d))

-- ═══ challenge 2b: the Kripke logical predicate ═════════════════════
-- Defined by recursion on the type; the world quantification sits in
-- the arrow case, over renamings.  `R A e` does not presuppose
-- `Γ ⊢ e ∶ A`.
R : ∀ {S} (A : Ty) → S ⊢ expr → Set
R ★ e = SN e
R {S} (A ⇒ᵗ B) e =
  ∀ {S₂} (ξ : S →ᴿ S₂) (n : S₂ ⊢ expr) → R A n → R B ((e [ ξ ]ᴿ) · n)

-- R is closed under renaming
R-ren : ∀ {S₁ S₂} (A : Ty) {e : S₁ ⊢ expr} → R A e → (ξ : S₁ →ᴿ S₂) → R A (e [ ξ ]ᴿ)
R-ren ★         d ξ = ren-SN d ξ
R-ren (A ⇒ᵗ B)  f ξ = λ ξ′ n rn → f (ξ ⨟ᴿ ξ′) n rn

-- ─── Theorem 3.3: the reducibility candidate conditions ─────────────
cr1 : ∀ {S} (A : Ty) {e : S ⊢ expr} → R A e → SN e
cr2 : ∀ {S} (A : Ty) {e e′ : S ⊢ expr} → e ⟶SN e′ → R A e′ → R A e
cr3 : ∀ {S} (A : Ty) {e : S ⊢ expr} → SNe e → R A e

cr1 ★ d = d
cr1 (A ⇒ᵗ B) {e = e} f =
  anti-SN e (ext-SN (cr1 B (f (wkᴿ expr) (` zero) (cr3 A (var zero)))))
cr2 ★ st d         = red st d
cr2 (A ⇒ᵗ B) st f  = λ ξ n rn → cr2 B (applSN (ren-⟶SN st ξ)) (f ξ n rn)
cr3 ★ ne           = neu ne
cr3 (A ⇒ᵗ B) ne    = λ ξ n rn → cr3 B (app (ren-SNe ne ξ) (cr1 A rn))

-- ─── Definition 3.3: semantic substitutions ─────────────────────────
-- σ is reducible at Γ when it sends each variable to a term reducible
-- at the type Γ gives it.
Rˢ : ∀ {S₁ S₂} → Ctx S₁ → S₁ →ˢ S₂ → Set
Rˢ {S₁} Γ σ = ∀ (x : S₁ ∋ expr) → R (Γ x) (x [ σ ]ˢ)

-- weakening of semantic substitutions
Rˢ-ren : ∀ {S₁ S₂ S₃} {Γ : Ctx S₁} (σ : S₁ →ˢ S₂) → Rˢ Γ σ → (ξ : S₂ →ᴿ S₃) →
  Rˢ Γ (σ ⨟ ⟨ ξ ⟩)
Rˢ-ren σ rσ ξ x = R-ren _ (rσ x) ξ

Rˢ-ext : ∀ {S₁ S₂} {Γ : Ctx S₁} (σ : S₁ →ˢ S₂) {A} (n : S₂ ⊢ expr) →
  R A n → Rˢ Γ σ → Rˢ (A ∷ₜ Γ) (n ∙ˢ σ)
Rˢ-ext σ n rn rσ zero    = rn
Rˢ-ext σ n rn rσ (suc x) = rσ x

-- ─── Lemma 3.20: the fundamental lemma ──────────────────────────────
-- induction on the typing derivation
fund : ∀ {S₁ S₂} {Γ : Ctx S₁} {e : S₁ ⊢ expr} {A} {σ : S₁ →ˢ S₂} →
  Γ ⊢ e ∶ A → Rˢ Γ σ → R A (e [ σ ]ˢ)
fund (⊢` {x = x} refl) rσ = rσ x
fund {σ = σ} (⊢λ d) rσ = λ ξ n rn →
  cr2 _ (βSN (cr1 _ rn))
        (fund {σ = n ∙ˢ (σ ⨟ ⟨ ξ ⟩)} d
              (Rˢ-ext (σ ⨟ ⟨ ξ ⟩) n rn (Rˢ-ren σ rσ ξ)))
fund {σ = σ} (⊢· d₁ d₂) rσ =
  fund {σ = σ} d₁ rσ idᴿ _ (fund {σ = σ} d₂ rσ)

Rˢ-id : ∀ {S} (Γ : Ctx S) → Rˢ Γ (idˢ {S})
Rˢ-id Γ x = cr3 (Γ x) (var x)

-- ─── Corollary 3.4 ──────────────────────────────────────────────────
-- every well-typed term is strongly normalising, in the inductive sense
strong-normalisation : ∀ {S} {Γ : Ctx S} {e : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → SN e
strong-normalisation {Γ = Γ} {A = A} d = cr1 A (fund {σ = idˢ} d (Rˢ-id Γ))

-- ─── the syntax really does contain untypable terms ─────────────────
-- so Corollary 3.4 is not the vacuous "every term is SN"

self-app : (expr ∷ []) ⊢ expr
self-app = (` zero) · (` zero)

Ω : [] ⊢ expr
Ω = (λx self-app) · (λx self-app)

-- ═══ challenge-referencing names ════════════════════════════════════

-- Lemma 3.2 [Weakening and exchange for typing]
lemma-3-2-typed-renaming : ∀ {S₁ S₂} {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {e : S₁ ⊢ expr} {A} → Γ₁ ⊢ e ∶ A → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (e [ ξ ]ᴿ) ∶ A
lemma-3-2-typed-renaming = _⊢⋯ᴿ_

-- Lemma 3.3 [Anti-renaming of typing]
lemma-3-3-anti-renaming : ∀ {S₁ S₂} {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  (e : S₁ ⊢ expr) {A} → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (e [ ξ ]ᴿ) ∶ A → Γ₁ ⊢ e ∶ A
lemma-3-3-anti-renaming = anti-ren-⊢

-- Substitution for typing.  The challenge uses this silently; its
-- Lemmas 3.4 and 3.5 are the corresponding statements for typed
-- REDUCTION, which are `ren-↝` and `sub-↝` in the Soundness modules.
typed-substitution : ∀ {S₁ S₂} {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {e : S₁ ⊢ expr} {A} → Γ₁ ⊢ e ∶ A → σ ∶ Γ₁ →ˢ Γ₂ → Γ₂ ⊢ (e [ σ ]ˢ) ∶ A
typed-substitution {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} d ⊢σ =
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
