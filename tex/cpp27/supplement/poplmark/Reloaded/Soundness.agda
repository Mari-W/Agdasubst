{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLMark Reloaded, Challenges 1a and 1b ════════════════════════
--
--   1a  properties of the accessibility predicate `sn`: subterm and
--       expansion closure, closure of neutrals, CONFLUENCE ("weak
--       standardisation") and BACKWARD CLOSURE   (Lemmas 3.8-3.13)
--   1b  soundness of the inductive characterisation:
--       SN ⟹ sn,  SNe ⟹ sn,  ⟶SN ⟹ ⟶sn        (Lemma 3.14, Thm 3.1)
--
-- Together with Reloaded/Normalization.agda (2a/2b) this closes the STLC
-- half of the challenge:  every WELL-TYPED term is strongly normalising
-- in the classical, accessibility sense.
--
-- The syntax is intrinsically SCOPED (Languages/STLC.agda), so `_↝_`,
-- `sn`, `ne` and `_⟶sn_` are relations on raw λ-terms and every lemma
-- of 1a is a statement about arbitrary terms, typed or not.  Typing
-- enters in exactly two places: `preservation` (the challenge's Lemma
-- 3.1, which the intrinsically typed encoding got for free and which is
-- proved below in four lines) and `corollary-3-4-sn`.
--
-- The σ-calculus contribution here is Lemma 3.7 (`sub-↝`, `ren-↝`):
-- reduction is closed under substitution because
--   (b [ n ]₀) [ σ ]ˢ ≡ (b [ (σ ↑ˢ expr) ]ˢ) [ n [ σ ]ˢ ]₀
-- holds DEFINITIONALLY, so the β case of each of those lemmas is a bare
-- constructor.  Everything else is ordinary induction on derivations.

module Reloaded.Soundness where

open import Languages.STLC
open import Reloaded.Normalization

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)

-- ─── full β-reduction, and strong normalisation as accessibility ────

infix 3 _↝_ _↝*_

data _↝_ : ∀ {S} → S ⊢ expr → S ⊢ expr → Set where
  β↝  : ∀ {S} {b : (expr ∷ S) ⊢ expr} {n : S ⊢ expr} → ((λx b) · n) ↝ (b [ n ]₀)
  ξλ  : ∀ {S} {b b′ : (expr ∷ S) ⊢ expr} → b ↝ b′ → (λx b) ↝ (λx b′)
  ξ·₁ : ∀ {S} {e e′ n : S ⊢ expr} → e ↝ e′ → (e · n) ↝ (e′ · n)
  ξ·₂ : ∀ {S} {e n n′ : S ⊢ expr} → n ↝ n′ → (e · n) ↝ (e · n′)

data _↝*_ : ∀ {S} → S ⊢ expr → S ⊢ expr → Set where
  done : ∀ {S} {e : S ⊢ expr} → e ↝* e
  _◅_  : ∀ {S} {e₁ e₂ e₃ : S ⊢ expr} → e₁ ↝ e₂ → e₂ ↝* e₃ → e₁ ↝* e₃

infixr 5 _◅_

data sn {S} (e : S ⊢ expr) : Set where
  acc : (∀ e′ → e ↝ e′ → sn e′) → sn e

-- neutral terms (the weaker `ne` of §3.3, not SNe)
data ne : ∀ {S} → S ⊢ expr → Set where
  nvar : ∀ {S} (x : S ∋ expr) → ne (` x)
  napp : ∀ {S} {r n : S ⊢ expr} → ne r → ne (r · n)

-- sn-flavoured strong head reduction
infix 3 _⟶sn_
data _⟶sn_ : ∀ {S} → S ⊢ expr → S ⊢ expr → Set where
  βsn    : ∀ {S} {b : (expr ∷ S) ⊢ expr} {n : S ⊢ expr} →
           sn n → ((λx b) · n) ⟶sn (b [ n ]₀)
  applsn : ∀ {S} {e e′ n : S ⊢ expr} →
           e ⟶sn e′ → (e · n) ⟶sn (e′ · n)

-- ─── Lemma 3.1: reduction preserves typing ──────────────────────────
-- NOT vacuous any more -- the syntax is scoped, not typed -- but the β
-- case is exactly the substitution lemma `⊢[]` of Reloaded.Normalization,
-- whose own proof is definitional in the σ-calculus.

preservation : ∀ {S} {Γ : Ctx S} {e e′ : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → e ↝ e′ → Γ ⊢ e′ ∶ A
preservation (⊢· (⊢λ db) dn) β↝       = ⊢[] db dn
preservation (⊢λ db)         (ξλ st)  = ⊢λ (preservation db st)
preservation (⊢· d₁ d₂)      (ξ·₁ st) = ⊢· (preservation d₁ st) d₂
preservation (⊢· d₁ d₂)      (ξ·₂ st) = ⊢· d₁ (preservation d₂ st)

preservation* : ∀ {S} {Γ : Ctx S} {e e′ : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → e ↝* e′ → Γ ⊢ e′ ∶ A
preservation* d done     = d
preservation* d (st ◅ r) = preservation* (preservation d st) r

-- ─── Lemma 3.6: multi-step congruences ──────────────────────────────

↝*-trans : ∀ {S} {e₁ e₂ e₃ : S ⊢ expr} → e₁ ↝* e₂ → e₂ ↝* e₃ → e₁ ↝* e₃
↝*-trans done      r = r
↝*-trans (st ◅ r₁) r = st ◅ ↝*-trans r₁ r

↝*-λ : ∀ {S} {b b′ : (expr ∷ S) ⊢ expr} → b ↝* b′ → (λx b) ↝* (λx b′)
↝*-λ done      = done
↝*-λ (st ◅ r)  = ξλ st ◅ ↝*-λ r

↝*-·₁ : ∀ {S} {e e′ n : S ⊢ expr} → e ↝* e′ → (e · n) ↝* (e′ · n)
↝*-·₁ done     = done
↝*-·₁ (st ◅ r) = ξ·₁ st ◅ ↝*-·₁ r

↝*-·₂ : ∀ {S} {e n n′ : S ⊢ expr} → n ↝* n′ → (e · n) ↝* (e · n′)
↝*-·₂ done     = done
↝*-·₂ (st ◅ r) = ξ·₂ st ◅ ↝*-·₂ r

-- ─── Lemma 3.7: reduction under renaming and substitution ───────────
-- Both β cases are `β↝` on the nose: the σ-calculus discharges
--   (b [ n ]₀) [ ξ ]ᴿ ≡ (b [ (ξ ↑ᴿ expr) ]ᴿ) [ n [ ξ ]ᴿ ]₀     and
--   (b [ n ]₀) [ σ ]ˢ ≡ (b [ (σ ↑ˢ expr) ]ˢ) [ n [ σ ]ˢ ]₀
-- definitionally.

ren-↝ : ∀ {S₁ S₂} {e e′ : S₁ ⊢ expr} → e ↝ e′ → (ξ : S₁ →ᴿ S₂) →
  (e [ ξ ]ᴿ) ↝ (e′ [ ξ ]ᴿ)
ren-↝ β↝       ξ = β↝
ren-↝ (ξλ st)  ξ = ξλ (ren-↝ st (ξ ↑ᴿ _))
ren-↝ (ξ·₁ st) ξ = ξ·₁ (ren-↝ st ξ)
ren-↝ (ξ·₂ st) ξ = ξ·₂ (ren-↝ st ξ)

sub-↝ : ∀ {S₁ S₂} {e e′ : S₁ ⊢ expr} → e ↝ e′ → (σ : S₁ →ˢ S₂) →
  (e [ σ ]ˢ) ↝ (e′ [ σ ]ˢ)
sub-↝ β↝       σ = β↝
sub-↝ (ξλ st)  σ = ξλ (sub-↝ st (σ ↑ˢ _))
sub-↝ (ξ·₁ st) σ = ξ·₁ (sub-↝ st σ)
sub-↝ (ξ·₂ st) σ = ξ·₂ (sub-↝ st σ)

ren-↝* : ∀ {S₁ S₂} {e e′ : S₁ ⊢ expr} → e ↝* e′ → (ξ : S₁ →ᴿ S₂) →
  (e [ ξ ]ᴿ) ↝* (e′ [ ξ ]ᴿ)
ren-↝* done     ξ = done
ren-↝* (st ◅ r) ξ = ren-↝ st ξ ◅ ren-↝* r ξ

-- Lemma 3.6(5): reducing INSIDE the substitution.  Stated pointwise, as
-- the map-level statement the two-world system wants.
sub-↝* : ∀ {S₁ S₂} (t : S₁ ⊢ expr) (σ σ′ : S₁ →ˢ S₂) →
  (∀ (y : S₁ ∋ expr) → (y [ σ ]ˢ) ↝* (y [ σ′ ]ˢ)) → (t [ σ ]ˢ) ↝* (t [ σ′ ]ˢ)
sub-↝* (` y)     σ σ′ h = h y
sub-↝* (λx b)    σ σ′ h = ↝*-λ (sub-↝* b (σ ↑ˢ _) (σ′ ↑ˢ _)
  λ { zero → done ; (suc y) → ren-↝* (h y) (wkᴿ _) })
sub-↝* (e₁ · e₂) σ σ′ h =
  ↝*-trans (↝*-·₁ (sub-↝* e₁ σ σ′ h)) (↝*-·₂ (sub-↝* e₂ σ σ′ h))

sub-↝*-arg : ∀ {S} (b : (expr ∷ S) ⊢ expr) {n n′ : S ⊢ expr} →
  n ↝ n′ → (b [ n ]₀) ↝* (b [ n′ ]₀)
sub-↝*-arg b {n} {n′} st = sub-↝* b (n ∙ˢ idˢ) (n′ ∙ˢ idˢ)
  λ { zero → st ◅ done ; (suc y) → done }

-- ─── Lemma 3.8 and the basic sn lemmas (3.9) ────────────────────────

sn-↝ : ∀ {S} {e e′ : S ⊢ expr} → sn e → e ↝ e′ → sn e′
sn-↝ (acc f) st = f _ st

sn-↝* : ∀ {S} {e e′ : S ⊢ expr} → sn e → e ↝* e′ → sn e′
sn-↝* d done      = d
sn-↝* d (st ◅ r)  = sn-↝* (sn-↝ d st) r

sn-var : ∀ {S} (x : S ∋ expr) → sn (` x)
sn-var x = acc λ _ ()

sn-abs : ∀ {S} {b : (expr ∷ S) ⊢ expr} → sn b → sn (λx b)
sn-abs (acc f) = acc λ where _ (ξλ st) → sn-abs (f _ st)

sn-app₁ : ∀ {S} {e n : S ⊢ expr} → sn (e · n) → sn e
sn-app₁ (acc f) = acc λ e′ st → sn-app₁ (f (e′ · _) (ξ·₁ st))

sn-app₂ : ∀ {S} {e n : S ⊢ expr} → sn (e · n) → sn n
sn-app₂ (acc f) = acc λ n′ st → sn-app₂ (f (_ · n′) (ξ·₂ st))

-- 3.9(3): anti-substitution
anti-sub-sn : ∀ {S₁ S₂} (t : S₁ ⊢ expr) (σ : S₁ →ˢ S₂) → sn (t [ σ ]ˢ) → sn t
anti-sub-sn t σ (acc f) = acc λ t′ st → anti-sub-sn t′ σ (f (t′ [ σ ]ˢ) (sub-↝ st σ))

-- ─── two impossibility lemmas ───────────────────────────────────────

ne-λ-⊥ : ∀ {S} {b : (expr ∷ S) ⊢ expr} → ne (λx b) → ⊥
ne-λ-⊥ ()

⟶sn-λ-⊥ : ∀ {S} {b : (expr ∷ S) ⊢ expr} {e′ : S ⊢ expr} → (λx b) ⟶sn e′ → ⊥
⟶sn-λ-⊥ ()

-- ─── Lemma 3.10: weak head expansion ────────────────────────────────
-- lexicographic in (sn n, sn b); the `sn b` argument is what the paper
-- obtains from 3.9(3), and we take it as a parameter.

sn-β-exp : ∀ {S} {b : (expr ∷ S) ⊢ expr} {n : S ⊢ expr} →
  sn n → sn b → sn (b [ n ]₀) → sn ((λx b) · n)
sn-β-exp {b = b} {n = n} snn@(acc fn) snb@(acc fb) h = acc λ where
  _ β↝            → h
  _ (ξ·₁ (ξλ st)) → sn-β-exp snn (fb _ st) (sn-↝ h (sub-↝ st (n ∙ˢ idˢ)))
  _ (ξ·₂ st)      → sn-β-exp (fn _ st) snb (sn-↝* h (sub-↝*-arg b st))

-- ─── Lemma 3.11: closure properties of neutral terms ────────────────

ne-↝ : ∀ {S} {r r′ : S ⊢ expr} → ne r → r ↝ r′ → ne r′
ne-↝ (napp ())  β↝
ne-↝ (napp nr) (ξ·₁ st) = napp (ne-↝ nr st)
ne-↝ (napp nr) (ξ·₂ st) = napp nr

ne-app-sn : ∀ {S} {r n : S ⊢ expr} → ne r → sn r → sn n → sn (r · n)
ne-app-sn nr snr@(acc fr) snn@(acc fn) = acc λ where
  _ β↝       → ⊥-elim (ne-λ-⊥ nr)
  _ (ξ·₁ st) → ne-app-sn (ne-↝ nr st) (fr _ st) snn
  _ (ξ·₂ st) → ne-app-sn nr snr (fn _ st)

-- ─── Lemma 3.12: confluence of sn ("weak standardisation") ──────────

confl : ∀ {S} {e m m′ : S ⊢ expr} → e ⟶sn m → e ↝ m′ →
  (m ≡ m′) ⊎ (Σ[ q ∈ S ⊢ expr ] ((m′ ⟶sn q) × (m ↝* q)))
confl (βsn snn) β↝              = inj₁ refl
confl (βsn {n = n} snn) (ξ·₁ (ξλ st)) =
  inj₂ (_ , βsn snn , sub-↝ st (n ∙ˢ idˢ) ◅ done)
confl (βsn {b = b} snn) (ξ·₂ st) =
  inj₂ (_ , βsn (sn-↝ snn st) , sub-↝*-arg b st)
confl (applsn st₀) β↝           = ⊥-elim (⟶sn-λ-⊥ st₀)
confl (applsn st₀) (ξ·₂ st)     = inj₂ (_ , applsn st₀ , ξ·₂ st ◅ done)
confl (applsn st₀) (ξ·₁ st) with confl st₀ st
... | inj₁ refl          = inj₁ refl
... | inj₂ (q , st′ , r) = inj₂ (q · _ , applsn st′ , ↝*-·₁ r)

-- ─── Lemma 3.13: backward closure of sn ─────────────────────────────
-- lexicographic in (sn e, sn n); the ξ·₁ case is where confluence is
-- cashed in.

sn-app-exp : ∀ {S} {e e′ n : S ⊢ expr} →
  sn n → sn e → e ⟶sn e′ → sn (e′ · n) → sn (e · n)
sn-app-exp-ξ : ∀ {S} {e e′ e″ n : S ⊢ expr} →
  sn n → sn e → e ⟶sn e′ → sn (e′ · n) → e ↝ e″ → sn (e″ · n)

sn-app-exp snn@(acc fn) sne st₀ h = acc λ where
  _ β↝       → ⊥-elim (⟶sn-λ-⊥ st₀)
  _ (ξ·₁ st) → sn-app-exp-ξ snn sne st₀ h st
  _ (ξ·₂ st) → sn-app-exp (fn _ st) sne st₀ (sn-↝ h (ξ·₂ st))

sn-app-exp-ξ snn sne@(acc fe) st₀ h st with confl st₀ st
... | inj₁ refl          = h
... | inj₂ (q , st′ , r) = sn-app-exp snn (fe _ st) st′ (sn-↝* h (↝*-·₁ r))

sn-⟶sn-exp : ∀ {S} {e e′ : S ⊢ expr} → e ⟶sn e′ → sn e′ → sn e
sn-⟶sn-exp (βsn {b = b} {n = n} snn) h =
  sn-β-exp snn (anti-sub-sn b (n ∙ˢ idˢ) h) h
sn-⟶sn-exp (applsn st₀) h =
  sn-app-exp (sn-app₂ h) (sn-⟶sn-exp st₀ (sn-app₁ h)) st₀ h

-- ═══ CHALLENGE 1b: soundness of the inductive definition ════════════

-- Lemma 3.14
SNe→ne : ∀ {S} {e : S ⊢ expr} → SNe e → ne e
SNe→ne (var x)   = nvar x
SNe→ne (app r n) = napp (SNe→ne r)

-- Theorem 3.1
sound-SNe : ∀ {S} {e : S ⊢ expr} → SNe e → sn e
sound-SN  : ∀ {S} {e : S ⊢ expr} → SN e → sn e
sound-⟶SN : ∀ {S} {e e′ : S ⊢ expr} → e ⟶SN e′ → e ⟶sn e′

sound-SNe (var x)   = sn-var x
sound-SNe (app r n) = ne-app-sn (SNe→ne r) (sound-SNe r) (sound-SN n)

sound-SN (abs d)    = sn-abs (sound-SN d)
sound-SN (neu r)    = sound-SNe r
sound-SN (red st d) = sn-⟶sn-exp (sound-⟶SN st) (sound-SN d)

sound-⟶SN (βSN n)     = βsn (sound-SN n)
sound-⟶SN (applSN st) = applsn (sound-⟶SN st)

-- ═══ THE CHALLENGE, ASSEMBLED ═══════════════════════════════════════
-- every WELL-TYPED term is strongly normalising, in the classical
-- accessibility sense (Cor. 3.4 + Thm 3.1)

strongly-normalising : ∀ {S} {Γ : Ctx S} {e : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → sn e
strongly-normalising d = sound-SN (strong-normalisation d)

-- ─── sanity: the encoding is not vacuous ────────────────────────────

Γ₀ : Ctx []
Γ₀ ()

Kid : [] ⊢ expr
Kid = λx (` zero)

⊢Kid : Γ₀ ⊢ Kid ∶ (★ ⇒ᵗ ★)
⊢Kid = ⊢λ (⊢` refl)

-- a genuine β-redex, and both notions of strong normalisation for it
redex : [] ⊢ expr
redex = (λx (` zero)) · Kid

⊢redex : Γ₀ ⊢ redex ∶ (★ ⇒ᵗ ★)
⊢redex = ⊢· (⊢λ (⊢` refl)) ⊢Kid

redex-steps : redex ↝ Kid
redex-steps = β↝

SN-redex : SN redex
SN-redex = strong-normalisation ⊢redex

sn-redex : sn redex
sn-redex = strongly-normalising ⊢redex

-- ─── and the typing hypothesis is doing real work ───────────────────
-- `Ω` (defined in Reloaded/Normalization.agda) is a well-SCOPED term that
-- is NOT strongly normalising.  Under the old intrinsically typed
-- encoding it could not even be written down, which is exactly why
-- `corollary-3-4-sn` was vacuous there and is not vacuous here.
-- `Ω ↝ Ω` is `β↝` on the nose: the σ-calculus computes the contractum
-- `((` zero) · (` zero)) [ λx ((` zero) · (` zero)) ]₀` to `Ω` itself.

Ω-loops : Ω ↝ Ω
Ω-loops = β↝

¬sn-Ω : sn Ω → ⊥
¬sn-Ω (acc f) = ¬sn-Ω (f Ω Ω-loops)

-- ═══ CHALLENGE-REFERENCING NAMES ════════════════════════════════════

-- Lemma 3.1 [Reduction preserves typing]
lemma-3-1-preservation : ∀ {S} {Γ : Ctx S} {e e′ : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → e ↝ e′ → Γ ⊢ e′ ∶ A
lemma-3-1-preservation = preservation

-- Lemma 3.14 [SNe implies ne]
lemma-3-14-SNe-ne : ∀ {S} {e : S ⊢ expr} → SNe e → ne e
lemma-3-14-SNe-ne = SNe→ne

-- Theorem 3.1 [Soundness of SN with respect to sn]
theorem-3-1-soundness : ∀ {S} {e : S ⊢ expr} → SN e → sn e
theorem-3-1-soundness = sound-SN

-- Corollary 3.4 + Theorem 3.1: every well-typed term is strongly
-- normalising in the classical accessibility sense
corollary-3-4-sn : ∀ {S} {Γ : Ctx S} {e : S ⊢ expr} {A} → Γ ⊢ e ∶ A → sn e
corollary-3-4-sn = strongly-normalising
