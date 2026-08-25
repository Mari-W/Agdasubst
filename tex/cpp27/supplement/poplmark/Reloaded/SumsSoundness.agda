{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLmark Reloaded STLC+, Challenges 1a and 1b (with sums) ═════
--
--   1a  subterm and expansion closure of `sn`, closure of neutrals,
--       confluence and backward closure          (Lemmas 3.8-3.13)
--   1b  soundness of the inductive characterisation:
--       SN ⟹ sn,  SNe ⟹ sn,  ⟶SN ⟹ ⟶sn       (Lemma 3.14, Thm 3.1)
--
-- With Reloaded/SumsNormalization.agda (2a/2b) this closes the STLC+
-- half.  Built on Languages/STLCSums.agda.  Reloaded/Soundness.agda
-- carries the same structure without sums.
--
-- The σ-calculus contribution is Lemma 3.7 (`sub-↝`, `ren-↝`):
--   (b [ n ]₀) [ σ ]ˢ ≡ (b [ (σ ↑ˢ expr) ]ˢ) [ n [ σ ]ˢ ]₀
-- holds definitionally, so each β case is a bare constructor.

module Reloaded.SumsSoundness where

open import Languages.STLCSums
open import Reloaded.SumsNormalization

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
  βinl↝ : ∀ {S} {m : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
          (case (inl m) u v) ↝ (u [ m ]₀)
  βinr↝ : ∀ {S} {m : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
          (case (inr m) u v) ↝ (v [ m ]₀)
  ξinl : ∀ {S} {e e′ : S ⊢ expr} → e ↝ e′ → inl e ↝ inl e′
  ξinr : ∀ {S} {e e′ : S ⊢ expr} → e ↝ e′ → inr e ↝ inr e′
  ξc₀ : ∀ {S} {e e′ : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
        e ↝ e′ → (case e u v) ↝ (case e′ u v)
  ξc₁ : ∀ {S} {e : S ⊢ expr} {u u′ v : (expr ∷ S) ⊢ expr} →
        u ↝ u′ → (case e u v) ↝ (case e u′ v)
  ξc₂ : ∀ {S} {e : S ⊢ expr} {u v v′ : (expr ∷ S) ⊢ expr} →
        v ↝ v′ → (case e u v) ↝ (case e u v′)

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
  ncse : ∀ {S} {r : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
         ne r → ne (case r u v)

-- sn-flavoured strong head reduction
infix 3 _⟶sn_
data _⟶sn_ : ∀ {S} → S ⊢ expr → S ⊢ expr → Set where
  βsn    : ∀ {S} {b : (expr ∷ S) ⊢ expr} {n : S ⊢ expr} →
           sn n → ((λx b) · n) ⟶sn (b [ n ]₀)
  applsn : ∀ {S} {e e′ n : S ⊢ expr} →
           e ⟶sn e′ → (e · n) ⟶sn (e′ · n)
  βinlsn : ∀ {S} {m : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
           sn m → sn v → (case (inl m) u v) ⟶sn (u [ m ]₀)
  βinrsn : ∀ {S} {m : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
           sn m → sn u → (case (inr m) u v) ⟶sn (v [ m ]₀)
  csesn  : ∀ {S} {e e′ : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
           e ⟶sn e′ → (case e u v) ⟶sn (case e′ u v)

-- ─── Lemma 3.1: reduction preserves typing ──────────────────────────
-- not vacuous any more -- the syntax is scoped, not typed -- but each
-- β case is exactly the substitution lemma `⊢[]` of
-- Reloaded.SumsNormalization, whose own proof is definitional.

preservation : ∀ {S} {Γ : Ctx S} {e e′ : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → e ↝ e′ → Γ ⊢ e′ ∶ A
preservation (⊢· (⊢λ db) dn)         β↝       = ⊢[] db dn
preservation (⊢λ db)                 (ξλ st)  = ⊢λ (preservation db st)
preservation (⊢· d₁ d₂)              (ξ·₁ st) = ⊢· (preservation d₁ st) d₂
preservation (⊢· d₁ d₂)              (ξ·₂ st) = ⊢· d₁ (preservation d₂ st)
preservation (⊢case (⊢inl dm) du dv) βinl↝    = ⊢[] du dm
preservation (⊢case (⊢inr dm) du dv) βinr↝    = ⊢[] dv dm
preservation (⊢inl d)                (ξinl st) = ⊢inl (preservation d st)
preservation (⊢inr d)                (ξinr st) = ⊢inr (preservation d st)
preservation (⊢case d du dv)         (ξc₀ st) = ⊢case (preservation d st) du dv
preservation (⊢case d du dv)         (ξc₁ st) = ⊢case d (preservation du st) dv
preservation (⊢case d du dv)         (ξc₂ st) = ⊢case d du (preservation dv st)

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

↝*-inl : ∀ {S} {e e′ : S ⊢ expr} → e ↝* e′ → inl e ↝* inl e′
↝*-inl done     = done
↝*-inl (st ◅ r) = ξinl st ◅ ↝*-inl r
↝*-inr : ∀ {S} {e e′ : S ⊢ expr} → e ↝* e′ → inr e ↝* inr e′
↝*-inr done     = done
↝*-inr (st ◅ r) = ξinr st ◅ ↝*-inr r
↝*-c₀ : ∀ {S} {e e′ : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
        e ↝* e′ → (case e u v) ↝* (case e′ u v)
↝*-c₀ done     = done
↝*-c₀ (st ◅ r) = ξc₀ st ◅ ↝*-c₀ r
↝*-c₁ : ∀ {S} {e : S ⊢ expr} {u u′ v : (expr ∷ S) ⊢ expr} →
        u ↝* u′ → (case e u v) ↝* (case e u′ v)
↝*-c₁ done     = done
↝*-c₁ (st ◅ r) = ξc₁ st ◅ ↝*-c₁ r
↝*-c₂ : ∀ {S} {e : S ⊢ expr} {u v v′ : (expr ∷ S) ⊢ expr} →
        v ↝* v′ → (case e u v) ↝* (case e u v′)
↝*-c₂ done     = done
↝*-c₂ (st ◅ r) = ξc₂ st ◅ ↝*-c₂ r

-- ─── Lemma 3.7: reduction under renaming and substitution ───────────

ren-↝ : ∀ {S₁ S₂} {e e′ : S₁ ⊢ expr} → e ↝ e′ → (ξ : S₁ →ᴿ S₂) →
  (e [ ξ ]ᴿ) ↝ (e′ [ ξ ]ᴿ)
ren-↝ β↝       ξ = β↝
ren-↝ (ξλ st)  ξ = ξλ (ren-↝ st (ξ ↑ᴿ _))
ren-↝ (ξ·₁ st) ξ = ξ·₁ (ren-↝ st ξ)
ren-↝ (ξ·₂ st) ξ = ξ·₂ (ren-↝ st ξ)
ren-↝ βinl↝    ξ = βinl↝
ren-↝ βinr↝    ξ = βinr↝
ren-↝ (ξinl st) ξ = ξinl (ren-↝ st ξ)
ren-↝ (ξinr st) ξ = ξinr (ren-↝ st ξ)
ren-↝ (ξc₀ st) ξ = ξc₀ (ren-↝ st ξ)
ren-↝ (ξc₁ st) ξ = ξc₁ (ren-↝ st (ξ ↑ᴿ _))
ren-↝ (ξc₂ st) ξ = ξc₂ (ren-↝ st (ξ ↑ᴿ _))

sub-↝ : ∀ {S₁ S₂} {e e′ : S₁ ⊢ expr} → e ↝ e′ → (σ : S₁ →ˢ S₂) →
  (e [ σ ]ˢ) ↝ (e′ [ σ ]ˢ)
sub-↝ β↝       σ = β↝
sub-↝ (ξλ st)  σ = ξλ (sub-↝ st (σ ↑ˢ _))
sub-↝ (ξ·₁ st) σ = ξ·₁ (sub-↝ st σ)
sub-↝ (ξ·₂ st) σ = ξ·₂ (sub-↝ st σ)
sub-↝ βinl↝    σ = βinl↝
sub-↝ βinr↝    σ = βinr↝
sub-↝ (ξinl st) σ = ξinl (sub-↝ st σ)
sub-↝ (ξinr st) σ = ξinr (sub-↝ st σ)
sub-↝ (ξc₀ st) σ = ξc₀ (sub-↝ st σ)
sub-↝ (ξc₁ st) σ = ξc₁ (sub-↝ st (σ ↑ˢ _))
sub-↝ (ξc₂ st) σ = ξc₂ (sub-↝ st (σ ↑ˢ _))

ren-↝* : ∀ {S₁ S₂} {e e′ : S₁ ⊢ expr} → e ↝* e′ → (ξ : S₁ →ᴿ S₂) →
  (e [ ξ ]ᴿ) ↝* (e′ [ ξ ]ᴿ)
ren-↝* done     ξ = done
ren-↝* (st ◅ r) ξ = ren-↝ st ξ ◅ ren-↝* r ξ

-- Lemma 3.6(5): reducing inside the substitution.
sub-↝* : ∀ {S₁ S₂} (t : S₁ ⊢ expr) (σ σ′ : S₁ →ˢ S₂) →
  (∀ (y : S₁ ∋ expr) → (y [ σ ]ˢ) ↝* (y [ σ′ ]ˢ)) → (t [ σ ]ˢ) ↝* (t [ σ′ ]ˢ)
sub-↝* (` y)     σ σ′ h = h y
sub-↝* (λx b)    σ σ′ h = ↝*-λ (sub-↝* b (σ ↑ˢ _) (σ′ ↑ˢ _)
  λ { zero → done ; (suc y) → ren-↝* (h y) (wkᴿ _) })
sub-↝* (e₁ · e₂) σ σ′ h =
  ↝*-trans (↝*-·₁ (sub-↝* e₁ σ σ′ h)) (↝*-·₂ (sub-↝* e₂ σ σ′ h))
sub-↝* (inl e) σ σ′ h = ↝*-inl (sub-↝* e σ σ′ h)
sub-↝* (inr e) σ σ′ h = ↝*-inr (sub-↝* e σ σ′ h)
sub-↝* (case e u v) σ σ′ h = ↝*-trans (↝*-c₀ (sub-↝* e σ σ′ h))
  (↝*-trans (↝*-c₁ (sub-↝* u (σ ↑ˢ _) (σ′ ↑ˢ _)
                     λ { zero → done ; (suc y) → ren-↝* (h y) (wkᴿ _) }))
            (↝*-c₂ (sub-↝* v (σ ↑ˢ _) (σ′ ↑ˢ _)
                     λ { zero → done ; (suc y) → ren-↝* (h y) (wkᴿ _) })))

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

sn-inl : ∀ {S} {e : S ⊢ expr} → sn e → sn (inl e)
sn-inl (acc f) = acc λ where _ (ξinl st) → sn-inl (f _ st)
sn-inr : ∀ {S} {e : S ⊢ expr} → sn e → sn (inr e)
sn-inr (acc f) = acc λ where _ (ξinr st) → sn-inr (f _ st)

sn-c₀ : ∀ {S} {e : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} → sn (case e u v) → sn e
sn-c₀ (acc f) = acc λ e′ st → sn-c₀ (f (case e′ _ _) (ξc₀ st))
sn-c₁ : ∀ {S} {e : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} → sn (case e u v) → sn u
sn-c₁ (acc f) = acc λ u′ st → sn-c₁ (f (case _ u′ _) (ξc₁ st))
sn-c₂ : ∀ {S} {e : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} → sn (case e u v) → sn v
sn-c₂ (acc f) = acc λ v′ st → sn-c₂ (f (case _ _ v′) (ξc₂ st))

-- 3.9(3): anti-substitution
anti-sub-sn : ∀ {S₁ S₂} (t : S₁ ⊢ expr) (σ : S₁ →ˢ S₂) → sn (t [ σ ]ˢ) → sn t
anti-sub-sn t σ (acc f) = acc λ t′ st → anti-sub-sn t′ σ (f (t′ [ σ ]ˢ) (sub-↝ st σ))

-- ─── impossibility lemmas ───────────────────────────────────────────

ne-λ-⊥ : ∀ {S} {b : (expr ∷ S) ⊢ expr} → ne (λx b) → ⊥
ne-λ-⊥ ()

⟶sn-λ-⊥ : ∀ {S} {b : (expr ∷ S) ⊢ expr} {e′ : S ⊢ expr} → (λx b) ⟶sn e′ → ⊥
⟶sn-λ-⊥ ()

ne-inl-⊥ : ∀ {S} {m : S ⊢ expr} → ne (inl m) → ⊥
ne-inl-⊥ ()
ne-inr-⊥ : ∀ {S} {m : S ⊢ expr} → ne (inr m) → ⊥
ne-inr-⊥ ()
⟶sn-inl-⊥ : ∀ {S} {m e′ : S ⊢ expr} → (inl m) ⟶sn e′ → ⊥
⟶sn-inl-⊥ ()
⟶sn-inr-⊥ : ∀ {S} {m e′ : S ⊢ expr} → (inr m) ⟶sn e′ → ⊥
⟶sn-inr-⊥ ()

-- ─── Lemma 3.10: weak head expansion ────────────────────────────────

sn-β-exp : ∀ {S} {b : (expr ∷ S) ⊢ expr} {n : S ⊢ expr} →
  sn n → sn b → sn (b [ n ]₀) → sn ((λx b) · n)
sn-β-exp {b = b} {n = n} snn@(acc fn) snb@(acc fb) h = acc λ where
  _ β↝            → h
  _ (ξ·₁ (ξλ st)) → sn-β-exp snn (fb _ st) (sn-↝ h (sub-↝ st (n ∙ˢ idˢ)))
  _ (ξ·₂ st)      → sn-β-exp (fn _ st) snb (sn-↝* h (sub-↝*-arg b st))

-- 3.10 for sums: weak head expansion of a case on an injection.
-- Lexicographic in (sn m, sn u, sn v).
sn-βinl-exp : ∀ {S} {m : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
  sn m → sn u → sn v → sn (u [ m ]₀) → sn (case (inl m) u v)
sn-βinl-exp {m = m} {u = u} snm@(acc fm) snu@(acc fu) snv@(acc fv) h = acc λ where
  _ βinl↝           → h
  _ (ξc₀ (ξinl st)) → sn-βinl-exp (fm _ st) snu snv (sn-↝* h (sub-↝*-arg u st))
  _ (ξc₁ st)        → sn-βinl-exp snm (fu _ st) snv (sn-↝ h (sub-↝ st (m ∙ˢ idˢ)))
  _ (ξc₂ st)        → sn-βinl-exp snm snu (fv _ st) h

sn-βinr-exp : ∀ {S} {m : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
  sn m → sn u → sn v → sn (v [ m ]₀) → sn (case (inr m) u v)
sn-βinr-exp {m = m} {v = v} snm@(acc fm) snu@(acc fu) snv@(acc fv) h = acc λ where
  _ βinr↝           → h
  _ (ξc₀ (ξinr st)) → sn-βinr-exp (fm _ st) snu snv (sn-↝* h (sub-↝*-arg v st))
  _ (ξc₁ st)        → sn-βinr-exp snm (fu _ st) snv h
  _ (ξc₂ st)        → sn-βinr-exp snm snu (fv _ st) (sn-↝ h (sub-↝ st (m ∙ˢ idˢ)))

-- ─── Lemma 3.11: closure properties of neutral terms ────────────────

ne-↝ : ∀ {S} {r r′ : S ⊢ expr} → ne r → r ↝ r′ → ne r′
ne-↝ (napp ())  β↝
ne-↝ (napp nr) (ξ·₁ st) = napp (ne-↝ nr st)
ne-↝ (napp nr) (ξ·₂ st) = napp nr
ne-↝ (ncse ())  βinl↝
ne-↝ (ncse ())  βinr↝
ne-↝ (ncse nr) (ξc₀ st) = ncse (ne-↝ nr st)
ne-↝ (ncse nr) (ξc₁ st) = ncse nr
ne-↝ (ncse nr) (ξc₂ st) = ncse nr

ne-app-sn : ∀ {S} {r n : S ⊢ expr} → ne r → sn r → sn n → sn (r · n)
ne-app-sn nr snr@(acc fr) snn@(acc fn) = acc λ where
  _ β↝       → ⊥-elim (ne-λ-⊥ nr)
  _ (ξ·₁ st) → ne-app-sn (ne-↝ nr st) (fr _ st) snn
  _ (ξ·₂ st) → ne-app-sn nr snr (fn _ st)

ne-case-sn : ∀ {S} {r : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
  ne r → sn r → sn u → sn v → sn (case r u v)
ne-case-sn nr snr@(acc fr) snu@(acc fu) snv@(acc fv) = acc λ where
  _ βinl↝    → ⊥-elim (ne-inl-⊥ nr)
  _ βinr↝    → ⊥-elim (ne-inr-⊥ nr)
  _ (ξc₀ st) → ne-case-sn (ne-↝ nr st) (fr _ st) snu snv
  _ (ξc₁ st) → ne-case-sn nr snr (fu _ st) snv
  _ (ξc₂ st) → ne-case-sn nr snr snu (fv _ st)

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
-- sums
confl (βinlsn snm snv) βinl↝ = inj₁ refl
confl (βinlsn {u = u} snm snv) (ξc₀ (ξinl st)) =
  inj₂ (_ , βinlsn (sn-↝ snm st) snv , sub-↝*-arg u st)
confl (βinlsn {m = m} snm snv) (ξc₁ st) =
  inj₂ (_ , βinlsn snm snv , sub-↝ st (m ∙ˢ idˢ) ◅ done)
confl (βinlsn snm snv) (ξc₂ st) = inj₂ (_ , βinlsn snm (sn-↝ snv st) , done)
confl (βinrsn snm snu) βinr↝ = inj₁ refl
confl (βinrsn {v = v} snm snu) (ξc₀ (ξinr st)) =
  inj₂ (_ , βinrsn (sn-↝ snm st) snu , sub-↝*-arg v st)
confl (βinrsn snm snu) (ξc₁ st) = inj₂ (_ , βinrsn snm (sn-↝ snu st) , done)
confl (βinrsn {m = m} snm snu) (ξc₂ st) =
  inj₂ (_ , βinrsn snm snu , sub-↝ st (m ∙ˢ idˢ) ◅ done)
confl (csesn st₀) βinl↝ = ⊥-elim (⟶sn-inl-⊥ st₀)
confl (csesn st₀) βinr↝ = ⊥-elim (⟶sn-inr-⊥ st₀)
confl (csesn st₀) (ξc₁ st) = inj₂ (_ , csesn st₀ , ξc₁ st ◅ done)
confl (csesn st₀) (ξc₂ st) = inj₂ (_ , csesn st₀ , ξc₂ st ◅ done)
confl (csesn st₀) (ξc₀ st) with confl st₀ st
... | inj₁ refl          = inj₁ refl
... | inj₂ (q , st′ , r) = inj₂ (case q _ _ , csesn st′ , ↝*-c₀ r)

-- ─── Lemma 3.13: backward closure of sn ─────────────────────────────

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

-- 3.13 for sums: lexicographic in (sn e, sn u, sn v)
sn-case-exp : ∀ {S} {e e′ : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
  sn u → sn v → sn e → e ⟶sn e′ → sn (case e′ u v) → sn (case e u v)
sn-case-exp-ξ : ∀ {S} {e e′ e″ : S ⊢ expr} {u v : (expr ∷ S) ⊢ expr} →
  sn u → sn v → sn e → e ⟶sn e′ → sn (case e′ u v) → e ↝ e″ → sn (case e″ u v)

sn-case-exp snu@(acc fu) snv@(acc fv) sne st₀ h = acc λ where
  _ βinl↝    → ⊥-elim (⟶sn-inl-⊥ st₀)
  _ βinr↝    → ⊥-elim (⟶sn-inr-⊥ st₀)
  _ (ξc₀ st) → sn-case-exp-ξ snu snv sne st₀ h st
  _ (ξc₁ st) → sn-case-exp (fu _ st) snv sne st₀ (sn-↝ h (ξc₁ st))
  _ (ξc₂ st) → sn-case-exp snu (fv _ st) sne st₀ (sn-↝ h (ξc₂ st))

sn-case-exp-ξ snu snv sne@(acc fe) st₀ h st with confl st₀ st
... | inj₁ refl          = h
... | inj₂ (q , st′ , r) =
  sn-case-exp snu snv (fe _ st) st′ (sn-↝* h (↝*-c₀ r))

sn-⟶sn-exp : ∀ {S} {e e′ : S ⊢ expr} → e ⟶sn e′ → sn e′ → sn e
sn-⟶sn-exp (βsn {b = b} {n = n} snn) h =
  sn-β-exp snn (anti-sub-sn b (n ∙ˢ idˢ) h) h
sn-⟶sn-exp (applsn st₀) h =
  sn-app-exp (sn-app₂ h) (sn-⟶sn-exp st₀ (sn-app₁ h)) st₀ h
sn-⟶sn-exp (βinlsn {m = m} {u = u} snm snv) h =
  sn-βinl-exp snm (anti-sub-sn u (m ∙ˢ idˢ) h) snv h
sn-⟶sn-exp (βinrsn {m = m} {v = v} snm snu) h =
  sn-βinr-exp snm snu (anti-sub-sn v (m ∙ˢ idˢ) h) h
sn-⟶sn-exp (csesn st₀) h =
  sn-case-exp (sn-c₁ h) (sn-c₂ h) (sn-⟶sn-exp st₀ (sn-c₀ h)) st₀ h

-- ═══ challenge 1b: soundness of the inductive definition ════════════

-- Lemma 3.14
SNe→ne : ∀ {S} {e : S ⊢ expr} → SNe e → ne e
SNe→ne (var x)   = nvar x
SNe→ne (app r n)   = napp (SNe→ne r)
SNe→ne (cse r u v) = ncse (SNe→ne r)

-- Theorem 3.1
sound-SNe : ∀ {S} {e : S ⊢ expr} → SNe e → sn e
sound-SN  : ∀ {S} {e : S ⊢ expr} → SN e → sn e
sound-⟶SN : ∀ {S} {e e′ : S ⊢ expr} → e ⟶SN e′ → e ⟶sn e′

sound-SNe (var x)   = sn-var x
sound-SNe (app r n)   = ne-app-sn (SNe→ne r) (sound-SNe r) (sound-SN n)
sound-SNe (cse r u v) =
  ne-case-sn (SNe→ne r) (sound-SNe r) (sound-SN u) (sound-SN v)

sound-SN (abs d)    = sn-abs (sound-SN d)
sound-SN (inlS d)   = sn-inl (sound-SN d)
sound-SN (inrS d)   = sn-inr (sound-SN d)
sound-SN (neu r)    = sound-SNe r
sound-SN (red st d) = sn-⟶sn-exp (sound-⟶SN st) (sound-SN d)

sound-⟶SN (βSN n)     = βsn (sound-SN n)
sound-⟶SN (applSN st) = applsn (sound-⟶SN st)
sound-⟶SN (βinl m v)  = βinlsn (sound-SN m) (sound-SN v)
sound-⟶SN (βinr m u)  = βinrsn (sound-SN m) (sound-SN u)
sound-⟶SN (cseSN st)  = csesn (sound-⟶SN st)

-- ═══ the challenge, assembled ═══════════════════════════════════════
-- every well-typed term is strongly normalising, in the classical
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

-- case (inl (λx.x)) of inl y → y | inr z → z   :  a genuine sum redex
sumredex : [] ⊢ expr
sumredex = case (inl Kid) (` zero) (` zero)

⊢sumredex : Γ₀ ⊢ sumredex ∶ (★ ⇒ᵗ ★)
⊢sumredex = ⊢case (⊢inl {B = ★ ⇒ᵗ ★} ⊢Kid) (⊢` refl) (⊢` refl)

sumredex-steps : sumredex ↝ Kid
sumredex-steps = βinl↝

SN-sumredex : SN sumredex
SN-sumredex = strong-normalisation ⊢sumredex

sn-sumredex : sn sumredex
sn-sumredex = strongly-normalising ⊢sumredex

-- ─── and the typing hypothesis is doing real work ───────────────────
-- `Ω` (defined in Reloaded/SumsNormalization.agda) is a well-scoped term
-- that is not strongly normalising.  Under the old intrinsically typed
-- encoding it could not even be written down.

Ω-loops : Ω ↝ Ω
Ω-loops = β↝

¬sn-Ω : sn Ω → ⊥
¬sn-Ω (acc f) = ¬sn-Ω (f Ω Ω-loops)

-- ═══ challenge-referencing names ════════════════════════════════════

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
