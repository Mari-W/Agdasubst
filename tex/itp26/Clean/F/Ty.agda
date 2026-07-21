{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.F.Ty — System F TYPES, a single-scope co-de-Bruijn σ-calculus.
--
-- `Ty Θ` is structurally IDENTICAL to the STLC term: a variable (`tvar`), a binary
-- former (`_⇒_`), and a unary binder (`∀'`).  So this is the Clean STLC recipe
-- applied verbatim to types — positions are thinnings, Sub = Pos→Ty↑, the same 11
-- σ-laws (in Clean.F.TyLaws).  The substitution names stay clean here; downstream
-- (the bi-scoped term level) imports this module QUALIFIED to avoid clashes.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.Ty where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Agda.Builtin.Equality.Rewrite
open import Clean.Pos public   -- Pos, oe-uniq, oe-⨾, Scaffold, Thin, Fac
postulate funext : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

-- §1  TYPE SYNTAX (co-de-Bruijn)
data Ty : Scope → Set where
  tvar : Ty (tt ∷ [])
  _⇒_  : (Ty ×ᴿ Ty) Θ → Ty Θ
  ∀'   : Bind tt Ty Θ → Ty Θ
infixr 6 _⇒_

opaque
  _⇒↑_ : ∀ {Θ} → Ty ↑ Θ → Ty ↑ Θ → Ty ↑ Θ
  A ⇒↑ B = _⇒_ <$> pairUp A B
infixr 6 _⇒↑_
opaque
  ∀↑ : ∀ {Θ} → Ty ↑ (tt ∷ Θ) → Ty ↑ Θ
  ∀↑ X = ∀' <$> bindUp X

-- §2  TYPE SUBSTITUTION as a function of positions (= STLC Sub, classifier Ty)
Sub : Scope → Scope → Set
Sub Δ Θ = Pos Θ → Ty ↑ Δ
_↾_ : ∀ {Δ sup Θ} → Sub Δ Θ → sup ⊑ Θ → Sub Δ sup
(σ ↾ θ) p = σ (p ⨾ θ)
infixl 8 _↾_
selL : ∀ {Θₗ Θᵣ Θ Δ} → Cover Θₗ Θᵣ Θ → Sub Δ Θ → Sub Δ Θₗ
selL cv σ = σ ↾ thinL cv
selR : ∀ {Θₗ Θᵣ Θ Δ} → Cover Θₗ Θᵣ Θ → Sub Δ Θ → Sub Δ Θᵣ
selR cv σ = σ ↾ thinR cv
var₀ : ∀ {Δ} → Ty ↑ (tt ∷ Δ)
var₀ = tvar ⇑ os oe

-- §3  PRIMITIVES (opaque)
opaque
  idS  : ∀ {Θ} → Sub Θ Θ
  ↑ₛ   : ∀ {Θ} → Sub (tt ∷ Θ) Θ
  _∙_  : ∀ {Δ Θ} → Ty ↑ Δ → Sub Δ Θ → Sub Δ (tt ∷ Θ)
  sub  : ∀ {Θ Δ} → Ty Θ → Sub Δ Θ → Ty ↑ Δ
  _⟪_⟫ : ∀ {Δ Ξ} → Ty ↑ Δ → Sub Ξ Δ → Ty ↑ Ξ
  _⨟_  : ∀ {Θ Δ Ξ} → Sub Δ Θ → Sub Ξ Δ → Sub Ξ Θ
  wkSub : ∀ {Δ Θ} → Sub Δ Θ → Sub (tt ∷ Δ) Θ
  lift : ∀ {Δ Θ} → Sub Δ Θ → Sub (tt ∷ Δ) (tt ∷ Θ)

  idS p = tvar ⇑ p
  ↑ₛ  p = tvar ⇑ o' p
  (u ∙ σ) (os p) = u
  (u ∙ σ) (o' p) = σ p
  sub tvar               σ = σ oi
  sub (_⇒_ (pair l r cv)) σ = (sub l (selL cv σ)) ⇒↑ (sub r (selR cv σ))
  sub (∀' (use t))        σ = ∀↑ (sub t (lift σ))
  sub (∀' (drop t))       σ = ∀' <$> (drop <$> sub t σ)
  (t ⇑ θ) ⟪ σ ⟫ = sub t (σ ↾ θ)
  (σ ⨟ τ) p = (σ p) ⟪ τ ⟫
  wkSub σ p = (σ p) ⟨ o' oi ⟩
  lift σ = var₀ ∙ wkSub σ
infixr 5 _∙_
infixl 8 _⟪_⟫
infixl 6 _⨟_
