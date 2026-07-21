{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- PROBE (obstruction 3): a confluent rewrite system for thinning composition.
-- Candidate normal form = oz/os/o' tree (⨾ fully ELIMINATED).  Orientation:
-- the 4 ⨾-clauses as rewrites (⨾ opaque).  Test: does --local-confluence-check
-- accept them?  And can the category laws (⨾oi/oi⨾/⨾⨾) co-register or only derive?
-- ════════════════════════════════════════════════════════════════════════════
module FOpH1.ThinRw where
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite

private variable Γ Δ Ξ Ω : List ⊤

data _⊑_ : List ⊤ → List ⊤ → Set where
  oz : [] ⊑ []
  os : Γ ⊑ Δ → (tt ∷ Γ) ⊑ (tt ∷ Δ)
  o' : Γ ⊑ Δ → Γ ⊑ (tt ∷ Δ)

opaque
  _⨾_ : Γ ⊑ Δ → Δ ⊑ Ξ → Γ ⊑ Ξ
  θ    ⨾ o' φ = o' (θ ⨾ φ)
  os θ ⨾ os φ = os (θ ⨾ φ)
  o' θ ⨾ os φ = o' (θ ⨾ φ)
  oz   ⨾ oz   = oz
infixr 7 _⨾_

oi : Γ ⊑ Γ
oi {[]}     = oz
oi {tt ∷ Γ} = os oi

-- ORIENTATION A: the 4 ⨾-elimination clauses as rewrites (normal form = tree)
opaque
  unfolding _⨾_
  ⨾-o'  : (θ : Γ ⊑ Δ)(φ : Δ ⊑ Ξ) → θ    ⨾ o' φ ≡ o' (θ ⨾ φ)
  ⨾-o'  θ φ = refl
  ⨾-osos : (θ : Γ ⊑ Δ)(φ : Δ ⊑ Ξ) → os θ ⨾ os φ ≡ os (θ ⨾ φ)
  ⨾-osos θ φ = refl
  ⨾-o'os : (θ : Γ ⊑ Δ)(φ : Δ ⊑ Ξ) → o' θ ⨾ os φ ≡ o' (θ ⨾ φ)
  ⨾-o'os θ φ = refl
  ⨾-ozoz : oz ⨾ oz ≡ oz
  ⨾-ozoz = refl
{-# REWRITE ⨾-o' ⨾-osos ⨾-o'os ⨾-ozoz #-}

-- with the clauses firing, the category laws are DERIVED theorems (structural):
oi⨾ : (θ : Γ ⊑ Δ) → oi ⨾ θ ≡ θ
oi⨾ oz     = refl
oi⨾ (os θ) = cong os (oi⨾ θ)
oi⨾ (o' θ) = cong o' (oi⨾ θ)

⨾oi : (θ : Γ ⊑ Δ) → θ ⨾ oi ≡ θ
⨾oi oz     = refl
⨾oi (os θ) = cong os (⨾oi θ)
⨾oi (o' θ) = cong o' (⨾oi θ)

⨾⨾ : (a : Γ ⊑ Δ)(b : Δ ⊑ Ξ)(c : Ξ ⊑ Ω) → (a ⨾ b) ⨾ c ≡ a ⨾ (b ⨾ c)
⨾⨾ a      b      (o' c) = cong o' (⨾⨾ a b c)
⨾⨾ a      (o' b) (os c) = cong o' (⨾⨾ a b c)
⨾⨾ (os a) (os b) (os c) = cong os (⨾⨾ a b c)
⨾⨾ (o' a) (os b) (os c) = cong o' (⨾⨾ a b c)
⨾⨾ oz     oz     oz     = refl

-- ════ PAYOFF: under Orientation A the vector ↾-algebra is FULLY STRUCTURAL ════
-- (os/os fires ⇒ every case is refl or cong(IH); contrast VecSub.agda where the
--  scaffold's opaque ⨾ forced the awkward oe-uniq base case and blocked ↾-assoc.)
data Vec (A : Set) : List ⊤ → Set where
  ε   : Vec A []
  _∙_ : ∀ {Γ} → A → Vec A Γ → Vec A (tt ∷ Γ)
infixr 5 _∙_

_↾ᵛ_ : ∀ {A Γ Δ} → Vec A Γ → Δ ⊑ Γ → Vec A Δ
ε       ↾ᵛ oz   = ε
(a ∙ v) ↾ᵛ os θ = a ∙ (v ↾ᵛ θ)
(a ∙ v) ↾ᵛ o' θ = v ↾ᵛ θ
infixl 8 _↾ᵛ_

↾ᵛ-⨾ : ∀ {A Γ Δ sup}(v : Vec A Γ)(θ : Δ ⊑ Γ)(φ : sup ⊑ Δ) → (v ↾ᵛ θ) ↾ᵛ φ ≡ v ↾ᵛ (φ ⨾ θ)
↾ᵛ-⨾ ε       oz     oz     = refl
↾ᵛ-⨾ (a ∙ v) (os θ) (os φ) = cong (a ∙_) (↾ᵛ-⨾ v θ φ)
↾ᵛ-⨾ (a ∙ v) (os θ) (o' φ) = ↾ᵛ-⨾ v θ φ
↾ᵛ-⨾ (a ∙ v) (o' θ) φ      = ↾ᵛ-⨾ v θ φ
