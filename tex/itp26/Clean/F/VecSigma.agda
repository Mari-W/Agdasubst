{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- PROBE 3: the SUB-COMPOSITION fragment of the co-de-Bruijn σ-calculus on the
-- first-order tight-VECTOR Sub, over Orientation-A thinnings (Clean.F.ThinRw).
-- Tests: Map (definitional?), Clos (structural?), Ass, lift-↾ — does the
-- sub-layer σ-calculus CLOSE structurally (no funext)?  Leaf = the variable.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.VecSigma where
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open import Agda.Builtin.Equality.Rewrite
open import Clean.F.ThinRw   -- _⊑_ (oz/os/o'), _⨾_ (Orientation A), oi, ⨾⨾/oi⨾/⨾oi

Scope = List ⊤
Pos : Scope → Set
Pos Θ = (tt ∷ []) ⊑ Θ

oe : ∀ {Γ} → [] ⊑ Γ
oe {[]}     = oz
oe {tt ∷ Γ} = o' oe

-- thing-with-thinning (the co-de-Bruijn leaf carrier)
record _↑_ (T : Scope → Set) (Δ : Scope) : Set where
  constructor _⇑_
  field {sup} : Scope
        thing : T sup
        thn   : sup ⊑ Δ
open _↑_

_⟨_⟩ : ∀ {T Δ Δ′} → T ↑ Δ → Δ ⊑ Δ′ → T ↑ Δ′
(t ⇑ θ) ⟨ ψ ⟩ = t ⇑ (θ ⨾ ψ)

data Ty : Scope → Set where
  tvar : Ty (tt ∷ [])

var₀ : ∀ {Δ} → Ty ↑ (tt ∷ Δ)
var₀ = tvar ⇑ os oe

-- ════ the FIRST-ORDER tight-vector substitution ════
data Sub (Δ : Scope) : Scope → Set where
  ε   : Sub Δ []
  _∙_ : ∀ {Θ} → Ty ↑ Δ → Sub Δ Θ → Sub Δ (tt ∷ Θ)
infixr 5 _∙_

lookup : ∀ {Δ Θ} → Pos Θ → Sub Δ Θ → Ty ↑ Δ
lookup (os q) (t ∙ σ) = t
lookup (o' q) (t ∙ σ) = lookup q σ

_↾_ : ∀ {Δ sup Θ} → Sub Δ Θ → sup ⊑ Θ → Sub Δ sup
ε       ↾ oz   = ε
(t ∙ σ) ↾ os θ = t ∙ (σ ↾ θ)
(t ∙ σ) ↾ o' θ = σ ↾ θ
infixl 8 _↾_

wkSub : ∀ {Δ Θ} → Sub Δ Θ → Sub (tt ∷ Δ) Θ
wkSub ε       = ε
wkSub (t ∙ σ) = (t ⟨ o' oi ⟩) ∙ wkSub σ

lift : ∀ {Δ Θ} → Sub Δ Θ → Sub (tt ∷ Δ) (tt ∷ Θ)
lift σ = var₀ ∙ wkSub σ

-- substitution action on the leaf (a variable = lookup)
_⟪_⟫ : ∀ {Δ Θ} → Ty ↑ Θ → Sub Δ Θ → Ty ↑ Δ
(tvar ⇑ θ) ⟪ σ ⟫ = lookup θ σ
infixl 8 _⟪_⟫

-- composition = map the action over the vector
_⨟_ : ∀ {Δ Ξ Θ} → Sub Δ Θ → Sub Ξ Δ → Sub Ξ Θ
ε       ⨟ τ = ε
(t ∙ σ) ⨟ τ = (t ⟪ τ ⟫) ∙ (σ ⨟ τ)
infixl 6 _⨟_

-- ════ THE σ-LAWS, MEASURED ════

-- Map: composition over cons — DEFINITIONAL (it's the ⨟ clause), refl.
Map : ∀ {Δ Ξ Θ}(t : Ty ↑ Δ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ)
    → (t ∙ σ) ⨟ τ ≡ (t ⟪ τ ⟫) ∙ (σ ⨟ τ)
Map t σ τ = refl

-- lookup commutes with ⨟ — structural (refl + IH)
lookup-⨟ : ∀ {Δ Ξ Θ}(p : Pos Θ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ)
         → lookup p (σ ⨟ τ) ≡ (lookup p σ) ⟪ τ ⟫
lookup-⨟ (os q) (t ∙ σ) τ = refl
lookup-⨟ (o' q) (t ∙ σ) τ = lookup-⨟ q σ τ

-- Clos: substitution composes — structural (= lookup-⨟ on the variable leaf)
Clos : ∀ {Δ Ξ Θ}(u : Ty ↑ Θ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ)
     → (u ⟪ σ ⟫) ⟪ τ ⟫ ≡ u ⟪ σ ⨟ τ ⟫
Clos (tvar ⇑ θ) σ τ = sym (lookup-⨟ θ σ τ)

-- Ass: composition is associative — structural, via Clos
Ass : ∀ {Δ Ξ Ω Θ}(σ : Sub Δ Θ)(τ : Sub Ξ Δ)(υ : Sub Ω Ξ)
    → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
Ass ε       τ υ = refl
Ass (t ∙ σ) τ υ = cong₂ _∙_ (Clos t τ υ) (Ass σ τ υ)

-- the binder-commutation law — structural (refl + IH), NO funext (the Bucket-A win)
wkSub-↾ : ∀ {Δ sup Θ}(σ : Sub Δ Θ)(θ : sup ⊑ Θ) → wkSub (σ ↾ θ) ≡ wkSub σ ↾ θ
wkSub-↾ ε       oz     = refl
wkSub-↾ (t ∙ σ) (os θ) = cong (_ ∙_) (wkSub-↾ σ θ)
wkSub-↾ (t ∙ σ) (o' θ) = wkSub-↾ σ θ
{-# REWRITE wkSub-↾ #-}

lift-↾ : ∀ {Δ Ξ sup}(σ : Sub Ξ Δ)(θ : sup ⊑ Δ) → lift (σ ↾ θ) ≡ (lift σ) ↾ (os θ)
lift-↾ σ θ = refl
