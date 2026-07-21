{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.Sub — the σ-calculus, FUNCTIONAL over THINNING-POSITIONS.
--   Sub Δ Γ = Pos Γ → Tm ↑ Δ          (Pos Γ = (tt∷[]) ⊑ Γ)
--   σ ↾ θ   = σ ∘ (_⨾ θ)              (restriction = PREcompose the position — by ⨾)
--   wkSub   = (_⟨ o' oi ⟩)            (weakening = POSTcompose a renaming)
-- Positions compose by `_⨾_`, which is already a registered monoid, so there is no
-- `act` and the spine/cover laws are free (selL-cop via Fac-L⨾).
-- ════════════════════════════════════════════════════════════════════════════
module Clean.Sub where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Agda.Builtin.Equality.Rewrite
open import Clean.Pos public   -- Pos, oe-uniq, oe-⨾, and (re-exported) Scaffold + Thin + Fac
postulate funext : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

-- §1  SYNTAX (co-de-Bruijn STLC)
data Tm : Scope → Set where
  var : Tm (tt ∷ [])
  app : (Tm ×ᴿ Tm) Γ → Tm Γ
  lam : Bind tt Tm Γ → Tm Γ
app↑ : ∀ {Δ} → Tm ↑ Δ → Tm ↑ Δ → Tm ↑ Δ
app↑ A B = app <$> pairUp A B
lam↑ : ∀ {Δ} → Tm ↑ (tt ∷ Δ) → Tm ↑ Δ
lam↑ X = lam <$> bindUp X

-- §2  SUBSTITUTION as a function of positions; restriction = PREcompose by ⨾
Sub : Scope → Scope → Set
Sub Δ Γ = Pos Γ → Tm ↑ Δ
_↾_ : ∀ {Δ sup Γ} → Sub Δ Γ → sup ⊑ Γ → Sub Δ sup
(σ ↾ θ) p = σ (p ⨾ θ)
infixl 8 _↾_
selL : ∀ {Γₗ Γᵣ Γ Δ} → Cover Γₗ Γᵣ Γ → Sub Δ Γ → Sub Δ Γₗ
selL cv σ = σ ↾ thinL cv
selR : ∀ {Γₗ Γᵣ Γ Δ} → Cover Γₗ Γᵣ Γ → Sub Δ Γ → Sub Δ Γᵣ
selR cv σ = σ ↾ thinR cv
var₀ : ∀ {Δ} → Tm ↑ (tt ∷ Δ)
var₀ = var ⇑ os oe

-- §3  PRIMITIVES (opaque ⇒ stable rewrite heads; reasons in Clean.Laws)
opaque
  idS  : ∀ {Γ} → Sub Γ Γ
  ↑ₛ   : ∀ {Γ} → Sub (tt ∷ Γ) Γ
  _∙_  : ∀ {Δ Γ} → Tm ↑ Δ → Sub Δ Γ → Sub Δ (tt ∷ Γ)
  sub  : ∀ {Γ Δ} → Tm Γ → Sub Δ Γ → Tm ↑ Δ
  _⟪_⟫ : ∀ {Δ Θ} → Tm ↑ Δ → Sub Θ Δ → Tm ↑ Θ
  _⨟_  : ∀ {Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  wkSub : ∀ {Δ Γ} → Sub Δ Γ → Sub (tt ∷ Δ) Γ
  lift : ∀ {Δ Γ} → Sub Δ Γ → Sub (tt ∷ Δ) (tt ∷ Γ)

  idS p = var ⇑ p
  ↑ₛ  p = var ⇑ o' p
  (u ∙ σ) (os p) = u
  (u ∙ σ) (o' p) = σ p
  sub var                 σ = σ oi
  sub (app (pair l r cv)) σ = app↑ (sub l (selL cv σ)) (sub r (selR cv σ))
  sub (lam (use t))       σ = lam↑ (sub t (lift σ))
  sub (lam (drop t))      σ = lam <$> (drop <$> sub t σ)
  (t ⇑ θ) ⟪ σ ⟫ = sub t (σ ↾ θ)
  (σ ⨟ τ) p = (σ p) ⟪ τ ⟫
  wkSub σ p = (σ p) ⟨ o' oi ⟩     -- POSTcompose renaming
  lift σ = var₀ ∙ wkSub σ
infixr 5 _∙_
infixl 8 _⟪_⟫
infixl 6 _⨟_
