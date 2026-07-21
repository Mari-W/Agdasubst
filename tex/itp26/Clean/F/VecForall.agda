{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- PROBE 5 (step a): the ∀-BINDER on the vector.  In the functional dev `⟪⟫-∀↑`
-- was THE irreducible subst (bindUp stuck on the abstract body, non-registrable).
-- Claim: on the vector its hard case (the bound var IS used) is `lift-↾ = refl`.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.VecForall where
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite
open import Clean.F.ThinRw

Scope = List ⊤
variable Γ Δ Ξ Θ sup : Scope

oe : [] ⊑ Γ
oe {[]}     = oz
oe {tt ∷ Γ} = o' oe

record _↑_ (T : Scope → Set) (Δ : Scope) : Set where
  constructor _⇑_
  field {scp} : Scope
        thing : T scp
        thn   : scp ⊑ Δ
_<$>_ : ∀ {S T Δ} → (∀ {Γ} → S Γ → T Γ) → S ↑ Δ → T ↑ Δ
f <$> (t ⇑ θ) = f t ⇑ θ

-- the binder carrier: a body either USES the bound var (lives in tt∷Θ) or drops it
data Bind (T : Scope → Set) : Scope → Set where
  use  : T (tt ∷ Θ) → Bind T Θ
  drop : T Θ        → Bind T Θ
bindUp : ∀ {T Δ} → T ↑ (tt ∷ Δ) → (Bind T) ↑ Δ
bindUp (t ⇑ os θ) = use  t ⇑ θ
bindUp (t ⇑ o' θ) = drop t ⇑ θ

data Ty : Scope → Set where
  tvar : Ty (tt ∷ [])
  ∀'   : Bind Ty Θ → Ty Θ

∀↑ : ∀ {Δ} → Ty ↑ (tt ∷ Δ) → Ty ↑ Δ
∀↑ X = ∀' <$> bindUp X
var₀ : ∀ {Δ} → Ty ↑ (tt ∷ Δ)
var₀ = tvar ⇑ os oe

data Sub (Δ : Scope) : Scope → Set where
  ε   : Sub Δ []
  _∙_ : Ty ↑ Δ → Sub Δ Θ → Sub Δ (tt ∷ Θ)
infixr 5 _∙_

_↾_ : Sub Δ Θ → sup ⊑ Θ → Sub Δ sup
ε       ↾ oz   = ε
(t ∙ σ) ↾ os θ = t ∙ (σ ↾ θ)
(t ∙ σ) ↾ o' θ = σ ↾ θ
infixl 8 _↾_

_⟨_⟩↑ : ∀ {Δ Δ′} → Ty ↑ Δ → Δ ⊑ Δ′ → Ty ↑ Δ′
(t ⇑ θ) ⟨ ψ ⟩↑ = t ⇑ (θ ⨾ ψ)
wkSub : Sub Δ Θ → Sub (tt ∷ Δ) Θ
wkSub ε       = ε
wkSub (t ∙ σ) = (t ⟨ o' oi ⟩↑) ∙ wkSub σ
-- wkSub commutes with restriction — structural, registered (so lift-↾ is refl)
wkSub-↾ : (σ : Sub Δ Θ)(θ : sup ⊑ Θ) → wkSub (σ ↾ θ) ≡ wkSub σ ↾ θ
wkSub-↾ ε       oz     = refl
wkSub-↾ (t ∙ σ) (os θ) = cong (_ ∙_) (wkSub-↾ σ θ)
wkSub-↾ (t ∙ σ) (o' θ) = wkSub-↾ σ θ
{-# REWRITE wkSub-↾ #-}

lift : Sub Δ Θ → Sub (tt ∷ Δ) (tt ∷ Θ)
lift σ = var₀ ∙ wkSub σ
lift-↾ : (σ : Sub Δ Θ)(θ : sup ⊑ Θ) → lift (σ ↾ θ) ≡ (lift σ) ↾ (os θ)
lift-↾ σ θ = refl

sub : Ty Θ → Sub Δ Θ → Ty ↑ Δ
sub tvar          (t ∙ ε) = t
sub (∀' (use t))  σ       = ∀↑ (sub t (lift σ))
sub (∀' (drop t)) σ       = ∀' <$> (drop <$> sub t σ)

_⟪_⟫ : Ty ↑ Θ → Sub Δ Θ → Ty ↑ Δ
(t ⇑ θ) ⟪ σ ⟫ = sub t (σ ↾ θ)
infixl 8 _⟪_⟫

-- ════ THE TEST: the ∀-distribution's USE case — REFL (via lift-↾) ════
-- (functional dev: this was IRREDUCIBLE — `bindUp` stuck, non-registrable subst.)
⟪⟫-∀↑-use : (x : Ty (tt ∷ sup))(ξ : sup ⊑ Δ)(τ : Sub Ξ Δ)
          → (∀↑ (x ⇑ os ξ)) ⟪ τ ⟫ ≡ ∀↑ ((x ⇑ os ξ) ⟪ lift τ ⟫)
⟪⟫-∀↑-use x ξ τ = refl
