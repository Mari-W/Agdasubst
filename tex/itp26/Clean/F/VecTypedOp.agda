{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- PROBE 8 — subTyTm with ZERO substs.  Same vector calculus, but with OPAQUE
-- formers so the arrow distribution `⟪⟫-⇒↑` is a REGISTERED rewrite (proven ONCE
-- via ↾-⨾ + Fac).  Under intrinsic typing there is NO atom-bridge to pay (no
-- subCx-vs-sub mismatch) ⇒ `subTyTm` is fully subst-free.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.VecTypedOp where
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Agda.Builtin.Equality.Rewrite
open import Clean.F.ThinRw

Scope = List ⊤
variable Γ Δ Ξ Θ Γₗ Γᵣ sup : Scope
Pos : Scope → Set
Pos Θ = (tt ∷ []) ⊑ Θ
oe : [] ⊑ Γ
oe {[]}     = oz
oe {tt ∷ Γ} = o' oe

data Cover : Scope → Scope → Scope → Set where
  done : Cover [] [] []
  bb   : Cover Γₗ Γᵣ Γ → Cover (tt ∷ Γₗ) (tt ∷ Γᵣ) (tt ∷ Γ)
  ll   : Cover Γₗ Γᵣ Γ → Cover (tt ∷ Γₗ) Γᵣ        (tt ∷ Γ)
  rr   : Cover Γₗ Γᵣ Γ → Cover Γₗ        (tt ∷ Γᵣ) (tt ∷ Γ)
thinL : Cover Γₗ Γᵣ Γ → Γₗ ⊑ Γ
thinL done = oz ; thinL (bb c) = os (thinL c) ; thinL (ll c) = os (thinL c) ; thinL (rr c) = o' (thinL c)
thinR : Cover Γₗ Γᵣ Γ → Γᵣ ⊑ Γ
thinR done = oz ; thinR (bb c) = os (thinR c) ; thinR (ll c) = o' (thinR c) ; thinR (rr c) = os (thinR c)
record Cop (α : Γₗ ⊑ Δ) (β : Γᵣ ⊑ Δ) : Set where
  constructor mkCop
  field {un} : Scope
        cov  : Cover Γₗ Γᵣ un
        out  : un ⊑ Δ
open Cop
cop : (α : Γₗ ⊑ Δ) (β : Γᵣ ⊑ Δ) → Cop α β
cop oz     oz     = mkCop done oz
cop (os α) (os β) = let c = cop α β in mkCop (bb (cov c)) (os (out c))
cop (os α) (o' β) = let c = cop α β in mkCop (ll (cov c)) (os (out c))
cop (o' α) (os β) = let c = cop α β in mkCop (rr (cov c)) (os (out c))
cop (o' α) (o' β) = let c = cop α β in mkCop (cov c)      (o' (out c))
Fac-L : (α : Γₗ ⊑ Δ) (β : Γᵣ ⊑ Δ) → thinL (cov (cop α β)) ⨾ out (cop α β) ≡ α
Fac-L oz oz = refl ; Fac-L (os α)(os β) = cong os (Fac-L α β) ; Fac-L (os α)(o' β) = cong os (Fac-L α β)
Fac-L (o' α)(os β) = cong o' (Fac-L α β) ; Fac-L (o' α)(o' β) = cong o' (Fac-L α β)
Fac-R : (α : Γₗ ⊑ Δ) (β : Γᵣ ⊑ Δ) → thinR (cov (cop α β)) ⨾ out (cop α β) ≡ β
Fac-R oz oz = refl ; Fac-R (os α)(os β) = cong os (Fac-R α β) ; Fac-R (os α)(o' β) = cong o' (Fac-R α β)
Fac-R (o' α)(os β) = cong os (Fac-R α β) ; Fac-R (o' α)(o' β) = cong o' (Fac-R α β)
{-# REWRITE Fac-L Fac-R #-}

record _↑_ (T : Scope → Set) (Δ : Scope) : Set where
  constructor _⇑_
  field {scp} : Scope
        thing : T scp
        thn   : scp ⊑ Δ
open _↑_
_<$>_ : ∀ {S T Δ} → (∀ {Γ} → S Γ → T Γ) → S ↑ Δ → T ↑ Δ
f <$> (t ⇑ θ) = f t ⇑ θ
data _×ᴿ_ (S T : Scope → Set) : Scope → Set where
  pair : S Γₗ → T Γᵣ → Cover Γₗ Γᵣ Γ → (S ×ᴿ T) Γ
pairUp : ∀ {S T Δ} → S ↑ Δ → T ↑ Δ → (S ×ᴿ T) ↑ Δ
pairUp (a ⇑ α) (b ⇑ β) = pair a b (cov (cop α β)) ⇑ out (cop α β)
data Ty : Scope → Set where
  tvar : Ty (tt ∷ [])
  _⇒_  : (Ty ×ᴿ Ty) Θ → Ty Θ

-- ★ the former is OPAQUE — that's what lets ⟪⟫-⇒↑ be a registered rewrite
opaque
  _⇒↑_ : ∀ {Δ} → Ty ↑ Δ → Ty ↑ Δ → Ty ↑ Δ
  A ⇒↑ B = _⇒_ <$> pairUp A B
infixr 6 _⇒↑_

data Sub (Δ : Scope) : Scope → Set where
  ε   : Sub Δ []
  _∙_ : Ty ↑ Δ → Sub Δ Θ → Sub Δ (tt ∷ Θ)
infixr 5 _∙_
_↾_ : Sub Δ Θ → sup ⊑ Θ → Sub Δ sup
ε ↾ oz = ε ; (t ∙ σ) ↾ os θ = t ∙ (σ ↾ θ) ; (t ∙ σ) ↾ o' θ = σ ↾ θ
infixl 8 _↾_
↾-⨾ : (σ : Sub Δ Θ)(θ : sup ⊑ Θ)(φ : Γ ⊑ sup) → (σ ↾ θ) ↾ φ ≡ σ ↾ (φ ⨾ θ)
↾-⨾ ε oz oz = refl ; ↾-⨾ (t ∙ σ)(os θ)(os φ) = cong (_ ∙_) (↾-⨾ σ θ φ)
↾-⨾ (t ∙ σ)(os θ)(o' φ) = ↾-⨾ σ θ φ ; ↾-⨾ (t ∙ σ)(o' θ) φ = ↾-⨾ σ θ φ
selL : Cover Γₗ Γᵣ Θ → Sub Δ Θ → Sub Δ Γₗ
selL cv σ = σ ↾ thinL cv
selR : Cover Γₗ Γᵣ Θ → Sub Δ Θ → Sub Δ Γᵣ
selR cv σ = σ ↾ thinR cv
sub : Ty Θ → Sub Δ Θ → Ty ↑ Δ
sub tvar              (t ∙ ε) = t
sub (_⇒_ (pair l r cv)) σ     = (sub l (selL cv σ)) ⇒↑ (sub r (selR cv σ))

-- ★ application is OPAQUE too (so the rewrite LHS is stable)
opaque
  _⟪_⟫ : Ty ↑ Θ → Sub Δ Θ → Ty ↑ Δ
  (t ⇑ θ) ⟪ σ ⟫ = sub t (σ ↾ θ)
infixl 8 _⟪_⟫

-- ★ proven ONCE (↾-⨾ + Fac), then REGISTERED ⇒ the distribution fires definitionally
opaque
  unfolding _⇒↑_ _⟪_⟫
  ⟪⟫-⇒↑ : ∀ {Δ Ξ}(A B : Ty ↑ Δ)(τ : Sub Ξ Δ) → (A ⇒↑ B) ⟪ τ ⟫ ≡ (A ⟪ τ ⟫) ⇒↑ (B ⟪ τ ⟫)
  ⟪⟫-⇒↑ (a ⇑ α) (b ⇑ β) τ =
    cong₂ (λ x y → (sub a x) ⇒↑ (sub b y))
          (↾-⨾ τ (out (cop α β)) (thinL (cov (cop α β))))
          (↾-⨾ τ (out (cop α β)) (thinR (cov (cop α β))))
{-# REWRITE ⟪⟫-⇒↑ #-}

-- ════ intrinsic typing + subst-free subTyTm ════
Cx : Scope → Set
Cx Θ = List (Ty ↑ Θ)
subCx : ∀ {Θ Δ} → Cx Θ → Sub Δ Θ → Cx Δ
subCx Γ στ = map (_⟪ στ ⟫) Γ
data _∋_ {Θ} : Cx Θ → Ty ↑ Θ → Set where
  here  : ∀ {Γ A}   → (A ∷ Γ) ∋ A
  there : ∀ {Γ A B} → Γ ∋ A → (B ∷ Γ) ∋ A
data Tm (Θ : Scope) : Cx Θ → Ty ↑ Θ → Set where
  var : ∀ {Γ A}   → Γ ∋ A                       → Tm Θ Γ A
  app : ∀ {Γ A B} → Tm Θ Γ (A ⇒↑ B) → Tm Θ Γ A  → Tm Θ Γ B
  lam : ∀ {Γ A B} → Tm Θ (A ∷ Γ) B              → Tm Θ Γ (A ⇒↑ B)
subVar : ∀ {Θ Δ Γ A}(x : Γ ∋ A)(στ : Sub Δ Θ) → subCx Γ στ ∋ (A ⟪ στ ⟫)
subVar here      στ = here
subVar (there x) στ = there (subVar x στ)

-- ★ ZERO substs: ⟪⟫-⇒↑ fires definitionally; intrinsic ⇒ no atom-bridge, no context seam
subTyTm : ∀ {Θ Δ Γ A} → Tm Θ Γ A → (στ : Sub Δ Θ) → Tm Δ (subCx Γ στ) (A ⟪ στ ⟫)
subTyTm (var x)   στ = var (subVar x στ)
subTyTm (app f a) στ = app (subTyTm f στ) (subTyTm a στ)
subTyTm (lam b)   στ = lam (subTyTm b στ)
