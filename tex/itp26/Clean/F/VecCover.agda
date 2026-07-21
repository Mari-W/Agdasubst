{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- PROBE 4 (the decisive one): the COVER + formers on the vector Sub, EVERYTHING
-- TRANSPARENT, registering only the THINNING-level laws (Orientation-A ⨾, Fac-L/R,
-- ↾-⨾).  Tests: is the arrow DISTRIBUTION free (refl)?  Is the atom-bridge just the
-- ⟪⟫ definition?  Does Clos close structurally with the cover?  No opacity anywhere.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.VecCover where
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Agda.Builtin.Equality.Rewrite
open import Clean.F.ThinRw   -- _⊑_, _⨾_ (Orientation A: clauses fire), oi

Scope = List ⊤
variable Γ Δ Ξ Θ Γₗ Γᵣ sup : Scope

Pos : Scope → Set
Pos Θ = (tt ∷ []) ⊑ Θ
oe : [] ⊑ Γ
oe {[]}     = oz
oe {tt ∷ Γ} = o' oe

-- ════ the cover (relevant pairing) ════
data Cover : Scope → Scope → Scope → Set where
  done : Cover [] [] []
  bb   : Cover Γₗ Γᵣ Γ → Cover (tt ∷ Γₗ) (tt ∷ Γᵣ) (tt ∷ Γ)
  ll   : Cover Γₗ Γᵣ Γ → Cover (tt ∷ Γₗ) Γᵣ        (tt ∷ Γ)
  rr   : Cover Γₗ Γᵣ Γ → Cover Γₗ        (tt ∷ Γᵣ) (tt ∷ Γ)

thinL : Cover Γₗ Γᵣ Γ → Γₗ ⊑ Γ
thinL done   = oz
thinL (bb c) = os (thinL c)
thinL (ll c) = os (thinL c)
thinL (rr c) = o' (thinL c)
thinR : Cover Γₗ Γᵣ Γ → Γᵣ ⊑ Γ
thinR done   = oz
thinR (bb c) = os (thinR c)
thinR (ll c) = o' (thinR c)
thinR (rr c) = os (thinR c)

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

-- the cover FACTORISATION laws — structural, registered (the thinning σ-rules)
Fac-L : (α : Γₗ ⊑ Δ) (β : Γᵣ ⊑ Δ) → thinL (cov (cop α β)) ⨾ out (cop α β) ≡ α
Fac-L oz     oz     = refl
Fac-L (os α) (os β) = cong os (Fac-L α β)
Fac-L (os α) (o' β) = cong os (Fac-L α β)
Fac-L (o' α) (os β) = cong o' (Fac-L α β)
Fac-L (o' α) (o' β) = cong o' (Fac-L α β)
Fac-R : (α : Γₗ ⊑ Δ) (β : Γᵣ ⊑ Δ) → thinR (cov (cop α β)) ⨾ out (cop α β) ≡ β
Fac-R oz     oz     = refl
Fac-R (os α) (os β) = cong os (Fac-R α β)
Fac-R (os α) (o' β) = cong o' (Fac-R α β)
Fac-R (o' α) (os β) = cong os (Fac-R α β)
Fac-R (o' α) (o' β) = cong o' (Fac-R α β)
{-# REWRITE Fac-L Fac-R #-}

-- ════ thing-with-thinning + the relevant-pair carrier ════
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

_⇒↑_ : ∀ {Δ} → Ty ↑ Δ → Ty ↑ Δ → Ty ↑ Δ
A ⇒↑ B = _⇒_ <$> pairUp A B
infixr 6 _⇒↑_

-- ════ the FIRST-ORDER tight-vector substitution ════
data Sub (Δ : Scope) : Scope → Set where
  ε   : Sub Δ []
  _∙_ : Ty ↑ Δ → Sub Δ Θ → Sub Δ (tt ∷ Θ)
infixr 5 _∙_

_↾_ : Sub Δ Θ → sup ⊑ Θ → Sub Δ sup
ε       ↾ oz   = ε
(t ∙ σ) ↾ os θ = t ∙ (σ ↾ θ)
(t ∙ σ) ↾ o' θ = σ ↾ θ
infixl 8 _↾_

-- ↾ associativity — structural, registered
↾-⨾ : (σ : Sub Δ Θ)(θ : sup ⊑ Θ)(φ : Γ ⊑ sup) → (σ ↾ θ) ↾ φ ≡ σ ↾ (φ ⨾ θ)
↾-⨾ ε       oz     oz     = refl
↾-⨾ (t ∙ σ) (os θ) (os φ) = cong (_ ∙_) (↾-⨾ σ θ φ)
↾-⨾ (t ∙ σ) (os θ) (o' φ) = ↾-⨾ σ θ φ
↾-⨾ (t ∙ σ) (o' θ) φ      = ↾-⨾ σ θ φ
-- NB: ↾-⨾ is NOT registered — it clashes with the ↾-elimination clauses (the same
-- A-vs-B duality as ⨾).  ↾ computes via its clauses; ↾-⨾ is an applied lemma.

selL : Cover Γₗ Γᵣ Θ → Sub Δ Θ → Sub Δ Γₗ
selL cv σ = σ ↾ thinL cv
selR : Cover Γₗ Γᵣ Θ → Sub Δ Θ → Sub Δ Γᵣ
selR cv σ = σ ↾ thinR cv

-- substitution action on raw Ty, and on Ty↑ (the latter IS the atom-bridge by defn)
sub : Ty Θ → Sub Δ Θ → Ty ↑ Δ
sub tvar              (t ∙ ε) = t
sub (_⇒_ (pair l r cv)) σ     = (sub l (selL cv σ)) ⇒↑ (sub r (selR cv σ))

_⟪_⟫ : Ty ↑ Θ → Sub Δ Θ → Ty ↑ Δ
(t ⇑ θ) ⟪ σ ⟫ = sub t (σ ↾ θ)
infixl 8 _⟪_⟫

_⨟_ : Sub Δ Θ → Sub Ξ Δ → Sub Ξ Θ
ε       ⨟ τ = ε
(t ∙ σ) ⨟ τ = (t ⟪ τ ⟫) ∙ (σ ⨟ τ)
infixl 6 _⨟_

-- ════ THE σ-LAWS ════

-- the atom-bridge is now DEFINITIONAL (it is the ⟪⟫ clause): refl.
atom-bridge : ∀ {Δ Θ sup}(a : Ty sup)(ξ : sup ⊑ Θ)(σ : Sub Δ Θ)
            → (a ⇑ ξ) ⟪ σ ⟫ ≡ sub a (σ ↾ ξ)
atom-bridge a ξ σ = refl

-- the arrow DISTRIBUTION — structural lemma (↾-⨾ bridges the cover-restriction,
-- Fac-L/R collapse it to the original support).  No opacity, no funext.
⟪⟫-⇒↑ : ∀ {Δ Ξ}(A B : Ty ↑ Δ)(τ : Sub Ξ Δ) → (A ⇒↑ B) ⟪ τ ⟫ ≡ (A ⟪ τ ⟫) ⇒↑ (B ⟪ τ ⟫)
⟪⟫-⇒↑ (a ⇑ α) (b ⇑ β) τ =
  cong₂ (λ x y → (sub a x) ⇒↑ (sub b y))
        (↾-⨾ τ (out (cop α β)) (thinL (cov (cop α β))))
        (↾-⨾ τ (out (cop α β)) (thinR (cov (cop α β))))

-- Map: refl (the ⨟ clause)
Map : (t : Ty ↑ Δ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ) → (t ∙ σ) ⨟ τ ≡ (t ⟪ τ ⟫) ∙ (σ ⨟ τ)
Map t σ τ = refl

-- restriction commutes with composition — structural
↾-⨟ : (σ : Sub Δ Θ)(θ : sup ⊑ Θ)(τ : Sub Ξ Δ) → (σ ↾ θ) ⨟ τ ≡ (σ ⨟ τ) ↾ θ
↾-⨟ ε       oz     τ = refl
↾-⨟ (t ∙ σ) (os θ) τ = cong (_ ∙_) (↾-⨟ σ θ τ)
↾-⨟ (t ∙ σ) (o' θ) τ = ↾-⨟ σ θ τ

-- Clos on raw sub — structural, with the COVER case (the decisive test)
Clos-sub : (t : Ty Θ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ) → (sub t σ) ⟪ τ ⟫ ≡ sub t (σ ⨟ τ)
Clos-sub tvar (t ∙ ε) τ = refl
Clos-sub (_⇒_ (pair l r cv)) σ τ =
  trans (⟪⟫-⇒↑ (sub l (selL cv σ)) (sub r (selR cv σ)) τ)
        (cong₂ _⇒↑_ (trans (Clos-sub l (selL cv σ) τ) (cong (sub l) (↾-⨟ σ (thinL cv) τ)))
                    (trans (Clos-sub r (selR cv σ) τ) (cong (sub r) (↾-⨟ σ (thinR cv) τ))))

-- Clos on Ty↑ — structural, via Clos-sub + ↾-⨟
Clos : (u : Ty ↑ Θ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ) → (u ⟪ σ ⟫) ⟪ τ ⟫ ≡ u ⟪ σ ⨟ τ ⟫
Clos (t ⇑ θ) σ τ = trans (Clos-sub t (σ ↾ θ) τ) (cong (sub t) (↾-⨟ σ θ τ))
