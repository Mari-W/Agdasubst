{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- MULTI-SORTED co-de-Bruijn foundation.  Generalises FOp.ThinRw + FOp.Ty's cover
-- machinery from `List ⊤` to `List Sort` (Sort = expr | type | kind, as in the
-- functional systemf.agda).  The sort is threaded through os/o'/bb/ll/rr and NEVER
-- inspected, so every thinning/cover law carries verbatim.  Orientation A: the four
-- ⨾-elimination clauses + Fac-L/Fac-R are the registered confluent rewrites.
-- ════════════════════════════════════════════════════════════════════════════
module FOpMS.ThinRw where
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Agda.Builtin.Equality.Rewrite

data Sort : Set where expr type kind : Sort

Scope = List Sort
private variable
  s s′ : Sort
  Γ Δ Ξ Ω Θ Γₗ Γᵣ sup : Scope

-- ════ thinnings over a heterogeneous scope ════
data _⊑_ : Scope → Scope → Set where
  oz : [] ⊑ []
  os : Γ ⊑ Δ → (s ∷ Γ) ⊑ (s ∷ Δ)
  o' : Γ ⊑ Δ → Γ ⊑ (s ∷ Δ)

opaque
  _⨾_ : Γ ⊑ Δ → Δ ⊑ Ξ → Γ ⊑ Ξ
  θ    ⨾ o' φ = o' (θ ⨾ φ)
  os θ ⨾ os φ = os (θ ⨾ φ)
  o' θ ⨾ os φ = o' (θ ⨾ φ)
  oz   ⨾ oz   = oz
infixr 7 _⨾_

oi : Γ ⊑ Γ
oi {[]}    = oz
oi {s ∷ Γ} = os oi

oe : [] ⊑ Γ
oe {[]}    = oz
oe {s ∷ Γ} = o' oe

-- ORIENTATION A: the 4 ⨾-elimination clauses as rewrites (normal form = os/o'/oz tree)
opaque
  unfolding _⨾_
  ⨾-o'   : (θ : Γ ⊑ Δ)(φ : Δ ⊑ Ξ) → _⨾_ {Ξ = s ∷ Ξ} θ (o' φ) ≡ o' (θ ⨾ φ)
  ⨾-o'   θ φ = refl
  ⨾-osos : (θ : Γ ⊑ Δ)(φ : Δ ⊑ Ξ) → (os {s = s} θ) ⨾ (os φ) ≡ os (θ ⨾ φ)
  ⨾-osos θ φ = refl
  ⨾-o'os : (θ : Γ ⊑ Δ)(φ : Δ ⊑ Ξ) → (o' {s = s} θ) ⨾ (os φ) ≡ o' (θ ⨾ φ)
  ⨾-o'os θ φ = refl
  ⨾-ozoz : oz ⨾ oz ≡ oz
  ⨾-ozoz = refl
{-# REWRITE ⨾-o' ⨾-osos ⨾-o'os ⨾-ozoz #-}

-- category laws are DERIVED (structural)
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

-- ════ positions (SORTED singleton supports) — a variable of sort s ════
Pos : Scope → Sort → Set
Pos Θ s = (s ∷ []) ⊑ Θ

-- ════ covers (relevant pairing) + factorisation ════
data Cover : Scope → Scope → Scope → Set where
  done : Cover [] [] []
  bb   : Cover Γₗ Γᵣ Γ → Cover (s ∷ Γₗ) (s ∷ Γᵣ) (s ∷ Γ)
  ll   : Cover Γₗ Γᵣ Γ → Cover (s ∷ Γₗ) Γᵣ       (s ∷ Γ)
  rr   : Cover Γₗ Γᵣ Γ → Cover Γₗ       (s ∷ Γᵣ) (s ∷ Γ)
thinL : Cover Γₗ Γᵣ Γ → Γₗ ⊑ Γ
thinL done = oz ; thinL (bb c) = os (thinL c) ; thinL (ll c) = os (thinL c) ; thinL (rr c) = o' (thinL c)
thinR : Cover Γₗ Γᵣ Γ → Γᵣ ⊑ Γ
thinR done = oz ; thinR (bb c) = os (thinR c) ; thinR (ll c) = o' (thinR c) ; thinR (rr c) = os (thinR c)
record Cop {Γₗ Γᵣ Δ}(α : Γₗ ⊑ Δ) (β : Γᵣ ⊑ Δ) : Set where
  constructor mkCop
  field {un} : Scope
        cov  : Cover Γₗ Γᵣ un
        out  : un ⊑ Δ
open Cop public
cop : (α : Γₗ ⊑ Δ) (β : Γᵣ ⊑ Δ) → Cop α β
cop oz     oz     = mkCop done oz
cop (os α) (os β) = let c = cop α β in mkCop (bb (cov c)) (os (out c))
cop (os α) (o' β) = let c = cop α β in mkCop (ll (cov c)) (os (out c))
cop (o' α) (os β) = let c = cop α β in mkCop (rr (cov c)) (os (out c))
cop (o' α) (o' β) = let c = cop α β in mkCop (cov c)      (o' (out c))
Fac-L : (α : Γₗ ⊑ Δ)(β : Γᵣ ⊑ Δ) → thinL (cov (cop α β)) ⨾ out (cop α β) ≡ α
Fac-L oz oz = refl ; Fac-L (os α)(os β) = cong os (Fac-L α β) ; Fac-L (os α)(o' β) = cong os (Fac-L α β)
Fac-L (o' α)(os β) = cong o' (Fac-L α β) ; Fac-L (o' α)(o' β) = cong o' (Fac-L α β)
Fac-R : (α : Γₗ ⊑ Δ)(β : Γᵣ ⊑ Δ) → thinR (cov (cop α β)) ⨾ out (cop α β) ≡ β
Fac-R oz oz = refl ; Fac-R (os α)(os β) = cong os (Fac-R α β) ; Fac-R (os α)(o' β) = cong o' (Fac-R α β)
Fac-R (o' α)(os β) = cong os (Fac-R α β) ; Fac-R (o' α)(o' β) = cong o' (Fac-R α β)
{-# REWRITE Fac-L Fac-R #-}

-- ════ the ↑ carrier (a thing together with the thinning of its support) ════
record _↑_ (T : Scope → Set) (Δ : Scope) : Set where
  constructor _⇑_
  field {scp} : Scope
        thing : T scp
        thn   : scp ⊑ Δ
open _↑_ public
_<$>_ : ∀ {S T Δ} → (∀ {Γ} → S Γ → T Γ) → S ↑ Δ → T ↑ Δ
f <$> (t ⇑ θ) = f t ⇑ θ
_⟨_⟩↑ : ∀ {T Δ Δ′} → T ↑ Δ → Δ ⊑ Δ′ → T ↑ Δ′
(t ⇑ θ) ⟨ ψ ⟩↑ = t ⇑ (θ ⨾ ψ)

-- relevant pair + sorted binder carriers
data _×ᴿ_ (S T : Scope → Set) : Scope → Set where
  pair : S Γₗ → T Γᵣ → Cover Γₗ Γᵣ Γ → (S ×ᴿ T) Γ
pairUp : ∀ {S T Δ} → S ↑ Δ → T ↑ Δ → (S ×ᴿ T) ↑ Δ
pairUp (a ⇑ α) (b ⇑ β) = pair a b (cov (cop α β)) ⇑ out (cop α β)
data Bind (s : Sort) (T : Scope → Set) : Scope → Set where
  use  : T (s ∷ Θ) → Bind s T Θ
  drop : T Θ       → Bind s T Θ
bindUp : ∀ {s T Δ} → T ↑ (s ∷ Δ) → (Bind s T) ↑ Δ
bindUp (t ⇑ os θ) = use  t ⇑ θ
bindUp (t ⇑ o' θ) = drop t ⇑ θ
