{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.Scaffold — LANGUAGE-INDEPENDENT co-de-Bruijn scaffolding.
--
-- The generic "shapes" every co-de-Bruijn syntax is built from, plus their
-- renaming action.  Still mentions NO object-language constructor — everything
-- is parametric in a predicate `T : Scope → Set`:
--     _↑_     a thing-with-thinning  (McBride §5, the co-de-Bruijn monad)
--     _×ᴿ_    a RELEVANT pair, carrying a Cover (McBride §8)
--     Bind    a binder, the bound var used-or-dropped (McBride §8)
--     pairUp  smart pairing  = merge supports via `cop`
--     bindUp  smart binding  = read the body's thinning for use/drop
--
-- PAYOFF: renaming `_⟨_⟩` carries-the-thinning (`_⨾_`), no traversal, so
-- functoriality is DEFINITIONAL (ren-id/ren-∘ by refl, via the monoid rewrites).
-- ════════════════════════════════════════════════════════════════════════════
module Sf.Scaffold (I : Set) where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Sf.Thin I public

-- a thing with a thinning into Δ (McBride §5)
record _↑_ (T : Scope → Set)(Δ : Scope) : Set where
  constructor _⇑_
  field {sup} : Scope
        thing : T sup
        thn   : sup ⊑ Δ
open _↑_ public
infix 4 _↑_

-- relevant pair: each side keeps EXACTLY its support, merged by a cover (§8)
record _×ᴿ_ (S T : Scope → Set)(Γ : Scope) : Set where
  constructor pair
  field {sₗ sᵣ} : Scope
        outl : S sₗ
        outr : T sᵣ
        cv   : Cover sₗ sᵣ Γ

-- binding: the bound variable (of sort b) is either used or dropped (§8)
data Bind (b : I)(T : Scope → Set) : Scope → Set where
  use  : T (b ∷ Γ) → Bind b T Γ
  drop : T Γ        → Bind b T Γ

-- renaming = carry the thinning, no traversal (McBride §5)
_⟨_⟩ : ∀ {T Δ Θ} → T ↑ Δ → Δ ⊑ Θ → T ↑ Θ
(t ⇑ θ) ⟨ φ ⟩ = t ⇑ (θ ⨾ φ)
infixl 8 _⟨_⟩

-- functoriality of renaming: DEFINITIONAL (via the THINNING MONOID rewrites)
ren-id : ∀ {T Δ}(u : T ↑ Δ) → u ⟨ oi ⟩ ≡ u
ren-id (t ⇑ θ) = refl
ren-∘  : ∀ {T Δ Θ Ξ}(u : T ↑ Δ)(φ : Δ ⊑ Θ)(ψ : Θ ⊑ Ξ) → (u ⟨ φ ⟩) ⟨ ψ ⟩ ≡ u ⟨ φ ⨾ ψ ⟩
ren-∘ (t ⇑ θ) φ ψ = refl

-- map a sort-preserving function under a thinning
_<$>_ : ∀ {S T Δ} → (∀ {Γ} → S Γ → T Γ) → (S ↑ Δ) → (T ↑ Δ)
f <$> (t ⇑ θ) = f t ⇑ θ
infixl 4 _<$>_

-- `<$>` is NATURAL in renaming: it only touches the thing, `_⟨_⟩` only the thinning
<$>-⟨⟩ : ∀ (S T : Scope → Set){Δ Δ′}(f : ∀ {Γ} → S Γ → T Γ)(X : S ↑ Δ)(ψ : Δ ⊑ Δ′) → (f <$> X) ⟨ ψ ⟩ ≡ (f <$> X ⟨ ψ ⟩)
<$>-⟨⟩ S T f (t ⇑ θ) ψ = refl

-- smart pairing (McBride §6 coproduct): merge the two supports via `cop`
pairUp : ∀ {S T Δ} → (S ↑ Δ) → (T ↑ Δ) → ((S ×ᴿ T) ↑ Δ)
pairUp (a ⇑ θ) (b ⇑ φ) = pair a b (cov (cop θ φ)) ⇑ out (cop θ φ)

-- smart binding: the body's thinning says whether the bound var survived
bindUp : ∀ {b T Δ} → (T ↑ (b ∷ Δ)) → (Bind b T ↑ Δ)
bindUp (t ⇑ os θ) = use t  ⇑ θ
bindUp (t ⇑ o' θ) = drop t ⇑ θ

-- weaken a thing-with-thinning by one binder = `o'` on its thinning, no traversal
wk↑ : ∀ {T} s {Δ} → T ↑ Δ → T ↑ (s ∷ Δ)
wk↑ s (t ⇑ ξ) = t ⇑ o' ξ

-- ── THE FUSION CRUX: cop commutes with post-composition `_⨾_`.  This (and only
-- this) is where `_⨾_` is needed propositionally; it is what makes pairUp commute
-- with renaming.  It is LANGUAGE-INDEPENDENT (pure thinning/cover algebra).
opaque
  unfolding cop _⨾_
  cop-⨾ : ∀ {Γ₁ Γ₂ Δ Δ′}(θ₁ : Γ₁ ⊑ Δ)(θ₂ : Γ₂ ⊑ Δ)(ψ : Δ ⊑ Δ′)
        → cop (θ₁ ⨾ ψ) (θ₂ ⨾ ψ)
        ≡ mkCop (inl (cop θ₁ θ₂)) (inr (cop θ₁ θ₂)) (out (cop θ₁ θ₂) ⨾ ψ) (cov (cop θ₁ θ₂))
  cop-⨾ θ₁      θ₂      oz       = refl
  cop-⨾ θ₁      θ₂      (o' ψ) rewrite cop-⨾ θ₁ θ₂ ψ = refl
  cop-⨾ (os θ₁) (os θ₂) (os ψ) rewrite cop-⨾ θ₁ θ₂ ψ = refl
  cop-⨾ (os θ₁) (o' θ₂) (os ψ) rewrite cop-⨾ θ₁ θ₂ ψ = refl
  cop-⨾ (o' θ₁) (os θ₂) (os ψ) rewrite cop-⨾ θ₁ θ₂ ψ = refl
  cop-⨾ (o' θ₁) (o' θ₂) (os ψ) rewrite cop-⨾ θ₁ θ₂ ψ = refl

-- combined: cop of post-composed cover-thinnings (needed by σ-law IdSubst).
-- Stable LHS (thinL/thinR opaque), so it is a sound rewrite.
cop-thin-⨾ : ∀ {sₗ sᵣ sup Δ}(cv : Cover sₗ sᵣ sup)(θ : sup ⊑ Δ)
           → cop (thinL cv ⨾ θ) (thinR cv ⨾ θ) ≡ mkCop (thinL cv) (thinR cv) θ cv
cop-thin-⨾ cv θ =
  trans (cop-⨾ (thinL cv) (thinR cv) θ) (cong (λ c → mkCop (inl c) (inr c) (out c ⨾ θ) (cov c)) (cop-thin cv))

-- pairUp / bindUp commute with renaming (immediate from cop-⨾ and the ⨾-clauses)
opaque
  unfolding cop _⨾_
  pairUp-⟨⟩ : ∀ {S T Δ Δ′}(A : S ↑ Δ)(B : T ↑ Δ)(ψ : Δ ⊑ Δ′)
            → (pairUp A B) ⟨ ψ ⟩ ≡ pairUp (A ⟨ ψ ⟩) (B ⟨ ψ ⟩)
  pairUp-⟨⟩ (a ⇑ α) (b ⇑ β) ψ rewrite cop-⨾ α β ψ = refl
  bindUp-⟨⟩ : ∀ {b T Δ Δ′}(X : T ↑ (b ∷ Δ))(ψ : Δ ⊑ Δ′)
            → (bindUp X) ⟨ ψ ⟩ ≡ bindUp (X ⟨ os ψ ⟩)
  bindUp-⟨⟩ (t ⇑ os ξ) ψ = refl
  bindUp-⟨⟩ (t ⇑ o' ξ) ψ = refl

-- pairUp commutes with o'-weakening — DEFINITIONAL via the cop (o' θ)(o' φ) clause
opaque
  unfolding cop
  pairUp-wk : ∀ {S T} s {Δ}(A : S ↑ Δ)(B : T ↑ Δ) → pairUp (wk↑ s A) (wk↑ s B) ≡ wk↑ s (pairUp A B)
  pairUp-wk s (a ⇑ θ) (b ⇑ φ) = refl

-- bridge: wk↑ A = A⟨o' oi⟩  (via the ⨾-o' clause)
opaque
  unfolding _⨾_
  ⨾-o' : ∀ {Γ Δ Θ} s (ξ : Γ ⊑ Δ)(ψ : Δ ⊑ Θ) → ξ ⨾ o' {s = s} ψ ≡ o' (ξ ⨾ ψ)
  ⨾-o' s ξ ψ = refl
wk↑≡⟨⟩ : ∀ {T} s {Δ}(A : T ↑ Δ) → wk↑ s A ≡ A ⟨ o' oi ⟩
wk↑≡⟨⟩ s (t ⇑ θ) = cong (t ⇑_) (sym (⨾-o' s θ oi))
