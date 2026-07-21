{-# OPTIONS --rewriting --local-confluence-check #-}
-- ============================================================================
-- Co-de-Bruijn terms + the renaming action, on top of CDBsig.
-- McBride, "Everybody's Got To Be Somewhere" (arXiv:1807.04085).  Section map:
--     _×ᴿ_ (relevant pair, carries a Cover) ...... §8 (relevant pairing)
--     Bind (binding, var used-or-dropped) ........ §8
--     Tm (var / app / lam) ....................... the co-de-Bruijn λ-syntax (§8)
--     _↑_ (a "thing with a thinning") + _⟨_⟩ ..... §5 "Things-with-Thinnings (a Monad)"
--
-- KEY PAYOFF: renaming a term is NOT a traversal — you carry the thinning and
-- compose it (`_⟨_⟩` = `_⨾_`).  So functoriality is definitional:
--     ren-id : u ⟨ oi ⟩    ≡ u           by refl  (via ⨾oi rewrite)
--     ren-∘  : u ⟨φ⟩⟨ψ⟩    ≡ u ⟨ φ ⨾ ψ ⟩ by refl  (via ⨾⨾  rewrite)
-- This is the coherence that needed a `subst` in every de-Bruijn build; here it
-- is free, because a variable carries no index.
-- ============================================================================
module CDBterm where
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import CDBsig

-- relevant pair: each side keeps EXACTLY its support, merged by a cover (§8)
record _×ᴿ_ (S T : Scope → Set) (Γ : Scope) : Set where
  constructor pair
  field {sₗ sᵣ} : Scope
        outl : S sₗ
        outr : T sᵣ
        cv   : Cover sₗ sᵣ Γ

-- binding: the bound variable is either used or dropped (§8)
data Bind (T : Scope → Set) : Scope → Set where
  use  : T (tt ∷ Γ) → Bind T Γ
  drop : T Γ        → Bind T Γ

-- the co-de-Bruijn λ-syntax: a term over EXACTLY its free variables Γ
data Tm : Scope → Set where
  var : Tm (tt ∷ [])
  app : (Tm ×ᴿ Tm) Γ → Tm Γ
  lam : Bind Tm Γ → Tm Γ

-- a thing with a thinning into Δ (McBride §5, the "co-de-Bruijn monad")
record _↑_ (T : Scope → Set)(Δ : Scope) : Set where
  constructor _⇑_
  field {sup} : Scope
        thing : T sup
        thn   : sup ⊑ Δ
open _↑_ public
infix 4 _↑_

-- renaming = carry the thinning, no traversal (McBride §5)
_⟨_⟩ : ∀ {T Δ Θ} → T ↑ Δ → Δ ⊑ Θ → T ↑ Θ
(t ⇑ θ) ⟨ φ ⟩ = t ⇑ (θ ⨾ φ)
infixl 8 _⟨_⟩

-- renaming functoriality (McBride §5): DEFINITIONAL — carry-the-thinning, no traversal
ren-id : ∀ {T Δ}(u : T ↑ Δ) → u ⟨ oi ⟩ ≡ u
ren-id (t ⇑ θ) = refl
ren-∘  : ∀ {T Δ Θ Ξ}(u : T ↑ Δ)(φ : Δ ⊑ Θ)(ψ : Θ ⊑ Ξ) → (u ⟨ φ ⟩) ⟨ ψ ⟩ ≡ u ⟨ φ ⨾ ψ ⟩
ren-∘ (t ⇑ θ) φ ψ = refl

-- smart app (McBride §6 coproduct): merges the two supports via `cop`
app↑ : ∀ {Δ} → (Tm ↑ Δ) → (Tm ↑ Δ) → Tm ↑ Δ
app↑ (l ⇑ θ) (r ⇑ φ) = app (pair l r (cov (cop θ φ))) ⇑ out (cop θ φ)

-- THE PAYOFF: `cop oi oi` was STUCK with thinnings opaque; with the cop/cov/oi
-- laws registered it now COMPUTES — app↑ reduces by refl:
test : app↑ (var ⇑ oi) (var ⇑ oi) ≡ (app (pair var var full) ⇑ oi)
test = refl
