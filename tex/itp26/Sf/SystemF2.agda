{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.SystemF2 — the TWO-SCOPE (bi-scoped) co-de-Bruijn System F SYNTAX.
--
-- This is the user's design: types and terms are GENUINELY SEPARATE co-de-Bruijn
-- families over INDEPENDENT scopes.
--
--   • `Ty Θ`    — a co-de-Bruijn type over a TYPE-scope Θ only.  Single-scope,
--     exactly the STLC pattern + a `∀` binder.  Reuses Sf.Scaffold/Sf.Sub at the
--     one-element sort ⊤ for the type-substitution engine.
--
--   • `Tm Θ Γ`  — a BI-SCOPED co-de-Bruijn term: it has a TYPE-support Θ AND a
--     TERM-support Γ, with SEPARATE thinnings and SEPARATE covers per scope.  A
--     term-variable carries NO type-support (`tmvar : Tm [] (tt ∷ [])`).  Type
--     annotations inside a term (`lam`, `App`) are `Ty`-things-with-thinnings into
--     the type-scope.
--
-- The point: type-variables and term-variables live in genuinely separate scopes
-- with separate thinnings, so a term context can be TIGHT over the term-scope
-- while types ride along over the independent type-scope.  That is what removes
-- the partial-restriction wall (the single-sorted `factor (os φ)(o' θ)`).
--
-- This file holds JUST the syntax (both families) + the type-substitution engine
-- for `Ty`.  The typing judgement lives in Sf.SystemF2Typing.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.SystemF2 where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Agda.Builtin.Equality.Rewrite

-- ════════════════════════════════════════════════════════════════════════════
-- THE TYPE SCOPE.  We open the generic co-de-Bruijn scaffold at sort ⊤: one kind
-- of TYPE variable.  `Scope`, thinnings `_⊑_`, covers, `cop`, `_↑_`, `_×ᴿ_`,
-- `Bind`, `pairUp`, `bindUp`, `wk↑`, `_⟨_⟩` are all in scope from here on and
-- refer to the TYPE scope.  (The term scope below reuses THE SAME algebra — it is
-- the same `Scope = List ⊤` — only applied independently to term variables.)
-- ════════════════════════════════════════════════════════════════════════════
open import Sf.Scaffold ⊤ public

-- ── TYPES: a single-scope co-de-Bruijn family over the type scope. ──
data Ty : Scope → Set where
  tvar : Ty (tt ∷ [])              -- the sole type variable
  _`→_ : (Ty ×ᴿ Ty) Θ → Ty Θ       -- function type
  `∀   : Bind tt Ty Θ → Ty Θ        -- universal (binds a type variable)

-- type-formers as smart constructors over things-with-thinnings (merge supports)
_⇒↑_ : ∀ {Θ} → Ty ↑ Θ → Ty ↑ Θ → Ty ↑ Θ
A ⇒↑ B = _`→_ <$> pairUp A B
infixr 5 _⇒↑_
∀↑ : ∀ {Θ} → Ty ↑ (tt ∷ Θ) → Ty ↑ Θ
∀↑ X = `∀ <$> bindUp X

-- instantiate the shared substitution CONTAINER with Ty + tvar (TYPE substitution)
open import Sf.Sub ⊤ (λ Θ _ → Ty Θ) tvar public

-- ── the TYPE-substitution ACTION.  OPAQUE so IdSubst can register. ──
opaque
  subT  : ∀ {Θ Ξ} → Ty Θ → Sub Ξ Θ → Ty ↑ Ξ
  subT tvar               ([] ,- u) = u
  subT (_`→_ (pair a b cv)) σ = _`→_ <$> pairUp (subT a (selL cv σ)) (subT b (selR cv σ))
  subT (`∀ (use t))         σ = `∀   <$> bindUp (subT t (wkSub σ ,- var₀))
  subT (`∀ (drop t))        σ = `∀   <$> (drop <$> subT t σ)

-- apply a type-substitution to a type-thing-with-thinning.  OPAQUE so neutral.
opaque
  unfolding subT
  _⟪_⟫T : ∀ {Θ Ξ} → Ty ↑ Θ → Sub Ξ Θ → Ty ↑ Ξ
  (t ⇑ θ) ⟪ τ ⟫T = subT t (τ ↾ θ)
infixl 8 _⟪_⟫T

-- ════════════════════════════════════════════════════════════════════════════
-- THE TERM FAMILY  `Tm Θ Γ` — BI-SCOPED.  Θ is the TYPE-support, Γ is the
-- TERM-support; the two scopes have INDEPENDENT thinnings and covers (both drawn
-- from the same `Sf.Thin` algebra at sort ⊤, applied per scope).
--
-- Binders reuse the GENERIC `Bind` by partial application at the right scope:
--   • `Bind tt (Tm Θᵦ) Γ`         binds a TERM var (a Γ-binder), for `lam`.
--   • `Bind tt (λ Θ → Tm Θ Γ) Θ`  binds a TYPE var (a Θ-binder), for `Lam`.
-- ════════════════════════════════════════════════════════════════════════════
data Tm : Scope → Scope → Set where
  -- a term variable.  THE KEY DESIGN POINT: its TYPE-support is `[]` (it carries
  -- NO type variables); its TERM-support is the singleton `tt ∷ []`.
  tmvar : Tm [] (tt ∷ [])
  -- application: merge BOTH scopes, INDEPENDENT covers (cθ on types, cγ on terms).
  app  : ∀ {Θₗ Θᵣ Θ Γₗ Γᵣ Γ}
       → Tm Θₗ Γₗ → Tm Θᵣ Γᵣ → Cover Θₗ Θᵣ Θ → Cover Γₗ Γᵣ Γ → Tm Θ Γ
  -- λ(x:a). body.  The annotation `a : Ty Θₐ` and the body's type-support Θᵦ merge
  -- via the TYPE-cover cθ.  The body binds a TERM variable (a Γ-binder).
  lam  : ∀ {Θₐ Θᵦ Θ Γ}
       → Ty Θₐ → Bind tt (Tm Θᵦ) Γ → Cover Θₐ Θᵦ Θ → Tm Θ Γ
  -- Λα. body.  The body binds a TYPE variable (a Θ-binder); the term scope Γ is
  -- unchanged.
  `Lam : ∀ {Θ Γ}
       → Bind tt (λ Θ′ → Tm Θ′ Γ) Θ → Tm Θ Γ
  -- e [a]  (type application).  The type argument `a : Ty Θₐ` merges into the type
  -- scope via cθ; the term scope Γ is shared (the arg has no term vars).
  `App : ∀ {Θₑ Θₐ Θ Γ}
       → Tm Θₑ Γ → Ty Θₐ → Cover Θₑ Θₐ Θ → Tm Θ Γ
