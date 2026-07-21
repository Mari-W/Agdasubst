{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.F.Tm — System F TERMS, a BI-SCOPED co-de-Bruijn family `Tm Θ Γ`.
--
-- Θ is the TYPE-support, Γ the TERM-support, with INDEPENDENT thinnings/covers per
-- scope.  A term-variable has type-support `[]` (`tmvar : Tm [] (tt∷[])`).  A
-- thing-with-thinning now carries TWO thinnings (`Bi`); renaming carries BOTH (free).
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.Tm where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
open import Clean.F.Ty using (Ty; tvar; _⇒_; ∀')   -- the type family (no type-sub names imported)
open import Clean.Pos public                        -- Scope, _⊑_, _⨾_, oe, Cover, cop, _↑_, _⇑_, Bind, use, drop, pair, ...

-- ── the bi-scoped TERM family ──
data Tm : Scope → Scope → Set where
  tmvar : Tm [] (tt ∷ [])                              -- type-support [], term-support singleton
  app   : ∀ {Θₗ Θᵣ Θ Γₗ Γᵣ Γ}                          -- merge BOTH scopes, independent covers
        → Tm Θₗ Γₗ → Tm Θᵣ Γᵣ → Cover Θₗ Θᵣ Θ → Cover Γₗ Γᵣ Γ → Tm Θ Γ
  lam   : ∀ {Θₐ Θᵦ Θ Γ}                                -- λ(x:A). body — A : Ty Θₐ, body binds a TERM var
        → Ty Θₐ → Bind tt (Tm Θᵦ) Γ → Cover Θₐ Θᵦ Θ → Tm Θ Γ
  Lam   : ∀ {Θ Γ}                                      -- Λα. body — body binds a TYPE var
        → Bind tt (λ Θ′ → Tm Θ′ Γ) Θ → Tm Θ Γ
  App   : ∀ {Θₑ Θₐ Θ Γ}                                -- e [A] — type application, merges the TYPE scope
        → Tm Θₑ Γ → Ty Θₐ → Cover Θₑ Θₐ Θ → Tm Θ Γ

-- ── bi-scoped thing-with-thinning: TWO thinnings (type-scope and term-scope) ──
record Bi (F : Scope → Scope → Set)(Θ Γ : Scope) : Set where
  constructor _⇑[_,_]
  field {spΘ spΓ} : Scope
        ent : F spΘ spΓ
        thΘ : spΘ ⊑ Θ
        thΓ : spΓ ⊑ Γ
open Bi public

-- rename a bi-scoped thing along BOTH thinnings (carry-the-thinning, no traversal)
_⟨_,_⟩b : ∀ {F Θ Γ Θ′ Γ′} → Bi F Θ Γ → Θ ⊑ Θ′ → Γ ⊑ Γ′ → Bi F Θ′ Γ′
(e ⇑[ θ , φ ]) ⟨ ψΘ , ψΓ ⟩b = e ⇑[ θ ⨾ ψΘ , φ ⨾ ψΓ ]
infixl 8 _⟨_,_⟩b

-- the two single-variable bi-scoped weakenings (pure thinning algebra, o'-extend)
wkΓ-T : ∀ {Θ Γ} → Bi Tm Θ Γ → Bi Tm Θ (tt ∷ Γ)
wkΓ-T (t ⇑[ θ , φ ]) = t ⇑[ θ , o' φ ]
wkΘ-T : ∀ {Θ Γ} → Bi Tm Θ Γ → Bi Tm (tt ∷ Θ) Γ
wkΘ-T (t ⇑[ θ , φ ]) = t ⇑[ o' θ , φ ]

-- ── BI-SCOPED SMART CONSTRUCTORS — merge each scope's supports INDEPENDENTLY ──
-- the term variable, as a bi-scoped thing (type-support [], term-support head slot)
var₀ᵇ : ∀ {Θ Γ} → Bi Tm Θ (tt ∷ Γ)
var₀ᵇ = tmvar ⇑[ oe , os oe ]

-- s t : merge BOTH scopes
appᵇ : ∀ {Θ Γ} → Bi Tm Θ Γ → Bi Tm Θ Γ → Bi Tm Θ Γ
appᵇ (l ⇑[ θₗ , φₗ ]) (r ⇑[ θᵣ , φᵣ ]) =
  app l r (cov (cop θₗ θᵣ)) (cov (cop φₗ φᵣ)) ⇑[ out (cop θₗ θᵣ) , out (cop φₗ φᵣ) ]

-- λ(x:A). body : merge A's type-support with the body's; read the body's TERM binder
lamᵇ : ∀ {Θ Γ} → Ty ↑ Θ → Bi Tm Θ (tt ∷ Γ) → Bi Tm Θ Γ
lamᵇ (a ⇑ θₐ) (t ⇑[ θᵦ , os φ ]) = lam a (use t)  (cov (cop θₐ θᵦ)) ⇑[ out (cop θₐ θᵦ) , φ ]
lamᵇ (a ⇑ θₐ) (t ⇑[ θᵦ , o' φ ]) = lam a (drop t) (cov (cop θₐ θᵦ)) ⇑[ out (cop θₐ θᵦ) , φ ]

-- Λα. body : read the body's TYPE binder; term scope unchanged
Lamᵇ : ∀ {Θ Γ} → Bi Tm (tt ∷ Θ) Γ → Bi Tm Θ Γ
Lamᵇ (t ⇑[ os θ , φ ]) = Lam (use t)  ⇑[ θ , φ ]
Lamᵇ (t ⇑[ o' θ , φ ]) = Lam (drop t) ⇑[ θ , φ ]

-- e [A] : merge the type-arg's support into the TYPE scope; term scope shared
Appᵇ : ∀ {Θ Γ} → Bi Tm Θ Γ → Ty ↑ Θ → Bi Tm Θ Γ
Appᵇ (e ⇑[ θₑ , φ ]) (a ⇑ θₐ) =
  App e a (cov (cop θₑ θₐ)) ⇑[ out (cop θₑ θₐ) , φ ]
