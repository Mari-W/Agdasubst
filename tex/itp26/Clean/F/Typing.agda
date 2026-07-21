{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.F.Typing — System F typing, BI-SCOPED, structural context, subst-free.
--
-- `Φ ⊢[ θ ] t ∶ A`:  Φ : Cx Θ Γ (TIGHT over Γ, types over FULL Θ);  t : Tm Θₜ Γ
-- (its OWN type-support Θₜ);  θ : Θₜ ⊑ Θ (the type-thinning — term scope carries
-- none);  A : Ty ↑ Θ.  Term-scope splits via cohL/cohR (structural); type-scope
-- composes via Fac-L/R — INDEPENDENT, both fire, so the gate is definitional.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.Typing where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite
open import Clean.F.Tm public                              -- Tm, Bi, smart constructors, wkΓ-T/wkΘ-T, Pos/Scaffold/Fac
open import Clean.F.Ty using (Ty; _⇒↑_; ∀↑; _⟪_⟫; _∙_; idS)  -- type formers + type-sub (for ⊢App / subCx)

-- ── STRUCTURAL term context: one `Ty ↑ Θ` per term-var, TIGHT over Γ, full over Θ ──
data Cx (Θ : Scope) : Scope → Set where
  ε    : Cx Θ []
  _,-_ : ∀ {Γ} → Cx Θ Γ → Ty ↑ Θ → Cx Θ (tt ∷ Γ)
infixl 5 _,-_

rest : ∀ {Θ Δ Γ} → Δ ⊑ Γ → Cx Θ Γ → Cx Θ Δ
rest oz     ε        = ε
rest (os θ) (Φ ,- A) = rest θ Φ ,- A
rest (o' θ) (Φ ,- A) = rest θ Φ
splitL : ∀ {Θ Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Cx Θ Γ → Cx Θ Γₗ
splitL czz     ε        = ε
splitL (css c) (Φ ,- A) = splitL c Φ ,- A
splitL (cs' c) (Φ ,- A) = splitL c Φ ,- A
splitL (c's c) (Φ ,- A) = splitL c Φ
splitR : ∀ {Θ Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Cx Θ Γ → Cx Θ Γᵣ
splitR czz     ε        = ε
splitR (css c) (Φ ,- A) = splitR c Φ ,- A
splitR (cs' c) (Φ ,- A) = splitR c Φ
splitR (c's c) (Φ ,- A) = splitR c Φ ,- A

-- ── term-scope context coherences (verbatim Clean STLC, classifier Ty↑Θ) ──
opaque
  unfolding oi
  rest-oi : ∀ {Θ Δ}(Ψ : Cx Θ Δ) → rest oi Ψ ≡ Ψ
  rest-oi ε        = refl
  rest-oi (Ψ ,- A) = cong (_,- A) (rest-oi Ψ)
{-# REWRITE rest-oi #-}
opaque
  unfolding oe
  rest-oe : ∀ {Θ Δ}(Ψ : Cx Θ Δ) → rest oe Ψ ≡ ε
  rest-oe ε        = refl
  rest-oe (Ψ ,- A) = rest-oe Ψ
{-# REWRITE rest-oe #-}
opaque
  unfolding covL covR full
  splitL-covL : ∀ {Θ Γ Δ}(φ : Γ ⊑ Δ)(Ψ : Cx Θ Δ) → splitL (covL φ) Ψ ≡ Ψ
  splitL-covL oz     ε        = refl
  splitL-covL (os φ) (Ψ ,- A) = cong (_,- A) (splitL-covL φ Ψ)
  splitL-covL (o' φ) (Ψ ,- A) = cong (_,- A) (splitL-covL φ Ψ)
  splitR-covL : ∀ {Θ Γ Δ}(φ : Γ ⊑ Δ)(Ψ : Cx Θ Δ) → splitR (covL φ) Ψ ≡ rest φ Ψ
  splitR-covL oz     ε        = refl
  splitR-covL (os φ) (Ψ ,- A) = cong (_,- A) (splitR-covL φ Ψ)
  splitR-covL (o' φ) (Ψ ,- A) = splitR-covL φ Ψ
  splitL-covR : ∀ {Θ Γ Δ}(θ : Γ ⊑ Δ)(Ψ : Cx Θ Δ) → splitL (covR θ) Ψ ≡ rest θ Ψ
  splitL-covR oz     ε        = refl
  splitL-covR (os θ) (Ψ ,- A) = cong (_,- A) (splitL-covR θ Ψ)
  splitL-covR (o' θ) (Ψ ,- A) = splitL-covR θ Ψ
  splitR-covR : ∀ {Θ Γ Δ}(θ : Γ ⊑ Δ)(Ψ : Cx Θ Δ) → splitR (covR θ) Ψ ≡ Ψ
  splitR-covR oz     ε        = refl
  splitR-covR (os θ) (Ψ ,- A) = cong (_,- A) (splitR-covR θ Ψ)
  splitR-covR (o' θ) (Ψ ,- A) = cong (_,- A) (splitR-covR θ Ψ)
  splitL-full : ∀ {Θ Γ}(Ψ : Cx Θ Γ) → splitL full Ψ ≡ Ψ
  splitL-full ε        = refl
  splitL-full (Ψ ,- A) = cong (_,- A) (splitL-full Ψ)
  splitR-full : ∀ {Θ Γ}(Ψ : Cx Θ Γ) → splitR full Ψ ≡ Ψ
  splitR-full ε        = refl
  splitR-full (Ψ ,- A) = cong (_,- A) (splitR-full Ψ)
{-# REWRITE splitL-covL splitR-covL splitL-covR splitR-covR splitL-full splitR-full #-}
opaque
  unfolding cop
  cohL : ∀ {Θ sₗ sᵣ Δ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(Ψ : Cx Θ Δ)
       → splitL (cov (cop θ φ)) (rest (out (cop θ φ)) Ψ) ≡ rest θ Ψ
  cohL oz     oz     ε        = refl
  cohL (os θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohL θ φ Ψ)
  cohL (os θ) (o' φ) (Ψ ,- A) = cong (_,- A) (cohL θ φ Ψ)
  cohL (o' θ) (os φ) (Ψ ,- A) = cohL θ φ Ψ
  cohL (o' θ) (o' φ) (Ψ ,- A) = cohL θ φ Ψ
  cohR : ∀ {Θ sₗ sᵣ Δ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(Ψ : Cx Θ Δ)
       → splitR (cov (cop θ φ)) (rest (out (cop θ φ)) Ψ) ≡ rest φ Ψ
  cohR oz     oz     ε        = refl
  cohR (os θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohR θ φ Ψ)
  cohR (os θ) (o' φ) (Ψ ,- A) = cohR θ φ Ψ
  cohR (o' θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohR θ φ Ψ)
  cohR (o' θ) (o' φ) (Ψ ,- A) = cohR θ φ Ψ
{-# REWRITE cohL cohR #-}

-- type-WEAKEN the whole context by one type-var (total, distributive — under Λ)
wkCx : ∀ {Θ Γ} → Cx Θ Γ → Cx (tt ∷ Θ) Γ
wkCx ε        = ε
wkCx (Φ ,- A) = wkCx Φ ,- wk↑ tt A
-- type-SUBSTITUTE the whole context (for type-β preservation)
subCx : ∀ {Θ Δ Γ} → Cx Θ Γ → Clean.F.Ty.Sub Δ Θ → Cx Δ Γ
subCx ε        στ = ε
subCx (Φ ,- A) στ = subCx Φ στ ,- (A ⟪ στ ⟫)

-- ════════════════════════════════════════════════════════════════════════════
-- THE TYPING JUDGEMENT — `Φ ⊢[ θ ] t ∶ A` (type-thinning θ; term scope tight).
-- ════════════════════════════════════════════════════════════════════════════
data _⊢[_]_∶_ : ∀ {Θₜ Θ Γ} → Cx Θ Γ → Θₜ ⊑ Θ → Tm Θₜ Γ → Ty ↑ Θ → Set where
  ⊢var  : ∀ {Θ}{A : Ty ↑ Θ} → (ε ,- A) ⊢[ oe ] tmvar ∶ A
  ⊢app  : ∀ {Θₗ Θᵣ Θₜ Θ Γₗ Γᵣ Γ}{Φ : Cx Θ Γ}{l : Tm Θₗ Γₗ}{r : Tm Θᵣ Γᵣ}
            {cθ : Cover Θₗ Θᵣ Θₜ}{θ : Θₜ ⊑ Θ}{cγ : Cover Γₗ Γᵣ Γ}{A B : Ty ↑ Θ}
        → splitL cγ Φ ⊢[ thinL cθ ⨾ θ ] l ∶ (A ⇒↑ B)
        → splitR cγ Φ ⊢[ thinR cθ ⨾ θ ] r ∶ A
        → Φ ⊢[ θ ] app l r cθ cγ ∶ B
  ⊢App  : ∀ {Θₑ Θₐ Θₜ Θ Γ}{Φ : Cx Θ Γ}{e : Tm Θₑ Γ}{a : Ty Θₐ}
            {cθ : Cover Θₑ Θₐ Θₜ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ (tt ∷ Θ)}
        → Φ ⊢[ thinL cθ ⨾ θ ] e ∶ ∀↑ B
        → Φ ⊢[ θ ] App e a cθ ∶ (B ⟪ (a ⇑ (thinR cθ ⨾ θ)) ∙ idS ⟫)
  ⊢lamᵘ : ∀ {Θₐ Θᵦ Θₜ Θ Γ}{Φ : Cx Θ Γ}{a : Ty Θₐ}{body : Tm Θᵦ (tt ∷ Γ)}
            {cθ : Cover Θₐ Θᵦ Θₜ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ Θ}
        → (Φ ,- (a ⇑ (thinL cθ ⨾ θ))) ⊢[ thinR cθ ⨾ θ ] body ∶ B
        → Φ ⊢[ θ ] lam a (use body) cθ ∶ ((a ⇑ (thinL cθ ⨾ θ)) ⇒↑ B)
  ⊢lamᵈ : ∀ {Θₐ Θᵦ Θₜ Θ Γ}{Φ : Cx Θ Γ}{a : Ty Θₐ}{body : Tm Θᵦ Γ}
            {cθ : Cover Θₐ Θᵦ Θₜ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ Θ}
        → Φ ⊢[ thinR cθ ⨾ θ ] body ∶ B
        → Φ ⊢[ θ ] lam a (drop body) cθ ∶ ((a ⇑ (thinL cθ ⨾ θ)) ⇒↑ B)
  ⊢Lamᵘ : ∀ {Θₜ Θ Γ}{Φ : Cx Θ Γ}{body : Tm (tt ∷ Θₜ) Γ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ (tt ∷ Θ)}
        → wkCx Φ ⊢[ os θ ] body ∶ B
        → Φ ⊢[ θ ] Lam (use body) ∶ ∀↑ B
  ⊢Lamᵈ : ∀ {Θₜ Θ Γ}{Φ : Cx Θ Γ}{body : Tm Θₜ Γ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ (tt ∷ Θ)}
        → wkCx Φ ⊢[ o' θ ] body ∶ B
        → Φ ⊢[ θ ] Lam (drop body) ∶ ∀↑ B
infix 4 _⊢[_]_∶_

-- ── typing of a BI-SCOPED term, and the smart constructors ──
_⊢↑_∶_ : ∀ {Θ Γ} → Cx Θ Γ → Bi Tm Θ Γ → Ty ↑ Θ → Set
Φ ⊢↑ (t ⇑[ θ , φ ]) ∶ A = rest φ Φ ⊢[ θ ] t ∶ A
infix 4 _⊢↑_∶_

-- application: definitional — term cover via cohL/cohR, type cover via Fac-L/R
⊢app↑ : ∀ {Θ Γ}{Φ : Cx Θ Γ}{A B}{L R : Bi Tm Θ Γ}
      → Φ ⊢↑ L ∶ (A ⇒↑ B) → Φ ⊢↑ R ∶ A → Φ ⊢↑ appᵇ L R ∶ B
⊢app↑ {L = l ⇑[ θₗ , φₗ ]}{R = r ⇑[ θᵣ , φᵣ ]} ⊢L ⊢R = ⊢app ⊢L ⊢R

-- the fresh term variable, typed
⊢fresh : ∀ {Θ Γ}{Φ : Cx Θ Γ}{A} → (Φ ,- A) ⊢↑ var₀ᵇ ∶ A
⊢fresh = ⊢var
