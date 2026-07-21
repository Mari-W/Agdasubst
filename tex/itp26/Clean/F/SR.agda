{-# OPTIONS --rewriting #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.F.SR — option #2: the type-SUBSTITUTION preserves typing (`subTyTm`-pres).
--
-- Renaming is subsumed (a renaming is a degenerate type-sub), so there is NO
-- separate ⊢-ren.  Arrow cases are FREE (the type-sub distribution ⟪⟫-⇒↑ is refl,
-- unlike renaming's cop-⨾); the ∀ case costs one bounded `subst` (⟪⟫-∀↑) + the
-- ∀-injectivity peel — exactly the Sf-version cost.  In progress.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.SR where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Agda.Builtin.Equality.Rewrite
import Clean.F.Ty as TY
open TY using (Ty)
open import Clean.F.TyLaws using (⟪⟫-⇒↑; ⟪⟫-∀↑; lift-↾; wk-skip; sub-wkSub; lift≡∙)
open import Clean.F.TmTy using (subTyTm)
open import Clean.F.TmLaws using (sub-wkΘSub-tm)
open import Clean.F.TmTyLaws using (subTyTm-wkΘ; lift-↾-o'; subTyTm-shift; ⟪↑ₛ⟫≡wk↑)
open import Clean.F.Typing

-- type-substitute the whole context (one entry's type ⟪ στ ⟫) — already in Typing as subCx
-- subCx-split commutations (structural; the term scope rides along)
subCx-splitL : ∀ {Θ Δ Γₗ Γᵣ Γ}(στ : TY.Sub Δ Θ)(cv : Cover Γₗ Γᵣ Γ)(Φ : Cx Θ Γ)
             → subCx (splitL cv Φ) στ ≡ splitL cv (subCx Φ στ)
subCx-splitL στ czz     ε        = refl
subCx-splitL στ (css c) (Φ ,- A) = cong (_,- (A TY.⟪ στ ⟫)) (subCx-splitL στ c Φ)
subCx-splitL στ (cs' c) (Φ ,- A) = cong (_,- (A TY.⟪ στ ⟫)) (subCx-splitL στ c Φ)
subCx-splitL στ (c's c) (Φ ,- A) = subCx-splitL στ c Φ
subCx-splitR : ∀ {Θ Δ Γₗ Γᵣ Γ}(στ : TY.Sub Δ Θ)(cv : Cover Γₗ Γᵣ Γ)(Φ : Cx Θ Γ)
             → subCx (splitR cv Φ) στ ≡ splitR cv (subCx Φ στ)
subCx-splitR στ czz     ε        = refl
subCx-splitR στ (css c) (Φ ,- A) = cong (_,- (A TY.⟪ στ ⟫)) (subCx-splitR στ c Φ)
subCx-splitR στ (cs' c) (Φ ,- A) = subCx-splitR στ c Φ
subCx-splitR στ (c's c) (Φ ,- A) = cong (_,- (A TY.⟪ στ ⟫)) (subCx-splitR στ c Φ)

⊢-cong : ∀ {Θₜ Θ Γ}{Φ Φ′ : Cx Θ Γ}{θ : Θₜ ⊑ Θ}{t}{A A′}
       → Φ ≡ Φ′ → A ≡ A′ → Φ ⊢[ θ ] t ∶ A → Φ′ ⊢[ θ ] t ∶ A′
⊢-cong refl refl d = d

-- subCx commutes with the term-scope restriction `rest`
subCx-rest : ∀ {Θ Δ sup Γ}(στ : TY.Sub Δ Θ)(δ : sup ⊑ Γ)(Φ : Cx Θ Γ) → subCx (rest δ Φ) στ ≡ rest δ (subCx Φ στ)
subCx-rest στ oz     ε        = refl
subCx-rest στ (os δ) (Φ ,- A) = cong (_,- (A TY.⟪ στ ⟫)) (subCx-rest στ δ Φ)
subCx-rest στ (o' δ) (Φ ,- A) = subCx-rest στ δ Φ

-- the cover-split = restriction along the cover-thinning (thinL opaque → needs unfolding)
opaque
  unfolding thinL thinR
  splitL≡rest : ∀ {Θ Γₗ Γᵣ Γ}(cv : Cover Γₗ Γᵣ Γ)(Φ : Cx Θ Γ) → splitL cv Φ ≡ rest (thinL cv) Φ
  splitL≡rest czz     ε        = refl
  splitL≡rest (css c) (Φ ,- A) = cong (_,- A) (splitL≡rest c Φ)
  splitL≡rest (cs' c) (Φ ,- A) = cong (_,- A) (splitL≡rest c Φ)
  splitL≡rest (c's c) (Φ ,- A) = splitL≡rest c Φ
  splitR≡rest : ∀ {Θ Γₗ Γᵣ Γ}(cv : Cover Γₗ Γᵣ Γ)(Φ : Cx Θ Γ) → splitR cv Φ ≡ rest (thinR cv) Φ
  splitR≡rest czz     ε        = refl
  splitR≡rest (css c) (Φ ,- A) = cong (_,- A) (splitR≡rest c Φ)
  splitR≡rest (cs' c) (Φ ,- A) = splitR≡rest c Φ
  splitR≡rest (c's c) (Φ ,- A) = cong (_,- A) (splitR≡rest c Φ)

-- rest is functorial (needed to thread term-thinnings through covers)
opaque
  unfolding _⨾_
  rest-⨾ : ∀ {Θ sup Δ Γ}(δ : sup ⊑ Δ)(γ : Δ ⊑ Γ)(Φ : Cx Θ Γ) → rest (δ ⨾ γ) Φ ≡ rest δ (rest γ Φ)
  rest-⨾ δ      oz     ε        = refl
  rest-⨾ (os δ) (os γ) (Φ ,- A) = cong (_,- A) (rest-⨾ δ γ Φ)
  rest-⨾ (o' δ) (os γ) (Φ ,- A) = rest-⨾ δ γ Φ
  rest-⨾ δ      (o' γ) (Φ ,- A) = rest-⨾ δ γ Φ

-- rest commutes with the type-weakening wkCx
rest-wkCx : ∀ {Θ sup Γ}(θ : sup ⊑ Γ)(Φ : Cx Θ Γ) → rest θ (wkCx Φ) ≡ wkCx (rest θ Φ)
rest-wkCx oz     ε        = refl
rest-wkCx (os θ) (Φ ,- A) = cong (_,- wk↑ tt A) (rest-wkCx θ Φ)
rest-wkCx (o' θ) (Φ ,- A) = rest-wkCx θ Φ

-- ── bi-scoped smart constructors for the typing (lam/Lam/App) — definitional via Fac-L/R ──
open import Clean.F.Tm using (Bi; _⇑[_,_]; lamᵇ; Lamᵇ; Appᵇ; wkΓ-T; wkΘ-T)
open import Clean.F.TyLaws using (_⇒↑_; ∀↑)
⊢lam↑ : ∀ {Θ Γ}{Ψ : Cx Θ Γ}{A B}{X : Bi Tm Θ (tt ∷ Γ)} → (Ψ ,- A) ⊢↑ X ∶ B → Ψ ⊢↑ lamᵇ A X ∶ (A ⇒↑ B)
⊢lam↑ {A = a ⇑ θₐ}{X = t ⇑[ θ , os φ ]} ⊢t = ⊢lamᵘ ⊢t
⊢lam↑ {A = a ⇑ θₐ}{X = t ⇑[ θ , o' φ ]} ⊢t = ⊢lamᵈ ⊢t
⊢Lam↑ : ∀ {Θ Γ}{Ψ : Cx Θ Γ}{B}{X : Bi Tm (tt ∷ Θ) Γ} → wkCx Ψ ⊢↑ X ∶ B → Ψ ⊢↑ Lamᵇ X ∶ ∀↑ B
⊢Lam↑ {Ψ = Ψ}{B = B}{X = t ⇑[ os θ , φ ]} ⊢t = ⊢Lamᵘ {B = B} (subst (λ Φ′ → Φ′ ⊢[ os θ ] t ∶ B) (rest-wkCx φ Ψ) ⊢t)
⊢Lam↑ {Ψ = Ψ}{B = B}{X = t ⇑[ o' θ , φ ]} ⊢t = ⊢Lamᵈ {B = B} (subst (λ Φ′ → Φ′ ⊢[ o' θ ] t ∶ B) (rest-wkCx φ Ψ) ⊢t)
⊢App↑ : ∀ {Θ Γ}{Ψ : Cx Θ Γ}{B}{E : Bi Tm Θ Γ}(A : Ty ↑ Θ) → Ψ ⊢↑ E ∶ ∀↑ B → Ψ ⊢↑ Appᵇ E A ∶ (B TY.⟪ A TY.∙ TY.idS ⟫)
⊢App↑ {B = B}{E = e ⇑[ θₑ , φ ]} (a ⇑ θₐ) ⊢e = ⊢App {B = B} ⊢e

-- ── the type-app composition law: it FOLLOWS FROM THE σ-LAWS (refl) ──
-- both sides normalise to `B ⟪ (u ⟪ στ ⟫) ∙ στ ⟫` via Clos/Map/IdL (LHS) and
-- Clos/lift-def/Map/VarCons/Ass/ShiftCons/IdR (RHS).  Proven here with ⟪⟫ OPAQUE
-- (so the registered σ-laws fire); used as a subst inside subTyTm-pres.
App-comm : ∀ {Θ Δ}(B : Ty ↑ (tt ∷ Θ))(u : Ty ↑ Θ)(στ : TY.Sub Δ Θ)
         → (B TY.⟪ u TY.∙ TY.idS ⟫) TY.⟪ στ ⟫ ≡ (B TY.⟪ TY.lift στ ⟫) TY.⟪ (u TY.⟪ στ ⟫) TY.∙ TY.idS ⟫
App-comm B u στ = refl

-- ── annotation bridge: ⟪⟫ on an ATOM = sub (the one ⟪⟫-fact that can't be a rewrite,
-- since `(a⇑ξ)⟪στ⟫` η-overlaps ⟪⟫-⇒↑).  Proven once here (Layer A), applied opaquely. ──
opaque
  unfolding TY._⟪_⟫ TY._↾_ TY.selL TY.selR
  ⟪⟫ᵇL : ∀ {Θ Δ Θₗ Θᵣ Θₜ}(a : Ty Θₗ)(cθ : Cover Θₗ Θᵣ Θₜ)(θ : Θₜ ⊑ Θ)(στ : TY.Sub Δ Θ)
       → (a ⇑ (thinL cθ ⨾ θ)) TY.⟪ στ ⟫ ≡ TY.sub a (TY.selL cθ (στ TY.↾ θ))
  ⟪⟫ᵇL a cθ θ στ = refl
  ⟪⟫ᵇR : ∀ {Θ Δ Θₗ Θᵣ Θₜ}(a : Ty Θᵣ)(cθ : Cover Θₗ Θᵣ Θₜ)(θ : Θₜ ⊑ Θ)(στ : TY.Sub Δ Θ)
       → (a ⇑ (thinR cθ ⨾ θ)) TY.⟪ στ ⟫ ≡ TY.sub a (TY.selR cθ (στ TY.↾ θ))
  ⟪⟫ᵇR a cθ θ στ = refl

-- ── type-weakening commutes with type-sub (for the Λ cases) ──
-- `(wk↑ A) ⟪ lift στ ⟫ ≡ wk↑ (A ⟪ στ ⟫)`: lift≡∙ exposes lift = var₀ ∙ wkSub, then
-- wk-skip drops the head and sub-wkSub commutes the shift out.
wk-comm : ∀ {Θ Δ}(A : Ty ↑ Θ)(στ : TY.Sub Δ Θ) → (wk↑ tt A) TY.⟪ TY.lift στ ⟫ ≡ wk↑ tt (A TY.⟪ στ ⟫)
wk-comm A στ = trans (cong (λ s → (wk↑ tt A) TY.⟪ s ⟫) (lift≡∙ στ))
                     (trans (wk-skip A TY.var₀ (TY.wkSub στ)) (sub-wkSub A στ))

subCx-wkCx : ∀ {Θ Δ Γ}(Φ : Cx Θ Γ)(στ : TY.Sub Δ Θ) → subCx (wkCx Φ) (TY.lift στ) ≡ wkCx (subCx Φ στ)
subCx-wkCx ε        στ = refl
subCx-wkCx (Φ ,- A) στ = cong₂ _,-_ (subCx-wkCx Φ στ) (wk-comm A στ)

-- condition helper: the recursive splitL/splitR conditions follow from the parent's
condL : ∀ {Θ Δ Γ Γ' Γₗ Γᵣ}(στ : TY.Sub Δ Θ)(ψ : Γ ⊑ Γ'){Ψ : Cx Δ Γ'}(cv : Cover Γₗ Γᵣ Γ)(Φ : Cx Θ Γ)
      → rest ψ Ψ ≡ subCx Φ στ → rest (thinL cv ⨾ ψ) Ψ ≡ subCx (splitL cv Φ) στ
condL στ ψ cv Φ eq = trans (trans (rest-⨾ (thinL cv) ψ _) (cong (rest (thinL cv)) eq))
                           (sym (trans (cong (λ X → subCx X στ) (splitL≡rest cv Φ)) (subCx-rest στ (thinL cv) Φ)))
condR : ∀ {Θ Δ Γ Γ' Γₗ Γᵣ}(στ : TY.Sub Δ Θ)(ψ : Γ ⊑ Γ'){Ψ : Cx Δ Γ'}(cv : Cover Γₗ Γᵣ Γ)(Φ : Cx Θ Γ)
      → rest ψ Ψ ≡ subCx Φ στ → rest (thinR cv ⨾ ψ) Ψ ≡ subCx (splitR cv Φ) στ
condR στ ψ cv Φ eq = trans (trans (rest-⨾ (thinR cv) ψ _) (cong (rest (thinR cv)) eq))
                           (sym (trans (cong (λ X → subCx X στ) (splitR≡rest cv Φ)) (subCx-rest στ (thinR cv) Φ)))

-- the Λ context-coherence (the structural cond for the wkCx recursion)
condΛ : ∀ {Θ Δ Γ Γ'}{Ψ : Cx Δ Γ'}(στ : TY.Sub Δ Θ)(ψ : Γ ⊑ Γ')(Φ : Cx Θ Γ)
      → rest ψ Ψ ≡ subCx Φ στ → rest ψ (wkCx Ψ) ≡ subCx (wkCx Φ) (TY.lift στ)
condΛ {Ψ = Ψ} στ ψ Φ eq = trans (rest-wkCx ψ Ψ) (trans (cong wkCx eq) (sym (subCx-wkCx Φ στ)))

-- ── per-rule smart constructors that absorb the type-former σ-steps (App-comm /
-- ⟪⟫-∀↑) — so subTyTm-pres reads as plain "apply the rule, substitution-aware" ──
-- subTyTm is TRANSPARENT (it's the action — no rewrite is keyed on it — so it just
-- recurses).  This block unfolds NOTHING: the type-sub CALCULUS (⟪⟫/sub/⇒↑/∀↑/↾/sel)
-- is opaque and driven purely by the registered rewrites + the applied ⟪⟫ᵇ bridges.
opaque
  ⊢App-sub : ∀ {Θ Δ Γ Γ′}{Ψ : Cx Δ Γ′}{Θₑ Θₐ Θₜ}{e : Tm Θₑ Γ}{a : Ty Θₐ}{cθ : Cover Θₑ Θₐ Θₜ}
               {θ : Θₜ ⊑ Θ}{B : Ty ↑ (tt ∷ Θ)}{στ : TY.Sub Δ Θ}{ψ : Γ ⊑ Γ′}
           → Ψ ⊢↑ subTyTm e ψ (TY.selL cθ (στ TY.↾ θ)) ∶ ((∀↑ B) TY.⟪ στ ⟫)
           → Ψ ⊢↑ subTyTm (App e a cθ) ψ (στ TY.↾ θ) ∶ ((B TY.⟪ (a ⇑ (thinR cθ ⨾ θ)) TY.∙ TY.idS ⟫) TY.⟪ στ ⟫)
  -- App-comm is now DEFINITIONAL (⟪⟫ opaque ⇒ σ-laws fire); ⟪⟫-∀↑ fired on the
  -- hypothesis by rewrite.  Sole remaining step: the annotation bridge ⟪⟫ᵇR.
  ⊢App-sub {Ψ = Ψ}{e = e}{a = a}{cθ = cθ}{θ = θ}{B = B}{στ = στ}{ψ = ψ} ⊢rec =
    subst (λ z → Ψ ⊢↑ subTyTm (App e a cθ) ψ (στ TY.↾ θ) ∶ ((B TY.⟪ TY.lift στ ⟫) TY.⟪ z TY.∙ TY.idS ⟫))
          (sym (⟪⟫ᵇR a cθ θ στ))
          (⊢App↑ {B = B TY.⟪ TY.lift στ ⟫}{E = subTyTm e ψ (TY.selL cθ (στ TY.↾ θ))}
                 (TY.sub a (TY.selR cθ (στ TY.↾ θ))) ⊢rec)
  ⊢Lam-sub-use : ∀ {Θ Δ Γ Γ′}{Ψ : Cx Δ Γ′}{Θₜ}{body : Tm (tt ∷ Θₜ) Γ}{θ : Θₜ ⊑ Θ}
                   {B : Ty ↑ (tt ∷ Θ)}{στ : TY.Sub Δ Θ}{ψ : Γ ⊑ Γ′}
               → wkCx Ψ ⊢↑ subTyTm body ψ (TY.lift στ TY.↾ os θ) ∶ (B TY.⟪ TY.lift στ ⟫)
               → Ψ ⊢↑ subTyTm (Lam (use body)) ψ (στ TY.↾ θ) ∶ ((∀↑ B) TY.⟪ στ ⟫)
  -- ⟪⟫-∀↑ fired on the conclusion by rewrite; sole step: the subject bridge lift-↾.
  ⊢Lam-sub-use {Ψ = Ψ}{body = body}{θ = θ}{B = B}{στ = στ}{ψ = ψ} ⊢rec =
    ⊢Lam↑ {B = B TY.⟪ TY.lift στ ⟫}{X = subTyTm body ψ (TY.lift (στ TY.↾ θ))}
          (subst (λ X → wkCx Ψ ⊢↑ X ∶ (B TY.⟪ TY.lift στ ⟫))
                 (cong (subTyTm body ψ) (sym (lift-↾ στ θ))) ⊢rec)
  ⊢Lam-sub-drop : ∀ {Θ Δ Γ Γ′}{Ψ : Cx Δ Γ′}{Θₜ}{body : Tm Θₜ Γ}{θ : Θₜ ⊑ Θ}
                    {B : Ty ↑ (tt ∷ Θ)}{στ : TY.Sub Δ Θ}{ψ : Γ ⊑ Γ′}
                → wkCx Ψ ⊢↑ subTyTm body ψ (TY.lift στ TY.↾ o' θ) ∶ (B TY.⟪ TY.lift στ ⟫)
                → Ψ ⊢↑ subTyTm (Lam (drop body)) ψ (στ TY.↾ θ) ∶ ((∀↑ B) TY.⟪ στ ⟫)
  ⊢Lam-sub-drop {Ψ = Ψ}{body = body}{θ = θ}{B = B}{στ = στ}{ψ = ψ} ⊢rec =
    ⊢Lam↑ {B = B TY.⟪ TY.lift στ ⟫}{X = wkΘ-T (subTyTm body ψ (στ TY.↾ θ))}
          (subst (λ X → wkCx Ψ ⊢↑ X ∶ (B TY.⟪ TY.lift στ ⟫))
                 (trans (cong (subTyTm body ψ) (lift-↾-o' στ θ)) (subTyTm-wkΘ body ψ (στ TY.↾ θ))) ⊢rec)

  -- the proof proper: each case is now "apply the (substitution-aware) rule"
  subTyTm-pres : ∀ {Θₜ Θ Δ Γ Γ′}{Φ : Cx Θ Γ}{Ψ : Cx Δ Γ′}{θ : Θₜ ⊑ Θ}{t : Tm Θₜ Γ}{A : Ty ↑ Θ}
                   (ψ : Γ ⊑ Γ′)(στ : TY.Sub Δ Θ) → rest ψ Ψ ≡ subCx Φ στ
               → Φ ⊢[ θ ] t ∶ A → Ψ ⊢↑ (subTyTm t ψ (στ TY.↾ θ)) ∶ (A TY.⟪ στ ⟫)
  subTyTm-pres {A = A} ψ στ eq ⊢var = subst (λ Φ′ → Φ′ ⊢[ oe ] tmvar ∶ (A TY.⟪ στ ⟫)) (sym eq) ⊢var
  subTyTm-pres {Φ = Φ} ψ στ eq (⊢app {l = l}{r = r}{cθ = cθ}{θ = θ}{cγ = cγ} ⊢l ⊢r) =
    ⊢app↑ {L = subTyTm l (thinL cγ ⨾ ψ) (TY.selL cθ (στ TY.↾ θ))}
          {R = subTyTm r (thinR cγ ⨾ ψ) (TY.selR cθ (στ TY.↾ θ))}
          (subTyTm-pres (thinL cγ ⨾ ψ) στ (condL στ ψ cγ Φ eq) ⊢l)
          (subTyTm-pres (thinR cγ ⨾ ψ) στ (condR στ ψ cγ Φ eq) ⊢r)
  subTyTm-pres {Ψ = Ψ} ψ στ eq (⊢lamᵘ {a = a}{body = body}{cθ = cθ}{θ = θ}{B = B} ⊢body) =
    subst (λ s → Ψ ⊢↑ lamᵇ s (subTyTm body (os ψ) (στ TY.↾ (thinR cθ ⨾ θ))) ∶ ((a ⇑ (thinL cθ ⨾ θ)) TY.⟪ στ ⟫ ⇒↑ (B TY.⟪ στ ⟫)))
          (⟪⟫ᵇL a cθ θ στ)
          (⊢lam↑ {X = subTyTm body (os ψ) (στ TY.↾ (thinR cθ ⨾ θ))} (subTyTm-pres (os ψ) στ (cong (_,- _) eq) ⊢body))
  subTyTm-pres {Ψ = Ψ} ψ στ eq (⊢lamᵈ {a = a}{body = body}{cθ = cθ}{θ = θ}{B = B} ⊢body) =
    subst (λ s → Ψ ⊢↑ lamᵇ s (wkΓ-T (subTyTm body ψ (στ TY.↾ (thinR cθ ⨾ θ)))) ∶ ((a ⇑ (thinL cθ ⨾ θ)) TY.⟪ στ ⟫ ⇒↑ (B TY.⟪ στ ⟫)))
          (⟪⟫ᵇL a cθ θ στ)
          (⊢lam↑ {X = wkΓ-T (subTyTm body ψ (στ TY.↾ (thinR cθ ⨾ θ)))} (subTyTm-pres ψ στ eq ⊢body))
  subTyTm-pres ψ στ eq (⊢App {e = e}{a = a}{cθ = cθ}{θ = θ}{B = B} ⊢e) =
    ⊢App-sub {e = e}{a = a}{cθ = cθ}{θ = θ}{B = B}{στ = στ}{ψ = ψ} (subTyTm-pres ψ στ eq ⊢e)
  subTyTm-pres {Φ = Φ} ψ στ eq (⊢Lamᵘ {body = body}{θ = θ}{B = B} ⊢body) =
    ⊢Lam-sub-use {body = body}{θ = θ}{B = B}{στ = στ}{ψ = ψ} (subTyTm-pres {Φ = wkCx Φ} ψ (TY.lift στ) (condΛ στ ψ Φ eq) ⊢body)
  subTyTm-pres {Φ = Φ} ψ στ eq (⊢Lamᵈ {body = body}{θ = θ}{B = B} ⊢body) =
    ⊢Lam-sub-drop {body = body}{θ = θ}{B = B}{στ = στ}{ψ = ψ} (subTyTm-pres {Φ = wkCx Φ} ψ (TY.lift στ) (condΛ στ ψ Φ eq) ⊢body)

-- ════════════════════════════════════════════════════════════════════════════
-- TERM-substitution preserves typing (`subTm`-pres), via a well-typed term-sub.
-- The Λ cases need TYPE-weakening preservation ⊢-wkΘ (a degenerate subTyTm-pres).
-- ════════════════════════════════════════════════════════════════════════════
import Clean.F.TmSub as TM
open import Clean.F.Tm using (Bi; _⇑[_,_]; lamᵇ; Lamᵇ; Appᵇ; appᵇ; var₀ᵇ; wkΓ-T; wkΘ-T)

-- the type at a term-var position
lookupCx : ∀ {Θ Γ} → (tt ∷ []) ⊑ Γ → Cx Θ Γ → Ty ↑ Θ
lookupCx (os q) (Φ ,- A) = A
lookupCx (o' q) (Φ ,- A) = lookupCx q Φ

-- lookupCx commutes with rest / splitL / splitR / wkCx
opaque
  unfolding _⨾_
  lookupCx-rest : ∀ {Θ Δ Γ}(ξ : Δ ⊑ Γ)(Φ : Cx Θ Γ)(p : (tt ∷ []) ⊑ Δ)
                → lookupCx p (rest ξ Φ) ≡ lookupCx (p ⨾ ξ) Φ
  lookupCx-rest (os ξ) (Φ ,- A) (os q) = refl
  lookupCx-rest (os ξ) (Φ ,- A) (o' q) = lookupCx-rest ξ Φ q
  lookupCx-rest (o' ξ) (Φ ,- A) p     = lookupCx-rest ξ Φ p

lookupCx-splitL : ∀ {Θ Γₗ Γᵣ Γ}(cv : Cover Γₗ Γᵣ Γ)(Φ : Cx Θ Γ)(p : (tt ∷ []) ⊑ Γₗ)
                → lookupCx p (splitL cv Φ) ≡ lookupCx (p ⨾ thinL cv) Φ
lookupCx-splitL cv Φ p = trans (cong (lookupCx p) (splitL≡rest cv Φ)) (lookupCx-rest (thinL cv) Φ p)
lookupCx-splitR : ∀ {Θ Γₗ Γᵣ Γ}(cv : Cover Γₗ Γᵣ Γ)(Φ : Cx Θ Γ)(p : (tt ∷ []) ⊑ Γᵣ)
                → lookupCx p (splitR cv Φ) ≡ lookupCx (p ⨾ thinR cv) Φ
lookupCx-splitR cv Φ p = trans (cong (lookupCx p) (splitR≡rest cv Φ)) (lookupCx-rest (thinR cv) Φ p)

lookupCx-wkCx : ∀ {Θ Γ}(Φ : Cx Θ Γ)(p : (tt ∷ []) ⊑ Γ) → lookupCx p (wkCx Φ) ≡ wk↑ tt (lookupCx p Φ)
lookupCx-wkCx (Φ ,- A) (os q) = refl
lookupCx-wkCx (Φ ,- A) (o' q) = lookupCx-wkCx Φ q

-- lookupCx at the identity position of a one-var context (the ⊢var case) — keeps `oi`
-- opaque in subTm-pres (proven in a Layer-A `unfolding oi` island, then registered)
opaque
  unfolding oi
  lookupCx-oi : ∀ {Θ}(A : Ty ↑ Θ) → lookupCx oi (ε ,- A) ≡ A
  lookupCx-oi A = refl

-- the reindexing is REGISTERED, not hand-substituted: lookupCx commutes with split/wkCx/oi
{-# REWRITE lookupCx-splitL lookupCx-splitR lookupCx-wkCx lookupCx-oi #-}

-- a well-typed term-sub: pointwise, each var's replacement is typed at its context type
WtSub : ∀ {Θ Δ Γ} → Cx Θ Δ → Cx Θ Γ → TM.TmSub Θ Δ Γ → Set
WtSub {Γ = Γ} Ψ Φ σ = (p : (tt ∷ []) ⊑ Γ) → Ψ ⊢↑ σ p ∶ lookupCx p Φ

-- TERM-weakening preserves typing — DEFINITIONAL (rest drops the new var)
wkΓ-pres : ∀ {Θ Γ}{Ψ : Cx Θ Γ}{A B}{u : Bi Tm Θ Γ} → Ψ ⊢↑ u ∶ B → (Ψ ,- A) ⊢↑ wkΓ-T u ∶ B
wkΓ-pres {u = t ⇑[ θ , φ ]} ⊢u = ⊢u

-- subCx with the shift is type-weakening (each entry A⟪↑ₛ⟫ = wk↑ A)
subCx-↑ₛ : ∀ {Θ Γ}(Φ : Cx Θ Γ) → subCx Φ TY.↑ₛ ≡ wkCx Φ
subCx-↑ₛ ε        = refl
subCx-↑ₛ (Φ ,- A) = cong₂ _,-_ (subCx-↑ₛ Φ) (⟪↑ₛ⟫≡wk↑ A)

-- TYPE-weakening preserves typing — NOW PROVEN: a degenerate subTyTm-pres (the shift sub ↑ₛ),
-- with subTyTm t φ (↑ₛ↾θ) = wkΘ-T t (subTyTm-shift) and B⟪↑ₛ⟫ = wk↑ B (⟪↑ₛ⟫≡wk↑).
⊢-wkΘ : ∀ {Θ Γ}{Ψ : Cx Θ Γ}{B}{u : Bi Tm Θ Γ} → Ψ ⊢↑ u ∶ B → wkCx Ψ ⊢↑ wkΘ-T u ∶ wk↑ tt B
⊢-wkΘ {Ψ = Ψ}{B = B}{u = t ⇑[ θ , φ ]} ⊢u =
  subst₂ (λ X C → wkCx Ψ ⊢↑ X ∶ C) (subTyTm-shift t φ θ) (⟪↑ₛ⟫≡wk↑ B)
         (subTyTm-pres {Ψ = wkCx Ψ} φ TY.↑ₛ (trans (rest-wkCx φ Ψ) (sym (subCx-↑ₛ (rest φ Ψ)))) ⊢u)

-- the sub closures
selL-pres : ∀ {Θ Δ Γₗ Γᵣ Γ}{Ψ : Cx Θ Δ}{Φ : Cx Θ Γ}{σ : TM.TmSub Θ Δ Γ}(cv : Cover Γₗ Γᵣ Γ)
          → WtSub Ψ Φ σ → WtSub Ψ (splitL cv Φ) (TM.selL cv σ)
selL-pres cv wσ p = wσ (p ⨾ thinL cv)
selR-pres : ∀ {Θ Δ Γₗ Γᵣ Γ}{Ψ : Cx Θ Δ}{Φ : Cx Θ Γ}{σ : TM.TmSub Θ Δ Γ}(cv : Cover Γₗ Γᵣ Γ)
          → WtSub Ψ Φ σ → WtSub Ψ (splitR cv Φ) (TM.selR cv σ)
selR-pres cv wσ p = wσ (p ⨾ thinR cv)

-- liftΓ σ = var₀ᵇ ∙ wkΓ-Sub σ.  This is a Layer-A lemma ABOUT the cons `_∙_` (its
-- application can't be a rewrite — non-confluent with IdCons), so it unfolds `_∙_` in
-- its own island — the analogue of ⟪⟫ᵇ for ⟪⟫.  subTm-pres only APPLIES it.
opaque
  unfolding TM._∙_
  liftΓ-pres : ∀ {Θ Δ Γ}{Ψ : Cx Θ Δ}{Φ : Cx Θ Γ}{σ : TM.TmSub Θ Δ Γ}{A}
             → WtSub Ψ Φ σ → WtSub (Ψ ,- A) (Φ ,- A) (TM.liftΓ σ)
  liftΓ-pres {Ψ = Ψ}{σ = σ}{A = A} wσ (os q) = ⊢fresh {Φ = Ψ}{A = A}
  liftΓ-pres {σ = σ}{A = A} wσ (o' q) = wkΓ-pres {A = A}{u = σ q} (wσ q)

liftΘ-pres : ∀ {Θ Δ Γ}{Ψ : Cx Θ Δ}{Φ : Cx Θ Γ}{σ : TM.TmSub Θ Δ Γ}
           → WtSub Ψ Φ σ → WtSub (wkCx Ψ) (wkCx Φ) (TM.liftΘ σ)
liftΘ-pres {σ = σ} wσ p = ⊢-wkΘ {u = σ p} (wσ p)

-- ── subTm-pres : the term-substitution preserves typing ──
-- subTm is TRANSPARENT (the action recurses); the var case is definitional via the
-- registered lookupCx-oi.  This block unfolds NOTHING.
opaque
  subTm-pres : ∀ {Θ Θ′ Δ Γ}{Ψ : Cx Θ Δ}{Φ : Cx Θ Γ}{σ : TM.TmSub Θ Δ Γ}{θ : Θ′ ⊑ Θ}{t : Tm Θ′ Γ}{A}
             → WtSub Ψ Φ σ → Φ ⊢[ θ ] t ∶ A → Ψ ⊢↑ TM.subTm t θ σ ∶ A
  subTm-pres wσ ⊢var = wσ oi
  subTm-pres {Ψ = Ψ}{Φ = Φ}{σ = σ} wσ (⊢app {l = l}{r = r}{cθ = cθ}{θ = θ}{cγ = cγ}{A = A}{B = B} ⊢l ⊢r) =
    ⊢app↑ {A = A}{B = B}{L = TM.subTm l (thinL cθ ⨾ θ) (TM.selL cγ σ)}{R = TM.subTm r (thinR cθ ⨾ θ) (TM.selR cγ σ)}
          (subTm-pres {Ψ = Ψ}{Φ = splitL cγ Φ}{σ = TM.selL cγ σ} (selL-pres {Φ = Φ}{σ = σ} cγ wσ) ⊢l)
          (subTm-pres {Ψ = Ψ}{Φ = splitR cγ Φ}{σ = TM.selR cγ σ} (selR-pres {Φ = Φ}{σ = σ} cγ wσ) ⊢r)
  subTm-pres {σ = σ} wσ (⊢lamᵘ {a = a}{body = body}{cθ = cθ}{θ = θ} ⊢body) =
    ⊢lam↑ {A = a ⇑ (thinL cθ ⨾ θ)}{X = TM.subTm body (thinR cθ ⨾ θ) (TM.liftΓ σ)}
          (subTm-pres (liftΓ-pres {σ = σ} {A = a ⇑ (thinL cθ ⨾ θ)} wσ) ⊢body)
  subTm-pres {σ = σ} wσ (⊢lamᵈ {a = a}{body = body}{cθ = cθ}{θ = θ} ⊢body) =
    ⊢lam↑ {A = a ⇑ (thinL cθ ⨾ θ)}{X = wkΓ-T (TM.subTm body (thinR cθ ⨾ θ) σ)}
          (wkΓ-pres {A = a ⇑ (thinL cθ ⨾ θ)}{u = TM.subTm body (thinR cθ ⨾ θ) σ} (subTm-pres wσ ⊢body))
  subTm-pres {Φ = Φ}{σ = σ} wσ (⊢Lamᵘ {body = body}{θ = θ} ⊢body) =
    ⊢Lam↑ {X = TM.subTm body (os θ) (TM.liftΘ σ)} (subTm-pres (liftΘ-pres {Φ = Φ} {σ = σ} wσ) ⊢body)
  subTm-pres {Ψ = Ψ}{Φ = Φ}{σ = σ} wσ (⊢Lamᵈ {body = body}{θ = θ}{B = B} ⊢body) =
    ⊢Lam↑ {X = wkΘ-T (TM.subTm body θ σ)}
          (subst (λ Z → wkCx Ψ ⊢↑ Z ∶ B) (sub-wkΘSub-tm body θ σ) (subTm-pres (liftΘ-pres {Φ = Φ} {σ = σ} wσ) ⊢body))
  subTm-pres {σ = σ} wσ (⊢App {e = e}{a = a}{cθ = cθ}{θ = θ}{B = B} ⊢e) =
    ⊢App↑ {B = B}{E = TM.subTm e (thinL cθ ⨾ θ) σ} (a ⇑ (thinR cθ ⨾ θ)) (subTm-pres wσ ⊢e)
