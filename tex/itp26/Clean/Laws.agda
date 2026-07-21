{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.Laws — §3  THE σ-CALCULUS REWRITE SYSTEM, over THINNING-POSITIONS.
--
-- Same 11 ACCL/σ_SP laws as before, but now positions are thinnings, so the
-- cover/spine coherences are FREE (selL-cop via Fac-L⨾; `⟪⟫-app↑ = refl`) and there
-- is no `act`.  The "position tax" is `oe-uniq` (head-slot lookups), in Clean.Pos.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.Laws where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Agda.Builtin.Equality.Rewrite
open import Clean.Sub public

-- IdCons (η₀):  var₀ ∙ ↑ ≡ id
opaque
  unfolding _∙_ ↑ₛ idS
  IdCons : ∀ {Γ} → (var₀ ∙ ↑ₛ) ≡ idS {tt ∷ Γ}
  IdCons = funext go
    where go : ∀ {Γ}(p : Pos (tt ∷ Γ)) → (var₀ ∙ ↑ₛ) p ≡ idS p
          go (os q) = cong (λ z → var ⇑ os z) (sym (oe-uniq q))
          go (o' q) = refl

-- VarCons:  var₀ ⟪ u ∙ σ ⟫ ≡ u
opaque
  unfolding _⟪_⟫ sub _∙_
  VarCons : ∀ {Δ Γ}(u : Tm ↑ Δ)(σ : Sub Δ Γ) → var₀ ⟪ u ∙ σ ⟫ ≡ u
  VarCons u σ = refl

-- ShiftCons:  ↑ ⨟ (u ∙ σ) ≡ σ
opaque
  unfolding _⨟_ _⟪_⟫ sub ↑ₛ _∙_
  ShiftCons : ∀ {Δ Γ}(u : Tm ↑ Δ)(σ : Sub Δ Γ) → ↑ₛ ⨟ (u ∙ σ) ≡ σ
  ShiftCons u σ = funext λ p → refl

-- Map:  (u ∙ σ) ⨟ τ ≡ (u⟪τ⟫) ∙ (σ ⨟ τ)
opaque
  unfolding _⨟_ _∙_
  Map : ∀ {Γ Δ Θ}(u : Tm ↑ Δ)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → (u ∙ σ) ⨟ τ ≡ (u ⟪ τ ⟫) ∙ (σ ⨟ τ)
  Map u σ τ = funext λ { (os p) → refl ; (o' p) → refl }

-- IdL:  id ⨟ σ ≡ σ
opaque
  unfolding _⨟_ _⟪_⟫ sub idS
  IdL : ∀ {Γ Δ}(σ : Sub Δ Γ) → idS ⨟ σ ≡ σ
  IdL σ = funext λ p → refl

-- SCons (η):  (var₀⟪σ⟫) ∙ (↑ ⨟ σ) ≡ σ
opaque
  unfolding _⨟_ _⟪_⟫ sub ↑ₛ _∙_ idS
  SCons : ∀ {Δ Γ}(σ : Sub Δ (tt ∷ Γ)) → (var₀ ⟪ σ ⟫) ∙ (↑ₛ ⨟ σ) ≡ σ
  SCons σ = funext λ { (os q) → cong (λ z → σ (os z)) (sym (oe-uniq q)) ; (o' q) → refl }

-- lift commutes with restricting the identity
opaque
  unfolding _∙_ idS ↑ₛ wkSub lift _⨾_ oe
  lift-idS↾ : ∀ {sup Δ}(θ : sup ⊑ Δ) → lift (idS ↾ θ) ≡ idS ↾ (os θ)
  lift-idS↾ θ = funext λ { (os p) → cong (λ z → var ⇑ os z) (sym (oe-uniq (p ⨾ θ)))
                         ; (o' p) → refl }

-- IdSubst (term induction)
opaque
  unfolding sub _⟪_⟫ idS
  sub-idEmb : ∀ {sup Δ}(t : Tm sup)(θ : sup ⊑ Δ) → sub t (idS ↾ θ) ≡ (t ⇑ θ)
  sub-idEmb var θ = refl
  sub-idEmb (app (pair l r cv)) θ =
    trans (cong₂ app↑ (sub-idEmb l (thinL cv ⨾ θ)) (sub-idEmb r (thinR cv ⨾ θ)))
          (cong (λ c → app (pair l r (cov c)) ⇑ out c) (cop-thin-⨾ cv θ))
  sub-idEmb (lam (use t)) θ =
    trans (cong (λ s → lam↑ (sub t s)) (lift-idS↾ θ)) (cong lam↑ (sub-idEmb t (os θ)))
  sub-idEmb (lam (drop t)) θ = cong (λ Z → lam <$> (drop <$> Z)) (sub-idEmb t θ)

  IdSubst : ∀ {Δ}(u : Tm ↑ Δ) → u ⟪ idS ⟫ ≡ u
  IdSubst (t ⇑ θ) = sub-idEmb t θ

-- ── RENAMING commutes with sub (needed for Clos) ──
app↑-⟨⟩ : ∀ {Δ Δ′}(A B : Tm ↑ Δ)(ψ : Δ ⊑ Δ′) → (app↑ A B) ⟨ ψ ⟩ ≡ app↑ (A ⟨ ψ ⟩) (B ⟨ ψ ⟩)
app↑-⟨⟩ A B ψ = trans (<$>-⟨⟩ (Tm ×ᴿ Tm) Tm app (pairUp A B) ψ) (cong (app <$>_) (pairUp-⟨⟩ A B ψ))
lam↑-⟨⟩ : ∀ {Δ Δ′}(X : Tm ↑ (tt ∷ Δ))(ψ : Δ ⊑ Δ′) → (lam↑ X) ⟨ ψ ⟩ ≡ lam↑ (X ⟨ os ψ ⟩)
lam↑-⟨⟩ X ψ = trans (<$>-⟨⟩ (Bind tt Tm) Tm lam (bindUp X) ψ) (cong (lam <$>_) (bindUp-⟨⟩ X ψ))

thinSub : ∀ {Δ Δ′ Γ} → Δ ⊑ Δ′ → Sub Δ Γ → Sub Δ′ Γ
thinSub ψ σ p = (σ p) ⟨ ψ ⟩

opaque
  unfolding _∙_ wkSub lift _⨾_ oe
  lift-thinSub : ∀ {Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ) → lift (thinSub ψ σ) ≡ thinSub (os ψ) (lift σ)
  lift-thinSub ψ σ = funext λ { (os p) → cong (λ z → var ⇑ os z) (sym (oe-uniq (oe ⨾ ψ))) ; (o' p) → refl }

opaque
  unfolding sub _⟪_⟫ wkSub
  sub-thin : ∀ {Γ Δ Δ′}(t : Tm Γ)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ) → sub t (thinSub ψ σ) ≡ (sub t σ) ⟨ ψ ⟩
  sub-thin var ψ σ = refl
  sub-thin (app (pair l r cv)) ψ σ =
    trans (cong₂ app↑ (sub-thin l ψ (selL cv σ)) (sub-thin r ψ (selR cv σ)))
          (sym (app↑-⟨⟩ (sub l (selL cv σ)) (sub r (selR cv σ)) ψ))
  sub-thin (lam (use t)) ψ σ =
    trans (cong (λ s → lam↑ (sub t s)) (lift-thinSub ψ σ))
          (trans (cong lam↑ (sub-thin t (os ψ) (lift σ))) (sym (lam↑-⟨⟩ (sub t (lift σ)) ψ)))
  sub-thin (lam (drop t)) ψ σ = cong (λ Z → lam <$> (drop <$> Z)) (sub-thin t ψ σ)

  sub-wk : ∀ {Γ Δ}(t : Tm Γ)(ρ : Sub Δ Γ) → sub t (wkSub ρ) ≡ wk↑ tt (sub t ρ)
  sub-wk t ρ = trans (sub-thin t (o' oi) ρ) (sym (wk↑≡⟨⟩ tt (sub t ρ)))

-- ⟪⟫ distributes over app↑ — REFL (selL-cop free via Fac-L⨾)
opaque
  unfolding _⟪_⟫ sub
  ⟪⟫-app↑ : ∀ {Δ Θ}(A B : Tm ↑ Δ)(τ : Sub Θ Δ) → (app↑ A B) ⟪ τ ⟫ ≡ app↑ (A ⟪ τ ⟫) (B ⟪ τ ⟫)
  ⟪⟫-app↑ (a ⇑ α) (b ⇑ β) τ = refl

-- weakening SKIPS the cons head:  (wk↑ u) ⟪ v ∙ ρ ⟫ ≡ u ⟪ ρ ⟫
opaque
  unfolding _⟪_⟫ sub _∙_ _⨾_
  wk-skip : ∀ {Δ Θ}(u : Tm ↑ Δ)(v : Tm ↑ Θ)(ρ : Sub Θ Δ) → (wk↑ tt u) ⟪ v ∙ ρ ⟫ ≡ u ⟪ ρ ⟫
  wk-skip (t ⇑ θ) v ρ = refl

opaque
  unfolding _⟪_⟫ sub wkSub
  sub-wkSub : ∀ {Δ Θ}(u : Tm ↑ Δ)(τ : Sub Θ Δ) → u ⟪ wkSub τ ⟫ ≡ wk↑ tt (u ⟪ τ ⟫)
  sub-wkSub (t ⇑ θ) τ = trans (sub-thin t (o' oi) (τ ↾ θ)) (sym (wk↑≡⟨⟩ tt (sub t (τ ↾ θ))))

opaque
  unfolding lift
  lift≡∙ : ∀ {Δ Γ}(σ : Sub Δ Γ) → lift σ ≡ var₀ ∙ wkSub σ
  lift≡∙ σ = refl

opaque
  unfolding _∙_ wkSub lift _⨾_
  lift-↾ : ∀ {Δ Θ sup}(τ : Sub Θ Δ)(ξ : sup ⊑ Δ) → lift (τ ↾ ξ) ≡ (lift τ) ↾ (os ξ)
  lift-↾ τ ξ = funext λ { (os p) → refl ; (o' p) → refl }

opaque
  unfolding _⨟_ _⟪_⟫ _∙_ wkSub lift
  lift-⨟ : ∀ {Γ Δ Θ}(σ : Sub Δ Γ)(τ : Sub Θ Δ) → (lift σ) ⨟ (lift τ) ≡ lift (σ ⨟ τ)
  lift-⨟ σ τ = funext λ { (os p) → VarCons var₀ (wkSub τ)
                        ; (o' p) → trans (cong (_⟪ lift τ ⟫) (sym (wk↑≡⟨⟩ tt (σ p))))
                                   (trans (wk-skip (σ p) var₀ (wkSub τ))
                                   (trans (sub-wkSub (σ p) τ) (wk↑≡⟨⟩ tt (σ p ⟪ τ ⟫)))) }

opaque
  unfolding _⟪_⟫ sub lift _∙_ wkSub _⨾_
  ⟪⟫-lam↑ : ∀ {Δ Θ}(X : Tm ↑ (tt ∷ Δ))(τ : Sub Θ Δ) → (lam↑ X) ⟪ τ ⟫ ≡ lam↑ (X ⟪ lift τ ⟫)
  ⟪⟫-lam↑ (t ⇑ os ξ) τ = cong (λ s → lam↑ (sub t s)) (lift-↾ τ ξ)
  ⟪⟫-lam↑ (t ⇑ o' ξ) τ = sym (cong lam↑ (sub-wk t (τ ↾ ξ)))

-- ══ Clos: substitution fusion (term induction) ══
opaque
  unfolding sub _⟪_⟫
  sub-fusion : ∀ {Γ Δ Θ}(t : Tm Γ)(ρ : Sub Δ Γ)(τ : Sub Θ Δ) → (sub t ρ) ⟪ τ ⟫ ≡ sub t (ρ ⨟ τ)
  sub-fusion var ρ τ = refl
  sub-fusion (app (pair l r cv)) ρ τ =
    trans (⟪⟫-app↑ (sub l (selL cv ρ)) (sub r (selR cv ρ)) τ)
          (cong₂ app↑ (sub-fusion l (selL cv ρ) τ) (sub-fusion r (selR cv ρ) τ))
  sub-fusion (lam (use t)) ρ τ =
    trans (⟪⟫-lam↑ (sub t (lift ρ)) τ)
          (cong lam↑ (trans (sub-fusion t (lift ρ) (lift τ)) (cong (sub t) (lift-⨟ ρ τ))))
  sub-fusion (lam (drop t)) ρ τ =
    trans (⟪⟫-lam↑ (wk↑ tt (sub t ρ)) τ)
          (cong lam↑ (trans (cong (λ s → (wk↑ tt (sub t ρ)) ⟪ s ⟫) (lift≡∙ τ))
                     (trans (wk-skip (sub t ρ) var₀ (wkSub τ))
                     (trans (sub-wkSub (sub t ρ) τ) (cong (wk↑ tt) (sub-fusion t ρ τ))))))

  Clos : ∀ {Δ Δ′ Θ}(u : Tm ↑ Δ)(σ : Sub Δ′ Δ)(τ : Sub Θ Δ′) → (u ⟪ σ ⟫) ⟪ τ ⟫ ≡ u ⟪ σ ⨟ τ ⟫
  Clos (t ⇑ θ) σ τ = sub-fusion t (σ ↾ θ) τ

opaque
  unfolding _⨟_
  Ass : ∀ {Γ Δ Δ′ Θ}(σ : Sub Δ Γ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
  Ass σ τ υ = funext λ p → Clos (σ p) τ υ
  IdR : ∀ {Γ Δ}(σ : Sub Δ Γ) → σ ⨟ idS ≡ σ
  IdR σ = funext λ p → IdSubst (σ p)

-- ── lift-def: RE-EXPRESS the hidden `lift` in PRIMITIVES ──
opaque
  unfolding ↑ₛ idS wkSub
  ↑ₛ≡wkSubidS : ∀ {Γ} → ↑ₛ {Γ} ≡ wkSub idS
  ↑ₛ≡wkSubidS = funext λ p → wk↑≡⟨⟩ tt (idS p)
opaque
  unfolding _⨟_ _⟪_⟫ wkSub
  wkSub≡⨟↑ : ∀ {Δ Γ}(σ : Sub Δ Γ) → wkSub σ ≡ σ ⨟ ↑ₛ
  wkSub≡⨟↑ σ = funext λ p →
    sym (trans (cong (σ p ⟪_⟫) ↑ₛ≡wkSubidS)
        (trans (sub-wkSub (σ p) idS)
        (trans (cong (wk↑ tt) (IdSubst (σ p))) (wk↑≡⟨⟩ tt (σ p)))))
lift-def : ∀ {Δ Γ}(σ : Sub Δ Γ) → lift σ ≡ var₀ ∙ (σ ⨟ ↑ₛ)
lift-def σ = trans (lift≡∙ σ) (cong (var₀ ∙_) (wkSub≡⨟↑ σ))

-- ════════════════════════════════════════════════════════════════════════════
{-# REWRITE IdCons VarCons ShiftCons Map IdL IdR SCons IdSubst Clos Ass lift-def #-}
