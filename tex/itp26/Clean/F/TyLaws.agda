{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.F.TyLaws — the σ-calculus laws for System F TYPES (= Clean.Laws on Ty).
-- The 11 ACCL/σ_SP laws, registered conf-0.  Verbatim the STLC recipe.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.TyLaws where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Agda.Builtin.Equality.Rewrite
open import Clean.F.Ty public

opaque
  unfolding _∙_ ↑ₛ idS
  IdCons : ∀ {Θ} → (var₀ ∙ ↑ₛ) ≡ idS {tt ∷ Θ}
  IdCons = funext go
    where go : ∀ {Θ}(p : Pos (tt ∷ Θ)) → (var₀ ∙ ↑ₛ) p ≡ idS p
          go (os q) = cong (λ z → tvar ⇑ os z) (sym (oe-uniq q))
          go (o' q) = refl

opaque
  unfolding _⟪_⟫ sub _∙_
  VarCons : ∀ {Δ Θ}(u : Ty ↑ Δ)(σ : Sub Δ Θ) → var₀ ⟪ u ∙ σ ⟫ ≡ u
  VarCons u σ = refl

opaque
  unfolding _⨟_ _⟪_⟫ sub ↑ₛ _∙_
  ShiftCons : ∀ {Δ Θ}(u : Ty ↑ Δ)(σ : Sub Δ Θ) → ↑ₛ ⨟ (u ∙ σ) ≡ σ
  ShiftCons u σ = funext λ p → refl

opaque
  unfolding _⨟_ _∙_
  Map : ∀ {Θ Δ Ξ}(u : Ty ↑ Δ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ) → (u ∙ σ) ⨟ τ ≡ (u ⟪ τ ⟫) ∙ (σ ⨟ τ)
  Map u σ τ = funext λ { (os p) → refl ; (o' p) → refl }

opaque
  unfolding _⨟_ _⟪_⟫ sub idS
  IdL : ∀ {Θ Δ}(σ : Sub Δ Θ) → idS ⨟ σ ≡ σ
  IdL σ = funext λ p → refl

opaque
  unfolding _⨟_ _⟪_⟫ sub ↑ₛ _∙_ idS
  SCons : ∀ {Δ Θ}(σ : Sub Δ (tt ∷ Θ)) → (var₀ ⟪ σ ⟫) ∙ (↑ₛ ⨟ σ) ≡ σ
  SCons σ = funext λ { (os q) → cong (λ z → σ (os z)) (sym (oe-uniq q)) ; (o' q) → refl }

opaque
  unfolding _∙_ idS ↑ₛ wkSub lift _⨾_ oe
  lift-idS↾ : ∀ {sup Δ}(θ : sup ⊑ Δ) → lift (idS ↾ θ) ≡ idS ↾ (os θ)
  lift-idS↾ θ = funext λ { (os p) → cong (λ z → tvar ⇑ os z) (sym (oe-uniq (p ⨾ θ)))
                         ; (o' p) → refl }

opaque
  unfolding sub _⟪_⟫ idS _⇒↑_ ∀↑
  sub-idEmb : ∀ {sup Δ}(t : Ty sup)(θ : sup ⊑ Δ) → sub t (idS ↾ θ) ≡ (t ⇑ θ)
  sub-idEmb tvar θ = refl
  sub-idEmb (_⇒_ (pair l r cv)) θ =
    trans (cong₂ _⇒↑_ (sub-idEmb l (thinL cv ⨾ θ)) (sub-idEmb r (thinR cv ⨾ θ)))
          (cong (λ c → _⇒_ (pair l r (cov c)) ⇑ out c) (cop-thin-⨾ cv θ))
  sub-idEmb (∀' (use t)) θ =
    trans (cong (λ s → ∀↑ (sub t s)) (lift-idS↾ θ)) (cong ∀↑ (sub-idEmb t (os θ)))
  sub-idEmb (∀' (drop t)) θ = cong (λ Z → ∀' <$> (drop <$> Z)) (sub-idEmb t θ)

  IdSubst : ∀ {Δ}(u : Ty ↑ Δ) → u ⟪ idS ⟫ ≡ u
  IdSubst (t ⇑ θ) = sub-idEmb t θ

-- ── RENAMING commutes with sub (for Clos) ──
opaque
  unfolding _⇒↑_ ∀↑
  ⇒↑-⟨⟩ : ∀ {Δ Δ′}(A B : Ty ↑ Δ)(ψ : Δ ⊑ Δ′) → (A ⇒↑ B) ⟨ ψ ⟩ ≡ (A ⟨ ψ ⟩) ⇒↑ (B ⟨ ψ ⟩)
  ⇒↑-⟨⟩ A B ψ = trans (<$>-⟨⟩ (Ty ×ᴿ Ty) Ty _⇒_ (pairUp A B) ψ) (cong (_⇒_ <$>_) (pairUp-⟨⟩ A B ψ))
  ∀↑-⟨⟩ : ∀ {Δ Δ′}(X : Ty ↑ (tt ∷ Δ))(ψ : Δ ⊑ Δ′) → (∀↑ X) ⟨ ψ ⟩ ≡ ∀↑ (X ⟨ os ψ ⟩)
  ∀↑-⟨⟩ X ψ = trans (<$>-⟨⟩ (Bind tt Ty) Ty ∀' (bindUp X) ψ) (cong (∀' <$>_) (bindUp-⟨⟩ X ψ))

thinSub : ∀ {Δ Δ′ Θ} → Δ ⊑ Δ′ → Sub Δ Θ → Sub Δ′ Θ
thinSub ψ σ p = (σ p) ⟨ ψ ⟩

opaque
  unfolding _∙_ wkSub lift _⨾_ oe
  lift-thinSub : ∀ {Δ Δ′ Θ}(ψ : Δ ⊑ Δ′)(σ : Sub Δ Θ) → lift (thinSub ψ σ) ≡ thinSub (os ψ) (lift σ)
  lift-thinSub ψ σ = funext λ { (os p) → cong (λ z → tvar ⇑ os z) (sym (oe-uniq (oe ⨾ ψ))) ; (o' p) → refl }

opaque
  unfolding sub _⟪_⟫ wkSub _⇒↑_ ∀↑
  sub-thin : ∀ {Θ Δ Δ′}(t : Ty Θ)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Θ) → sub t (thinSub ψ σ) ≡ (sub t σ) ⟨ ψ ⟩
  sub-thin tvar ψ σ = refl
  sub-thin (_⇒_ (pair l r cv)) ψ σ =
    trans (cong₂ _⇒↑_ (sub-thin l ψ (selL cv σ)) (sub-thin r ψ (selR cv σ)))
          (sym (⇒↑-⟨⟩ (sub l (selL cv σ)) (sub r (selR cv σ)) ψ))
  sub-thin (∀' (use t)) ψ σ =
    trans (cong (λ s → ∀↑ (sub t s)) (lift-thinSub ψ σ))
          (trans (cong ∀↑ (sub-thin t (os ψ) (lift σ))) (sym (∀↑-⟨⟩ (sub t (lift σ)) ψ)))
  sub-thin (∀' (drop t)) ψ σ = cong (λ Z → ∀' <$> (drop <$> Z)) (sub-thin t ψ σ)

  sub-wk : ∀ {Θ Δ}(t : Ty Θ)(ρ : Sub Δ Θ) → sub t (wkSub ρ) ≡ wk↑ tt (sub t ρ)
  sub-wk t ρ = trans (sub-thin t (o' oi) ρ) (sym (wk↑≡⟨⟩ tt (sub t ρ)))

opaque
  unfolding _⟪_⟫ sub _⇒↑_
  ⟪⟫-⇒↑ : ∀ {Δ Ξ}(A B : Ty ↑ Δ)(τ : Sub Ξ Δ) → (A ⇒↑ B) ⟪ τ ⟫ ≡ (A ⟪ τ ⟫) ⇒↑ (B ⟪ τ ⟫)
  ⟪⟫-⇒↑ (a ⇑ α) (b ⇑ β) τ = refl

opaque
  unfolding _⟪_⟫ sub _∙_ _⨾_
  wk-skip : ∀ {Δ Ξ}(u : Ty ↑ Δ)(v : Ty ↑ Ξ)(ρ : Sub Ξ Δ) → (wk↑ tt u) ⟪ v ∙ ρ ⟫ ≡ u ⟪ ρ ⟫
  wk-skip (t ⇑ θ) v ρ = refl

opaque
  unfolding _⟪_⟫ sub wkSub
  sub-wkSub : ∀ {Δ Ξ}(u : Ty ↑ Δ)(τ : Sub Ξ Δ) → u ⟪ wkSub τ ⟫ ≡ wk↑ tt (u ⟪ τ ⟫)
  sub-wkSub (t ⇑ θ) τ = trans (sub-thin t (o' oi) (τ ↾ θ)) (sym (wk↑≡⟨⟩ tt (sub t (τ ↾ θ))))

opaque
  unfolding lift
  lift≡∙ : ∀ {Δ Θ}(σ : Sub Δ Θ) → lift σ ≡ var₀ ∙ wkSub σ
  lift≡∙ σ = refl

opaque
  unfolding _∙_ wkSub lift _⨾_
  lift-↾ : ∀ {Δ Ξ sup}(τ : Sub Ξ Δ)(ξ : sup ⊑ Δ) → lift (τ ↾ ξ) ≡ (lift τ) ↾ (os ξ)
  lift-↾ τ ξ = funext λ { (os p) → refl ; (o' p) → refl }

opaque
  unfolding _⨟_ _⟪_⟫ _∙_ wkSub lift
  lift-⨟ : ∀ {Θ Δ Ξ}(σ : Sub Δ Θ)(τ : Sub Ξ Δ) → (lift σ) ⨟ (lift τ) ≡ lift (σ ⨟ τ)
  lift-⨟ σ τ = funext λ { (os p) → VarCons var₀ (wkSub τ)
                        ; (o' p) → trans (cong (_⟪ lift τ ⟫) (sym (wk↑≡⟨⟩ tt (σ p))))
                                   (trans (wk-skip (σ p) var₀ (wkSub τ))
                                   (trans (sub-wkSub (σ p) τ) (wk↑≡⟨⟩ tt (σ p ⟪ τ ⟫)))) }

opaque
  unfolding _⟪_⟫ sub lift _∙_ wkSub _⨾_ ∀↑
  ⟪⟫-∀↑ : ∀ {Δ Ξ}(X : Ty ↑ (tt ∷ Δ))(τ : Sub Ξ Δ) → (∀↑ X) ⟪ τ ⟫ ≡ ∀↑ (X ⟪ lift τ ⟫)
  ⟪⟫-∀↑ (t ⇑ os ξ) τ = cong (λ s → ∀↑ (sub t s)) (lift-↾ τ ξ)
  ⟪⟫-∀↑ (t ⇑ o' ξ) τ = sym (cong ∀↑ (sub-wk t (τ ↾ ξ)))

opaque
  unfolding sub _⟪_⟫ _⇒↑_ ∀↑
  sub-fusion : ∀ {Θ Δ Ξ}(t : Ty Θ)(ρ : Sub Δ Θ)(τ : Sub Ξ Δ) → (sub t ρ) ⟪ τ ⟫ ≡ sub t (ρ ⨟ τ)
  sub-fusion tvar ρ τ = refl
  sub-fusion (_⇒_ (pair l r cv)) ρ τ =
    trans (⟪⟫-⇒↑ (sub l (selL cv ρ)) (sub r (selR cv ρ)) τ)
          (cong₂ _⇒↑_ (sub-fusion l (selL cv ρ) τ) (sub-fusion r (selR cv ρ) τ))
  sub-fusion (∀' (use t)) ρ τ =
    trans (⟪⟫-∀↑ (sub t (lift ρ)) τ)
          (cong ∀↑ (trans (sub-fusion t (lift ρ) (lift τ)) (cong (sub t) (lift-⨟ ρ τ))))
  sub-fusion (∀' (drop t)) ρ τ =
    trans (⟪⟫-∀↑ (wk↑ tt (sub t ρ)) τ)
          (cong ∀↑ (trans (cong (λ s → (wk↑ tt (sub t ρ)) ⟪ s ⟫) (lift≡∙ τ))
                     (trans (wk-skip (sub t ρ) var₀ (wkSub τ))
                     (trans (sub-wkSub (sub t ρ) τ) (cong (wk↑ tt) (sub-fusion t ρ τ))))))

  Clos : ∀ {Δ Δ′ Ξ}(u : Ty ↑ Δ)(σ : Sub Δ′ Δ)(τ : Sub Ξ Δ′) → (u ⟪ σ ⟫) ⟪ τ ⟫ ≡ u ⟪ σ ⨟ τ ⟫
  Clos (t ⇑ θ) σ τ = sub-fusion t (σ ↾ θ) τ

opaque
  unfolding _⨟_
  Ass : ∀ {Θ Δ Δ′ Ξ}(σ : Sub Δ Θ)(τ : Sub Δ′ Δ)(υ : Sub Ξ Δ′) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
  Ass σ τ υ = funext λ p → Clos (σ p) τ υ
  IdR : ∀ {Θ Δ}(σ : Sub Δ Θ) → σ ⨟ idS ≡ σ
  IdR σ = funext λ p → IdSubst (σ p)

opaque
  unfolding ↑ₛ idS wkSub
  ↑ₛ≡wkSubidS : ∀ {Θ} → ↑ₛ {Θ} ≡ wkSub idS
  ↑ₛ≡wkSubidS = funext λ p → wk↑≡⟨⟩ tt (idS p)
opaque
  unfolding _⨟_ _⟪_⟫ wkSub
  wkSub≡⨟↑ : ∀ {Δ Θ}(σ : Sub Δ Θ) → wkSub σ ≡ σ ⨟ ↑ₛ
  wkSub≡⨟↑ σ = funext λ p →
    sym (trans (cong (σ p ⟪_⟫) ↑ₛ≡wkSubidS)
        (trans (sub-wkSub (σ p) idS)
        (trans (cong (wk↑ tt) (IdSubst (σ p))) (wk↑≡⟨⟩ tt (σ p)))))
lift-def : ∀ {Δ Θ}(σ : Sub Δ Θ) → lift σ ≡ var₀ ∙ (σ ⨟ ↑ₛ)
lift-def σ = trans (lift≡∙ σ) (cong (var₀ ∙_) (wkSub≡⨟↑ σ))

{-# REWRITE IdCons VarCons ShiftCons Map IdL IdR SCons IdSubst Clos Ass lift-def #-}

-- the type-former DISTRIBUTIONS now compute (formers opaque ⇒ linear LHS)
{-# REWRITE ⟪⟫-⇒↑ ⟪⟫-∀↑ #-}
-- NB: lift-↾ CANNOT be registered: `Sub` is functional, so `τ↾ξ` η-expands to
-- `λz→(τ↾ξ)z` and the ↾-application law fires inside ⇒ `lift(τ↾ξ)` reduces (illegal LHS).
-- The binder-commutation laws stay applied `subst`s until Sub is first-order (a vector).
