{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.SystemF2VTy — the single-scope TYPE σ-engine for the vector System F.
-- A verbatim port of Sf.STLC's σ-laws, specialised to the type family `Ty`
-- (sort ⊤, constructors tvar / _`→_ / `∀).  Registers the full σ_SP rewrite set
-- for the TYPE substitution `subT`, so type-substitution is DEFINITIONAL.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.SystemF2VTy where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Agda.Builtin.Equality.Rewrite

open import Sf.Scaffold ⊤ public

data Ty : Scope → Set where
  tvar : Ty (tt ∷ [])
  _`→_ : (Ty ×ᴿ Ty) Θ → Ty Θ
  `∀   : Bind tt Ty Θ → Ty Θ

_⇒↑_ : ∀ {Θ} → Ty ↑ Θ → Ty ↑ Θ → Ty ↑ Θ
A ⇒↑ B = _`→_ <$> pairUp A B
infixr 5 _⇒↑_
∀↑ : ∀ {Θ} → Ty ↑ (tt ∷ Θ) → Ty ↑ Θ
∀↑ X = `∀ <$> bindUp X

open import Sf.Sub ⊤ (λ Θ _ → Ty Θ) tvar public

opaque
  subT  : ∀ {Θ Ξ} → Ty Θ → Sub Ξ Θ → Ty ↑ Ξ
  subT tvar                ([] ,- u) = u
  subT (_`→_ (pair a b cv)) σ = _`→_ <$> pairUp (subT a (selL cv σ)) (subT b (selR cv σ))
  subT (`∀ (use t))         σ = `∀   <$> bindUp (subT t (wkSub σ ,- var₀))
  subT (`∀ (drop t))        σ = `∀   <$> (drop <$> subT t σ)

opaque
  unfolding subT
  _⟪_⟫T : ∀ {Θ Ξ} → Ty ↑ Θ → Sub Ξ Θ → Ty ↑ Ξ
  (t ⇑ θ) ⟪ τ ⟫T = subT t (τ ↾ θ)
infixl 8 _⟪_⟫T

_⨟_ : ∀ {Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
[]       ⨟ τ = []
(σ ,- u) ⨟ τ = (σ ⨟ τ) ,- (u ⟪ τ ⟫T)
infixl 6 _⨟_

-- ── σ-laws (verbatim Sf.STLC, retyped for Ty / `→ / ∀) ──
selL-⨟ : ∀ {Γₗ Γᵣ Γ Δ Θ}(cv : Cover Γₗ Γᵣ Γ)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → selL cv (σ ⨟ τ) ≡ (selL cv σ) ⨟ τ
selL-⨟ czz     []       τ = refl
selL-⨟ (css c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫T)) (selL-⨟ c σ τ)
selL-⨟ (cs' c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫T)) (selL-⨟ c σ τ)
selL-⨟ (c's c) (σ ,- u) τ = selL-⨟ c σ τ
selR-⨟ : ∀ {Γₗ Γᵣ Γ Δ Θ}(cv : Cover Γₗ Γᵣ Γ)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → selR cv (σ ⨟ τ) ≡ (selR cv σ) ⨟ τ
selR-⨟ czz     []       τ = refl
selR-⨟ (css c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫T)) (selR-⨟ c σ τ)
selR-⨟ (cs' c) (σ ,- u) τ = selR-⨟ c σ τ
selR-⨟ (c's c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫T)) (selR-⨟ c σ τ)

opaque
  unfolding cop
  selL-cop : ∀ {sₗ sᵣ Δ Θ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(τ : Sub Θ Δ) → selL (cov (cop θ φ)) (τ ↾ out (cop θ φ)) ≡ τ ↾ θ
  selL-cop oz     oz     []       = refl
  selL-cop (os θ) (os φ) (τ ,- u) = cong (_,- u) (selL-cop θ φ τ)
  selL-cop (os θ) (o' φ) (τ ,- u) = cong (_,- u) (selL-cop θ φ τ)
  selL-cop (o' θ) (os φ) (τ ,- u) = selL-cop θ φ τ
  selL-cop (o' θ) (o' φ) (τ ,- u) = selL-cop θ φ τ
  selR-cop : ∀ {sₗ sᵣ Δ Θ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(τ : Sub Θ Δ) → selR (cov (cop θ φ)) (τ ↾ out (cop θ φ)) ≡ τ ↾ φ
  selR-cop oz     oz     []       = refl
  selR-cop (os θ) (os φ) (τ ,- u) = cong (_,- u) (selR-cop θ φ τ)
  selR-cop (os θ) (o' φ) (τ ,- u) = selR-cop θ φ τ
  selR-cop (o' θ) (os φ) (τ ,- u) = cong (_,- u) (selR-cop θ φ τ)
  selR-cop (o' θ) (o' φ) (τ ,- u) = selR-cop θ φ τ

opaque
  unfolding _⟪_⟫T subT
  ⟪⟫-→↑ : ∀ {Δ Θ}(A B : Ty ↑ Δ)(υ : Sub Θ Δ) → (A ⇒↑ B) ⟪ υ ⟫T ≡ (A ⟪ υ ⟫T) ⇒↑ (B ⟪ υ ⟫T)
  ⟪⟫-→↑ (l ⇑ θ) (r ⇑ φ) υ = cong₂ _⇒↑_ (cong (subT l) (selL-cop θ φ υ)) (cong (subT r) (selR-cop θ φ υ))

→↑-⟨⟩ : ∀ {Δ Δ′}(A B : Ty ↑ Δ)(ψ : Δ ⊑ Δ′) → (A ⇒↑ B) ⟨ ψ ⟩ ≡ (A ⟨ ψ ⟩) ⇒↑ (B ⟨ ψ ⟩)
→↑-⟨⟩ A B ψ = trans (<$>-⟨⟩ (Ty ×ᴿ Ty) Ty _`→_ (pairUp A B) ψ) (cong (_`→_ <$>_) (pairUp-⟨⟩ A B ψ))
∀↑-⟨⟩ : ∀ {Δ Δ′}(X : Ty ↑ (tt ∷ Δ))(ψ : Δ ⊑ Δ′) → (∀↑ X) ⟨ ψ ⟩ ≡ ∀↑ (X ⟨ os ψ ⟩)
∀↑-⟨⟩ X ψ = trans (<$>-⟨⟩ (Bind tt Ty) Ty `∀ (bindUp X) ψ) (cong (`∀ <$>_) (bindUp-⟨⟩ X ψ))

opaque
  unfolding oe _⨾_
  liftThin : ∀ {Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ) → (wkSub (thinSub ψ σ) ,- var₀) ≡ thinSub (os ψ) (wkSub σ ,- var₀)
  liftThin ψ σ = cong₂ _,-_ (wkSub-thinSub ψ σ) (cong (tvar ⇑_) (cong os (sym (oe⨾ ψ))))
    where oe⨾ : ∀ {Δ Δ′}(ψ : Δ ⊑ Δ′) → oe ⨾ ψ ≡ oe
          oe⨾ oz     = refl
          oe⨾ (os ψ) = cong o' (oe⨾ ψ)
          oe⨾ (o' ψ) = cong o' (oe⨾ ψ)

opaque
  unfolding subT
  sub-thin : ∀ {Γ Δ Δ′}(t : Ty Γ)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ) → subT t (thinSub ψ σ) ≡ (subT t σ) ⟨ ψ ⟩
  sub-thin tvar ψ ([] ,- (t ⇑ η)) = refl
  sub-thin (_`→_ (pair l r cv)) ψ σ =
    trans (cong₂ _⇒↑_ (cong (subT l) (selL-thin cv ψ σ)) (cong (subT r) (selR-thin cv ψ σ)))
    (trans (cong₂ _⇒↑_ (sub-thin l ψ (selL cv σ)) (sub-thin r ψ (selR cv σ)))
           (sym (→↑-⟨⟩ (subT l (selL cv σ)) (subT r (selR cv σ)) ψ)))
  sub-thin (`∀ (use t)) ψ σ =
    trans (cong (λ e → ∀↑ (subT t e)) (liftThin ψ σ))
    (trans (cong ∀↑ (sub-thin t (os ψ) (wkSub σ ,- var₀)))
           (sym (∀↑-⟨⟩ (subT t (wkSub σ ,- var₀)) ψ)))
  sub-thin (`∀ (drop t)) ψ σ = cong (λ Z → `∀ (drop (thing Z)) ⇑ thn Z) (sub-thin t ψ σ)

sub-wk : ∀ {s Γ Δ}(t : Ty Γ)(ρ : Sub Δ Γ) → subT t (wkSub {s} ρ) ≡ wk↑ s (subT t ρ)
sub-wk {s} t ρ = trans (cong (subT t) (wkSub≡thin ρ)) (trans (sub-thin t (o' oi) ρ) (sym (wk↑≡⟨⟩ s (subT t ρ))))

opaque
  unfolding _⟪_⟫T subT
  ⟪⟫-∀↑ : ∀ {Δ Θ}(X : Ty ↑ (tt ∷ Δ))(υ : Sub Θ Δ) → (∀↑ X) ⟪ υ ⟫T ≡ ∀↑ (X ⟪ wkSub υ ,- var₀ ⟫T)
  ⟪⟫-∀↑ (t ⇑ os ξ) υ = cong (λ e → ∀↑ (subT t (e ,- var₀))) (sym (wk-↾ υ ξ))
  ⟪⟫-∀↑ (t ⇑ o' ξ) υ = sym (trans (cong (λ e → ∀↑ (subT t e)) (wk-↾ υ ξ)) (cong ∀↑ (sub-wk t (υ ↾ ξ))))

opaque
  unfolding _⟪_⟫T subT wkSub
  wkSub-⨟ : ∀ {s Γ Δ Θ}(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (wkSub {s} σ) ⨟ (wkSub υ ,- var₀) ≡ wkSub (σ ⨟ υ)
  wkSub-⨟ []             υ = refl
  wkSub-⨟ (σ ,- (t ⇑ ξ)) υ = cong₂ _,-_ (wkSub-⨟ σ υ) (trans (cong (subT t) (wk-↾ υ ξ)) (sub-wk t (υ ↾ ξ)))
opaque
  unfolding _⟪_⟫T subT
  lift-⨟ : ∀ {Γ Δ Θ}(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (wkSub σ ,- var₀) ⨟ (wkSub υ ,- var₀) ≡ wkSub (σ ⨟ υ) ,- var₀
  lift-⨟ σ υ = cong₂ _,-_ (wkSub-⨟ σ υ) (cong (λ e → subT tvar (e ,- var₀)) (↾-oe (wkSub υ)))

↾-⨟ : ∀ {Δ Δ′ Θ sup}(τ : Sub Δ′ Δ)(θ : sup ⊑ Δ)(υ : Sub Θ Δ′) → (τ ↾ θ) ⨟ υ ≡ (τ ⨟ υ) ↾ θ
↾-⨟ []       oz     υ = refl
↾-⨟ (τ ,- u) (os θ) υ = cong (_,- (u ⟪ υ ⟫T)) (↾-⨟ τ θ υ)
↾-⨟ (τ ,- u) (o' θ) υ = ↾-⨟ τ θ υ

opaque
  unfolding _⟪_⟫T subT
  sub-fusion : ∀ {Γ Δ Θ}(t : Ty Γ)(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (subT t σ) ⟪ υ ⟫T ≡ subT t (σ ⨟ υ)
  sub-fusion tvar ([] ,- u) υ = refl
  sub-fusion (_`→_ (pair l r cv)) σ υ =
    trans (⟪⟫-→↑ (subT l (selL cv σ)) (subT r (selR cv σ)) υ)
    (trans (cong₂ _⇒↑_ (sub-fusion l (selL cv σ) υ) (sub-fusion r (selR cv σ) υ))
           (cong₂ _⇒↑_ (cong (subT l) (sym (selL-⨟ cv σ υ))) (cong (subT r) (sym (selR-⨟ cv σ υ)))))
  sub-fusion (`∀ (use t)) σ υ =
    trans (⟪⟫-∀↑ (subT t (wkSub σ ,- var₀)) υ)
          (cong ∀↑ (trans (sub-fusion t (wkSub σ ,- var₀) (wkSub υ ,- var₀)) (cong (subT t) (lift-⨟ σ υ))))
  sub-fusion (`∀ (drop t)) σ υ = cong (λ Z → `∀ (drop (thing Z)) ⇑ thn Z) (sub-fusion t σ υ)

opaque
  unfolding _⟪_⟫T
  ⟪⟫-fusion : ∀ {Δ Δ′ Θ}(u : Ty ↑ Δ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (u ⟪ τ ⟫T) ⟪ υ ⟫T ≡ u ⟪ τ ⨟ υ ⟫T
  ⟪⟫-fusion (t ⇑ θ) τ υ = trans (sub-fusion t (τ ↾ θ) υ) (cong (subT t) (↾-⨟ τ θ υ))

Ass : ∀ {Γ Δ Δ′ Θ}(σ : Sub Δ Γ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
Ass []       τ υ = refl
Ass (σ ,- u) τ υ = cong₂ _,-_ (Ass σ τ υ) (⟪⟫-fusion u τ υ)
{-# REWRITE ⟪⟫-fusion Ass #-}

opaque
  unfolding _⟪_⟫T subT wkSub
  wk-⨟-cons : ∀ {s Γ Δ Θ}(σ : Sub Δ Γ)(τ : Sub Θ Δ)(u : Ty ↑ Θ) → wkSub {s} σ ⨟ (τ ,- u) ≡ σ ⨟ τ
  wk-⨟-cons []             τ u = refl
  wk-⨟-cons (σ ,- (t ⇑ ξ)) τ u = cong (_,- subT t (τ ↾ ξ)) (wk-⨟-cons σ τ u)

opaque
  unfolding _⟪_⟫T idS subT wkSub
  IdL : ∀ {Γ Δ}(σ : Sub Δ Γ) → idS ⨟ σ ≡ σ
  IdL []             = refl
  IdL (σ ,- (t ⇑ ξ)) =
    cong₂ _,-_ (trans (wk-⨟-cons idS σ (t ⇑ ξ)) (IdL σ)) (cong (subT tvar) (cong (_,- (t ⇑ ξ)) (↾-oe σ)))
{-# REWRITE IdL #-}

opaque
  unfolding subT
  VarCons-z : ∀ {Δ}(u : Ty ↑ Δ) → subT tvar ([] ,- u) ≡ u
  VarCons-z u = refl
{-# REWRITE VarCons-z #-}

↾-oe-Ty : ∀ {Θ Δ}(τ : Sub Θ Δ) → τ ↾ oe ≡ []
↾-oe-Ty = ↾-oe
{-# REWRITE ↾-oe-Ty #-}

opaque
  unfolding idS subT wkSub oe oi
  sub-idS : ∀ {sup}(t : Ty sup) → subT t idS ≡ (t ⇑ oi)
  sub-idS tvar = refl
  sub-idS (_`→_ (pair l r cv)) =
    trans (cong₂ _⇒↑_
            (trans (cong (subT l) (trans (selL-idS cv) (idEmb-thinSub (thinL cv))))
                   (trans (sub-thin l (thinL cv) idS) (cong (_⟨ thinL cv ⟩) (sub-idS l))))
            (trans (cong (subT r) (trans (selR-idS cv) (idEmb-thinSub (thinR cv))))
                   (trans (sub-thin r (thinR cv) idS) (cong (_⟨ thinR cv ⟩) (sub-idS r)))))
          (cong (λ c → _`→_ (pair l r (cov c)) ⇑ out c) (cop-thin cv))
  sub-idS (`∀ (use t))  = cong ∀↑ (sub-idS t)
  sub-idS (`∀ (drop t)) = cong (λ Z → `∀ (drop (thing Z)) ⇑ thn Z) (sub-idS t)

sub-idEmb : ∀ {sup Δ}(t : Ty sup)(θ : sup ⊑ Δ) → subT t (idEmb θ) ≡ (t ⇑ θ)
sub-idEmb t θ = trans (cong (subT t) (idEmb-thinSub θ)) (trans (sub-thin t θ idS) (cong (_⟨ θ ⟩) (sub-idS t)))

opaque
  unfolding _⟪_⟫T subT
  ⟪⟫-id : ∀ {Δ}(u : Ty ↑ Δ) → u ⟪ idS ⟫T ≡ u
  ⟪⟫-id (t ⇑ θ) = trans (cong (subT t) (idS↾-idEmb θ)) (sub-idEmb t θ)

IdR : ∀ {Γ Δ}(σ : Sub Δ Γ) → σ ⨟ idS ≡ σ
IdR []       = refl
IdR (σ ,- u) = cong₂ _,-_ (IdR σ) (⟪⟫-id u)
{-# REWRITE ⟪⟫-id IdR sub-idS #-}
