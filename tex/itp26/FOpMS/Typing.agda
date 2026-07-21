{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- EXTRINSIC TYPING + TYPE-SUBSTITUTION-PRESERVES-TYPING for the GENUINELY
-- MULTI-SORTED co-de-Bruijn System F of FOpMS.Tm.  ONE scope Θ holds BOTH expr
-- and type variables; ONE vector `Sub` acts on both; the substitution lemma is
-- ONE `sub-pres` threading a single `WtSub` (FOpMS's `sub'` THREADS the thinning
-- and restricts σ ONCE at the leaf, so — unlike Sf's selL/selR engine — the
-- substitution is NEVER peeled; the well-typed-sub is threaded UNCHANGED).
--
-- Design (from Sf.SystemFTyping): the judgement `Φ ⊢[ θ ] t ∶ A` is on the RAW
-- constructors with a CARRIED thinning θ : sup ⊑ Δ, so it is INVERTIBLE by
-- constructor pattern-match.  The smart typed constructors ⊢app↑/⊢lam↑/… are
-- DERIVED and DEFINITIONAL: Fac-L/Fac-R (registered rewrites) collapse
-- `thinL (cov (cop θ φ)) ⨾ out (cop θ φ) ≡ θ`.
-- ════════════════════════════════════════════════════════════════════════════
module FOpMS.Typing where
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Agda.Builtin.Equality.Rewrite
open import FOpMS.ThinRw
open import FOpMS.Tm

private variable
  s s′ t : Sort
  Γ Δ Ξ Ω Θ sup : Scope

-- one-fresh-variable weakening of a ⇑-carrier (the classifier-weakening of lookup)
wk↑ : ∀ {T : Scope → Set} (s : Sort) {Δ} → T ↑ Δ → T ↑ (s ∷ Δ)
wk↑ s X = X ⟨ o' oi ⟩↑
-- the closed kind ⋆ as a ⇑-carrier over any scope
⋆↑ : Tm kind ↑ Δ
⋆↑ = ⋆ ⇑ oe

-- ════ CONTEXTS: a FULL telescope over the whole scope.  An expr-var carries its
-- type `Tm type ↑ prefix`; a type-var carries nothing (System F: sole kind ⋆). ════
data Cx : Scope → Set where
  ε    : Cx []
  _,*  : Cx Γ → Cx (type ∷ Γ)
  _,-_ : Cx Γ → (Tm type ↑ Γ) → Cx (expr ∷ Γ)
infixl 5 _,-_
infixl 6 _,*

-- lookup an expr-var, returning its stored type WEAKENED up to the full scope
lookup : Cx Δ → Pos Δ expr → Tm type ↑ Δ
lookup (Φ ,- A) (os θ) = wk↑ expr A
lookup (Φ ,- A) (o' θ) = wk↑ expr (lookup Φ θ)
lookup (Φ ,*)   (o' θ) = wk↑ type (lookup Φ θ)

-- ════ type-former injectivity (peel the cover via Fac-L/Fac-R) ════
domOf codOf : Tm type ↑ Δ → Tm type ↑ Δ
domOf (_⇒_ (pair l r cv) ⇑ θ) = l ⇑ (thinL cv ⨾ θ)
domOf X = X
codOf (_⇒_ (pair l r cv) ⇑ θ) = r ⇑ (thinR cv ⨾ θ)
codOf X = X
domOf-⇒↑ : (A B : Tm type ↑ Δ) → domOf (A ⇒↑ B) ≡ A
domOf-⇒↑ A B = refl
codOf-⇒↑ : (A B : Tm type ↑ Δ) → codOf (A ⇒↑ B) ≡ B
codOf-⇒↑ A B = refl
⇒↑-injˡ : {A B A′ B′ : Tm type ↑ Δ} → (A ⇒↑ B) ≡ (A′ ⇒↑ B′) → A ≡ A′
⇒↑-injˡ {A = A}{B}{A′}{B′} e = trans (sym (domOf-⇒↑ A B)) (trans (cong domOf e) (domOf-⇒↑ A′ B′))
⇒↑-injʳ : {A B A′ B′ : Tm type ↑ Δ} → (A ⇒↑ B) ≡ (A′ ⇒↑ B′) → B ≡ B′
⇒↑-injʳ {A = A}{B}{A′}{B′} e = trans (sym (codOf-⇒↑ A B)) (trans (cong codOf e) (codOf-⇒↑ A′ B′))
bodyOf : Tm type ↑ Δ → Tm type ↑ (type ∷ Δ)
bodyOf (∀' (pair k (use b)  cv) ⇑ θ) = b ⇑ os (thinR cv ⨾ θ)
bodyOf (∀' (pair k (drop b) cv) ⇑ θ) = b ⇑ o' (thinR cv ⨾ θ)
bodyOf X = wk↑ type X
bodyOf-∀↑ : (K : Tm kind ↑ Δ)(B : Tm type ↑ (type ∷ Δ)) → bodyOf (∀↑ K B) ≡ B
bodyOf-∀↑ K (b ⇑ os φ) = refl
bodyOf-∀↑ K (b ⇑ o' φ) = refl
∀↑-inj : {K K′ : Tm kind ↑ Δ}{B B′ : Tm type ↑ (type ∷ Δ)} → (∀↑ K B) ≡ (∀↑ K′ B′) → B ≡ B′
∀↑-inj {K = K}{K′}{B}{B′} e = trans (sym (bodyOf-∀↑ K B)) (trans (cong bodyOf e) (bodyOf-∀↑ K′ B′))

-- ════ THE TYPING JUDGEMENT (raw constructors, carried thinning θ) ════
data _⊢[_]_∶_ : ∀ {sup Δ} → Cx Δ → sup ⊑ Δ → Tm expr sup → Tm type ↑ Δ → Set where
  ⊢var  : ∀ {Δ}{Φ : Cx Δ}{θ : Pos Δ expr}
        → Φ ⊢[ θ ] var ∶ lookup Φ θ
  ⊢app  : ∀ {sₗ sᵣ sup Δ}{Φ : Cx Δ}{l : Tm expr sₗ}{r : Tm expr sᵣ}{cv : Cover sₗ sᵣ sup}
            {θ : sup ⊑ Δ}{A B : Tm type ↑ Δ}
        → Φ ⊢[ thinL cv ⨾ θ ] l ∶ (A ⇒↑ B)
        → Φ ⊢[ thinR cv ⨾ θ ] r ∶ A
        → Φ ⊢[ θ ] app (pair l r cv) ∶ B
  ⊢lamᵘ : ∀ {sₐ sᵦ sup Δ}{Φ : Cx Δ}{a : Tm type sₐ}{body : Tm expr (expr ∷ sᵦ)}
            {cv : Cover sₐ sᵦ sup}{θ : sup ⊑ Δ}{B : Tm type ↑ Δ}
        → (Φ ,- (a ⇑ (thinL cv ⨾ θ))) ⊢[ os (thinR cv ⨾ θ) ] body ∶ wk↑ expr B
        → Φ ⊢[ θ ] lam (pair a (use body) cv) ∶ ((a ⇑ (thinL cv ⨾ θ)) ⇒↑ B)
  ⊢lamᵈ : ∀ {sₐ sᵦ sup Δ}{Φ : Cx Δ}{a : Tm type sₐ}{body : Tm expr sᵦ}
            {cv : Cover sₐ sᵦ sup}{θ : sup ⊑ Δ}{B : Tm type ↑ Δ}
        → (Φ ,- (a ⇑ (thinL cv ⨾ θ))) ⊢[ o' (thinR cv ⨾ θ) ] body ∶ wk↑ expr B
        → Φ ⊢[ θ ] lam (pair a (drop body) cv) ∶ ((a ⇑ (thinL cv ⨾ θ)) ⇒↑ B)
  ⊢Lamᵘ : ∀ {sup Δ}{Φ : Cx Δ}{body : Tm expr (type ∷ sup)}{θ : sup ⊑ Δ}{B : Tm type ↑ (type ∷ Δ)}
        → (Φ ,*) ⊢[ os θ ] body ∶ B
        → Φ ⊢[ θ ] Lam (use body) ∶ ∀↑ ⋆↑ B
  ⊢Lamᵈ : ∀ {sup Δ}{Φ : Cx Δ}{body : Tm expr sup}{θ : sup ⊑ Δ}{B : Tm type ↑ (type ∷ Δ)}
        → (Φ ,*) ⊢[ o' θ ] body ∶ B
        → Φ ⊢[ θ ] Lam (drop body) ∶ ∀↑ ⋆↑ B
  ⊢App  : ∀ {sₑ sₐ sup Δ}{Φ : Cx Δ}{e : Tm expr sₑ}{a : Tm type sₐ}{cv : Cover sₑ sₐ sup}
            {θ : sup ⊑ Δ}{K : Tm kind ↑ Δ}{B : Tm type ↑ (type ∷ Δ)}
        → Φ ⊢[ thinL cv ⨾ θ ] e ∶ ∀↑ K B
        → Φ ⊢[ θ ] App (pair e a cv) ∶ (B ⟪ (a ⇑ (thinR cv ⨾ θ)) ∙ ids ⟫)
infix 4 _⊢[_]_∶_

-- typing of a ⇑-carrier
_⊢↑_∶_ : ∀ {Δ} → Cx Δ → Tm expr ↑ Δ → Tm type ↑ Δ → Set
Φ ⊢↑ (t ⇑ θ) ∶ A = Φ ⊢[ θ ] t ∶ A
infix 4 _⊢↑_∶_

-- ════ SMART TYPED CONSTRUCTORS — definitional via Fac-L/Fac-R ════
⊢app↑ : ∀ {Δ}{Φ : Cx Δ}{A B : Tm type ↑ Δ}(L R : Tm expr ↑ Δ)
      → Φ ⊢↑ L ∶ (A ⇒↑ B) → Φ ⊢↑ R ∶ A → Φ ⊢↑ (app↑ L R) ∶ B
⊢app↑ (l ⇑ θ) (r ⇑ φ) ⊢L ⊢R = ⊢app {cv = cov (cop θ φ)} ⊢L ⊢R
⊢lam↑ : ∀ {sₐ Δ}{Φ : Cx Δ}{B : Tm type ↑ Δ}(a : Tm type sₐ)(α : sₐ ⊑ Δ)(body : Tm expr ↑ (expr ∷ Δ))
      → (Φ ,- (a ⇑ α)) ⊢↑ body ∶ wk↑ expr B → Φ ⊢↑ (lam↑ (a ⇑ α) body) ∶ ((a ⇑ α) ⇒↑ B)
⊢lam↑ a α (t ⇑ os θ) ⊢t = ⊢lamᵘ ⊢t
⊢lam↑ a α (t ⇑ o' θ) ⊢t = ⊢lamᵈ ⊢t
⊢Lam↑ : ∀ {Δ}{Φ : Cx Δ}{B : Tm type ↑ (type ∷ Δ)}(body : Tm expr ↑ (type ∷ Δ))
      → (Φ ,*) ⊢↑ body ∶ B → Φ ⊢↑ (Lam↑ body) ∶ ∀↑ ⋆↑ B
⊢Lam↑ (t ⇑ os θ) ⊢t = ⊢Lamᵘ ⊢t
⊢Lam↑ (t ⇑ o' θ) ⊢t = ⊢Lamᵈ ⊢t
⊢App↑ : ∀ {Δ}{Φ : Cx Δ}{K : Tm kind ↑ Δ}(B : Tm type ↑ (type ∷ Δ))(E : Tm expr ↑ Δ)(A : Tm type ↑ Δ)
      → Φ ⊢↑ E ∶ ∀↑ K B → Φ ⊢↑ (App↑ E A) ∶ (B ⟪ A ∙ ids ⟫)
⊢App↑ {K = K} B (e ⇑ θ) (a ⇑ φ) ⊢E = ⊢App {K = K}{B = B} ⊢E
⊢fresh : ∀ {Δ}{Φ : Cx Δ}{A : Tm type ↑ Δ} → (Φ ,- A) ⊢↑ var↑ ∶ wk↑ expr A
⊢fresh = ⊢var

-- ════════════════════════════════════════════════════════════════════════════
-- σ-ALGEBRA HELPERS.  All bridge the residual σ-laws (weakening naturality of
-- `sub'` = `sub'-ren`/`sub'-↾` + the ⨟-identities) — the SAME sort-agnostic
-- family as single-sorted FOp.
-- ════════════════════════════════════════════════════════════════════════════
-- (X ⟨ r ⟩↑) ⟪ τ ⟫ ≡ X ⟪ τ ↾ r ⟫   (renaming = restriction of the target)
ren-⟪⟫ : (X : Tm t ↑ Δ)(r : Δ ⊑ Ω)(τ : Sub Ξ Ω) → (X ⟨ r ⟩↑) ⟪ τ ⟫ ≡ X ⟪ τ ↾ r ⟫
ren-⟪⟫ (x ⇑ θ) r τ = sym (sub'-↾ x θ r τ)
-- (X ⟨ o' oi ⟩↑) ⟪ u ∙ σ ⟫ ≡ X ⟪ σ ⟫   (weaken-then-cons cancels)
wk-cancel : (X : Tm t ↑ Θ)(u : Tm s ↑ Δ)(σ : Sub Δ Θ) → (wk↑ s X) ⟪ u ∙ σ ⟫ ≡ X ⟪ σ ⟫
wk-cancel X u σ = trans (ren-⟪⟫ X (o' oi) (u ∙ σ)) (cong (X ⟪_⟫) (↾-oi σ))
-- A ⟪ wkSub σ ⟫ ≡ wk↑ (A ⟪ σ ⟫)
wkSub-⟪⟫ : (X : Tm t ↑ Θ)(σ : Sub Δ Θ) → X ⟪ wkSub {s = s} σ ⟫ ≡ wk↑ s (X ⟪ σ ⟫)
wkSub-⟪⟫ (x ⇑ θ) σ = sub'-ren x θ σ (o' oi)

-- ⨟ identities and mapWk/⨟ interaction
⨟ids : (σ : Sub Δ Θ) → σ ⨟ ids ≡ σ
⨟ids ε       = refl
⨟ids (u ∙ σ) = cong₂ _∙_ (⟪⟫-id u) (⨟ids σ)
mapWk-⨟ : (ρ : Sub Δ Θ)(r : Δ ⊑ Ω)(τ : Sub Ξ Ω) → mapWk ρ r ⨟ τ ≡ ρ ⨟ (τ ↾ r)
mapWk-⨟ ε       r τ = refl
mapWk-⨟ (u ∙ ρ) r τ = cong₂ _∙_ (ren-⟪⟫ u r τ) (mapWk-⨟ ρ r τ)
wkSub-⨟ : (ρ : Sub Δ Θ)(u : Tm s ↑ Ξ)(τ : Sub Ξ Δ) → wkSub {s = s} ρ ⨟ (u ∙ τ) ≡ ρ ⨟ τ
wkSub-⨟ ρ u τ = trans (mapWk-⨟ ρ (o' oi) (u ∙ τ)) (cong (ρ ⨟_) (↾-oi τ))
ids⨟ : (σ : Sub Δ Θ) → ids ⨟ σ ≡ σ
ids⨟ {Θ = []}    ε       = refl
ids⨟ {Θ = _ ∷ _} (u ∙ σ) = cong (u ∙_) (trans (wkSub-⨟ ids u σ) (ids⨟ σ))

-- ════ ⊢App-result naturality (App-comm) — the co-de-Bruijn `inst-lift` ════
inst-lift-comm : (A : Tm type ↑ Θ)(σ : Sub Δ Θ) → (A ∙ ids) ⨟ σ ≡ (lift σ) ⨟ ((A ⟪ σ ⟫) ∙ ids)
inst-lift-comm A σ = cong₂ _∙_ refl (trans (ids⨟ σ) (sym (trans (wkSub-⨟ σ (A ⟪ σ ⟫) ids) (⨟ids σ))))
App-comm : (B : Tm type ↑ (type ∷ Θ))(A : Tm type ↑ Θ)(σ : Sub Δ Θ)
         → (B ⟪ A ∙ ids ⟫) ⟪ σ ⟫ ≡ (B ⟪ lift σ ⟫) ⟪ (A ⟪ σ ⟫) ∙ ids ⟫
App-comm B A σ = trans (Clos B (A ∙ ids) σ)
                 (trans (cong (B ⟪_⟫) (inst-lift-comm A σ))
                        (sym (Clos B (lift σ) ((A ⟪ σ ⟫) ∙ ids))))

-- (u ⟪ σ ⟫) ⟨ r ⟩↑ ≡ u ⟪ mapWk σ r ⟫  (rename after sub = sub by renamed target)
renToSub : (u : Tm t ↑ Δ)(σ : Sub Ξ Δ)(r : Ξ ⊑ Ω) → (u ⟪ σ ⟫) ⟨ r ⟩↑ ≡ u ⟪ mapWk σ r ⟫
renToSub (x ⇑ θ) σ r = sym (sub'-ren x θ σ r)
-- ⊢App-result naturality under renaming (App-ren)
App-ren : (B : Tm type ↑ (type ∷ Θ))(A : Tm type ↑ Θ)(r : Θ ⊑ Ω)
        → (B ⟨ os r ⟩↑) ⟪ (A ⟨ r ⟩↑) ∙ ids ⟫ ≡ (B ⟪ A ∙ ids ⟫) ⟨ r ⟩↑
App-ren B A r =
  trans (ren-⟪⟫ B (os r) ((A ⟨ r ⟩↑) ∙ ids))
    (trans (cong (λ z → B ⟪ (A ⟨ r ⟩↑) ∙ z ⟫) (ids↾-mapWk r))
           (sym (renToSub B (A ∙ ids) r)))


-- ════════════════════════════════════════════════════════════════════════════
-- RENAMING (thinning) PRESERVES TYPING.  In the UNIFIED setting a thinning acts
-- on the WHOLE scope, so it must distribute over the type-formers — via the
-- PROVEN ⟨⟩-⇒↑/⟨⟩-∀↑ and the weakening-commute helpers below (all the SAME
-- thinning-naturality family; in single-sorted FOp these were absent only because
-- term-renaming there never touched the type scope).  ⊢-ren is a HELPER (uses
-- transports); sub-pres/preserve only APPLY it.
-- ════════════════════════════════════════════════════════════════════════════
private variable
  Ω′ : Scope
-- weakening commutes with thinning
wk↑-⟨⟩ : ∀ {T : Scope → Set}{Δ Ω}(X : T ↑ Δ)(ψ : Δ ⊑ Ω) → (wk↑ s X) ⟨ os ψ ⟩↑ ≡ wk↑ s (X ⟨ ψ ⟩↑)
wk↑-⟨⟩ X ψ = trans (⟨⟩-⨾ X (o' oi) (os ψ))
             (trans (cong (X ⟨_⟩↑) (cong o' (trans (oi⨾ ψ) (sym (⨾oi ψ)))))
                    (sym (⟨⟩-⨾ X ψ (o' oi))))
wk-⟨⟩ : ∀ {T : Scope → Set}{Δ Ω}(X : T ↑ Δ)(ψ : Δ ⊑ Ω) → wk↑ s (X ⟨ ψ ⟩↑) ≡ X ⟨ o' ψ ⟩↑
wk-⟨⟩ X ψ = trans (⟨⟩-⨾ X ψ (o' oi)) (cong (X ⟨_⟩↑) (cong o' (⨾oi ψ)))
ren-oi : ∀ {T : Scope → Set}{Δ}(X : T ↑ Δ) → X ⟨ oi ⟩↑ ≡ X
ren-oi (x ⇑ θ) = cong (x ⇑_) (⨾oi θ)
⋆↑-⟨⟩ : ∀ {Δ Ω}(ψ : Δ ⊑ Ω) → ⋆↑ ⟨ ψ ⟩↑ ≡ ⋆↑
⋆↑-⟨⟩ ψ = cong (⋆ ⇑_) (oe-unique (oe ⨾ ψ))

-- context renaming relation (Φ′ over Ω is Φ over Δ renamed/extended along ψ)
data CxR : ∀ {Δ Ω} → Δ ⊑ Ω → Cx Δ → Cx Ω → Set where
  ozᶜ : CxR oz ε ε
  os* : ∀ {Δ Ω}{ψ : Δ ⊑ Ω}{Φ Φ′} → CxR ψ Φ Φ′ → CxR (os ψ) (Φ ,*) (Φ′ ,*)
  os- : ∀ {Δ Ω}{ψ : Δ ⊑ Ω}{Φ Φ′}(A : Tm type ↑ Δ) → CxR ψ Φ Φ′ → CxR (os ψ) (Φ ,- A) (Φ′ ,- (A ⟨ ψ ⟩↑))
  o'* : ∀ {Δ Ω}{ψ : Δ ⊑ Ω}{Φ Φ′} → CxR ψ Φ Φ′ → CxR (o' ψ) Φ (Φ′ ,*)
  o'- : ∀ {Δ Ω}{ψ : Δ ⊑ Ω}{Φ Φ′}(C : Tm type ↑ Ω) → CxR ψ Φ Φ′ → CxR (o' ψ) Φ (Φ′ ,- C)

cxr-id : ∀ {Δ}(Φ : Cx Δ) → CxR oi Φ Φ
cxr-id ε        = ozᶜ
cxr-id (Φ ,*)   = os* (cxr-id Φ)
cxr-id (Φ ,- A) = subst (λ B → CxR (os oi) (Φ ,- A) (Φ ,- B)) (ren-oi A) (os- A (cxr-id Φ))

lookup-ren : ∀ {Δ Ω}{ψ : Δ ⊑ Ω}{Φ : Cx Δ}{Φ′ : Cx Ω}
           → CxR ψ Φ Φ′ → (x : Pos Δ expr) → lookup Φ′ (x ⨾ ψ) ≡ (lookup Φ x) ⟨ ψ ⟩↑
lookup-ren (os- {ψ = ψ} A r) (os x) = sym (wk↑-⟨⟩ A ψ)
lookup-ren (os- {ψ = ψ}{Φ = Φ} A r) (o' x) = trans (cong (wk↑ expr) (lookup-ren r x)) (sym (wk↑-⟨⟩ (lookup Φ x) ψ))
lookup-ren (os* {ψ = ψ}{Φ = Φ} r)   (o' x) = trans (cong (wk↑ type) (lookup-ren r x)) (sym (wk↑-⟨⟩ (lookup Φ x) ψ))
lookup-ren (o'* {ψ = ψ}{Φ = Φ} r)   x      = trans (cong (wk↑ type) (lookup-ren r x)) (wk-⟨⟩ (lookup Φ x) ψ)
lookup-ren (o'- {ψ = ψ}{Φ = Φ} C r) x      = trans (cong (wk↑ expr) (lookup-ren r x)) (wk-⟨⟩ (lookup Φ x) ψ)

⊢-ren : ∀ {sup Δ Ω}{ψ : Δ ⊑ Ω}{Φ : Cx Δ}{Φ′ : Cx Ω}{θ : sup ⊑ Δ}{e : Tm expr sup}{A : Tm type ↑ Δ}
      → CxR ψ Φ Φ′ → Φ ⊢[ θ ] e ∶ A → Φ′ ⊢[ θ ⨾ ψ ] e ∶ (A ⟨ ψ ⟩↑)
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢var {θ = θ}) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] var ∶ T) (lookup-ren r θ) ⊢var
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢app {l = l}{r = rt}{cv = cv}{θ = θ}{A = A}{B = B} ⊢l ⊢r) =
  ⊢app {cv = cv}
    (subst (λ T → Φ′ ⊢[ thinL cv ⨾ (θ ⨾ ψ) ] l ∶ T) (⟨⟩-⇒↑ A B ψ)
      (subst (λ φ → Φ′ ⊢[ φ ] l ∶ ((A ⇒↑ B) ⟨ ψ ⟩↑)) (⨾⨾ (thinL cv) θ ψ) (⊢-ren r ⊢l)))
    (subst (λ φ → Φ′ ⊢[ φ ] rt ∶ (A ⟨ ψ ⟩↑)) (⨾⨾ (thinR cv) θ ψ) (⊢-ren r ⊢r))
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢lamᵘ {a = a}{body = body}{cv = cv}{θ = θ}{B = B} ⊢t) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] lam (pair a (use body) cv) ∶ T)
        (sym (trans (⟨⟩-⇒↑ (a ⇑ (thinL cv ⨾ θ)) B ψ)
                    (cong (λ z → (a ⇑ z) ⇒↑ (B ⟨ ψ ⟩↑)) (⨾⨾ (thinL cv) θ ψ))))
    (⊢lamᵘ {a = a}{cv = cv}{θ = θ ⨾ ψ}{B = B ⟨ ψ ⟩↑}
      (subst (λ C → (Φ′ ,- C) ⊢[ os (thinR cv ⨾ (θ ⨾ ψ)) ] body ∶ wk↑ expr (B ⟨ ψ ⟩↑))
             (cong (a ⇑_) (⨾⨾ (thinL cv) θ ψ))
        (subst (λ φ → (Φ′ ,- (a ⇑ ((thinL cv ⨾ θ) ⨾ ψ))) ⊢[ os φ ] body ∶ wk↑ expr (B ⟨ ψ ⟩↑))
               (⨾⨾ (thinR cv) θ ψ)
          (subst (λ T → (Φ′ ,- (a ⇑ ((thinL cv ⨾ θ) ⨾ ψ))) ⊢[ os (thinR cv ⨾ θ) ⨾ os ψ ] body ∶ T)
                 (wk↑-⟨⟩ B ψ)
            (⊢-ren (os- (a ⇑ (thinL cv ⨾ θ)) r) ⊢t)))))
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢lamᵈ {a = a}{body = body}{cv = cv}{θ = θ}{B = B} ⊢t) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] lam (pair a (drop body) cv) ∶ T)
        (sym (trans (⟨⟩-⇒↑ (a ⇑ (thinL cv ⨾ θ)) B ψ)
                    (cong (λ z → (a ⇑ z) ⇒↑ (B ⟨ ψ ⟩↑)) (⨾⨾ (thinL cv) θ ψ))))
    (⊢lamᵈ {a = a}{cv = cv}{θ = θ ⨾ ψ}{B = B ⟨ ψ ⟩↑}
      (subst (λ C → (Φ′ ,- C) ⊢[ o' (thinR cv ⨾ (θ ⨾ ψ)) ] body ∶ wk↑ expr (B ⟨ ψ ⟩↑))
             (cong (a ⇑_) (⨾⨾ (thinL cv) θ ψ))
        (subst (λ φ → (Φ′ ,- (a ⇑ ((thinL cv ⨾ θ) ⨾ ψ))) ⊢[ o' φ ] body ∶ wk↑ expr (B ⟨ ψ ⟩↑))
               (⨾⨾ (thinR cv) θ ψ)
          (subst (λ T → (Φ′ ,- (a ⇑ ((thinL cv ⨾ θ) ⨾ ψ))) ⊢[ o' (thinR cv ⨾ θ) ⨾ os ψ ] body ∶ T)
                 (wk↑-⟨⟩ B ψ)
            (⊢-ren (os- (a ⇑ (thinL cv ⨾ θ)) r) ⊢t)))))
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢Lamᵘ {body = body}{θ = θ}{B = B} ⊢t) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] Lam (use body) ∶ T)
        (sym (trans (⟨⟩-∀↑ ⋆↑ B ψ) (cong (λ K → ∀↑ K (B ⟨ os ψ ⟩↑)) (⋆↑-⟨⟩ ψ))))
    (⊢Lamᵘ {θ = θ ⨾ ψ}{B = B ⟨ os ψ ⟩↑} (⊢-ren (os* r) ⊢t))
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢Lamᵈ {body = body}{θ = θ}{B = B} ⊢t) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] Lam (drop body) ∶ T)
        (sym (trans (⟨⟩-∀↑ ⋆↑ B ψ) (cong (λ K → ∀↑ K (B ⟨ os ψ ⟩↑)) (⋆↑-⟨⟩ ψ))))
    (⊢Lamᵈ {θ = θ ⨾ ψ}{B = B ⟨ os ψ ⟩↑} (⊢-ren (os* r) ⊢t))
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢App {e = e}{a = a}{cv = cv}{θ = θ}{K = K}{B = B} ⊢e) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] App (pair e a cv) ∶ T)
        (trans (cong (λ z → (B ⟨ os ψ ⟩↑) ⟪ (a ⇑ z) ∙ ids ⟫) (sym (⨾⨾ (thinR cv) θ ψ)))
               (App-ren B (a ⇑ (thinR cv ⨾ θ)) ψ))
    (⊢App {a = a}{cv = cv}{θ = θ ⨾ ψ}{K = K ⟨ ψ ⟩↑}{B = B ⟨ os ψ ⟩↑}
      (subst (λ T → Φ′ ⊢[ thinL cv ⨾ (θ ⨾ ψ) ] e ∶ T) (⟨⟩-∀↑ K B ψ)
        (subst (λ φ → Φ′ ⊢[ φ ] e ∶ ((∀↑ K B) ⟨ ψ ⟩↑)) (⨾⨾ (thinL cv) θ ψ) (⊢-ren r ⊢e))))

-- one-fresh-binder context weakening (specialised from ⊢-ren along o' oi).  The
-- output thinning is θ ⨾ o' oi (= the thn of a `wk↑` carrier), so it is SUBST-FREE.
⊢wk-tm : ∀ {sup Δ}{Ψ : Cx Δ}{θ : sup ⊑ Δ}{e : Tm expr sup}{T : Tm type ↑ Δ}(C : Tm type ↑ Δ)
       → Ψ ⊢[ θ ] e ∶ T → (Ψ ,- C) ⊢[ θ ⨾ o' oi ] e ∶ wk↑ expr T
⊢wk-tm {Ψ = Ψ} C ⊢t = ⊢-ren (o'- C (cxr-id Ψ)) ⊢t
⊢wk-ty : ∀ {sup Δ}{Ψ : Cx Δ}{θ : sup ⊑ Δ}{e : Tm expr sup}{T : Tm type ↑ Δ}
       → Ψ ⊢[ θ ] e ∶ T → (Ψ ,*) ⊢[ θ ⨾ o' oi ] e ∶ wk↑ type T
⊢wk-ty {Ψ = Ψ} ⊢t = ⊢-ren (o'* (cxr-id Ψ)) ⊢t

-- ════════════════════════════════════════════════════════════════════════════
-- WELL-TYPED SUBSTITUTION and the SUBSTITUTION LEMMA `sub-pres`.  Because FOpMS's
-- `sub'` THREADS θ (restricting σ once at the leaf), σ is NEVER peeled: `sub-pres`
-- threads ONE `WtSub` unchanged through app/App, and only extends it (lift) under
-- a binder.  This ONE lemma is BOTH type-substitution- and term-substitution-
-- preserves-typing (β and type-β are its instances in SR).
-- ════════════════════════════════════════════════════════════════════════════
data WtSub {Δ}(Ψ : Cx Δ) : ∀ {Θ} → Sub Δ Θ → Cx Θ → Set where
  ε    : WtSub Ψ ε ε
  _∙*_ : ∀ {Θ}{σ : Sub Δ Θ}{Φ : Cx Θ}(u : Tm type ↑ Δ) → WtSub Ψ σ Φ → WtSub Ψ (u ∙ σ) (Φ ,*)
  _∙-_ : ∀ {Θ}{σ : Sub Δ Θ}{Φ : Cx Θ}{A : Tm type ↑ Θ}{u : Tm expr ↑ Δ}
       → Ψ ⊢↑ u ∶ (A ⟪ σ ⟫) → WtSub Ψ σ Φ → WtSub Ψ (u ∙ σ) (Φ ,- A)
infixr 5 _∙*_ _∙-_

-- entry weakening at a σ-moved classifier (the wkSub-⟪⟫ coercion lives here)
⊢wkσ-tm : ∀ {Δ Θ}{Ψ : Cx Δ}{A : Tm type ↑ Θ}{u : Tm expr ↑ Δ}{σ : Sub Δ Θ}(C : Tm type ↑ Δ)
        → Ψ ⊢↑ u ∶ (A ⟪ σ ⟫) → (Ψ ,- C) ⊢↑ (wk↑ expr u) ∶ (A ⟪ wkSub {s = expr} σ ⟫)
⊢wkσ-tm {Ψ = Ψ}{A = A}{u = u}{σ = σ} C ⊢u =
  subst (λ T → (Ψ ,- C) ⊢↑ (wk↑ expr u) ∶ T) (sym (wkSub-⟪⟫ {s = expr} A σ)) (⊢wk-tm C ⊢u)
⊢wkσ-ty : ∀ {Δ Θ}{Ψ : Cx Δ}{A : Tm type ↑ Θ}{u : Tm expr ↑ Δ}{σ : Sub Δ Θ}
        → Ψ ⊢↑ u ∶ (A ⟪ σ ⟫) → (Ψ ,*) ⊢↑ (wk↑ type u) ∶ (A ⟪ wkSub {s = type} σ ⟫)
⊢wkσ-ty {Ψ = Ψ}{A = A}{u = u}{σ = σ} ⊢u =
  subst (λ T → (Ψ ,*) ⊢↑ (wk↑ type u) ∶ T) (sym (wkSub-⟪⟫ {s = type} A σ)) (⊢wk-ty ⊢u)
⊢freshσ : ∀ {Δ Θ}{Ψ : Cx Δ}{A : Tm type ↑ Θ}{σ : Sub Δ Θ}
        → (Ψ ,- (A ⟪ σ ⟫)) ⊢↑ var↑ ∶ (A ⟪ wkSub {s = expr} σ ⟫)
⊢freshσ {Ψ = Ψ}{A = A}{σ = σ} = subst (λ T → (Ψ ,- (A ⟪ σ ⟫)) ⊢↑ var↑ ∶ T) (sym (wkSub-⟪⟫ {s = expr} A σ)) ⊢fresh

-- weaken a whole well-typed-sub by one fresh target binder
wkSub-pres-tm : ∀ {Δ Θ}{Ψ : Cx Δ}{σ : Sub Δ Θ}{Φ : Cx Θ}(C : Tm type ↑ Δ)
              → WtSub Ψ σ Φ → WtSub (Ψ ,- C) (wkSub σ) Φ
wkSub-pres-tm C ε        = ε
wkSub-pres-tm C (u ∙* w) = wk↑ expr u ∙* wkSub-pres-tm C w
wkSub-pres-tm C (_∙-_ {σ = σ}{A = A} ⊢u w) = ⊢wkσ-tm {A = A}{σ = σ} C ⊢u ∙- wkSub-pres-tm C w
wkSub-pres-ty : ∀ {Δ Θ}{Ψ : Cx Δ}{σ : Sub Δ Θ}{Φ : Cx Θ}
              → WtSub Ψ σ Φ → WtSub (Ψ ,*) (wkSub {s = type} σ) Φ
wkSub-pres-ty ε        = ε
wkSub-pres-ty (u ∙* w) = wk↑ type u ∙* wkSub-pres-ty w
wkSub-pres-ty (_∙-_ {σ = σ}{A = A} ⊢u w) = ⊢wkσ-ty {A = A}{σ = σ} ⊢u ∙- wkSub-pres-ty w

-- the variable case: read the selected entry, discharging the lookup weakenings
var-pres : ∀ {Δ Θ}{Ψ : Cx Δ}{σ : Sub Δ Θ}{Φ : Cx Θ}
         → WtSub Ψ σ Φ → (p : Pos Θ expr) → Ψ ⊢↑ look p σ ∶ (lookup Φ p ⟪ σ ⟫)
var-pres {Ψ = Ψ} (_∙-_ {σ = σ}{A = A}{u = u} ⊢u w) (os oe) =
  subst (λ T → Ψ ⊢↑ u ∶ T) (sym (wk-cancel A u σ)) ⊢u
var-pres {Ψ = Ψ} (_∙-_ {σ = σ}{Φ = Φ}{u = u} ⊢u w) (o' p) =
  subst (λ T → Ψ ⊢↑ look p σ ∶ T) (sym (wk-cancel (lookup Φ p) u σ)) (var-pres w p)
var-pres {Ψ = Ψ} (_∙*_ {σ = σ}{Φ = Φ} u w) (o' p) =
  subst (λ T → Ψ ⊢↑ look p σ ∶ T) (sym (wk-cancel (lookup Φ p) u σ)) (var-pres w p)

-- ★ SUBSTITUTION PRESERVES TYPING.  ARROW/app/App distributions are DEFINITIONAL
-- (H1: ⟪⟫-⇒↑/⟪⟫-app↑/⟪⟫-App↑ are refl), so those cases are subst-free; the ∀/lam/
-- Lam residuals are the sub'-drop / wk-⟪⟫ / ⟪⟫-∀↑ / App-comm bridges.
sub-pres : ∀ {sup Δ Θ}{Ψ : Cx Δ}{σ : Sub Δ Θ}{Φ : Cx Θ}{θ : sup ⊑ Θ}{e : Tm expr sup}{A : Tm type ↑ Θ}
         → WtSub Ψ σ Φ → Φ ⊢[ θ ] e ∶ A → Ψ ⊢↑ (sub' e θ σ) ∶ (A ⟪ σ ⟫)
sub-pres w (⊢var {θ = p}) = var-pres w p
sub-pres w (⊢app {cv = cv} ⊢l ⊢r) = ⊢app↑ _ _ (sub-pres w ⊢l) (sub-pres w ⊢r)
sub-pres {Ψ = Ψ}{σ = σ} w (⊢lamᵘ {a = a}{body = body}{cv = cv}{θ = θ}{B = B} ⊢t) =
  ⊢lam↑ (thing dom) (thn dom) (sub' body (os (thinR cv ⨾ θ)) (lift σ))
    (subst (λ T → (Ψ ,- dom) ⊢↑ (sub' body (os (thinR cv ⨾ θ)) (lift σ)) ∶ T) (wk-⟪⟫ B σ)
      (sub-pres (⊢freshσ {A = a ⇑ (thinL cv ⨾ θ)}{σ = σ} ∙- wkSub-pres-tm dom w) ⊢t))
  where dom = (a ⇑ (thinL cv ⨾ θ)) ⟪ σ ⟫
sub-pres {Ψ = Ψ}{σ = σ} w (⊢lamᵈ {a = a}{body = body}{cv = cv}{θ = θ}{B = B} ⊢t) =
  ⊢lam↑ (thing dom) (thn dom) (subBind (drop body) (thinR cv ⨾ θ) σ)
    (subst (λ T → (Ψ ,- dom) ⊢↑ (subBind (drop body) (thinR cv ⨾ θ) σ) ∶ T) (wk-⟪⟫ B σ)
      (subst (λ M → (Ψ ,- dom) ⊢↑ M ∶ ((wk↑ expr B) ⟪ lift σ ⟫)) (sub'-drop body (thinR cv ⨾ θ) σ)
        (sub-pres (⊢freshσ {A = a ⇑ (thinL cv ⨾ θ)}{σ = σ} ∙- wkSub-pres-tm dom w) ⊢t)))
  where dom = (a ⇑ (thinL cv ⨾ θ)) ⟪ σ ⟫
sub-pres {Ψ = Ψ}{σ = σ} w (⊢Lamᵘ {body = body}{θ = θ}{B = B} ⊢t) =
  subst (λ T → Ψ ⊢↑ (Lam↑ (sub' body (os θ) (lift σ))) ∶ T) (sym (⟪⟫-∀↑ ⋆↑ B σ))
    (⊢Lam↑ (sub' body (os θ) (lift σ)) (sub-pres (var↑ ∙* wkSub-pres-ty w) ⊢t))
sub-pres {Ψ = Ψ}{σ = σ} w (⊢Lamᵈ {body = body}{θ = θ}{B = B} ⊢t) =
  subst (λ T → Ψ ⊢↑ (Lam↑ (subBind (drop body) θ σ)) ∶ T) (sym (⟪⟫-∀↑ ⋆↑ B σ))
    (⊢Lam↑ (subBind (drop body) θ σ)
      (subst (λ M → (Ψ ,*) ⊢↑ M ∶ (B ⟪ lift σ ⟫)) (sub'-drop body θ σ)
        (sub-pres (var↑ ∙* wkSub-pres-ty w) ⊢t)))
sub-pres {Ψ = Ψ}{σ = σ} w (⊢App {e = e}{a = a}{cv = cv}{θ = θ}{K = K}{B = B} ⊢e) =
  subst (λ T → Ψ ⊢↑ (App↑ (sub' e (thinL cv ⨾ θ) σ) (sub' a (thinR cv ⨾ θ) σ)) ∶ T)
        (sym (App-comm B (a ⇑ (thinR cv ⨾ θ)) σ))
    (⊢App↑ {K = K ⟪ σ ⟫} (B ⟪ lift σ ⟫) (sub' e (thinL cv ⨾ θ) σ) (sub' a (thinR cv ⨾ θ) σ)
      (subst (λ T → Ψ ⊢↑ (sub' e (thinL cv ⨾ θ) σ) ∶ T) (⟪⟫-∀↑ K B σ) (sub-pres w ⊢e)))
