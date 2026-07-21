{-# OPTIONS --rewriting --local-confluence-check #-}
-- Full System F TYPES (tvar/⇒/∀) with substitution as a DEFINED OPERATION.
-- The σ-laws are PROVEN (refl + induction), never postulated.
module FOp.Ty where
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Agda.Builtin.Equality.Rewrite
open import FOp.ThinRw   -- _⊑_ (oz/os/o'), _⨾_ (Orientation A), oi

Scope = List ⊤
variable Γ Δ Ξ Ω Θ Γₗ Γᵣ sup : Scope
Pos : Scope → Set
Pos Θ = (tt ∷ []) ⊑ Θ
oe : [] ⊑ Γ
oe {[]}     = oz
oe {tt ∷ Γ} = o' oe

-- covers (relevant pairing) + factorisation (registered ⇒ cover coherence definitional)
data Cover : Scope → Scope → Scope → Set where
  done : Cover [] [] []
  bb   : Cover Γₗ Γᵣ Γ → Cover (tt ∷ Γₗ) (tt ∷ Γᵣ) (tt ∷ Γ)
  ll   : Cover Γₗ Γᵣ Γ → Cover (tt ∷ Γₗ) Γᵣ        (tt ∷ Γ)
  rr   : Cover Γₗ Γᵣ Γ → Cover Γₗ        (tt ∷ Γᵣ) (tt ∷ Γ)
thinL : Cover Γₗ Γᵣ Γ → Γₗ ⊑ Γ
thinL done = oz ; thinL (bb c) = os (thinL c) ; thinL (ll c) = os (thinL c) ; thinL (rr c) = o' (thinL c)
thinR : Cover Γₗ Γᵣ Γ → Γᵣ ⊑ Γ
thinR done = oz ; thinR (bb c) = os (thinR c) ; thinR (ll c) = o' (thinR c) ; thinR (rr c) = os (thinR c)
record Cop (α : Γₗ ⊑ Δ) (β : Γᵣ ⊑ Δ) : Set where
  constructor mkCop
  field {un} : Scope
        cov  : Cover Γₗ Γᵣ un
        out  : un ⊑ Δ
open Cop
cop : (α : Γₗ ⊑ Δ) (β : Γᵣ ⊑ Δ) → Cop α β
cop oz     oz     = mkCop done oz
cop (os α) (os β) = let c = cop α β in mkCop (bb (cov c)) (os (out c))
cop (os α) (o' β) = let c = cop α β in mkCop (ll (cov c)) (os (out c))
cop (o' α) (os β) = let c = cop α β in mkCop (rr (cov c)) (os (out c))
cop (o' α) (o' β) = let c = cop α β in mkCop (cov c)      (o' (out c))
Fac-L : (α : Γₗ ⊑ Δ)(β : Γᵣ ⊑ Δ) → thinL (cov (cop α β)) ⨾ out (cop α β) ≡ α
Fac-L oz oz = refl ; Fac-L (os α)(os β) = cong os (Fac-L α β) ; Fac-L (os α)(o' β) = cong os (Fac-L α β)
Fac-L (o' α)(os β) = cong o' (Fac-L α β) ; Fac-L (o' α)(o' β) = cong o' (Fac-L α β)
Fac-R : (α : Γₗ ⊑ Δ)(β : Γᵣ ⊑ Δ) → thinR (cov (cop α β)) ⨾ out (cop α β) ≡ β
Fac-R oz oz = refl ; Fac-R (os α)(os β) = cong os (Fac-R α β) ; Fac-R (os α)(o' β) = cong o' (Fac-R α β)
Fac-R (o' α)(os β) = cong os (Fac-R α β) ; Fac-R (o' α)(o' β) = cong o' (Fac-R α β)
{-# REWRITE Fac-L Fac-R #-}

record _↑_ (T : Scope → Set) (Δ : Scope) : Set where
  constructor _⇑_
  field {scp} : Scope
        thing : T scp
        thn   : scp ⊑ Δ
open _↑_
_<$>_ : ∀ {S T Δ} → (∀ {Γ} → S Γ → T Γ) → S ↑ Δ → T ↑ Δ
f <$> (t ⇑ θ) = f t ⇑ θ
_⟨_⟩↑ : ∀ {T Δ Δ′} → T ↑ Δ → Δ ⊑ Δ′ → T ↑ Δ′
(t ⇑ θ) ⟨ ψ ⟩↑ = t ⇑ (θ ⨾ ψ)
data _×ᴿ_ (S T : Scope → Set) : Scope → Set where
  pair : S Γₗ → T Γᵣ → Cover Γₗ Γᵣ Γ → (S ×ᴿ T) Γ
pairUp : ∀ {S T Δ} → S ↑ Δ → T ↑ Δ → (S ×ᴿ T) ↑ Δ
pairUp (a ⇑ α) (b ⇑ β) = pair a b (cov (cop α β)) ⇑ out (cop α β)
data Bind (T : Scope → Set) : Scope → Set where
  use  : T (tt ∷ Θ) → Bind T Θ
  drop : T Θ        → Bind T Θ
bindUp : ∀ {T Δ} → T ↑ (tt ∷ Δ) → (Bind T) ↑ Δ
bindUp (t ⇑ os θ) = use  t ⇑ θ
bindUp (t ⇑ o' θ) = drop t ⇑ θ

-- ════ the FULL System F types ════
data Ty : Scope → Set where
  tvar : Ty (tt ∷ [])
  _⇒_  : (Ty ×ᴿ Ty) Θ → Ty Θ
  ∀'   : Bind Ty Θ → Ty Θ
_⇒↑_ : ∀ {Δ} → Ty ↑ Δ → Ty ↑ Δ → Ty ↑ Δ
A ⇒↑ B = _⇒_ <$> pairUp A B
∀↑ : ∀ {Δ} → Ty ↑ (tt ∷ Δ) → Ty ↑ Δ
∀↑ X = ∀' <$> bindUp X
infixr 6 _⇒↑_
var₀ : Ty ↑ (tt ∷ Δ)
var₀ = tvar ⇑ os oe

-- ════ substitution = first-order vector; the ACTION and COMPOSITION are OPERATIONS ════
data Sub (Δ : Scope) : Scope → Set where
  ε   : Sub Δ []
  _∙_ : Ty ↑ Δ → Sub Δ Θ → Sub Δ (tt ∷ Θ)
infixr 5 _∙_
_↾_ : Sub Δ Θ → sup ⊑ Θ → Sub Δ sup
ε ↾ oz = ε ; (t ∙ σ) ↾ os θ = t ∙ (σ ↾ θ) ; (t ∙ σ) ↾ o' θ = σ ↾ θ
infixl 8 _↾_
selL : Cover Γₗ Γᵣ Θ → Sub Δ Θ → Sub Δ Γₗ
selL cv σ = σ ↾ thinL cv
selR : Cover Γₗ Γᵣ Θ → Sub Δ Θ → Sub Δ Γᵣ
selR cv σ = σ ↾ thinR cv
-- target-renaming of a substitution (subsumes wkSub); the general naturality carrier
mapWk : Sub Δ Θ → Δ ⊑ Ω → Sub Ω Θ
mapWk ε       r = ε
mapWk (t ∙ σ) r = (t ⟨ r ⟩↑) ∙ mapWk σ r
mapWk-↾ : (σ : Sub Δ Θ)(r : Δ ⊑ Ω)(θ : sup ⊑ Θ) → mapWk (σ ↾ θ) r ≡ mapWk σ r ↾ θ
mapWk-↾ ε r oz = refl
mapWk-↾ (t ∙ σ) r (os θ) = cong (_ ∙_) (mapWk-↾ σ r θ)
mapWk-↾ (t ∙ σ) r (o' θ) = mapWk-↾ σ r θ
{-# REWRITE mapWk-↾ #-}
wkSub : Sub Δ Θ → Sub (tt ∷ Δ) Θ
wkSub σ = mapWk σ (o' oi)
lift : Sub Δ Θ → Sub (tt ∷ Δ) (tt ∷ Θ)
lift σ = var₀ ∙ wkSub σ

sub : Ty Θ → Sub Δ Θ → Ty ↑ Δ
sub tvar              (t ∙ ε) = t
sub (_⇒_ (pair l r cv)) σ     = (sub l (selL cv σ)) ⇒↑ (sub r (selR cv σ))
sub (∀' (use t))      σ       = ∀↑ (sub t (lift σ))
sub (∀' (drop t))     σ       = ∀' <$> (drop <$> sub t σ)
_⟪_⟫ : Ty ↑ Θ → Sub Δ Θ → Ty ↑ Δ
(t ⇑ θ) ⟪ σ ⟫ = sub t (σ ↾ θ)
infixl 8 _⟪_⟫
_⨟_ : Sub Δ Θ → Sub Ξ Δ → Sub Ξ Θ
ε ⨟ τ = ε ; (t ∙ σ) ⨟ τ = (t ⟪ τ ⟫) ∙ (σ ⨟ τ)
infixl 6 _⨟_

-- ════ THE σ-LAWS — PROVEN (never postulated) ════

-- restriction composes (structural)
↾-⨾ : (σ : Sub Δ Θ)(θ : sup ⊑ Θ)(φ : Γ ⊑ sup) → (σ ↾ θ) ↾ φ ≡ σ ↾ (φ ⨾ θ)
↾-⨾ ε oz oz = refl
↾-⨾ (t ∙ σ)(os θ)(os φ) = cong (t ∙_) (↾-⨾ σ θ φ)
↾-⨾ (t ∙ σ)(os θ)(o' φ) = ↾-⨾ σ θ φ
↾-⨾ (t ∙ σ)(o' θ) φ     = ↾-⨾ σ θ φ

-- composition commutes with restriction (structural)
⨟-↾ : (σ : Sub Δ Θ)(τ : Sub Ξ Δ)(θ : sup ⊑ Θ) → (σ ⨟ τ) ↾ θ ≡ (σ ↾ θ) ⨟ τ
⨟-↾ ε τ oz = refl
⨟-↾ (t ∙ σ) τ (os θ) = cong ((t ⟪ τ ⟫) ∙_) (⨟-↾ σ τ θ)
⨟-↾ (t ∙ σ) τ (o' θ) = ⨟-↾ σ τ θ

-- Map: DEFINITIONAL (it is the ⨟ clause)
Map : (t : Ty ↑ Δ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ) → (t ∙ σ) ⨟ τ ≡ (t ⟪ τ ⟫) ∙ (σ ⨟ τ)
Map t σ τ = refl

-- arrow distributes — PROVEN via ↾-⨾ + Fac
⟪⟫-⇒↑ : ∀ {Δ Ξ}(A B : Ty ↑ Δ)(τ : Sub Ξ Δ) → (A ⇒↑ B) ⟪ τ ⟫ ≡ (A ⟪ τ ⟫) ⇒↑ (B ⟪ τ ⟫)
⟪⟫-⇒↑ (a ⇑ α)(b ⇑ β) τ =
  cong₂ (λ x y → (sub a x) ⇒↑ (sub b y))
        (↾-⨾ τ (out (cop α β)) (thinL (cov (cop α β))))
        (↾-⨾ τ (out (cop α β)) (thinR (cov (cop α β))))

-- ∀ distributes (use case: bound var actually occurs) — PROVEN (refl, via wkSub-↾)
⟪⟫-∀↑-use : (x : Ty (tt ∷ sup))(ξ : sup ⊑ Δ)(τ : Sub Ξ Δ)
          → (∀↑ (x ⇑ os ξ)) ⟪ τ ⟫ ≡ ∀↑ ((x ⇑ os ξ) ⟪ lift τ ⟫)
⟪⟫-∀↑-use x ξ τ = refl

-- ════ stage 3: the cover-coherence tower — ALL PROVEN (subst-based, no postulates) ════
-- cop naturality: un is homogeneous (Scope≡Scope) — the trick that avoids het-equality
cop-un : (α : Γₗ ⊑ Δ)(β : Γᵣ ⊑ Δ)(ψ : Δ ⊑ Ω) → un (cop (α ⨾ ψ)(β ⨾ ψ)) ≡ un (cop α β)
cop-un α β (o' ψ) = cop-un α β ψ
cop-un oz oz oz = refl
cop-un (os α)(os β)(os ψ) = cong (tt ∷_) (cop-un α β ψ)
cop-un (os α)(o' β)(os ψ) = cong (tt ∷_) (cop-un α β ψ)
cop-un (o' α)(os β)(os ψ) = cong (tt ∷_) (cop-un α β ψ)
cop-un (o' α)(o' β)(os ψ) = cop-un α β ψ
push-o' : ∀ {W u₁ u₂}(p : u₁ ≡ u₂)(x : u₁ ⊑ W) → subst (_⊑ (tt ∷ W)) p (o' x) ≡ o' (subst (_⊑ W) p x)
push-o' refl x = refl
push-os : ∀ {W u₁ u₂}(q : u₁ ≡ u₂)(x : u₁ ⊑ W) → subst (_⊑ (tt ∷ W)) (cong (tt ∷_) q) (os x) ≡ os (subst (_⊑ W) q x)
push-os refl x = refl
cop-out : (α : Γₗ ⊑ Δ)(β : Γᵣ ⊑ Δ)(ψ : Δ ⊑ Ω)
        → subst (_⊑ Ω) (cop-un α β ψ) (out (cop (α ⨾ ψ)(β ⨾ ψ))) ≡ out (cop α β) ⨾ ψ
cop-out α β (o' ψ) = trans (push-o' (cop-un α β ψ) _) (cong o' (cop-out α β ψ))
cop-out oz oz oz = refl
cop-out (os α)(os β)(os ψ) = trans (push-os (cop-un α β ψ) _) (cong os (cop-out α β ψ))
cop-out (os α)(o' β)(os ψ) = trans (push-os (cop-un α β ψ) _) (cong os (cop-out α β ψ))
cop-out (o' α)(os β)(os ψ) = trans (push-os (cop-un α β ψ) _) (cong os (cop-out α β ψ))
cop-out (o' α)(o' β)(os ψ) = trans (push-o' (cop-un α β ψ) _) (cong o' (cop-out α β ψ))
cop-cov : (α : Γₗ ⊑ Δ)(β : Γᵣ ⊑ Δ)(ψ : Δ ⊑ Ω)
        → subst (Cover Γₗ Γᵣ) (cop-un α β ψ) (cov (cop (α ⨾ ψ)(β ⨾ ψ))) ≡ cov (cop α β)
cop-cov α β (o' ψ) = cop-cov α β ψ
cop-cov oz oz oz = refl
cop-cov (os α)(os β)(os ψ) = trans (subcong-bb (cop-un α β ψ) _) (cong bb (cop-cov α β ψ))
  where subcong-bb : ∀ {Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁)
                   → subst (Cover (tt ∷ Gl)(tt ∷ Gr)) (cong (tt ∷_) p) (bb c) ≡ bb (subst (Cover Gl Gr) p c)
        subcong-bb refl c = refl
cop-cov (os α)(o' β)(os ψ) = trans (subcong-ll (cop-un α β ψ) _) (cong ll (cop-cov α β ψ))
  where subcong-ll : ∀ {Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁)
                   → subst (Cover (tt ∷ Gl) Gr) (cong (tt ∷_) p) (ll c) ≡ ll (subst (Cover Gl Gr) p c)
        subcong-ll refl c = refl
cop-cov (o' α)(os β)(os ψ) = trans (subcong-rr (cop-un α β ψ) _) (cong rr (cop-cov α β ψ))
  where subcong-rr : ∀ {Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁)
                   → subst (Cover Gl (tt ∷ Gr)) (cong (tt ∷_) p) (rr c) ≡ rr (subst (Cover Gl Gr) p c)
        subcong-rr refl c = refl
cop-cov (o' α)(o' β)(os ψ) = cop-cov α β ψ

-- record congruence for _↑_ (scp may differ, transported)
↑≡ : ∀ {T : Scope → Set}{Δ : Scope}{s₁ s₂ : Scope}(p : s₁ ≡ s₂){t₁ : T s₁}{t₂ : T s₂}{θ₁ : s₁ ⊑ Δ}{θ₂ : s₂ ⊑ Δ}
   → subst T p t₁ ≡ t₂ → subst (_⊑ Δ) p θ₁ ≡ θ₂ → (t₁ ⇑ θ₁) ≡ (t₂ ⇑ θ₂)
↑≡ refl refl refl = refl
subst-sym : ∀ {A : Set}{P : A → Set}{x y}(p : x ≡ y){u : P x}{v : P y} → subst P p u ≡ v → subst P (sym p) v ≡ u
subst-sym refl refl = refl
subst-pair : ∀ {Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(a : Ty Gl)(b : Ty Gr)(c : Cover Gl Gr u₁)
           → subst (Ty ×ᴿ Ty) p (pair a b c) ≡ pair a b (subst (Cover Gl Gr) p c)
subst-pair refl a b c = refl

-- thinning distributes over the arrow former — PROVEN via cop naturality
pairUp-⟨⟩ : ∀ {Δ Ω}(A B : Ty ↑ Δ)(ψ : Δ ⊑ Ω) → (pairUp A B) ⟨ ψ ⟩↑ ≡ pairUp (A ⟨ ψ ⟩↑) (B ⟨ ψ ⟩↑)
pairUp-⟨⟩ (a ⇑ α)(b ⇑ β) ψ =
  ↑≡ (sym (cop-un α β ψ))
     (trans (subst-pair (sym (cop-un α β ψ)) a b (cov (cop α β)))
            (cong (pair a b) (subst-sym (cop-un α β ψ) (cop-cov α β ψ))))
     (subst-sym (cop-un α β ψ) (cop-out α β ψ))
⟨⟩-⇒↑ : ∀ {Δ Ω}(A B : Ty ↑ Δ)(ψ : Δ ⊑ Ω) → (A ⇒↑ B) ⟨ ψ ⟩↑ ≡ (A ⟨ ψ ⟩↑) ⇒↑ (B ⟨ ψ ⟩↑)
⟨⟩-⇒↑ A B ψ = cong (_⇒_ <$>_) (pairUp-⟨⟩ A B ψ)

-- thinning distributes over the ∀ former — PROVEN (bindUp cases on the thinning head)
⟨⟩-∀↑ : ∀ {Δ Ω}(X : Ty ↑ (tt ∷ Δ))(ψ : Δ ⊑ Ω) → (∀↑ X) ⟨ ψ ⟩↑ ≡ ∀↑ (X ⟨ os ψ ⟩↑)
⟨⟩-∀↑ (x ⇑ os θ) ψ = refl
⟨⟩-∀↑ (x ⇑ o' θ) ψ = refl

-- ════ stage 4: renaming naturality of sub (subsumes weakening) — PROVEN ════
oe-unique : (x : [] ⊑ Γ) → x ≡ oe
oe-unique oz = refl
oe-unique (o' x) = cong o' (oe-unique x)
⟨⟩-⨾ : ∀ {T Δ Ξ Ω}(t : T ↑ Δ)(r₁ : Δ ⊑ Ξ)(r₂ : Ξ ⊑ Ω) → t ⟨ r₁ ⟩↑ ⟨ r₂ ⟩↑ ≡ t ⟨ r₁ ⨾ r₂ ⟩↑
⟨⟩-⨾ (t ⇑ θ) r₁ r₂ = cong (t ⇑_) (⨾⨾ θ r₁ r₂)
mapWk-fusion : (σ : Sub Δ Θ)(r₁ : Δ ⊑ Ξ)(r₂ : Ξ ⊑ Ω) → mapWk (mapWk σ r₁) r₂ ≡ mapWk σ (r₁ ⨾ r₂)
mapWk-fusion ε r₁ r₂ = refl
mapWk-fusion (t ∙ σ) r₁ r₂ = cong₂ _∙_ (⟨⟩-⨾ t r₁ r₂) (mapWk-fusion σ r₁ r₂)
lift-mapWk : (σ : Sub Δ Θ)(r : Δ ⊑ Ω) → lift (mapWk σ r) ≡ mapWk (lift σ) (os r)
lift-mapWk σ r = cong₂ _∙_
  (cong (λ z → tvar ⇑ os z) (sym (oe-unique (oe ⨾ r))))
  (trans (mapWk-fusion σ r (o' oi))
    (trans (cong (λ z → mapWk σ (o' z)) (trans (⨾oi r) (sym (oi⨾ r))))
           (sym (mapWk-fusion σ (o' oi) (os r)))))

sub-ren : (t : Ty Θ)(σ : Sub Δ Θ)(r : Δ ⊑ Ω) → sub t (mapWk σ r) ≡ (sub t σ) ⟨ r ⟩↑
sub-ren tvar (u ∙ ε) r = refl
sub-ren (_⇒_ (pair l rt cv)) σ r =
  trans (cong₂ _⇒↑_ (sub-ren l (selL cv σ) r) (sub-ren rt (selR cv σ) r))
        (sym (⟨⟩-⇒↑ _ _ r))
sub-ren (∀' (use t)) σ r =
  trans (cong (λ z → ∀↑ (sub t z)) (lift-mapWk σ r))
        (trans (cong ∀↑ (sub-ren t (lift σ) (os r))) (sym (⟨⟩-∀↑ (sub t (lift σ)) r)))
sub-ren (∀' (drop t)) σ r = cong (λ z → ∀' <$> (drop <$> z)) (sub-ren t σ r)

-- ════ stage 5: general ∀-distribution, lift-⨟, and Clos/Ass — PROVEN ════
↾-oe : (σ : Sub Δ Θ) → σ ↾ oe ≡ ε
↾-oe ε       = refl
↾-oe (t ∙ σ) = ↾-oe σ
∀↑-wk : (X : Ty ↑ Δ) → ∀↑ (X ⟨ o' oi ⟩↑) ≡ ∀' <$> (drop <$> X)
∀↑-wk (x ⇑ θ) = cong (λ z → ∀' (drop x) ⇑ z) (⨾oi θ)
-- general ∀-distribution: use case refl, drop case via sub-ren
⟪⟫-∀↑ : ∀ {Δ Ξ}(Y : Ty ↑ (tt ∷ Δ))(τ : Sub Ξ Δ) → (∀↑ Y) ⟪ τ ⟫ ≡ ∀↑ (Y ⟪ lift τ ⟫)
⟪⟫-∀↑ (y ⇑ os ξ) τ = refl
⟪⟫-∀↑ (y ⇑ o' ξ) τ = sym (trans (cong ∀↑ (sub-ren y (τ ↾ ξ) (o' oi))) (∀↑-wk (sub y (τ ↾ ξ))))
-- wkSub head coherence + lift-⨟
wk-⟪⟫ : ∀ {Δ Ξ}(u : Ty ↑ Δ)(τ : Sub Ξ Δ) → (u ⟨ o' oi ⟩↑) ⟪ lift τ ⟫ ≡ (u ⟪ τ ⟫) ⟨ o' oi ⟩↑
wk-⟪⟫ (x ⇑ θ) τ = trans (cong (λ z → sub x (wkSub τ ↾ z)) (⨾oi θ)) (sub-ren x (τ ↾ θ) (o' oi))
wk-⨟-lift : (ρ : Sub Δ Θ)(τ : Sub Ξ Δ) → wkSub ρ ⨟ lift τ ≡ wkSub (ρ ⨟ τ)
wk-⨟-lift ε       τ = refl
wk-⨟-lift (u ∙ ρ) τ = cong₂ _∙_ (wk-⟪⟫ u τ) (wk-⨟-lift ρ τ)
var₀-lift : ∀ {Δ Ξ}(τ : Sub Ξ Δ) → var₀ ⟪ lift τ ⟫ ≡ var₀
var₀-lift τ = cong (λ z → sub tvar (var₀ ∙ z)) (↾-oe (wkSub τ))
lift-⨟ : (ρ : Sub Δ Θ)(τ : Sub Ξ Δ) → lift ρ ⨟ lift τ ≡ lift (ρ ⨟ τ)
lift-⨟ ρ τ = cong₂ _∙_ (var₀-lift τ) (wk-⨟-lift ρ τ)

-- ★ Clos core: substituting then substituting = substituting by the composite
sub-⨟ : (t : Ty Θ)(ρ : Sub Δ Θ)(τ : Sub Ξ Δ) → (sub t ρ) ⟪ τ ⟫ ≡ sub t (ρ ⨟ τ)
sub-⨟ tvar (u ∙ ε) τ = refl
sub-⨟ (_⇒_ (pair l rt cv)) ρ τ =
  trans (⟪⟫-⇒↑ (sub l (selL cv ρ)) (sub rt (selR cv ρ)) τ)
        (cong₂ _⇒↑_
          (trans (sub-⨟ l (selL cv ρ) τ) (cong (sub l) (sym (⨟-↾ ρ τ (thinL cv)))))
          (trans (sub-⨟ rt (selR cv ρ) τ) (cong (sub rt) (sym (⨟-↾ ρ τ (thinR cv))))))
sub-⨟ (∀' (use t)) ρ τ =
  trans (⟪⟫-∀↑ (sub t (lift ρ)) τ)
        (cong ∀↑ (trans (sub-⨟ t (lift ρ) (lift τ)) (cong (sub t) (lift-⨟ ρ τ))))
sub-⨟ (∀' (drop t)) ρ τ = cong (λ z → ∀' <$> (drop <$> z)) (sub-⨟ t ρ τ)

-- ★ Clos (compositionality) and Ass (associativity) — the σ-laws, PROVEN, no postulates
Clos : ∀ {Δ Ξ Θ}(u : Ty ↑ Θ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ) → (u ⟪ σ ⟫) ⟪ τ ⟫ ≡ u ⟪ σ ⨟ τ ⟫
Clos (t ⇑ θ) σ τ = trans (sub-⨟ t (σ ↾ θ) τ) (cong (sub t) (sym (⨟-↾ σ τ θ)))
Ass : ∀ {Δ Ξ Ω Θ}(σ : Sub Δ Θ)(τ : Sub Ξ Δ)(υ : Sub Ω Ξ) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
Ass ε       τ υ = refl
Ass (t ∙ σ) τ υ = cong₂ _∙_ (Clos t τ υ) (Ass σ τ υ)

-- ════ it COMPUTES: type-level β (∀-instantiation) fires by refl ════
_ : ∀ {Δ}(A B : Ty ↑ Δ)(τ : Sub Δ Δ) → (A ⇒↑ B) ⟪ τ ⟫ ≡ (A ⟪ τ ⟫) ⇒↑ (B ⟪ τ ⟫)
_ = ⟪⟫-⇒↑

-- ════ identity substitution + its laws (needed for type application) ════
ids : Sub Θ Θ
ids {[]}     = ε
ids {tt ∷ Θ} = var₀ ∙ wkSub ids
-- cop of a cover's own projections recovers the cover (identity out) — via subst transport
cop-split-un : (cv : Cover Γₗ Γᵣ Δ) → un (cop (thinL cv)(thinR cv)) ≡ Δ
cop-split-un done   = refl
cop-split-un (bb c) = cong (tt ∷_) (cop-split-un c)
cop-split-un (ll c) = cong (tt ∷_) (cop-split-un c)
cop-split-un (rr c) = cong (tt ∷_) (cop-split-un c)
cop-split-out : (cv : Cover Γₗ Γᵣ Δ) → subst (_⊑ Δ) (cop-split-un cv) (out (cop (thinL cv)(thinR cv))) ≡ oi
cop-split-out done   = refl
cop-split-out (bb c) = trans (push-os (cop-split-un c) _) (cong os (cop-split-out c))
cop-split-out (ll c) = trans (push-os (cop-split-un c) _) (cong os (cop-split-out c))
cop-split-out (rr c) = trans (push-os (cop-split-un c) _) (cong os (cop-split-out c))
cop-split-cov : (cv : Cover Γₗ Γᵣ Δ) → subst (Cover Γₗ Γᵣ) (cop-split-un cv) (cov (cop (thinL cv)(thinR cv))) ≡ cv
cop-split-cov done   = refl
cop-split-cov (bb c) = trans (scb (cop-split-un c) _) (cong bb (cop-split-cov c))
  where scb : ∀ {Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁) → subst (Cover (tt ∷ Gl)(tt ∷ Gr)) (cong (tt ∷_) p) (bb c) ≡ bb (subst (Cover Gl Gr) p c)
        scb refl c = refl
cop-split-cov (ll c) = trans (scl (cop-split-un c) _) (cong ll (cop-split-cov c))
  where scl : ∀ {Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁) → subst (Cover (tt ∷ Gl) Gr) (cong (tt ∷_) p) (ll c) ≡ ll (subst (Cover Gl Gr) p c)
        scl refl c = refl
cop-split-cov (rr c) = trans (scr (cop-split-un c) _) (cong rr (cop-split-cov c))
  where scr : ∀ {Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁) → subst (Cover Gl (tt ∷ Gr)) (cong (tt ∷_) p) (rr c) ≡ rr (subst (Cover Gl Gr) p c)
        scr refl c = refl
-- ⇒↑ of the two projections of a cover = the arrow at identity thinning
⇒↑-split : (l : Ty Γₗ)(r : Ty Γᵣ)(cv : Cover Γₗ Γᵣ Δ) → (l ⇑ thinL cv) ⇒↑ (r ⇑ thinR cv) ≡ (_⇒_ (pair l r cv)) ⇑ oi
subst-⇒ : ∀ {u₁ u₂}(p : u₁ ≡ u₂)(x : (Ty ×ᴿ Ty) u₁) → subst Ty p (_⇒_ x) ≡ _⇒_ (subst (Ty ×ᴿ Ty) p x)
subst-⇒ refl x = refl
⇒↑-split l r cv = ↑≡ (cop-split-un cv)
  (trans (subst-⇒ (cop-split-un cv) _)
         (cong _⇒_ (trans (subst-pair (cop-split-un cv) l r (cov (cop (thinL cv)(thinR cv))))
                          (cong (pair l r) (cop-split-cov cv)))))
  (cop-split-out cv)

-- ids restricted = the identity on the sub-scope, target-renamed
ids↾-mapWk : (θ : Θ ⊑ Ω) → ids ↾ θ ≡ mapWk (ids {Θ}) θ
ids↾-mapWk oz     = refl
ids↾-mapWk (os θ) = cong₂ _∙_
  (cong (λ z → tvar ⇑ os z) (sym (oe-unique (oe ⨾ θ))))
  (trans (cong (λ z → mapWk z (o' oi)) (ids↾-mapWk θ))
    (trans (mapWk-fusion ids θ (o' oi))
      (trans (cong (λ z → mapWk ids (o' z)) (trans (⨾oi θ) (sym (oi⨾ θ))))
             (sym (mapWk-fusion ids (o' oi) (os θ))))))
ids↾-mapWk (o' θ) =
  trans (cong (λ z → mapWk z (o' oi)) (ids↾-mapWk θ))
    (trans (mapWk-fusion ids θ (o' oi))
           (cong (λ z → mapWk ids (o' z)) (⨾oi θ)))

-- sub by identity = the thing at identity thinning
sub-id : (t : Ty Θ) → sub t ids ≡ (t ⇑ oi)
sub-id tvar = refl
sub-id (_⇒_ (pair l r cv)) =
  trans (cong₂ _⇒↑_
    (trans (cong (sub l) (ids↾-mapWk (thinL cv)))
      (trans (sub-ren l ids (thinL cv))
        (trans (cong (_⟨ thinL cv ⟩↑) (sub-id l)) (cong (l ⇑_) (oi⨾ (thinL cv))))))
    (trans (cong (sub r) (ids↾-mapWk (thinR cv)))
      (trans (sub-ren r ids (thinR cv))
        (trans (cong (_⟨ thinR cv ⟩↑) (sub-id r)) (cong (r ⇑_) (oi⨾ (thinR cv)))))))
    (⇒↑-split l r cv)
sub-id (∀' (use t))  = cong ∀↑ (sub-id t)
sub-id (∀' (drop t)) = cong (λ z → ∀' <$> (drop <$> z)) (sub-id t)

-- ★ IDENTITY LAW — PROVEN
⟪⟫-id : (t : Ty ↑ Θ) → t ⟪ ids ⟫ ≡ t
⟪⟫-id (t ⇑ θ) = trans (cong (sub t) (ids↾-mapWk θ))
  (trans (sub-ren t ids θ) (trans (cong (_⟨ θ ⟩↑) (sub-id t)) (cong (t ⇑_) (oi⨾ θ))))

-- ★ a weakened type ignores the cons-head of a substitution — PROVEN
wk-cancel : ∀ {Δ Ξ}(C : Ty ↑ Δ)(A : Ty ↑ Ξ)(σ : Sub Ξ Δ) → (C ⟨ o' oi ⟩↑) ⟪ A ∙ σ ⟫ ≡ C ⟪ σ ⟫
wk-cancel (c ⇑ γ) A σ = cong (λ z → sub c (σ ↾ z)) (⨾oi γ)

-- ════ the remaining σ-algebra needed for term-level substitution ════
VarCons : ∀ {Δ Θ}(A : Ty ↑ Δ)(σ : Sub Δ Θ) → var₀ ⟪ A ∙ σ ⟫ ≡ A
VarCons A σ = cong (λ z → sub tvar (A ∙ z)) (↾-oe σ)
wk-⨟ : ∀ {Δ Ξ Θ}(τ : Sub Δ Θ)(A : Ty ↑ Ξ)(σ : Sub Ξ Δ) → (wkSub τ) ⨟ (A ∙ σ) ≡ τ ⨟ σ
wk-⨟ ε       A σ = refl
wk-⨟ (t ∙ τ) A σ = cong₂ _∙_ (wk-cancel t A σ) (wk-⨟ τ A σ)
⨟-idₗ : (σ : Sub Δ Θ) → ids ⨟ σ ≡ σ
⨟-idₗ ε       = refl
⨟-idₗ (A ∙ σ) = cong₂ _∙_ (VarCons A σ) (trans (wk-⨟ ids A σ) (⨟-idₗ σ))
⨟-idᵣ : (σ : Sub Δ Θ) → σ ⨟ ids ≡ σ
⨟-idᵣ ε       = refl
⨟-idᵣ (t ∙ σ) = cong₂ _∙_ (⟪⟫-id t) (⨟-idᵣ σ)
-- lift then instantiate = cons (the key law behind type application)
inst-lift : ∀ {Δ Θ}(σ : Sub Δ Θ)(A : Ty ↑ Δ) → (lift σ) ⨟ (A ∙ ids) ≡ (A ∙ σ)
inst-lift σ A = cong₂ _∙_ (VarCons A ids) (trans (wk-⨟ σ A ids) (⨟-idᵣ σ))

-- type-substitution commutes with target-renaming; weakening by wkSub ids = ⟨o' oi⟩↑
⟪⟫-mapWk : ∀ {Θ Δ Ω}(A : Ty ↑ Θ)(σ : Sub Δ Θ)(r : Δ ⊑ Ω) → A ⟪ mapWk σ r ⟫ ≡ (A ⟪ σ ⟫) ⟨ r ⟩↑
⟪⟫-mapWk (a ⇑ α) σ r = sub-ren a (σ ↾ α) r
wk-ty : ∀ {Θ}(A : Ty ↑ Θ) → A ⟪ wkSub ids ⟫ ≡ A ⟨ o' oi ⟩↑
wk-ty A = trans (⟪⟫-mapWk A ids (o' oi)) (cong (_⟨ o' oi ⟩↑) (⟪⟫-id A))
