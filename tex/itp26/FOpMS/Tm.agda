{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- GENUINELY MULTI-SORTED co-de-Bruijn System F.  ONE scope Θ : List Sort holding
-- BOTH expr and type variables; ONE term family Tm : Sort → Scope → Set; ONE
-- vector substitution Sub Δ Θ acting on ALL sorts at once.  The faithful analog of
-- the multi-sorted functional systemf.agda (Sort = expr|type|kind, unified _⋯ˢ_).
--
-- H1 re-representation (from FOpH1): `sub'` THREADS an outer thinning θ and restricts
-- σ EXACTLY ONCE, at the variable leaf (via `look`), composing cover thinnings through
-- the CONFLUENT ⨾ (Orientation A).  Consequence: the form-distribution laws for every
-- constructor (arrow, application, ×ᴿ formers) become REFL, and the ∀/Λ/λ `use` cases
-- become REFL — Fac-L/Fac-R fire on the composed thinning argument.
-- ════════════════════════════════════════════════════════════════════════════
module FOpMS.Tm where
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Agda.Builtin.Equality.Rewrite
open import FOpMS.ThinRw   -- Sort, Scope, _⊑_, _⨾_, oi, oe, Pos, Cover, cop, Fac-*, _↑_, _×ᴿ_, Bind

private variable
  s s′ : Sort
  Γ Δ Ξ Ω Θ Γₗ Γᵣ sup : Scope

-- ════ the FULL multi-sorted System F syntax as ONE co-de-Bruijn family ════
-- Variables via the sorted `Pos`-carrier (a Tm s (s ∷ []) is a single var of sort s).
-- Cross-sort binders via Bind expr / Bind type.  Relevant pairs via _×ᴿ_.
data Tm : Sort → Scope → Set where
  -- variable of sort s (its scope is the singleton support s ∷ [])
  var  : Tm s (s ∷ [])
  -- type formers (sort type)
  _⇒_  : (Tm type ×ᴿ Tm type) Θ → Tm type Θ                -- arrow
  ∀'   : (Tm kind ×ᴿ Bind type (Tm type)) Θ → Tm type Θ    -- ∀[α∶ k ] t : binds a TYPE var in a type
  -- expr formers (sort expr)
  lam  : (Tm type ×ᴿ Bind expr (Tm expr)) Θ → Tm expr Θ    -- λx : domain annotation ×ᴿ body binding an EXPR var
  Lam  : Bind type (Tm expr) Θ → Tm expr Θ                 -- Λα : binds a TYPE var in an expr
  app  : (Tm expr ×ᴿ Tm expr) Θ → Tm expr Θ               -- e₁ · e₂
  App  : (Tm expr ×ᴿ Tm type) Θ → Tm expr Θ               -- e • t  (expr applied to a type)
  -- kind former
  ⋆    : Tm kind []

-- ════ smart constructors (build the ⇑-carrier former from ⇑-carrier arguments) ════
_⇒↑_ : Tm type ↑ Δ → Tm type ↑ Δ → Tm type ↑ Δ
A ⇒↑ B = _⇒_ <$> pairUp A B
infixr 6 _⇒↑_
∀↑ : Tm kind ↑ Δ → Tm type ↑ (type ∷ Δ) → Tm type ↑ Δ
∀↑ K X = ∀' <$> pairUp K (bindUp X)
lam↑ : Tm type ↑ Δ → Tm expr ↑ (expr ∷ Δ) → Tm expr ↑ Δ
lam↑ A X = lam <$> pairUp A (bindUp X)
Lam↑ : Tm expr ↑ (type ∷ Δ) → Tm expr ↑ Δ
Lam↑ X = Lam <$> bindUp X
app↑ : Tm expr ↑ Δ → Tm expr ↑ Δ → Tm expr ↑ Δ
app↑ E₁ E₂ = app <$> pairUp E₁ E₂
App↑ : Tm expr ↑ Δ → Tm type ↑ Δ → Tm expr ↑ Δ
App↑ E T = App <$> pairUp E T
var↑ : Tm s ↑ (s ∷ Δ)
var↑ = var ⇑ os oe

-- ════ the UNIFIED vector substitution — ONE entry per position, SORTED ════
data Sub (Δ : Scope) : Scope → Set where
  ε   : Sub Δ []
  _∙_ : Tm s ↑ Δ → Sub Δ Θ → Sub Δ (s ∷ Θ)
infixr 5 _∙_
_↾_ : Sub Δ Θ → sup ⊑ Θ → Sub Δ sup
ε ↾ oz = ε ; (t ∙ σ) ↾ os θ = t ∙ (σ ↾ θ) ; (t ∙ σ) ↾ o' θ = σ ↾ θ
infixl 8 _↾_
-- direct variable lookup: the SINGLE ↾ (restrict σ by a Pos) collapsed to a leaf pick
look : Pos Θ s → Sub Δ Θ → Tm s ↑ Δ
look (os θ) (t ∙ σ) = t
look (o' θ) (t ∙ σ) = look θ σ
-- target-renaming of a substitution (subsumes wkSub); the general naturality carrier
mapWk : Sub Δ Θ → Δ ⊑ Ω → Sub Ω Θ
mapWk ε       r = ε
mapWk (t ∙ σ) r = (t ⟨ r ⟩↑) ∙ mapWk σ r
mapWk-↾ : (σ : Sub Δ Θ)(r : Δ ⊑ Ω)(θ : sup ⊑ Θ) → mapWk (σ ↾ θ) r ≡ mapWk σ r ↾ θ
mapWk-↾ ε r oz = refl
mapWk-↾ (t ∙ σ) r (os θ) = cong (_ ∙_) (mapWk-↾ σ r θ)
mapWk-↾ (t ∙ σ) r (o' θ) = mapWk-↾ σ r θ
{-# REWRITE mapWk-↾ #-}
wkSub : Sub Δ Θ → Sub (s ∷ Δ) Θ
wkSub {s = s} σ = mapWk σ (o' oi)
-- lift over a SORTED binder: fresh var of sort s in front, everything else weakened
lift : Sub Δ Θ → Sub (s ∷ Δ) (s ∷ Θ)
lift {s = s} σ = var↑ ∙ wkSub σ

-- ════ H1: sub' THREADS the outer thinning, restricting σ ONCE (at `look`) ════
-- the cover thinnings compose via the CONFLUENT ⨾ (never a double ↾).  ONE function
-- across ALL sorts — the multi-sorted unification.  `subBind` handles a SORTED binder:
-- `use` recurses under a fresh var (lift σ, os θ); `drop` recurses then weakens.
sub'    : Tm s Θ → Θ ⊑ Δ → Sub Ξ Δ → Tm s ↑ Ξ
subBind : ∀ {s′ s Θ Δ Ξ} → Bind s′ (Tm s) Θ → Θ ⊑ Δ → Sub Ξ Δ → Tm s ↑ (s′ ∷ Ξ)

sub' var                  θ σ = look θ σ
sub' (_⇒_ (pair l r cv))  θ σ = (sub' l (thinL cv ⨾ θ) σ) ⇒↑ (sub' r (thinR cv ⨾ θ) σ)
sub' (∀' (pair k b cv))   θ σ = ∀↑ (sub' k (thinL cv ⨾ θ) σ) (subBind b (thinR cv ⨾ θ) σ)
sub' (lam (pair a b cv))  θ σ = lam↑ (sub' a (thinL cv ⨾ θ) σ) (subBind b (thinR cv ⨾ θ) σ)
sub' (Lam b)              θ σ = Lam↑ (subBind b θ σ)
sub' (app (pair l r cv))  θ σ = app↑ (sub' l (thinL cv ⨾ θ) σ) (sub' r (thinR cv ⨾ θ) σ)
sub' (App (pair e t cv))  θ σ = App↑ (sub' e (thinL cv ⨾ θ) σ) (sub' t (thinR cv ⨾ θ) σ)
sub' ⋆                    θ σ = ⋆ ⇑ oe

subBind (use x)  θ σ = sub' x (os θ) (lift σ)                    -- bound var occurs: lift
subBind (drop x) θ σ = (sub' x θ σ) ⟨ o' oi ⟩↑                   -- bound var absent: weaken result

_⟪_⟫ : Tm s ↑ Θ → Sub Δ Θ → Tm s ↑ Δ
(t ⇑ θ) ⟪ σ ⟫ = sub' t θ σ
infixl 8 _⟪_⟫
_⨟_ : Sub Δ Θ → Sub Ξ Δ → Sub Ξ Θ
ε ⨟ τ = ε ; (t ∙ σ) ⨟ τ = (t ⟪ τ ⟫) ∙ (σ ⨟ τ)
infixl 6 _⨟_

-- ════════════════════════════════════════════════════════════════════════════
-- σ-LAWS — PROVEN (never postulated).  Generalisation of FOpH1/Ty to multi-sorted.
-- ════════════════════════════════════════════════════════════════════════════

-- ════ FORM-DISTRIBUTION LAWS — REFL via H1 threading ════
-- For every pair-based former, the smart constructor packs the two subterms with a
-- fresh cop; sub' unpacks with thinL/thinR ⨾ out and Fac-L/Fac-R (REGISTERED) fire
-- on the composed thinning argument BEFORE sub' inspects the subterm.  ⇒ all REFL.
⟪⟫-⇒↑ : ∀ {Δ Ξ}(A B : Tm type ↑ Δ)(τ : Sub Ξ Δ) → (A ⇒↑ B) ⟪ τ ⟫ ≡ (A ⟪ τ ⟫) ⇒↑ (B ⟪ τ ⟫)
⟪⟫-⇒↑ (a ⇑ α)(b ⇑ β) τ = refl
⟪⟫-app↑ : ∀ {Δ Ξ}(E₁ E₂ : Tm expr ↑ Δ)(τ : Sub Ξ Δ) → (app↑ E₁ E₂) ⟪ τ ⟫ ≡ app↑ (E₁ ⟪ τ ⟫) (E₂ ⟪ τ ⟫)
⟪⟫-app↑ (a ⇑ α)(b ⇑ β) τ = refl
⟪⟫-App↑ : ∀ {Δ Ξ}(E : Tm expr ↑ Δ)(T : Tm type ↑ Δ)(τ : Sub Ξ Δ) → (App↑ E T) ⟪ τ ⟫ ≡ App↑ (E ⟪ τ ⟫) (T ⟪ τ ⟫)
⟪⟫-App↑ (e ⇑ α)(t ⇑ β) τ = refl

-- ∀ / lam distribute (use case: bound var actually occurs) — REFL (H1)
⟪⟫-∀↑-use : ∀ {Δ Ξ}(K : Tm kind ↑ Δ)(x : Tm type (type ∷ sup))(ξ : sup ⊑ Δ)(τ : Sub Ξ Δ)
          → (∀↑ K (x ⇑ os ξ)) ⟪ τ ⟫ ≡ ∀↑ (K ⟪ τ ⟫) ((x ⇑ os ξ) ⟪ lift τ ⟫)
⟪⟫-∀↑-use K x ξ τ = refl
⟪⟫-lam↑-use : ∀ {Δ Ξ}(A : Tm type ↑ Δ)(x : Tm expr (expr ∷ sup))(ξ : sup ⊑ Δ)(τ : Sub Ξ Δ)
            → (lam↑ A (x ⇑ os ξ)) ⟪ τ ⟫ ≡ lam↑ (A ⟪ τ ⟫) ((x ⇑ os ξ) ⟪ lift τ ⟫)
⟪⟫-lam↑-use A x ξ τ = refl
⟪⟫-Lam↑-use : ∀ {Δ Ξ}(x : Tm expr (type ∷ sup))(ξ : sup ⊑ Δ)(τ : Sub Ξ Δ)
            → (Lam↑ (x ⇑ os ξ)) ⟪ τ ⟫ ≡ Lam↑ ((x ⇑ os ξ) ⟪ lift τ ⟫)
⟪⟫-Lam↑-use x ξ τ = refl

-- ════ cop-coherence tower — cop naturality, ALL PROVEN (subst-based) ════
-- un is homogeneous (Scope≡Scope): the trick that avoids het-equality.  Sort-agnostic.
cop-un : (α : Γₗ ⊑ Δ)(β : Γᵣ ⊑ Δ)(ψ : Δ ⊑ Ω) → un (cop (α ⨾ ψ)(β ⨾ ψ)) ≡ un (cop α β)
cop-un α β (o' ψ) = cop-un α β ψ
cop-un oz oz oz = refl
cop-un (os α)(os β)(os {s = r} ψ) = cong (r ∷_) (cop-un α β ψ)
cop-un (os α)(o' β)(os {s = r} ψ) = cong (r ∷_) (cop-un α β ψ)
cop-un (o' α)(os β)(os {s = r} ψ) = cong (r ∷_) (cop-un α β ψ)
cop-un (o' α)(o' β)(os ψ) = cop-un α β ψ
push-o' : ∀ {r W u₁ u₂}(p : u₁ ≡ u₂)(x : u₁ ⊑ W) → subst (_⊑ (r ∷ W)) p (o' x) ≡ o' (subst (_⊑ W) p x)
push-o' refl x = refl
push-os : ∀ {r W u₁ u₂}(q : u₁ ≡ u₂)(x : u₁ ⊑ W) → subst (_⊑ (r ∷ W)) (cong (r ∷_) q) (os x) ≡ os (subst (_⊑ W) q x)
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
  where subcong-bb : ∀ {r Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁)
                   → subst (Cover (r ∷ Gl)(r ∷ Gr)) (cong (r ∷_) p) (bb c) ≡ bb (subst (Cover Gl Gr) p c)
        subcong-bb refl c = refl
cop-cov (os α)(o' β)(os ψ) = trans (subcong-ll (cop-un α β ψ) _) (cong ll (cop-cov α β ψ))
  where subcong-ll : ∀ {r Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁)
                   → subst (Cover (r ∷ Gl) Gr) (cong (r ∷_) p) (ll c) ≡ ll (subst (Cover Gl Gr) p c)
        subcong-ll refl c = refl
cop-cov (o' α)(os β)(os ψ) = trans (subcong-rr (cop-un α β ψ) _) (cong rr (cop-cov α β ψ))
  where subcong-rr : ∀ {r Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁)
                   → subst (Cover Gl (r ∷ Gr)) (cong (r ∷_) p) (rr c) ≡ rr (subst (Cover Gl Gr) p c)
        subcong-rr refl c = refl
cop-cov (o' α)(o' β)(os ψ) = cop-cov α β ψ

-- record congruence for _↑_ (scp may differ, transported)
↑≡ : ∀ {T : Scope → Set}{Δ : Scope}{s₁ s₂ : Scope}(p : s₁ ≡ s₂){t₁ : T s₁}{t₂ : T s₂}{θ₁ : s₁ ⊑ Δ}{θ₂ : s₂ ⊑ Δ}
   → subst T p t₁ ≡ t₂ → subst (_⊑ Δ) p θ₁ ≡ θ₂ → (t₁ ⇑ θ₁) ≡ (t₂ ⇑ θ₂)
↑≡ refl refl refl = refl
subst-sym : ∀ {A : Set}{P : A → Set}{x y}(p : x ≡ y){u : P x}{v : P y} → subst P p u ≡ v → subst P (sym p) v ≡ u
subst-sym refl refl = refl
subst-pair : ∀ {S T : Scope → Set}{Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(a : S Gl)(b : T Gr)(c : Cover Gl Gr u₁)
           → subst (S ×ᴿ T) p (pair a b c) ≡ pair a b (subst (Cover Gl Gr) p c)
subst-pair refl a b c = refl

-- pairUp distributes over thinning — PROVEN via cop naturality (sort/type-agnostic)
pairUp-⟨⟩ : ∀ {S T Δ Ω}(A : S ↑ Δ)(B : T ↑ Δ)(ψ : Δ ⊑ Ω) → (pairUp A B) ⟨ ψ ⟩↑ ≡ pairUp (A ⟨ ψ ⟩↑) (B ⟨ ψ ⟩↑)
pairUp-⟨⟩ (a ⇑ α)(b ⇑ β) ψ =
  ↑≡ (sym (cop-un α β ψ))
     (trans (subst-pair (sym (cop-un α β ψ)) a b (cov (cop α β)))
            (cong (pair a b) (subst-sym (cop-un α β ψ) (cop-cov α β ψ))))
     (subst-sym (cop-un α β ψ) (cop-out α β ψ))

-- ════ ⟨⟩ distributes over each former — PROVEN ════
⟨⟩-⇒↑ : ∀ {Δ Ω}(A B : Tm type ↑ Δ)(ψ : Δ ⊑ Ω) → (A ⇒↑ B) ⟨ ψ ⟩↑ ≡ (A ⟨ ψ ⟩↑) ⇒↑ (B ⟨ ψ ⟩↑)
⟨⟩-⇒↑ A B ψ = cong (_⇒_ <$>_) (pairUp-⟨⟩ A B ψ)
⟨⟩-app↑ : ∀ {Δ Ω}(E₁ E₂ : Tm expr ↑ Δ)(ψ : Δ ⊑ Ω) → (app↑ E₁ E₂) ⟨ ψ ⟩↑ ≡ app↑ (E₁ ⟨ ψ ⟩↑) (E₂ ⟨ ψ ⟩↑)
⟨⟩-app↑ E₁ E₂ ψ = cong (app <$>_) (pairUp-⟨⟩ E₁ E₂ ψ)
⟨⟩-App↑ : ∀ {Δ Ω}(E : Tm expr ↑ Δ)(T : Tm type ↑ Δ)(ψ : Δ ⊑ Ω) → (App↑ E T) ⟨ ψ ⟩↑ ≡ App↑ (E ⟨ ψ ⟩↑) (T ⟨ ψ ⟩↑)
⟨⟩-App↑ E T ψ = cong (App <$>_) (pairUp-⟨⟩ E T ψ)
-- bindUp distributes over thinning (cases on the thinning head)
bindUp-⟨⟩ : ∀ {s′ T Δ Ω}(X : T ↑ (s′ ∷ Δ))(ψ : Δ ⊑ Ω) → (bindUp X) ⟨ ψ ⟩↑ ≡ bindUp (X ⟨ os ψ ⟩↑)
bindUp-⟨⟩ (x ⇑ os θ) ψ = refl
bindUp-⟨⟩ (x ⇑ o' θ) ψ = refl
⟨⟩-∀↑ : ∀ {Δ Ω}(K : Tm kind ↑ Δ)(X : Tm type ↑ (type ∷ Δ))(ψ : Δ ⊑ Ω) → (∀↑ K X) ⟨ ψ ⟩↑ ≡ ∀↑ (K ⟨ ψ ⟩↑) (X ⟨ os ψ ⟩↑)
⟨⟩-∀↑ K X ψ = trans (cong (∀' <$>_) (pairUp-⟨⟩ K (bindUp X) ψ)) (cong (λ z → ∀' <$> pairUp (K ⟨ ψ ⟩↑) z) (bindUp-⟨⟩ X ψ))
⟨⟩-lam↑ : ∀ {Δ Ω}(A : Tm type ↑ Δ)(X : Tm expr ↑ (expr ∷ Δ))(ψ : Δ ⊑ Ω) → (lam↑ A X) ⟨ ψ ⟩↑ ≡ lam↑ (A ⟨ ψ ⟩↑) (X ⟨ os ψ ⟩↑)
⟨⟩-lam↑ A X ψ = trans (cong (lam <$>_) (pairUp-⟨⟩ A (bindUp X) ψ)) (cong (λ z → lam <$> pairUp (A ⟨ ψ ⟩↑) z) (bindUp-⟨⟩ X ψ))
⟨⟩-Lam↑ : ∀ {Δ Ω}(X : Tm expr ↑ (type ∷ Δ))(ψ : Δ ⊑ Ω) → (Lam↑ X) ⟨ ψ ⟩↑ ≡ Lam↑ (X ⟨ os ψ ⟩↑)
⟨⟩-Lam↑ X ψ = cong (Lam <$>_) (bindUp-⟨⟩ X ψ)

-- ════ ⨾ / target-renaming plumbing ════
oe-unique : (x : [] ⊑ Γ) → x ≡ oe
oe-unique oz = refl
oe-unique (o' x) = cong o' (oe-unique x)
⟨⟩-⨾ : ∀ {T Δ Ξ Ω}(t : T ↑ Δ)(r₁ : Δ ⊑ Ξ)(r₂ : Ξ ⊑ Ω) → t ⟨ r₁ ⟩↑ ⟨ r₂ ⟩↑ ≡ t ⟨ r₁ ⨾ r₂ ⟩↑
⟨⟩-⨾ (t ⇑ θ) r₁ r₂ = cong (t ⇑_) (⨾⨾ θ r₁ r₂)
mapWk-fusion : (σ : Sub Δ Θ)(r₁ : Δ ⊑ Ξ)(r₂ : Ξ ⊑ Ω) → mapWk (mapWk σ r₁) r₂ ≡ mapWk σ (r₁ ⨾ r₂)
mapWk-fusion ε r₁ r₂ = refl
mapWk-fusion (t ∙ σ) r₁ r₂ = cong₂ _∙_ (⟨⟩-⨾ t r₁ r₂) (mapWk-fusion σ r₁ r₂)
lift-mapWk : (σ : Sub Δ Θ)(r : Δ ⊑ Ω) → lift {s = s} (mapWk σ r) ≡ mapWk (lift {s = s} σ) (os r)
lift-mapWk {s = s} σ r = cong₂ _∙_
  (cong (λ z → var ⇑ os z) (sym (oe-unique (oe ⨾ r))))
  (trans (mapWk-fusion σ r (o' oi))
    (trans (cong (λ z → mapWk σ (o' z)) (trans (⨾oi r) (sym (oi⨾ r))))
           (sym (mapWk-fusion σ (o' oi) (os r)))))

-- ════ renaming naturality of sub' (subsumes weakening) — PROVEN ════
look-mapWk : (θ : Pos Θ s)(σ : Sub Δ Θ)(r : Δ ⊑ Ω) → look θ (mapWk σ r) ≡ (look θ σ) ⟨ r ⟩↑
look-mapWk (os θ) (t ∙ σ) r = refl
look-mapWk (o' θ) (t ∙ σ) r = look-mapWk θ σ r

sub'-ren    : (t : Tm s Θ)(θ : Θ ⊑ Δ)(σ : Sub Ξ Δ)(r : Ξ ⊑ Ω) → sub' t θ (mapWk σ r) ≡ (sub' t θ σ) ⟨ r ⟩↑
subBind-ren : ∀ {s′ s Θ Δ Ξ Ω}(b : Bind s′ (Tm s) Θ)(θ : Θ ⊑ Δ)(σ : Sub Ξ Δ)(r : Ξ ⊑ Ω)
            → subBind b θ (mapWk σ r) ≡ (subBind b θ σ) ⟨ os r ⟩↑
sub'-ren var θ σ r = look-mapWk θ σ r
sub'-ren (_⇒_ (pair l rt cv)) θ σ r =
  trans (cong₂ _⇒↑_ (sub'-ren l (thinL cv ⨾ θ) σ r) (sub'-ren rt (thinR cv ⨾ θ) σ r))
        (sym (⟨⟩-⇒↑ _ _ r))
sub'-ren (∀' (pair k b cv)) θ σ r =
  trans (cong₂ ∀↑ (sub'-ren k (thinL cv ⨾ θ) σ r) (subBind-ren b (thinR cv ⨾ θ) σ r))
        (sym (⟨⟩-∀↑ (sub' k (thinL cv ⨾ θ) σ) (subBind b (thinR cv ⨾ θ) σ) r))
sub'-ren (lam (pair a b cv)) θ σ r =
  trans (cong₂ lam↑ (sub'-ren a (thinL cv ⨾ θ) σ r) (subBind-ren b (thinR cv ⨾ θ) σ r))
        (sym (⟨⟩-lam↑ (sub' a (thinL cv ⨾ θ) σ) (subBind b (thinR cv ⨾ θ) σ) r))
sub'-ren (Lam b) θ σ r =
  trans (cong Lam↑ (subBind-ren b θ σ r)) (sym (⟨⟩-Lam↑ (subBind b θ σ) r))
sub'-ren (app (pair l rt cv)) θ σ r =
  trans (cong₂ app↑ (sub'-ren l (thinL cv ⨾ θ) σ r) (sub'-ren rt (thinR cv ⨾ θ) σ r))
        (sym (⟨⟩-app↑ _ _ r))
sub'-ren (App (pair e t cv)) θ σ r =
  trans (cong₂ App↑ (sub'-ren e (thinL cv ⨾ θ) σ r) (sub'-ren t (thinR cv ⨾ θ) σ r))
        (sym (⟨⟩-App↑ _ _ r))
sub'-ren ⋆ θ σ r = cong (⋆ ⇑_) (sym (oe-unique (oe ⨾ r)))
subBind-ren (use x)  θ σ r =
  trans (cong (λ z → sub' x (os θ) z) (lift-mapWk σ r)) (sub'-ren x (os θ) (lift σ) (os r))
subBind-ren (drop x) θ σ r =
  trans (cong (_⟨ o' oi ⟩↑) (sub'-ren x θ σ r))
    (trans (⟨⟩-⨾ (sub' x θ σ) r (o' oi))
      (trans (cong (sub' x θ σ ⟨_⟩↑) (cong o' (trans (⨾oi r) (sym (oi⨾ r))))) (sym (⟨⟩-⨾ (sub' x θ σ) (o' oi) (os r)))))

-- ════ restriction = thinning composition (the single-↾ identity, PROVEN not registered) ════
-- ↾-⨾ is the non-confluent restriction-composition law; kept PROVEN (not a rewrite).
↾-⨾ : (σ : Sub Δ Θ)(θ : sup ⊑ Θ)(φ : Γ ⊑ sup) → (σ ↾ θ) ↾ φ ≡ σ ↾ (φ ⨾ θ)
↾-⨾ ε oz oz = refl
↾-⨾ (t ∙ σ)(os θ)(os φ) = cong (t ∙_) (↾-⨾ σ θ φ)
↾-⨾ (t ∙ σ)(os θ)(o' φ) = ↾-⨾ σ θ φ
↾-⨾ (t ∙ σ)(o' θ) φ     = ↾-⨾ σ θ φ

sub'-↾    : (t : Tm s Θ)(θ : Θ ⊑ Δ)(φ : Δ ⊑ Ω)(σ : Sub Ξ Ω) → sub' t θ (σ ↾ φ) ≡ sub' t (θ ⨾ φ) σ
subBind-↾ : ∀ {s′ s Θ Δ Ω Ξ}(b : Bind s′ (Tm s) Θ)(θ : Θ ⊑ Δ)(φ : Δ ⊑ Ω)(σ : Sub Ξ Ω)
          → subBind b θ (σ ↾ φ) ≡ subBind b (θ ⨾ φ) σ
sub'-↾ var θ φ σ = go θ φ σ
  where go : (θ : Pos Θ s)(φ : Θ ⊑ Ω)(σ : Sub Ξ Ω) → look θ (σ ↾ φ) ≡ look (θ ⨾ φ) σ
        go θ      (o' φ) (a ∙ σ) = go θ φ σ
        go (os θ) (os φ) (a ∙ σ) = refl
        go (o' θ) (os φ) (a ∙ σ) = go θ φ σ
sub'-↾ (_⇒_ (pair l r cv)) θ φ σ =
  cong₂ _⇒↑_
    (trans (sub'-↾ l (thinL cv ⨾ θ) φ σ) (cong (λ z → sub' l z σ) (⨾⨾ (thinL cv) θ φ)))
    (trans (sub'-↾ r (thinR cv ⨾ θ) φ σ) (cong (λ z → sub' r z σ) (⨾⨾ (thinR cv) θ φ)))
sub'-↾ (∀' (pair k b cv)) θ φ σ =
  cong₂ ∀↑
    (trans (sub'-↾ k (thinL cv ⨾ θ) φ σ) (cong (λ z → sub' k z σ) (⨾⨾ (thinL cv) θ φ)))
    (trans (subBind-↾ b (thinR cv ⨾ θ) φ σ) (cong (λ z → subBind b z σ) (⨾⨾ (thinR cv) θ φ)))
sub'-↾ (lam (pair a b cv)) θ φ σ =
  cong₂ lam↑
    (trans (sub'-↾ a (thinL cv ⨾ θ) φ σ) (cong (λ z → sub' a z σ) (⨾⨾ (thinL cv) θ φ)))
    (trans (subBind-↾ b (thinR cv ⨾ θ) φ σ) (cong (λ z → subBind b z σ) (⨾⨾ (thinR cv) θ φ)))
sub'-↾ (Lam b) θ φ σ = cong Lam↑ (subBind-↾ b θ φ σ)
sub'-↾ (app (pair l r cv)) θ φ σ =
  cong₂ app↑
    (trans (sub'-↾ l (thinL cv ⨾ θ) φ σ) (cong (λ z → sub' l z σ) (⨾⨾ (thinL cv) θ φ)))
    (trans (sub'-↾ r (thinR cv ⨾ θ) φ σ) (cong (λ z → sub' r z σ) (⨾⨾ (thinR cv) θ φ)))
sub'-↾ (App (pair e t cv)) θ φ σ =
  cong₂ App↑
    (trans (sub'-↾ e (thinL cv ⨾ θ) φ σ) (cong (λ z → sub' e z σ) (⨾⨾ (thinL cv) θ φ)))
    (trans (sub'-↾ t (thinR cv ⨾ θ) φ σ) (cong (λ z → sub' t z σ) (⨾⨾ (thinR cv) θ φ)))
sub'-↾ ⋆ θ φ σ = refl
subBind-↾ (use x)  θ φ σ = sub'-↾ x (os θ) (os φ) (lift σ)
subBind-↾ (drop x) θ φ σ = cong (_⟨ o' oi ⟩↑) (sub'-↾ x θ φ σ)

-- ════ general binder distribution (drop case via weakening naturality) ════
↾-oi : (σ : Sub Δ Θ) → σ ↾ oi ≡ σ
↾-oi ε       = refl
↾-oi (t ∙ σ) = cong (t ∙_) (↾-oi σ)
-- σ acting on a DROPPED bound var: skip the head of lift, then weaken
sub'-drop : (y : Tm s Θ)(ξ : Θ ⊑ Δ)(τ : Sub Ξ Δ) → sub' y (o' ξ) (lift {s = s′} τ) ≡ (sub' y ξ τ) ⟨ o' oi ⟩↑
sub'-drop {s′ = s′} y ξ τ =
  trans (cong (λ z → sub' y z (lift τ)) (cong o' (sym (⨾oi ξ))))
    (trans (sym (sub'-↾ y ξ (o' oi) (lift τ)))
      (trans (cong (sub' y ξ) (↾-oi (wkSub τ))) (sub'-ren y ξ τ (o' oi))))
-- ════ GENERAL binder distribution: use case REFL, drop case via sub'-drop ════
-- These generalise ⟪⟫-∀↑-use to arbitrary bind heads; the DROP case is the residual
-- weakening-naturality bridge (NOT refl — same family as single-sorted ⟪⟫-∀↑-drop).
-- Because ∀↑/lam↑ carry the use/drop head through unchanged (the binder is a separate
-- cop component from K/A), the drop case reduces to sub'-drop directly (no ∀↑-wk needed).
⟪⟫-∀↑ : ∀ {Δ Ξ}(K : Tm kind ↑ Δ)(Y : Tm type ↑ (type ∷ Δ))(τ : Sub Ξ Δ)
      → (∀↑ K Y) ⟪ τ ⟫ ≡ ∀↑ (K ⟪ τ ⟫) (Y ⟪ lift τ ⟫)
⟪⟫-∀↑ K (y ⇑ os ξ) τ = refl
⟪⟫-∀↑ K (y ⇑ o' ξ) τ = cong (∀↑ (K ⟪ τ ⟫)) (sym (sub'-drop y ξ τ))
⟪⟫-lam↑ : ∀ {Δ Ξ}(A : Tm type ↑ Δ)(Y : Tm expr ↑ (expr ∷ Δ))(τ : Sub Ξ Δ)
        → (lam↑ A Y) ⟪ τ ⟫ ≡ lam↑ (A ⟪ τ ⟫) (Y ⟪ lift τ ⟫)
⟪⟫-lam↑ A (y ⇑ os ξ) τ = refl
⟪⟫-lam↑ A (y ⇑ o' ξ) τ = cong (lam↑ (A ⟪ τ ⟫)) (sym (sub'-drop y ξ τ))
⟪⟫-Lam↑ : ∀ {Δ Ξ}(Y : Tm expr ↑ (type ∷ Δ))(τ : Sub Ξ Δ)
        → (Lam↑ Y) ⟪ τ ⟫ ≡ Lam↑ (Y ⟪ lift τ ⟫)
⟪⟫-Lam↑ (y ⇑ os ξ) τ = refl
⟪⟫-Lam↑ (y ⇑ o' ξ) τ = cong Lam↑ (sym (sub'-drop y ξ τ))

-- ════ Clos core: substituting then substituting = by the composite ════
look-⨟ : (θ : Pos Θ s)(ρ : Sub Δ Θ)(τ : Sub Ξ Δ) → (look θ ρ) ⟪ τ ⟫ ≡ look θ (ρ ⨟ τ)
look-⨟ (os θ) (t ∙ ρ) τ = refl
look-⨟ (o' θ) (t ∙ ρ) τ = look-⨟ θ ρ τ
↾-oe : (σ : Sub Δ Θ) → σ ↾ oe ≡ ε
↾-oe ε       = refl
↾-oe (t ∙ σ) = ↾-oe σ
var₀-lift : ∀ {Δ Ξ}(τ : Sub Ξ Δ) → var↑ {s = s} ⟪ lift τ ⟫ ≡ var↑
var₀-lift τ = refl
wk-⟪⟫ : ∀ {Δ Ξ}(u : Tm s ↑ Δ)(τ : Sub Ξ Δ) → (u ⟨ o' oi ⟩↑) ⟪ lift {s = s′} τ ⟫ ≡ (u ⟪ τ ⟫) ⟨ o' oi ⟩↑
wk-⟪⟫ (x ⇑ θ) τ = trans (cong (λ z → sub' x z (lift τ)) (cong o' (⨾oi θ))) (sub'-drop x θ τ)
wk-⨟-lift : (ρ : Sub Δ Θ)(τ : Sub Ξ Δ) → wkSub {s = s′} ρ ⨟ lift {s = s′} τ ≡ wkSub (ρ ⨟ τ)
wk-⨟-lift ε       τ = refl
wk-⨟-lift (u ∙ ρ) τ = cong₂ _∙_ (wk-⟪⟫ u τ) (wk-⨟-lift ρ τ)
lift-⨟ : (ρ : Sub Δ Θ)(τ : Sub Ξ Δ) → lift {s = s′} ρ ⨟ lift {s = s′} τ ≡ lift (ρ ⨟ τ)
lift-⨟ ρ τ = cong₂ _∙_ (var₀-lift τ) (wk-⨟-lift ρ τ)

-- subBind-⨟: the subBinder result, further substituted under lift, = subBind of ρ⨟τ.
-- use → recurse under lift + lift-⨟ ; drop → the sub' pushes through the weakening (wk-⟪⟫).
sub'-⨟    : ∀ {Θ Δ Ω Ξ}(t : Tm s Θ)(θ : Θ ⊑ Δ)(ρ : Sub Ω Δ)(τ : Sub Ξ Ω)
          → (sub' t θ ρ) ⟪ τ ⟫ ≡ sub' t θ (ρ ⨟ τ)
subBind-⨟ : ∀ {s′ s Θ Δ Ω Ξ}(b : Bind s′ (Tm s) Θ)(θ : Θ ⊑ Δ)(ρ : Sub Ω Δ)(τ : Sub Ξ Ω)
          → (subBind b θ ρ) ⟪ lift {s = s′} τ ⟫ ≡ subBind b θ (ρ ⨟ τ)
sub'-⨟ var θ ρ τ = look-⨟ θ ρ τ
sub'-⨟ (_⇒_ (pair l rt cv)) θ ρ τ =
  trans (⟪⟫-⇒↑ (sub' l (thinL cv ⨾ θ) ρ) (sub' rt (thinR cv ⨾ θ) ρ) τ)
        (cong₂ _⇒↑_ (sub'-⨟ l (thinL cv ⨾ θ) ρ τ) (sub'-⨟ rt (thinR cv ⨾ θ) ρ τ))
sub'-⨟ (∀' (pair k b cv)) θ ρ τ =
  trans (⟪⟫-∀↑ (sub' k (thinL cv ⨾ θ) ρ) (subBind b (thinR cv ⨾ θ) ρ) τ)
        (cong₂ ∀↑ (sub'-⨟ k (thinL cv ⨾ θ) ρ τ) (subBind-⨟ b (thinR cv ⨾ θ) ρ τ))
sub'-⨟ (lam (pair a b cv)) θ ρ τ =
  trans (⟪⟫-lam↑ (sub' a (thinL cv ⨾ θ) ρ) (subBind b (thinR cv ⨾ θ) ρ) τ)
        (cong₂ lam↑ (sub'-⨟ a (thinL cv ⨾ θ) ρ τ) (subBind-⨟ b (thinR cv ⨾ θ) ρ τ))
sub'-⨟ (Lam b) θ ρ τ =
  trans (⟪⟫-Lam↑ (subBind b θ ρ) τ) (cong Lam↑ (subBind-⨟ b θ ρ τ))
sub'-⨟ (app (pair l rt cv)) θ ρ τ =
  trans (⟪⟫-app↑ (sub' l (thinL cv ⨾ θ) ρ) (sub' rt (thinR cv ⨾ θ) ρ) τ)
        (cong₂ app↑ (sub'-⨟ l (thinL cv ⨾ θ) ρ τ) (sub'-⨟ rt (thinR cv ⨾ θ) ρ τ))
sub'-⨟ (App (pair e t cv)) θ ρ τ =
  trans (⟪⟫-App↑ (sub' e (thinL cv ⨾ θ) ρ) (sub' t (thinR cv ⨾ θ) ρ) τ)
        (cong₂ App↑ (sub'-⨟ e (thinL cv ⨾ θ) ρ τ) (sub'-⨟ t (thinR cv ⨾ θ) ρ τ))
sub'-⨟ ⋆ θ ρ τ = refl
subBind-⨟ (use x) θ ρ τ =
  trans (sub'-⨟ x (os θ) (lift ρ) (lift τ)) (cong (sub' x (os θ)) (lift-⨟ ρ τ))
subBind-⨟ (drop x) θ ρ τ =
  trans (wk-⟪⟫ (sub' x θ ρ) τ) (cong (_⟨ o' oi ⟩↑) (sub'-⨟ x θ ρ τ))

-- ★ Clos (compositionality) and Ass (associativity) — the σ-laws, PROVEN, no postulates
Clos : ∀ {Δ Ξ Θ}(u : Tm s ↑ Θ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ) → (u ⟪ σ ⟫) ⟪ τ ⟫ ≡ u ⟪ σ ⨟ τ ⟫
Clos (t ⇑ θ) σ τ = sub'-⨟ t θ σ τ
Ass : ∀ {Δ Ξ Ω Θ}(σ : Sub Δ Θ)(τ : Sub Ξ Δ)(υ : Sub Ω Ξ) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
Ass ε       τ υ = refl
Ass (t ∙ σ) τ υ = cong₂ _∙_ (Clos t τ υ) (Ass σ τ υ)

-- ════ identity substitution + ⟪⟫-id ════
ids : Sub Θ Θ
ids {[]}     = ε
ids {s ∷ Θ} = var↑ ∙ wkSub ids
-- cop of a cover's own projections recovers the cover (identity out) — via subst transport
cop-split-un : (cv : Cover Γₗ Γᵣ Δ) → un (cop (thinL cv)(thinR cv)) ≡ Δ
cop-split-un done   = refl
cop-split-un (bb {s = r} c) = cong (r ∷_) (cop-split-un c)
cop-split-un (ll {s = r} c) = cong (r ∷_) (cop-split-un c)
cop-split-un (rr {s = r} c) = cong (r ∷_) (cop-split-un c)
cop-split-out : (cv : Cover Γₗ Γᵣ Δ) → subst (_⊑ Δ) (cop-split-un cv) (out (cop (thinL cv)(thinR cv))) ≡ oi
cop-split-out done   = refl
cop-split-out (bb c) = trans (push-os (cop-split-un c) _) (cong os (cop-split-out c))
cop-split-out (ll c) = trans (push-os (cop-split-un c) _) (cong os (cop-split-out c))
cop-split-out (rr c) = trans (push-os (cop-split-un c) _) (cong os (cop-split-out c))
cop-split-cov : (cv : Cover Γₗ Γᵣ Δ) → subst (Cover Γₗ Γᵣ) (cop-split-un cv) (cov (cop (thinL cv)(thinR cv))) ≡ cv
cop-split-cov done   = refl
cop-split-cov (bb c) = trans (scb (cop-split-un c) _) (cong bb (cop-split-cov c))
  where scb : ∀ {r Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁) → subst (Cover (r ∷ Gl)(r ∷ Gr)) (cong (r ∷_) p) (bb c) ≡ bb (subst (Cover Gl Gr) p c)
        scb refl c = refl
cop-split-cov (ll c) = trans (scl (cop-split-un c) _) (cong ll (cop-split-cov c))
  where scl : ∀ {r Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁) → subst (Cover (r ∷ Gl) Gr) (cong (r ∷_) p) (ll c) ≡ ll (subst (Cover Gl Gr) p c)
        scl refl c = refl
cop-split-cov (rr c) = trans (scr (cop-split-un c) _) (cong rr (cop-split-cov c))
  where scr : ∀ {r Gl Gr u₁ u₂}(p : u₁ ≡ u₂)(c : Cover Gl Gr u₁) → subst (Cover Gl (r ∷ Gr)) (cong (r ∷_) p) (rr c) ≡ rr (subst (Cover Gl Gr) p c)
        scr refl c = refl

-- ids restricted = the identity on the sub-scope, target-renamed
ids↾-mapWk : (θ : Θ ⊑ Ω) → ids ↾ θ ≡ mapWk (ids {Θ}) θ
ids↾-mapWk oz     = refl
ids↾-mapWk (os θ) = cong₂ _∙_
  (cong (λ z → var ⇑ os z) (sym (oe-unique (oe ⨾ θ))))
  (trans (cong (λ z → mapWk z (o' oi)) (ids↾-mapWk θ))
    (trans (mapWk-fusion ids θ (o' oi))
      (trans (cong (λ z → mapWk ids (o' z)) (trans (⨾oi θ) (sym (oi⨾ θ))))
             (sym (mapWk-fusion ids (o' oi) (os θ))))))
ids↾-mapWk (o' θ) =
  trans (cong (λ z → mapWk z (o' oi)) (ids↾-mapWk θ))
    (trans (mapWk-fusion ids θ (o' oi))
           (cong (λ z → mapWk ids (o' z)) (⨾oi θ)))

-- look at ids picks var, thinned by the position; then sub'-id by structural recursion
look-ids : (θ : Pos Θ s) → look θ (ids {Θ}) ≡ var ⇑ θ
look-ids (os θ) = cong (λ z → var ⇑ os z) (sym (oe-unique θ))
look-ids (o' θ) = trans (look-mapWk θ ids (o' oi))
  (trans (cong (_⟨ o' oi ⟩↑) (look-ids θ)) (cong (var ⇑_) (⨾oi (o' θ))))

bindUp⁻¹ : ∀ {s′ s Θ Ω} → Bind s′ (Tm s) Θ → Θ ⊑ Ω → Tm s ↑ (s′ ∷ Ω)
bindUp⁻¹ (use x)  θ = x ⇑ os θ
bindUp⁻¹ (drop x) θ = x ⇑ o' θ
-- bind-aware variants: case the bind so bindUp⁻¹ reduces and ⟨os ψ⟩↑ commutes (via ⨾-osos/⨾-o'os)
⟨⟩-∀↑ᵇ : ∀ {Δ Ω Γᵣ}(K : Tm kind ↑ Δ)(b : Bind type (Tm type) Γᵣ)(θᵣ : Γᵣ ⊑ Δ)(ψ : Δ ⊑ Ω)
       → (∀↑ K (bindUp⁻¹ b θᵣ)) ⟨ ψ ⟩↑ ≡ ∀↑ (K ⟨ ψ ⟩↑) (bindUp⁻¹ b (θᵣ ⨾ ψ))
⟨⟩-∀↑ᵇ K (use x)  θᵣ ψ = ⟨⟩-∀↑ K (x ⇑ os θᵣ) ψ
⟨⟩-∀↑ᵇ K (drop x) θᵣ ψ = ⟨⟩-∀↑ K (x ⇑ o' θᵣ) ψ
⟨⟩-lam↑ᵇ : ∀ {Δ Ω Γᵣ}(A : Tm type ↑ Δ)(b : Bind expr (Tm expr) Γᵣ)(θᵣ : Γᵣ ⊑ Δ)(ψ : Δ ⊑ Ω)
         → (lam↑ A (bindUp⁻¹ b θᵣ)) ⟨ ψ ⟩↑ ≡ lam↑ (A ⟨ ψ ⟩↑) (bindUp⁻¹ b (θᵣ ⨾ ψ))
⟨⟩-lam↑ᵇ A (use x)  θᵣ ψ = ⟨⟩-lam↑ A (x ⇑ os θᵣ) ψ
⟨⟩-lam↑ᵇ A (drop x) θᵣ ψ = ⟨⟩-lam↑ A (x ⇑ o' θᵣ) ψ
sub'-id    : (t : Tm s Θ)(θ : Θ ⊑ Ω) → sub' t θ ids ≡ (t ⇑ θ)
subBind-id : ∀ {s′ s Θ Ω}(b : Bind s′ (Tm s) Θ)(θ : Θ ⊑ Ω) → subBind b θ ids ≡ bindUp⁻¹ b θ

-- ════ split lemmas: former of the two cover-projections = the raw former at oi ════
subst-form : ∀ {F : Scope → Set}{u₁ u₂}(mk : ∀ {Θ} → F Θ → Tm s Θ)(p : u₁ ≡ u₂)(x : F u₁)
           → subst (Tm s) p (mk x) ≡ mk (subst F p x)
subst-form mk refl x = refl
-- pairUp of the two projections recovers `pair … cv` (at identity out) — via transport
pairUp-split : ∀ {S T Γₗ Γᵣ Δ}(l : S Γₗ)(r : T Γᵣ)(cv : Cover Γₗ Γᵣ Δ)
             → pairUp (l ⇑ thinL cv) (r ⇑ thinR cv) ≡ (pair l r cv ⇑ oi)
pairUp-split {S = S}{T = T} l r cv = ↑≡ {T = S ×ᴿ T} (cop-split-un cv)
  (trans (subst-pair (cop-split-un cv) l r (cov (cop (thinL cv)(thinR cv))))
         (cong (pair l r) (cop-split-cov cv)))
  (cop-split-out cv)

sub'-id var θ = look-ids θ
sub'-id (_⇒_ (pair l r cv)) θ =
  trans (cong₂ _⇒↑_ (sub'-id l (thinL cv ⨾ θ)) (sub'-id r (thinR cv ⨾ θ)))
    (trans (sym (⟨⟩-⇒↑ (l ⇑ thinL cv) (r ⇑ thinR cv) θ))
      (trans (cong (_⟨ θ ⟩↑) (cong (_⇒_ <$>_) (pairUp-split l r cv)))
             (cong (_⇒_ (pair l r cv) ⇑_) (oi⨾ θ))))
sub'-id (∀' (pair k b cv)) θ =
  trans (cong₂ ∀↑ (sub'-id k (thinL cv ⨾ θ)) (subBind-id b (thinR cv ⨾ θ)))
    (trans (sym (⟨⟩-∀↑ᵇ (k ⇑ thinL cv) b (thinR cv) θ))
      (trans (cong (_⟨ θ ⟩↑) (∀↑-split k b cv))
             (cong (∀' (pair k b cv) ⇑_) (oi⨾ θ))))
  where ∀↑-split : ∀ {Γₗ Γᵣ Ψ}(k : Tm kind Γₗ)(b : Bind type (Tm type) Γᵣ)(cv : Cover Γₗ Γᵣ Ψ)
                 → ∀↑ (k ⇑ thinL cv) (bindUp⁻¹ b (thinR cv)) ≡ (∀' (pair k b cv) ⇑ oi)
        ∀↑-split k (use x)  cv = cong (∀' <$>_) (pairUp-split k (use x) cv)
        ∀↑-split k (drop x) cv = cong (∀' <$>_) (pairUp-split k (drop x) cv)
sub'-id (lam (pair a b cv)) θ =
  trans (cong₂ lam↑ (sub'-id a (thinL cv ⨾ θ)) (subBind-id b (thinR cv ⨾ θ)))
    (trans (sym (⟨⟩-lam↑ᵇ (a ⇑ thinL cv) b (thinR cv) θ))
      (trans (cong (_⟨ θ ⟩↑) (lam↑-split a b cv))
             (cong (lam (pair a b cv) ⇑_) (oi⨾ θ))))
  where lam↑-split : ∀ {Γₗ Γᵣ Ψ}(a : Tm type Γₗ)(b : Bind expr (Tm expr) Γᵣ)(cv : Cover Γₗ Γᵣ Ψ)
                   → lam↑ (a ⇑ thinL cv) (bindUp⁻¹ b (thinR cv)) ≡ (lam (pair a b cv) ⇑ oi)
        lam↑-split a (use x)  cv = cong (lam <$>_) (pairUp-split a (use x) cv)
        lam↑-split a (drop x) cv = cong (lam <$>_) (pairUp-split a (drop x) cv)
sub'-id (Lam b) θ =
  trans (cong Lam↑ (subBind-id b θ)) (Lam↑-split b θ)
  where Lam↑-split : ∀ {Γᵣ Δ}(b : Bind type (Tm expr) Γᵣ)(θ : Γᵣ ⊑ Δ) → Lam↑ (bindUp⁻¹ b θ) ≡ (Lam b ⇑ θ)
        Lam↑-split (use x)  θ = refl
        Lam↑-split (drop x) θ = refl
sub'-id (app (pair l r cv)) θ =
  trans (cong₂ app↑ (sub'-id l (thinL cv ⨾ θ)) (sub'-id r (thinR cv ⨾ θ)))
    (trans (sym (⟨⟩-app↑ (l ⇑ thinL cv) (r ⇑ thinR cv) θ))
      (trans (cong (_⟨ θ ⟩↑) (cong (app <$>_) (pairUp-split l r cv)))
             (cong (app (pair l r cv) ⇑_) (oi⨾ θ))))
sub'-id (App (pair e t cv)) θ =
  trans (cong₂ App↑ (sub'-id e (thinL cv ⨾ θ)) (sub'-id t (thinR cv ⨾ θ)))
    (trans (sym (⟨⟩-App↑ (e ⇑ thinL cv) (t ⇑ thinR cv) θ))
      (trans (cong (_⟨ θ ⟩↑) (cong (App <$>_) (pairUp-split e t cv)))
             (cong (App (pair e t cv) ⇑_) (oi⨾ θ))))
sub'-id ⋆ θ = cong (⋆ ⇑_) (sym (oe-unique θ))
subBind-id (use x)  θ = sub'-id x (os θ)
subBind-id (drop x) θ =
  trans (cong (_⟨ o' oi ⟩↑) (sub'-id x θ)) (cong (x ⇑_) (cong o' (⨾oi θ)))

-- ★ IDENTITY LAW — PROVEN
⟪⟫-id : (t : Tm s ↑ Θ) → t ⟪ ids ⟫ ≡ t
⟪⟫-id (t ⇑ θ) = sub'-id t θ
