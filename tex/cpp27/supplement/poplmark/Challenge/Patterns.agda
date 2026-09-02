{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLmark Challenge, Parts 1B and 2B, full language ═════════════
-- F<: with records, projection, patterns and `let p = t in t'`.
--
--   1B  Lemma 3.1    transitivity of subtyping with record types,
--                    and (`transitivityᴿ°`) for the challenge's SA-Rcd,
--                    which has no reflexivity rule
--       Lemma 3.2    narrowing, with the trailing ∆
--   2B  Lemma A.17   matched patterns preserve typing (`⊢match`)
--       Theorem 3.3  preservation
--       Theorem 3.4  progress
--
-- The statements are collected at the end of this file.

module Challenge.Patterns where

open import Languages.FsubPatterns

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst) renaming (trans to ≡-trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; drop)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; n≤1+n)

-- ─── the n-fold scope extension, specialised to `expr` ──────────────
-- Definitional aliases for the core's sort-generic `ext*` / `↑ᴿ*[ b ]` /
-- `↑ˢ*[ b ]`, so every rewrite rule of the generic family still fires.

ext : ℕ → Scope → Scope
ext = ext* expr

_↑ᴿ*_ : S₁ →ᴿ S₂ → ∀ n → (ext n S₁) →ᴿ (ext n S₂)
ξ ↑ᴿ* n = ξ ↑ᴿ*[ expr ] n

_↑ˢ*_ : S₁ →ˢ S₂ → ∀ n → (ext n S₁) →ˢ (ext n S₂)
σ ↑ˢ* n = σ ↑ˢ*[ expr ] n

-- ─── variables ──────────────────────────────────────────────────────

variable
  e e₁ e₂ e′              : S ⊢ expr
  A A₁ A₂ B B₁ B₂ C P Q U : S ⊢ type
  rt rt₁ rt₂              : S ⊢ rtype
  re re₁ re₂              : S ⊢ rexpr
  p p₁ p₂                 : S ⊢ pat n₁ n₂
  ps ps₁ ps₂              : S ⊢ rpat n₁ n₂
  α                       : S ∋ s
  l l′                    : Label

-- ─── contexts ───────────────────────────────────────────────────────

↑ˢᵗ_ : Sort → Sort
↑ˢᵗ _ = type

_∶⊢_ : Scope → Sort → Set
S ∶⊢ s = S ⊢ (↑ˢᵗ s)

depth : S ∋ s → ℕ
depth zero    = zero
depth (suc x) = suc (depth x)

drop-∈ : S ∋ s → Scope → Scope
drop-∈ x S = drop (suc (depth x)) S

Ctx : Scope → Set
Ctx S = ∀ s → (x : S ∋ s) → drop-∈ x S ∶⊢ s

_∷ₜ_ : S ∶⊢ s → Ctx S → Ctx (s ∷ S)
(t ∷ₜ Γ) _ zero    = t
(t ∷ₜ Γ) _ (suc x) = Γ _ x

wk-drop-∈ : (x : S ∋ s) → drop-∈ x S ⊢ s′ → S ⊢ s′
wk-drop-∈ zero    t = weaken t
wk-drop-∈ (suc x) t = weaken (wk-drop-∈ x t)

wk-telescope : Ctx S → S ∋ s → S ∶⊢ s
wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

_∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

variable
  Γ Γ₁ Γ₂ : Ctx S


-- ─── field membership ───────────────────────────────────────────────
-- `Has rt l A` is the challenge's  lᵢ ∈ {kⱼ}  together with the
-- selection of the field type: l is a field of rt, at its first
-- occurrence, with type A.
data Has {S} : S ⊢ rtype → Label → S ⊢ type → Set where
  here  : ∀ {l A rt} → Has (consT l A rt) l A
  there : ∀ {l A l′ A′ rt} → l ≢ l′ → Has rt l A → Has (consT l′ A′ rt) l A

data HasE {S} : S ⊢ rexpr → Label → S ⊢ expr → Set where
  hereE  : ∀ {l e re} → HasE (consE l e re) l e
  thereE : ∀ {l e l′ e′ re} → l ≢ l′ → HasE re l e → HasE (consE l′ e′ re) l e

HasE-unique : ∀ {S} {re : S ⊢ rexpr} {l e e′} → HasE re l e → HasE re l e′ → e ≡ e′
HasE-unique hereE          hereE          = refl
HasE-unique hereE          (thereE ne _)  = ⊥-elim (ne refl)
HasE-unique (thereE ne _)  hereE          = ⊥-elim (ne refl)
HasE-unique (thereE _ a)   (thereE _ b)   = HasE-unique a b

-- membership is stable under both kinds of map, definitionally
Has-ren : ∀ {S₁ S₂} {rt : S₁ ⊢ rtype} {l A} {ξ : S₁ →ᴿ S₂} →
  Has rt l A → Has (rt [ ξ ]ᴿ) l (A [ ξ ]ᴿ)
Has-ren here            = here
Has-ren {ξ = ξ} (there ne h) = there ne (Has-ren {ξ = ξ} h)

Has-sub : ∀ {S₁ S₂} {rt : S₁ ⊢ rtype} {l A} {σ : S₁ →ˢ S₂} →
  Has rt l A → Has (rt [ σ ]ˢ) l (A [ σ ]ˢ)
Has-sub here            = here
Has-sub {σ = σ} (there ne h) = there ne (Has-sub {σ = σ} h)

-- well-formedness of a record body: nil-terminated with distinct labels
data NotIn {S} (l : Label) : S ⊢ rtype → Set where
  ni-nil  : NotIn l nilT
  ni-cons : ∀ {l′ A rt} → l ≢ l′ → NotIn l rt → NotIn l (consT l′ A rt)

data WfR {S} : S ⊢ rtype → Set where
  wf-nil  : WfR nilT
  wf-cons : ∀ {l A rt} → NotIn l rt → WfR rt → WfR (consT l A rt)

notin-≢ : ∀ {S} {rt : S ⊢ rtype} {l l′ A} → NotIn l rt → Has rt l′ A → l′ ≢ l
notin-≢ (ni-cons ne ni) here        = λ eq → ne (sym eq)
notin-≢ (ni-cons ne ni) (there _ h) = notin-≢ ni h


-- ═══ patterns: telescopes, matching, and the scope they bind ════════

-- A telescope of n₂−n₁ types, all written in the ambient scope S: what
-- a pattern binds.  (`Tele` further down is a different thing, the
-- context extension ∆ of the challenge's narrowing lemma.)
--
-- It is not a sort of the signature.  A sort gets a variable
-- constructor, and `_++ᵗ_` and `wk↑` below have no clause for a
-- telescope that is a variable: from one there is neither a telescope
-- of the concatenated arity nor a renaming between the two extended
-- scopes to be had.
data Tel (S : Scope) : ℕ → ℕ → Set where
  []  : ∀ {n} → Tel S n n
  _∷_ : ∀ {n₁ n₂} → S ⊢ type → Tel S (suc n₁) n₂ → Tel S n₁ n₂

-- The values a match produces, indexed the same way.
data Vals (S : Scope) : ℕ → ℕ → Set where
  []  : ∀ {n} → Vals S n n
  _∷_ : ∀ {n₁ n₂} → S ⊢ expr → Vals S (suc n₁) n₂ → Vals S n₁ n₂

infixr 5 _∷_

_++ᵗ_ : ∀ {S n₁ n₂ n₃} → Tel S n₁ n₂ → Tel S n₂ n₃ → Tel S n₁ n₃
[]       ++ᵗ ys = ys
(A ∷ xs) ++ᵗ ys = A ∷ (xs ++ᵗ ys)

_++ᵛ_ : ∀ {S n₁ n₂ n₃} → Vals S n₁ n₂ → Vals S n₂ n₃ → Vals S n₁ n₃
[]       ++ᵛ ys = ys
(v ∷ xs) ++ᵛ ys = v ∷ (xs ++ᵛ ys)

-- The context extension.  `w` is the weakening from the ambient scope
-- into the scope reached so far, passed as a parameter.
ext-ctx : ∀ {S n₁ n₂} → Tel S n₁ n₂ → (S →ᴿ ext n₁ S) →
  Ctx (ext n₁ S) → Ctx (ext n₂ S)
ext-ctx []      w Γ = Γ
ext-ctx (A ∷ Δ) w Γ = ext-ctx Δ (w ⨟ᴿ wkᴿ expr) ((A [ w ]ᴿ) ∷ₜ Γ)

-- The weakening a telescope itself induces (recursion on Δ, not on n).
wk↑ : ∀ {S n₁ n₂} → Tel S n₁ n₂ → (ext n₁ S) →ᴿ (ext n₂ S)
wk↑ []      = idᴿ
wk↑ (A ∷ Δ) = wkᴿ expr ⨟ᴿ wk↑ Δ

-- The substitution a value vector induces: E-LetV's σₙ ⨟ ⋯ ⨟ σ₁.
sub : ∀ {S n₁ n₂} → Vals S n₁ n₂ → (S →ᴿ ext n₁ S) →
  (ext n₂ S) →ˢ (ext n₁ S)
sub []       w = idˢ
sub (v ∷ vs) w = sub vs (w ⨟ᴿ wkᴿ expr) ⨟ ((v [ w ]ᴿ) ∙ˢ idˢ)

-- ─── P-Var and P-Rcd ────────────────────────────────────────────────
infix 3 _⊢ᵖ_⇒_ _⊢ʳ_⇒_
data _⊢ᵖ_⇒_ {S} : ∀ {n₁ n₂} → S ⊢ pat n₁ n₂ → S ⊢ type → Tel S n₁ n₂ → Set
data _⊢ʳ_⇒_ {S} : ∀ {n₁ n₂} → S ⊢ rpat n₁ n₂ → S ⊢ rtype → Tel S n₁ n₂ → Set

data _⊢ᵖ_⇒_ {S} where
  P-var : ∀ {n} {A : S ⊢ type} → _⊢ᵖ_⇒_ {n₁ = n} (pvar A) A (A ∷ [])
  P-rcd : ∀ {n₁ n₂} {ps : S ⊢ rpat n₁ n₂} {rt Δ} →
          WfR rt → ps ⊢ʳ rt ⇒ Δ → (prcd ps) ⊢ᵖ (RcdT rt) ⇒ Δ

data _⊢ʳ_⇒_ {S} where
  P-nil  : ∀ {n} → _⊢ʳ_⇒_ {n₁ = n} nilP nilT []
  P-cons : ∀ {n₁ n₂ n₃ l} {p : S ⊢ pat n₁ n₂} {ps : S ⊢ rpat n₂ n₃}
           {A rt Δ₁ Δ₂} → p ⊢ᵖ A ⇒ Δ₁ → ps ⊢ʳ rt ⇒ Δ₂ →
           (consP l p ps) ⊢ʳ (consT l A rt) ⇒ (Δ₁ ++ᵗ Δ₂)

-- ─── M-Var and M-Rcd ────────────────────────────────────────────────
data Match  {S} : ∀ {n₁ n₂} → S ⊢ pat n₁ n₂ → S ⊢ expr → Vals S n₁ n₂ → Set
data Matchᴿ {S} : ∀ {n₁ n₂} → S ⊢ rpat n₁ n₂ → S ⊢ rexpr → Vals S n₁ n₂ → Set

data Match {S} where
  M-var : ∀ {n A v} → Match {n₁ = n} (pvar A) v (v ∷ [])
  M-rcd : ∀ {n₁ n₂} {ps : S ⊢ rpat n₁ n₂} {re vs} →
          Matchᴿ ps re vs → Match (prcd ps) (RcdE re) vs

data Matchᴿ {S} where
  M-nil  : ∀ {n re} → Matchᴿ {n₁ = n} nilP re []
  M-cons : ∀ {n₁ n₂ n₃ l} {p : S ⊢ pat n₁ n₂} {ps : S ⊢ rpat n₂ n₃}
           {re e ws vs} → HasE re l e → Match p e ws → Matchᴿ ps re vs →
           Matchᴿ (consP l p ps) re (ws ++ᵛ vs)

-- ─── patterns and telescopes under a map ────────────────────────────
Tel-ren : ∀ {S₁ S₂ n₁ n₂} → Tel S₁ n₁ n₂ → (S₁ →ᴿ S₂) → Tel S₂ n₁ n₂
Tel-ren []      ξ = []
Tel-ren (A ∷ Δ) ξ = (A [ ξ ]ᴿ) ∷ Tel-ren Δ ξ

Tel-sub : ∀ {S₁ S₂ n₁ n₂} → Tel S₁ n₁ n₂ → (S₁ →ˢ S₂) → Tel S₂ n₁ n₂
Tel-sub []      σ = []
Tel-sub (A ∷ Δ) σ = (A [ σ ]ˢ) ∷ Tel-sub Δ σ

Tel-ren-++ : ∀ {S₁ S₂ n₁ n₂ n₃} (Δ₁ : Tel S₁ n₁ n₂) (Δ₂ : Tel S₁ n₂ n₃)
  (ξ : S₁ →ᴿ S₂) → Tel-ren (Δ₁ ++ᵗ Δ₂) ξ ≡ (Tel-ren Δ₁ ξ ++ᵗ Tel-ren Δ₂ ξ)
Tel-ren-++ []       Δ₂ ξ = refl
Tel-ren-++ (A ∷ Δ₁) Δ₂ ξ = cong (_ ∷_) (Tel-ren-++ Δ₁ Δ₂ ξ)

Tel-sub-++ : ∀ {S₁ S₂ n₁ n₂ n₃} (Δ₁ : Tel S₁ n₁ n₂) (Δ₂ : Tel S₁ n₂ n₃)
  (σ : S₁ →ˢ S₂) → Tel-sub (Δ₁ ++ᵗ Δ₂) σ ≡ (Tel-sub Δ₁ σ ++ᵗ Tel-sub Δ₂ σ)
Tel-sub-++ []       Δ₂ σ = refl
Tel-sub-++ (A ∷ Δ₁) Δ₂ σ = cong (_ ∷_) (Tel-sub-++ Δ₁ Δ₂ σ)

-- the commutation the `let` cases of the traversals need
wk↑-ren : ∀ {S₁ S₂ n₁ n₂} (Δ : Tel S₁ n₁ n₂) (ξ : S₁ →ᴿ S₂) →
  (wk↑ Δ ⨟ᴿ (ξ ↑ᴿ* n₂)) ≡ ((ξ ↑ᴿ* n₁) ⨟ᴿ wk↑ (Tel-ren Δ ξ))
wk↑-ren []      ξ = refl
wk↑-ren (A ∷ Δ) ξ = cong (wkᴿ expr ⨟ᴿ_) (wk↑-ren Δ ξ)

wk↑-sub : ∀ {S₁ S₂ n₁ n₂} (Δ : Tel S₁ n₁ n₂) (σ : S₁ →ˢ S₂) →
  (⟨ wk↑ Δ ⟩ ⨟ (σ ↑ˢ* n₂)) ≡ ((σ ↑ˢ* n₁) ⨟ ⟨ wk↑ (Tel-sub Δ σ) ⟩)
wk↑-sub []      σ = refl
wk↑-sub (A ∷ Δ) σ = cong (⟨ wkᴿ expr ⟩ ⨟_) (wk↑-sub Δ σ)

-- pattern typing is stable under both kinds of map
⊢ᵖ-ren  : ∀ {S₁ S₂ n₁ n₂} {p : S₁ ⊢ pat n₁ n₂} {A Δ} (ξ : S₁ →ᴿ S₂) →
  p ⊢ᵖ A ⇒ Δ → (p [ ξ ]ᴿ) ⊢ᵖ (A [ ξ ]ᴿ) ⇒ (Tel-ren Δ ξ)
⊢ʳ-ren  : ∀ {S₁ S₂ n₁ n₂} {ps : S₁ ⊢ rpat n₁ n₂} {rt Δ} (ξ : S₁ →ᴿ S₂) →
  ps ⊢ʳ rt ⇒ Δ → (ps [ ξ ]ᴿ) ⊢ʳ (rt [ ξ ]ᴿ) ⇒ (Tel-ren Δ ξ)
WfR-ren : ∀ {S₁ S₂} {rt : S₁ ⊢ rtype} (ξ : S₁ →ᴿ S₂) → WfR rt → WfR (rt [ ξ ]ᴿ)
NotIn-ren : ∀ {S₁ S₂} {rt : S₁ ⊢ rtype} {l} (ξ : S₁ →ᴿ S₂) →
  NotIn l rt → NotIn l (rt [ ξ ]ᴿ)
NotIn-ren ξ ni-nil          = ni-nil
NotIn-ren ξ (ni-cons ne ni) = ni-cons ne (NotIn-ren ξ ni)
WfR-ren ξ wf-nil          = wf-nil
WfR-ren ξ (wf-cons ni w)  = wf-cons (NotIn-ren ξ ni) (WfR-ren ξ w)
⊢ᵖ-ren ξ P-var         = P-var
⊢ᵖ-ren ξ (P-rcd w pt)  = P-rcd (WfR-ren ξ w) (⊢ʳ-ren ξ pt)
⊢ʳ-ren ξ P-nil         = P-nil
⊢ʳ-ren {Δ = _} ξ (P-cons {Δ₁ = Δ₁} {Δ₂ = Δ₂} pt₁ pt₂) =
  subst (λ z → _ ⊢ʳ _ ⇒ z) (sym (Tel-ren-++ Δ₁ Δ₂ ξ))
        (P-cons (⊢ᵖ-ren ξ pt₁) (⊢ʳ-ren ξ pt₂))

⊢ᵖ-sub  : ∀ {S₁ S₂ n₁ n₂} {p : S₁ ⊢ pat n₁ n₂} {A Δ} (σ : S₁ →ˢ S₂) →
  p ⊢ᵖ A ⇒ Δ → (p [ σ ]ˢ) ⊢ᵖ (A [ σ ]ˢ) ⇒ (Tel-sub Δ σ)
⊢ʳ-sub  : ∀ {S₁ S₂ n₁ n₂} {ps : S₁ ⊢ rpat n₁ n₂} {rt Δ} (σ : S₁ →ˢ S₂) →
  ps ⊢ʳ rt ⇒ Δ → (ps [ σ ]ˢ) ⊢ʳ (rt [ σ ]ˢ) ⇒ (Tel-sub Δ σ)
WfR-sub : ∀ {S₁ S₂} {rt : S₁ ⊢ rtype} (σ : S₁ →ˢ S₂) → WfR rt → WfR (rt [ σ ]ˢ)
NotIn-sub : ∀ {S₁ S₂} {rt : S₁ ⊢ rtype} {l} (σ : S₁ →ˢ S₂) →
  NotIn l rt → NotIn l (rt [ σ ]ˢ)
NotIn-sub σ ni-nil          = ni-nil
NotIn-sub σ (ni-cons ne ni) = ni-cons ne (NotIn-sub σ ni)
WfR-sub σ wf-nil         = wf-nil
WfR-sub σ (wf-cons ni w) = wf-cons (NotIn-sub σ ni) (WfR-sub σ w)
⊢ᵖ-sub σ P-var        = P-var
⊢ᵖ-sub σ (P-rcd w pt) = P-rcd (WfR-sub σ w) (⊢ʳ-sub σ pt)
⊢ʳ-sub σ P-nil        = P-nil
⊢ʳ-sub σ (P-cons {Δ₁ = Δ₁} {Δ₂ = Δ₂} pt₁ pt₂) =
  subst (λ z → _ ⊢ʳ _ ⇒ z) (sym (Tel-sub-++ Δ₁ Δ₂ σ))
        (P-cons (⊢ᵖ-sub σ pt₁) (⊢ʳ-sub σ pt₂))

-- ─── the judgments ──────────────────────────────────────────────────
-- Record subtyping and record-term typing need their own judgments:
-- both sides live at sort `rtype`/`rexpr`, not at `type`, so they do
-- not fit the `Γ ⊢ t ∶ (A : S ∶⊢ s)` shape.

infix 3 _⊢_∶_ _⊢_<:ᴿ_ _⊢_∶ᴿ_

data _⊢_∶_   : Ctx S → S ⊢ s → S ∶⊢ s → Set
data _⊢_<:ᴿ_ : Ctx S → S ⊢ rtype → S ⊢ rtype → Set
data _⊢_∶ᴿ_  : Ctx S → S ⊢ rexpr → S ⊢ rtype → Set

data _⊢_∶_ where
  -- algorithmic subtyping
  <:-top  : Γ ⊢ A ∶ Top
  <:-refl : ∀ {α : S ∋ type} {Γ : Ctx S} → Γ ⊢ (` α) ∶ (` α)
  <:-var  : ∀ {α : S ∋ type} {Γ : Ctx S} {U B} →
    Γ ∋ α ∶ U → Γ ⊢ U ∶ B → Γ ⊢ (` α) ∶ B
  <:-⇒    : Γ ⊢ B₁ ∶ A₁ → Γ ⊢ A₂ ∶ B₂ → Γ ⊢ (A₁ ⇒ A₂) ∶ (B₁ ⇒ B₂)
  <:-∀    : Γ ⊢ B₁ ∶ A₁ → (B₁ ∷ₜ Γ) ⊢ A₂ ∶ B₂ →
            Γ ⊢ (∀[<: A₁ ] A₂) ∶ (∀[<: B₁ ] B₂)
  <:-rcd  : Γ ⊢ rt₁ <:ᴿ rt₂ → Γ ⊢ (RcdT rt₁) ∶ (RcdT rt₂)
  -- typing
  ⊢`      : ∀ {x : S ∋ expr} {Γ : Ctx S} {A} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  -- vacuous on the challenge's language: F<: has no variables at the
  -- record-body and pattern sorts, but the syntax admits one at every sort.
  ⊢`ᴿ     : ∀ {x : S ∋ rtype} {Γ : Ctx S} {A} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  ⊢`ᴱ     : ∀ {x : S ∋ rexpr} {Γ : Ctx S} {A} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  ⊢`ᴾ     : ∀ {n₁ n₂} {x : S ∋ pat n₁ n₂} {Γ : Ctx S} {A} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  ⊢`ᴾᴿ    : ∀ {n₁ n₂} {x : S ∋ rpat n₁ n₂} {Γ : Ctx S} {A} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  ⊢λ      : (A ∷ₜ Γ) ⊢ e ∶ weaken B → Γ ⊢ (λx[ A ] e) ∶ (A ⇒ B)
  ⊢Λ      : (A ∷ₜ Γ) ⊢ e ∶ B → Γ ⊢ (Λα[<: A ] e) ∶ (∀[<: A ] B)
  ⊢·      : Γ ⊢ e₁ ∶ (A ⇒ B) → Γ ⊢ e₂ ∶ A → Γ ⊢ (e₁ · e₂) ∶ B
  ⊢•      : Γ ⊢ e ∶ (∀[<: A ] B) → Γ ⊢ C ∶ A → Γ ⊢ (e • C) ∶ (B [ C ]₀)
  ⊢rcd    : Γ ⊢ re ∶ᴿ rt → Γ ⊢ (RcdE re) ∶ (RcdT rt)
  ⊢#      : ∀ {Γ : Ctx S} {e rt l A} →
            Γ ⊢ e ∶ (RcdT rt) → Has rt l A → Γ ⊢ (e # l) ∶ A
  -- T-Let.  ∆ is the telescope P-Var/P-Rcd produce; the result type B
  -- is weakened through ∆ exactly as ⊢λ weakens through one binder.
  ⊢let    : ∀ {n} {Γ : Ctx S} {p : S ⊢ pat 0 n} {Δ : Tel S 0 n}
            {e₁ : S ⊢ expr} {e₂ : (ext n S) ⊢ expr} {A B} →
            Γ ⊢ e₁ ∶ A → p ⊢ᵖ A ⇒ Δ →
            (ext-ctx Δ idᴿ Γ) ⊢ e₂ ∶ (B [ wk↑ Δ ]ᴿ) → Γ ⊢ (letP p e₁ e₂) ∶ B
  ⊢<:     : Γ ⊢ e ∶ A → Γ ⊢ A ∶ B → Γ ⊢ e ∶ B

-- sa-Rcd, read as an induction over the right-hand record:
-- every field of the supertype must be present in the subtype, with a
-- subtype-related field type.  Width, depth and permutation at once.
data _⊢_<:ᴿ_ where
  <:ᴿ-nil  : ∀ {Γ : Ctx S} {rt} → Γ ⊢ rt <:ᴿ nilT
  -- Explicit reflexivity.  In the challenge this rule is admissible
  -- (SA-Rcd plus distinct labels derives it); here it is primitive,
  -- because the syntax admits a record body that is a variable, at
  -- which the structural proof of reflexivity has no case.
  -- `<:ᴿ-var-forces-refl` below shows it cannot simply be dropped;
  -- `_⊢_<:ᴿ°_` at the end of this file eliminates it, and
  -- Challenge/Records.agda does the same at the level of types.
  <:ᴿ-refl : ∀ {Γ : Ctx S} {rt} → Γ ⊢ rt <:ᴿ rt
  <:ᴿ-cons : ∀ {Γ : Ctx S} {rt₁ rt₂ l A B} →
    Has rt₁ l A → Γ ⊢ A ∶ B → Γ ⊢ rt₁ <:ᴿ rt₂ → Γ ⊢ rt₁ <:ᴿ (consT l B rt₂)

-- T-Rcd
data _⊢_∶ᴿ_ where
  ⊢ᴿ-nil  : ∀ {Γ : Ctx S} → Γ ⊢ nilE ∶ᴿ nilT
  ⊢ᴿ-cons : ∀ {Γ : Ctx S} {l e re A rt} →
    Γ ⊢ e ∶ A → Γ ⊢ re ∶ᴿ rt → Γ ⊢ (consE l e re) ∶ᴿ (consT l A rt)

infix 3 _⊢_<:_
_⊢_<:_ : Ctx S → S ⊢ type → S ⊢ type → Set
Γ ⊢ A <: B = Γ ⊢ A ∶ B

-- ─── reflexivity ────────────────────────────────────────────────────

<:-reflexive : ∀ (A : S ⊢ type) {Γ : Ctx S} → Γ ⊢ A <: A
<:-reflexive Top          = <:-top
<:-reflexive (` α)        = <:-refl
<:-reflexive (A ⇒ B)      = <:-⇒ (<:-reflexive A) (<:-reflexive B)
<:-reflexive (∀[<: A ] B) = <:-∀ (<:-reflexive A) (<:-reflexive B)
<:-reflexive (RcdT rt)    = <:-rcd <:ᴿ-refl

⊢var : ∀ {Γ : Ctx S} {x : S ∋ s} {A : S ∶⊢ s} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
⊢var {s = expr}  eq = ⊢` eq
⊢var {s = type}  eq = <:-var eq (<:-reflexive _)
⊢var {s = rtype} eq = ⊢`ᴿ eq
⊢var {s = rexpr} eq = ⊢`ᴱ eq
⊢var {s = pat n₁ n₂}  eq = ⊢`ᴾ eq
⊢var {s = rpat n₁ n₂} eq = ⊢`ᴾᴿ eq

-- ─── typed renamings ────────────────────────────────────────────────

_∶_→ᴿ_ : S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ᴿ_ {S₁} ξ Γ₁ Γ₂ = ∀ s (x : S₁ ∋ s) (A : S₁ ∶⊢ s) →
  Γ₁ ∋ x ∶ A → Γ₂ ∋ (x [ ξ ]ᴿ) ∶ (A [ ξ ]ᴿ)

⊢wkᴿ : (A : S ∶⊢ s′) → wkᴿ s′ ∶ Γ →ᴿ (A ∷ₜ Γ)
⊢wkᴿ A _ x _ refl = refl

⊢↑ᴿ : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} → ξ ∶ Γ₁ →ᴿ Γ₂ →
  (A : S₁ ∶⊢ s) → (ξ ↑ᴿ s) ∶ (A ∷ₜ Γ₁) →ᴿ ((A [ ξ ]ᴿ) ∷ₜ Γ₂)
⊢↑ᴿ ⊢ξ A _ zero    _ refl = refl
⊢↑ᴿ ⊢ξ A _ (suc x) _ refl = cong weaken (⊢ξ _ x _ refl)

⊢ext-ctxᴿ : ∀ {S₁ S₂ n₁ n₂} {ξ : S₁ →ᴿ S₂}
  {Γ₁ : Ctx (ext n₁ S₁)} {Γ₂ : Ctx (ext n₁ S₂)}
  (Δ : Tel S₁ n₁ n₂) (w₁ : S₁ →ᴿ ext n₁ S₁) (w₂ : S₂ →ᴿ ext n₁ S₂) →
  (w₁ ⨟ᴿ (ξ ↑ᴿ* n₁)) ≡ (ξ ⨟ᴿ w₂) → (ξ ↑ᴿ* n₁) ∶ Γ₁ →ᴿ Γ₂ →
  (ξ ↑ᴿ* n₂) ∶ (ext-ctx Δ w₁ Γ₁) →ᴿ (ext-ctx (Tel-ren Δ ξ) w₂ Γ₂)
⊢ext-ctxᴿ []      w₁ w₂ eq ⊢ξ = ⊢ξ
⊢ext-ctxᴿ {n₁ = n₁} {ξ = ξ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (A ∷ Δ) w₁ w₂ eq ⊢ξ =
  ⊢ext-ctxᴿ Δ (w₁ ⨟ᴿ wkᴿ expr) (w₂ ⨟ᴿ wkᴿ expr) (cong (_⨟ᴿ wkᴿ expr) eq)
    (subst (λ z → ((ξ ↑ᴿ* n₁) ↑ᴿ expr) ∶ ((A [ w₁ ]ᴿ) ∷ₜ Γ₁) →ᴿ (z ∷ₜ Γ₂))
           (cong (A [_]ᴿ) eq) (⊢↑ᴿ ⊢ξ (A [ w₁ ]ᴿ)))

⊢idᴿ : ∀ {S} {Γ : Ctx S} → idᴿ ∶ Γ →ᴿ Γ
⊢idᴿ s x A eq = eq

⊢⨟ᴿ : ∀ {S₁ S₂ S₃} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃}
  {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {Γ₃ : Ctx S₃} →
  ξ₁ ∶ Γ₁ →ᴿ Γ₂ → ξ₂ ∶ Γ₂ →ᴿ Γ₃ → (ξ₁ ⨟ᴿ ξ₂) ∶ Γ₁ →ᴿ Γ₃
⊢⨟ᴿ ⊢ξ₁ ⊢ξ₂ s x A eq = ⊢ξ₂ _ _ _ (⊢ξ₁ _ _ _ eq)

infixl 5 _⊢⋯ᴿ_
_⊢⋯ᴿ_  : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {t : S₁ ⊢ s} {A : S₁ ∶⊢ s} →
  Γ₁ ⊢ t ∶ A → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (t [ ξ ]ᴿ) ∶ (A [ ξ ]ᴿ)
_⊢⋯ᴿᴿ_ : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {rt₁ rt₂ : S₁ ⊢ rtype} →
  Γ₁ ⊢ rt₁ <:ᴿ rt₂ → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (rt₁ [ ξ ]ᴿ) <:ᴿ (rt₂ [ ξ ]ᴿ)
_⊢⋯ᴿᴱ_ : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {re : S₁ ⊢ rexpr} {rt : S₁ ⊢ rtype} →
  Γ₁ ⊢ re ∶ᴿ rt → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (re [ ξ ]ᴿ) ∶ᴿ (rt [ ξ ]ᴿ)

<:-top          ⊢⋯ᴿ ⊢ξ = <:-top
<:-refl         ⊢⋯ᴿ ⊢ξ = <:-refl
(<:-var ⊢α ⊢U)  ⊢⋯ᴿ ⊢ξ = <:-var (⊢ξ _ _ _ ⊢α) (⊢U ⊢⋯ᴿ ⊢ξ)
(<:-⇒ d₁ d₂)    ⊢⋯ᴿ ⊢ξ = <:-⇒ (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)
(<:-∀ d₁ d₂)    ⊢⋯ᴿ ⊢ξ = <:-∀ (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢↑ᴿ ⊢ξ _)
(<:-rcd r)      ⊢⋯ᴿ ⊢ξ = <:-rcd (r ⊢⋯ᴿᴿ ⊢ξ)
(⊢` ⊢x)         ⊢⋯ᴿ ⊢ξ = ⊢` (⊢ξ _ _ _ ⊢x)
(⊢`ᴿ ⊢x)        ⊢⋯ᴿ ⊢ξ = ⊢`ᴿ (⊢ξ _ _ _ ⊢x)
(⊢`ᴱ ⊢x)        ⊢⋯ᴿ ⊢ξ = ⊢`ᴱ (⊢ξ _ _ _ ⊢x)
(⊢`ᴾ ⊢x)        ⊢⋯ᴿ ⊢ξ = ⊢`ᴾ (⊢ξ _ _ _ ⊢x)
(⊢`ᴾᴿ ⊢x)       ⊢⋯ᴿ ⊢ξ = ⊢`ᴾᴿ (⊢ξ _ _ _ ⊢x)
(⊢λ d)          ⊢⋯ᴿ ⊢ξ = ⊢λ (d ⊢⋯ᴿ ⊢↑ᴿ ⊢ξ _)
(⊢Λ d)          ⊢⋯ᴿ ⊢ξ = ⊢Λ (d ⊢⋯ᴿ ⊢↑ᴿ ⊢ξ _)
(⊢· d₁ d₂)      ⊢⋯ᴿ ⊢ξ = ⊢· (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)
(⊢• d₁ d₂)      ⊢⋯ᴿ ⊢ξ = ⊢• (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)
(⊢rcd d)        ⊢⋯ᴿ ⊢ξ = ⊢rcd (d ⊢⋯ᴿᴱ ⊢ξ)
(⊢# d h)        ⊢⋯ᴿ ⊢ξ = ⊢# (d ⊢⋯ᴿ ⊢ξ) (Has-ren h)
_⊢⋯ᴿ_ {ξ = ξ} {Γ₂ = Γ₂} (⊢let {n = n} {Δ = Δ} {e₂ = e₂} {B = B} d pt body) ⊢ξ =
  ⊢let (d ⊢⋯ᴿ ⊢ξ) (⊢ᵖ-ren ξ pt)
    (subst (λ z → (ext-ctx (Tel-ren Δ ξ) idᴿ Γ₂) ⊢ (e₂ [ (ξ ↑ᴿ* n) ]ᴿ) ∶ z)
           (cong (B [_]ᴿ) (wk↑-ren Δ ξ))
           (body ⊢⋯ᴿ ⊢ext-ctxᴿ Δ idᴿ idᴿ refl ⊢ξ))
(⊢<: d₁ d₂)     ⊢⋯ᴿ ⊢ξ = ⊢<: (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)

<:ᴿ-nil            ⊢⋯ᴿᴿ ⊢ξ = <:ᴿ-nil
<:ᴿ-refl           ⊢⋯ᴿᴿ ⊢ξ = <:ᴿ-refl
(<:ᴿ-cons h d r)   ⊢⋯ᴿᴿ ⊢ξ = <:ᴿ-cons (Has-ren h) (d ⊢⋯ᴿ ⊢ξ) (r ⊢⋯ᴿᴿ ⊢ξ)

⊢ᴿ-nil          ⊢⋯ᴿᴱ ⊢ξ = ⊢ᴿ-nil
(⊢ᴿ-cons d ds)  ⊢⋯ᴿᴱ ⊢ξ = ⊢ᴿ-cons (d ⊢⋯ᴿ ⊢ξ) (ds ⊢⋯ᴿᴱ ⊢ξ)

⊢weaken : ∀ {S s s′} {Γ : Ctx S} {t : S ⊢ s} {A : S ∶⊢ s} (P : S ∶⊢ s′) →
  Γ ⊢ t ∶ A → (_∷ₜ_ {s = s′} P Γ) ⊢ weaken t ∶ weaken A
⊢weaken P d = d ⊢⋯ᴿ ⊢wkᴿ P

-- ═══ Part 1B: transitivity and narrowing, with records ══════════════
-- Records force a numeric measure: the cut type of a record step is a
-- field reached through a `Has` proof, which the termination checker
-- does not see as a structural subterm.

size  : S ⊢ type  → ℕ
sizeR : S ⊢ rtype → ℕ
size Top          = 1
size (` α)        = 1
size (A ⇒ B)      = suc (size A + size B)
size (∀[<: A ] B) = suc (size A + size B)
size (RcdT rt)    = suc (sizeR rt)
sizeR (` x)          = 0    -- vacuous: no record-body variables in F<:
sizeR nilT           = 0
sizeR (consT l A rt) = suc (size A + sizeR rt)

size-ren  : ∀ (A : S₁ ⊢ type)  (ξ : S₁ →ᴿ S₂) → size (A [ ξ ]ᴿ) ≡ size A
sizeR-ren : ∀ (rt : S₁ ⊢ rtype) (ξ : S₁ →ᴿ S₂) → sizeR (rt [ ξ ]ᴿ) ≡ sizeR rt
size-ren Top ξ          = refl
size-ren (` α) ξ        = refl
size-ren (A ⇒ B) ξ      = cong₂ (λ a b → suc (a + b)) (size-ren A ξ) (size-ren B ξ)
size-ren (∀[<: A ] B) ξ = cong₂ (λ a b → suc (a + b)) (size-ren A ξ) (size-ren B (ξ ↑ᴿ type))
size-ren (RcdT rt) ξ    = cong suc (sizeR-ren rt ξ)
sizeR-ren (` x) ξ          = refl
sizeR-ren nilT ξ           = refl
sizeR-ren (consT l A rt) ξ = cong₂ (λ a b → suc (a + b)) (size-ren A ξ) (sizeR-ren rt ξ)

Has-size : ∀ {rt : S ⊢ rtype} {l A} → Has rt l A → size A ≤ sizeR rt
Has-size {A = A} (here {rt = rt})  = ≤-trans (m≤m+n (size A) (sizeR rt)) (n≤1+n _)
Has-size (there {A′ = A′} {rt = rt} ne h) =
  ≤-trans (Has-size h) (≤-trans (m≤n+m (sizeR rt) (size A′)) (n≤1+n _))

-- The `s ≡ type` component records that the entry being narrowed is a
-- type binding X<:Q, which is what the challenge's narrowing lemma
-- narrows; it also discharges the vacuous sorts.
Narrowing : ∀ {S} → Ctx S → S ⊢ type → Ctx S → Set
Narrowing {S} Γ₂ Q Γ₁ = ∀ s (x : S ∋ s) →
    (wk-telescope Γ₂ x ≡ wk-telescope Γ₁ x)
  ⊎ ((s ≡ type) × (wk-telescope Γ₁ x ≡ Q) × (Γ₂ ⊢ wk-telescope Γ₂ x <: Q))

narrow-here : ∀ {S} {Γ : Ctx S} {P Q : S ⊢ type} →
  Γ ⊢ P <: Q → Narrowing {type ∷ S} (P ∷ₜ Γ) (weaken Q) (Q ∷ₜ Γ)
narrow-here d _ zero    = inj₂ (refl , refl , ⊢weaken _ d)
narrow-here d _ (suc y) = inj₁ refl

narrow-ext : ∀ {S} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} → Narrowing Γ₂ Q Γ₁ →
  ∀ s (P : S ∶⊢ s) → Narrowing {s ∷ S} (P ∷ₜ Γ₂) (weaken Q) (P ∷ₜ Γ₁)
narrow-ext nr s P _ zero = inj₁ refl
narrow-ext nr s P _ (suc y) with nr _ y
... | inj₁ eq             = inj₁ (cong weaken eq)
... | inj₂ (st , eq , d)  = inj₂ (st , cong weaken eq , ⊢weaken P d)

narrow-tel : ∀ {S n₁ n₂} {Γ₁ Γ₂ : Ctx (ext n₁ S)} {Q : (ext n₁ S) ⊢ type}
  (Δ : Tel S n₁ n₂) (w : S →ᴿ ext n₁ S) →
  Narrowing Γ₂ Q Γ₁ → Narrowing (ext-ctx Δ w Γ₂) (Q [ wk↑ Δ ]ᴿ) (ext-ctx Δ w Γ₁)
narrow-tel []      w nr = nr
narrow-tel (A ∷ Δ) w nr = narrow-tel Δ (w ⨟ᴿ wkᴿ expr) (narrow-ext nr expr (A [ w ]ᴿ))

-- Recursion is structural on the fuel `n` bounding `size Q`; the
-- `<:-var` clause keeps `n` and shrinks the derivation.

<:-trans  : ∀ (n : ℕ) {S} {Γ : Ctx S} {A Q B : S ⊢ type} →
  size Q ≤ n → Γ ⊢ A <: Q → Γ ⊢ Q <: B → Γ ⊢ A <: B
<:-transᴿ : ∀ (n : ℕ) {S} {Γ : Ctx S} {rs rq rt : S ⊢ rtype} →
  sizeR rq ≤ n → Γ ⊢ rs <:ᴿ rq → Γ ⊢ rq <:ᴿ rt → Γ ⊢ rs <:ᴿ rt
narrow  : ∀ (n : ℕ) {S} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} {t : S ⊢ s} {A : S ∶⊢ s} →
  size Q ≤ n → Narrowing Γ₂ Q Γ₁ → Γ₁ ⊢ t ∶ A → Γ₂ ⊢ t ∶ A
narrowᴿ : ∀ (n : ℕ) {S} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} {rt₁ rt₂ : S ⊢ rtype} →
  size Q ≤ n → Narrowing Γ₂ Q Γ₁ → Γ₁ ⊢ rt₁ <:ᴿ rt₂ → Γ₂ ⊢ rt₁ <:ᴿ rt₂
narrowᴱ : ∀ (n : ℕ) {S} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} {re : S ⊢ rexpr} {rt : S ⊢ rtype} →
  size Q ≤ n → Narrowing Γ₂ Q Γ₁ → Γ₁ ⊢ re ∶ᴿ rt → Γ₂ ⊢ re ∶ᴿ rt

-- inversion of record subtyping at a field: the join used by <:-transᴿ
<:ᴿ-inv : ∀ {Γ : Ctx S} {rs rq : S ⊢ rtype} {l C} →
  Γ ⊢ rs <:ᴿ rq → Has rq l C → Σ[ A ∈ S ⊢ type ] (Has rs l A × Γ ⊢ A <: C)
<:ᴿ-inv <:ᴿ-refl h = _ , h , <:-reflexive _
<:ᴿ-inv (<:ᴿ-cons h d r) here      = _ , h , d
<:ᴿ-inv (<:ᴿ-cons h d r) (there ne m) = <:ᴿ-inv r m

<:-trans n le d₁ <:-top = <:-top
<:-trans n le <:-refl d₂ = d₂
<:-trans n le (<:-var e u) d₂ = <:-var e (<:-trans n le u d₂)
<:-trans (suc n) (s≤s le) (<:-⇒ a₁ a₂) (<:-⇒ b₁ b₂) =
  <:-⇒ (<:-trans n (≤-trans (m≤m+n _ _) le) b₁ a₁)
       (<:-trans n (≤-trans (m≤n+m _ _) le) a₂ b₂)
<:-trans (suc n) (s≤s le) (<:-∀ {B₁ = Q₁} {B₂ = Q₂} a₁ a₂) (<:-∀ b₁ b₂) =
  <:-∀ (<:-trans n (≤-trans (m≤m+n (size Q₁) (size Q₂)) le) b₁ a₁)
       (<:-trans n (≤-trans (m≤n+m (size Q₂) (size Q₁)) le)
         (narrow n (subst (_≤ n) (sym (size-ren Q₁ (wkᴿ type)))
                          (≤-trans (m≤m+n (size Q₁) (size Q₂)) le))
            (narrow-here b₁) a₂)
         b₂)
<:-trans (suc n) (s≤s le) (<:-rcd r₁) (<:-rcd r₂) = <:-rcd (<:-transᴿ n le r₁ r₂)

<:-transᴿ n le r₁ <:ᴿ-nil = <:ᴿ-nil
<:-transᴿ n le r₁ <:ᴿ-refl = r₁
<:-transᴿ n le r₁ (<:ᴿ-cons h d r₂) with <:ᴿ-inv r₁ h
... | (A , h′ , d′) =
  <:ᴿ-cons h′ (<:-trans n (≤-trans (Has-size h) le) d′ d) (<:-transᴿ n le r₁ r₂)

narrow n le nr <:-top  = <:-top
narrow n le nr <:-refl = <:-refl
narrow n le nr (<:-var {α = α} e u) with nr _ α
... | inj₁ eq₂              = <:-var (≡-trans eq₂ e) (narrow n le nr u)
... | inj₂ (refl , eqQ , d) = <:-var refl
      (<:-trans n le d
        (subst (λ z → _ ⊢ z ∶ _) (≡-trans (sym e) eqQ) (narrow n le nr u)))
narrow n le nr (<:-⇒ d₁ d₂) = <:-⇒ (narrow n le nr d₁) (narrow n le nr d₂)
narrow n le nr (<:-∀ d₁ d₂) =
  <:-∀ (narrow n le nr d₁)
       (narrow n (subst (_≤ n) (sym (size-ren _ (wkᴿ type))) le)
               (narrow-ext nr type _) d₂)
narrow n le nr (<:-rcd r) = <:-rcd (narrowᴿ n le nr r)
narrow n le nr (⊢`ᴿ {x = x} e) with nr _ x
... | inj₁ eq₂         = ⊢`ᴿ (≡-trans eq₂ e)
... | inj₂ (() , _ , _)
narrow n le nr (⊢`ᴱ {x = x} e) with nr _ x
... | inj₁ eq₂         = ⊢`ᴱ (≡-trans eq₂ e)
... | inj₂ (() , _ , _)
narrow n le nr (⊢`ᴾ {x = x} e) with nr _ x
... | inj₁ eq₂         = ⊢`ᴾ (≡-trans eq₂ e)
... | inj₂ (() , _ , _)
narrow n le nr (⊢`ᴾᴿ {x = x} e) with nr _ x
... | inj₁ eq₂         = ⊢`ᴾᴿ (≡-trans eq₂ e)
... | inj₂ (() , _ , _)
narrow n le nr (⊢` {x = x} e) with nr _ x
... | inj₁ eq₂         = ⊢` (≡-trans eq₂ e)
... | inj₂ (() , _ , _)
narrow n le nr (⊢λ d) =
  ⊢λ (narrow n (subst (_≤ n) (sym (size-ren _ (wkᴿ expr))) le) (narrow-ext nr expr _) d)
narrow n le nr (⊢Λ d) =
  ⊢Λ (narrow n (subst (_≤ n) (sym (size-ren _ (wkᴿ type))) le) (narrow-ext nr type _) d)
narrow n le nr (⊢· d₁ d₂)  = ⊢· (narrow n le nr d₁) (narrow n le nr d₂)
narrow n le nr (⊢• d₁ d₂)  = ⊢• (narrow n le nr d₁) (narrow n le nr d₂)
narrow n le nr (⊢rcd d)    = ⊢rcd (narrowᴱ n le nr d)
narrow n le nr (⊢# d h)    = ⊢# (narrow n le nr d) h
narrow n le nr (⊢let {Δ = Δ} d pt body) =
  ⊢let (narrow n le nr d) pt
       (narrow n (subst (_≤ n) (sym (size-ren _ (wk↑ Δ))) le)
               (narrow-tel Δ idᴿ nr) body)
narrow n le nr (⊢<: d₁ d₂) = ⊢<: (narrow n le nr d₁) (narrow n le nr d₂)

narrowᴿ n le nr <:ᴿ-nil = <:ᴿ-nil
narrowᴿ n le nr <:ᴿ-refl = <:ᴿ-refl
narrowᴿ n le nr (<:ᴿ-cons h d r) = <:ᴿ-cons h (narrow n le nr d) (narrowᴿ n le nr r)

narrowᴱ n le nr ⊢ᴿ-nil = ⊢ᴿ-nil
narrowᴱ n le nr (⊢ᴿ-cons d ds) = ⊢ᴿ-cons (narrow n le nr d) (narrowᴱ n le nr ds)

-- ═══ Part 1B, as the challenge states it ════════════════════════════

-- 3.1 Lemma [Transitivity]: If Γ ⊢ S <: Q and Γ ⊢ Q <: T then Γ ⊢ S <: T
transitivity : ∀ {Γ : Ctx S} {A Q B : S ⊢ type} →
  Γ ⊢ A <: Q → Γ ⊢ Q <: B → Γ ⊢ A <: B
transitivity {Q = Q} = <:-trans (size Q) ≤-refl

-- 3.2 Lemma [Narrowing]: If Γ, X<:Q, ∆ ⊢ M <: N and Γ ⊢ P <: Q
--                        then Γ, X<:P, ∆ ⊢ M <: N
-- (∆ = ∅ here; the general ∆ follows by iterating narrow-ext, and the
--  sort-generic statement narrows a typing derivation as well)
narrowing : ∀ {Γ : Ctx S} {P Q : S ⊢ type} {t : (type ∷ S) ⊢ s} {A} →
  Γ ⊢ P <: Q → (Q ∷ₜ Γ) ⊢ t ∶ A → (P ∷ₜ Γ) ⊢ t ∶ A
narrowing {Q = Q} d =
  narrow (size Q) (subst (_≤ size Q) (sym (size-ren Q (wkᴿ type))) ≤-refl)
         (narrow-here d)

-- ─── typed substitutions ────────────────────────────────────────────

_∶_→ˢ_ : S₁ →ˢ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ˢ_ {S₁} σ Γ₁ Γ₂ = ∀ s (x : S₁ ∋ s) (A : S₁ ∶⊢ s) →
  Γ₁ ∋ x ∶ A → Γ₂ ⊢ (x [ σ ]ˢ) ∶ (A [ σ ]ˢ)

⊢↑ˢ : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} → σ ∶ Γ₁ →ˢ Γ₂ →
  (A : S₁ ∶⊢ s) → (σ ↑ˢ s) ∶ (A ∷ₜ Γ₁) →ˢ ((A [ σ ]ˢ) ∷ₜ Γ₂)
⊢↑ˢ ⊢σ A _ zero    _ refl = ⊢var refl
⊢↑ˢ {σ = σ} ⊢σ A _ (suc x) _ refl = ⊢weaken (A [ σ ]ˢ) (⊢σ _ x _ refl)

⊢ext-ctxˢ : ∀ {S₁ S₂ n₁ n₂} {σ : S₁ →ˢ S₂}
  {Γ₁ : Ctx (ext n₁ S₁)} {Γ₂ : Ctx (ext n₁ S₂)}
  (Δ : Tel S₁ n₁ n₂) (w₁ : S₁ →ᴿ ext n₁ S₁) (w₂ : S₂ →ᴿ ext n₁ S₂) →
  (⟨ w₁ ⟩ ⨟ (σ ↑ˢ* n₁)) ≡ (σ ⨟ ⟨ w₂ ⟩) → (σ ↑ˢ* n₁) ∶ Γ₁ →ˢ Γ₂ →
  (σ ↑ˢ* n₂) ∶ (ext-ctx Δ w₁ Γ₁) →ˢ (ext-ctx (Tel-sub Δ σ) w₂ Γ₂)
⊢ext-ctxˢ []      w₁ w₂ eq ⊢σ = ⊢σ
⊢ext-ctxˢ {n₁ = n₁} {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (A ∷ Δ) w₁ w₂ eq ⊢σ =
  ⊢ext-ctxˢ Δ (w₁ ⨟ᴿ wkᴿ expr) (w₂ ⨟ᴿ wkᴿ expr) (cong (_⨟ ⟨ wkᴿ expr ⟩) eq)
    (subst (λ z → ((σ ↑ˢ* n₁) ↑ˢ expr) ∶ ((A [ w₁ ]ᴿ) ∷ₜ Γ₁) →ˢ (z ∷ₜ Γ₂))
           (cong (A [_]ˢ) eq) (⊢↑ˢ {σ = σ ↑ˢ* n₁} ⊢σ (A [ w₁ ]ᴿ)))

infixl 5 _⊢⋯ˢ_
_⊢⋯ˢ_  : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {t : S₁ ⊢ s} {A : S₁ ∶⊢ s} →
  Γ₁ ⊢ t ∶ A → σ ∶ Γ₁ →ˢ Γ₂ → Γ₂ ⊢ (t [ σ ]ˢ) ∶ (A [ σ ]ˢ)
_⊢⋯ˢᴿ_ : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {rt₁ rt₂ : S₁ ⊢ rtype} →
  Γ₁ ⊢ rt₁ <:ᴿ rt₂ → σ ∶ Γ₁ →ˢ Γ₂ → Γ₂ ⊢ (rt₁ [ σ ]ˢ) <:ᴿ (rt₂ [ σ ]ˢ)
_⊢⋯ˢᴱ_ : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {re : S₁ ⊢ rexpr} {rt : S₁ ⊢ rtype} →
  Γ₁ ⊢ re ∶ᴿ rt → σ ∶ Γ₁ →ˢ Γ₂ → Γ₂ ⊢ (re [ σ ]ˢ) ∶ᴿ (rt [ σ ]ˢ)

_⊢⋯ˢ_ {σ = σ} <:-top  ⊢σ = <:-top
_⊢⋯ˢ_ {σ = σ} <:-refl ⊢σ = <:-reflexive _
_⊢⋯ˢ_ {σ = σ} (<:-var {α = α} e u) ⊢σ =
  transitivity (⊢σ _ α _ e) (_⊢⋯ˢ_ {σ = σ} u ⊢σ)
_⊢⋯ˢ_ {σ = σ} (<:-⇒ d₁ d₂) ⊢σ =
  <:-⇒ (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)
_⊢⋯ˢ_ {σ = σ} (<:-∀ d₁ d₂) ⊢σ =
  <:-∀ (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ ↑ˢ _} d₂ (⊢↑ˢ {σ = σ} ⊢σ _))
_⊢⋯ˢ_ {σ = σ} (<:-rcd r) ⊢σ = <:-rcd (_⊢⋯ˢᴿ_ {σ = σ} r ⊢σ)
_⊢⋯ˢ_ (⊢` e) ⊢σ = ⊢σ _ _ _ e
_⊢⋯ˢ_ (⊢`ᴿ e) ⊢σ = ⊢σ _ _ _ e
_⊢⋯ˢ_ (⊢`ᴱ e) ⊢σ = ⊢σ _ _ _ e
_⊢⋯ˢ_ (⊢`ᴾ e) ⊢σ = ⊢σ _ _ _ e
_⊢⋯ˢ_ (⊢`ᴾᴿ e) ⊢σ = ⊢σ _ _ _ e
_⊢⋯ˢ_ {σ = σ} (⊢λ d) ⊢σ = ⊢λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} d (⊢↑ˢ {σ = σ} ⊢σ _))
_⊢⋯ˢ_ {σ = σ} (⊢Λ d) ⊢σ = ⊢Λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} d (⊢↑ˢ {σ = σ} ⊢σ _))
_⊢⋯ˢ_ {σ = σ} (⊢· d₁ d₂) ⊢σ =
  ⊢· (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)
_⊢⋯ˢ_ {σ = σ} (⊢• d₁ d₂) ⊢σ =
  ⊢• (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)
_⊢⋯ˢ_ {σ = σ} (⊢rcd d) ⊢σ = ⊢rcd (_⊢⋯ˢᴱ_ {σ = σ} d ⊢σ)
_⊢⋯ˢ_ {σ = σ} (⊢# d h) ⊢σ = ⊢# (_⊢⋯ˢ_ {σ = σ} d ⊢σ) (Has-sub {σ = σ} h)
_⊢⋯ˢ_ {σ = σ} {Γ₂ = Γ₂} (⊢let {n = n} {Δ = Δ} {e₂ = e₂} {B = B} d pt body) ⊢σ =
  ⊢let (_⊢⋯ˢ_ {σ = σ} d ⊢σ) (⊢ᵖ-sub σ pt)
    (subst (λ z → (ext-ctx (Tel-sub Δ σ) idᴿ Γ₂) ⊢ (e₂ [ (σ ↑ˢ* n) ]ˢ) ∶ z)
           (cong (B [_]ˢ) (wk↑-sub Δ σ))
           (_⊢⋯ˢ_ {σ = σ ↑ˢ* n} body (⊢ext-ctxˢ Δ idᴿ idᴿ refl ⊢σ)))
_⊢⋯ˢ_ {σ = σ} (⊢<: d₁ d₂) ⊢σ =
  ⊢<: (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)

_⊢⋯ˢᴿ_ {σ = σ} <:ᴿ-nil  ⊢σ = <:ᴿ-nil
_⊢⋯ˢᴿ_ {σ = σ} <:ᴿ-refl ⊢σ = <:ᴿ-refl
_⊢⋯ˢᴿ_ {σ = σ} (<:ᴿ-cons h d r) ⊢σ =
  <:ᴿ-cons (Has-sub {σ = σ} h) (_⊢⋯ˢ_ {σ = σ} d ⊢σ) (_⊢⋯ˢᴿ_ {σ = σ} r ⊢σ)

_⊢⋯ˢᴱ_ {σ = σ} ⊢ᴿ-nil ⊢σ = ⊢ᴿ-nil
_⊢⋯ˢᴱ_ {σ = σ} (⊢ᴿ-cons d ds) ⊢σ =
  ⊢ᴿ-cons (_⊢⋯ˢ_ {σ = σ} d ⊢σ) (_⊢⋯ˢᴱ_ {σ = σ} ds ⊢σ)

⊢[] : ∀ {Γ : Ctx S} {t : S ⊢ s} {A : S ∶⊢ s} →
  Γ ⊢ t ∶ A → (t ∙ˢ idˢ) ∶ (A ∷ₜ Γ) →ˢ Γ
⊢[] d _ zero    _ refl = d
⊢[] d _ (suc x) _ refl = ⊢var refl

⊢idˢ : ∀ {S} {Γ : Ctx S} → idˢ ∶ Γ →ˢ Γ
⊢idˢ s x A eq = ⊢var eq

⊢⨟ : ∀ {S₁ S₂ S₃} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃}
  {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {Γ₃ : Ctx S₃} →
  σ₁ ∶ Γ₁ →ˢ Γ₂ → σ₂ ∶ Γ₂ →ˢ Γ₃ → (σ₁ ⨟ σ₂) ∶ Γ₁ →ˢ Γ₃
⊢⨟ {σ₂ = σ₂} ⊢σ₁ ⊢σ₂ s x A eq = _⊢⋯ˢ_ {σ = σ₂} (⊢σ₁ _ _ _ eq) ⊢σ₂

-- the matched values are well typed, pointwise
data AllTyped {S} (Γ : Ctx S) : ∀ {n₁ n₂} → Tel S n₁ n₂ → Vals S n₁ n₂ → Set where
  []  : ∀ {n} → AllTyped Γ {n} {n} [] []
  _∷_ : ∀ {n₁ n₂ A v} {Δ : Tel S (suc n₁) n₂} {vs : Vals S (suc n₁) n₂} →
        Γ ⊢ v ∶ A → AllTyped Γ Δ vs → AllTyped Γ (A ∷ Δ) (v ∷ vs)

AllTyped-++ : ∀ {S n₁ n₂ n₃} {Γ : Ctx S} {Δ₁ : Tel S n₁ n₂} {Δ₂ : Tel S n₂ n₃}
  {ws : Vals S n₁ n₂} {vs : Vals S n₂ n₃} →
  AllTyped Γ Δ₁ ws → AllTyped Γ Δ₂ vs → AllTyped Γ (Δ₁ ++ᵗ Δ₂) (ws ++ᵛ vs)
AllTyped-++ []       bs = bs
AllTyped-++ (d ∷ ds) bs = d ∷ AllTyped-++ ds bs

-- E-LetV's substitution is well typed
⊢sub : ∀ {S n₁ n₂} {Γ : Ctx S} {Γ′ : Ctx (ext n₁ S)}
  {Δ : Tel S n₁ n₂} {vs : Vals S n₁ n₂} (w : S →ᴿ ext n₁ S) →
  w ∶ Γ →ᴿ Γ′ → AllTyped Γ Δ vs → (sub vs w) ∶ (ext-ctx Δ w Γ′) →ˢ Γ′
⊢sub w ⊢w []                          = ⊢idˢ
⊢sub {Γ′ = Γ′} w ⊢w (_∷_ {A = A} {v = v} {vs = vs} d ds) =
  ⊢⨟ {σ₁ = sub vs (w ⨟ᴿ wkᴿ expr)} {σ₂ = (v [ w ]ᴿ) ∙ˢ idˢ}
     (⊢sub (w ⨟ᴿ wkᴿ expr) (⊢⨟ᴿ {Γ₂ = Γ′} {Γ₃ = (A [ w ]ᴿ) ∷ₜ Γ′} ⊢w (⊢wkᴿ (A [ w ]ᴿ))) ds)
     (⊢[] (d ⊢⋯ᴿ ⊢w))

-- and it undoes the weakening the let-body's type carries
sub-wk : ∀ {S n₁ n₂} {Γ : Ctx S} {Δ : Tel S n₁ n₂} {vs : Vals S n₁ n₂} →
  AllTyped Γ Δ vs → (w : S →ᴿ ext n₁ S) →
  ∀ {s} (t : (ext n₁ S) ⊢ s) → (t [ wk↑ Δ ]ᴿ) [ (sub vs w) ]ˢ ≡ t
sub-wk []       w t = refl
sub-wk (_∷_ {v = v} d ds) w t =
  cong (_[ ((v [ w ]ᴿ) ∙ˢ idˢ) ]ˢ) (sub-wk ds (w ⨟ᴿ wkᴿ expr) (t [ wkᴿ expr ]ᴿ))

-- ═══ Part 2B: preservation and progress ════════════════════════════

data Val    : S ⊢ expr → Set
data ValsᴿE : S ⊢ rexpr → Set

data Val where
  vλ   : Val (λx[ A ] e)
  vΛ   : Val (Λα[<: A ] e)
  vrcd : ValsᴿE re → Val (RcdE re)

data ValsᴿE where
  vnil  : ValsᴿE (nilE {S = S})
  vcons : Val e → ValsᴿE re → ValsᴿE (consE l e re)

infix 3 _↪_ _↪ᴿ_
data _↪_  : S ⊢ expr → S ⊢ expr → Set
data _↪ᴿ_ : S ⊢ rexpr → S ⊢ rexpr → Set

data _↪_ where
  β-λ    : Val e₂ → ((λx[ A ] e₁) · e₂) ↪ (e₁ [ e₂ ]₀)
  β-Λ    : ((Λα[<: A ] e) • C) ↪ (e [ C ]₀)
  β-#    : ∀ {re : S ⊢ rexpr} {l e} → ValsᴿE re → HasE re l e → ((RcdE re) # l) ↪ e
  ξ-·₁   : e₁ ↪ e → (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂   : Val e₁ → e₂ ↪ e → (e₁ · e₂) ↪ (e₁ · e)
  ξ-•    : e ↪ e′ → (e • C) ↪ (e′ • C)
  ξ-#    : e ↪ e′ → (e # l) ↪ (e′ # l)
  ξ-rcd  : re₁ ↪ᴿ re₂ → (RcdE re₁) ↪ (RcdE re₂)
  -- E-LetV
  β-let  : ∀ {n} {p : S ⊢ pat 0 n} {v : S ⊢ expr} {e₂ : (ext n S) ⊢ expr} {vs} →
           Val v → Match p v vs → (letP p v e₂) ↪ (e₂ [ (sub vs idᴿ) ]ˢ)
  -- the `let p = E in t` evaluation context
  ξ-let  : ∀ {n} {p : S ⊢ pat 0 n} {e₁ e₁′ : S ⊢ expr} {e₂ : (ext n S) ⊢ expr} →
           e₁ ↪ e₁′ → (letP p e₁ e₂) ↪ (letP p e₁′ e₂)

-- E-Ctx for the record context {lᵢ=vᵢ, lⱼ=E, lₖ=tₖ}: the fields before
-- the hole must already be values
data _↪ᴿ_ where
  ξ-here : e ↪ e′ → (consE l e re) ↪ᴿ (consE l e′ re)
  ξ-tail : Val e → re₁ ↪ᴿ re₂ → (consE l e re₁) ↪ᴿ (consE l e re₂)

-- inversion, with the subtyping step built in
inv-λ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (λx[ A ] e) ∶ C → Γ ⊢ C <: (B₁ ⇒ B₂) →
  (Γ ⊢ B₁ <: A) × ((A ∷ₜ Γ) ⊢ e ∶ weaken B₂)
inv-λ (⊢λ d)    (<:-⇒ s₁ s₂) = s₁ , ⊢<: d (⊢weaken _ s₂)
inv-λ (⊢<: d s) sub          = inv-λ d (transitivity s sub)

inv-Λ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (Λα[<: A ] e) ∶ C → Γ ⊢ C <: (∀[<: B₁ ] B₂) →
  (Γ ⊢ B₁ <: A) × ((B₁ ∷ₜ Γ) ⊢ e ∶ B₂)
inv-Λ (⊢Λ d)    (<:-∀ s₁ s₂) = s₁ , ⊢<: (narrowing s₁ d) s₂
inv-Λ (⊢<: d s) sub          = inv-Λ d (transitivity s sub)

-- inversion for records: if a record value has a record type, then for
-- every field of that type there is a correspondingly-typed field in
-- the term
inv-rcd : ∀ {Γ : Ctx S} {re C rt l B} →
  Γ ⊢ (RcdE re) ∶ C → Γ ⊢ C <: (RcdT rt) → Has rt l B →
  Σ[ e ∈ S ⊢ expr ] (HasE re l e × Γ ⊢ e ∶ B)
inv-rcdᴱ : ∀ {Γ : Ctx S} {re rt l B} →
  Γ ⊢ re ∶ᴿ rt → Has rt l B → Σ[ e ∈ S ⊢ expr ] (HasE re l e × Γ ⊢ e ∶ B)
inv-rcdᴱ (⊢ᴿ-cons d ds) here      = _ , hereE , d
inv-rcdᴱ (⊢ᴿ-cons d ds) (there ne h) with inv-rcdᴱ ds h
... | (e , m , de) = e , thereE ne m , de
inv-rcd (⊢rcd d) (<:-rcd r) h with <:ᴿ-inv r h
... | (A , h′ , sub) with inv-rcdᴱ d h′
...   | (e , m , de) = e , m , ⊢<: de sub
inv-rcd (⊢<: d s) sub h = inv-rcd d (transitivity s sub) h

-- ─── canonical-forms exclusions ─────────────────────────────────────
not-Λ-⇒ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (Λα[<: A ] e) ∶ C → Γ ⊢ C <: (B₁ ⇒ B₂) → ⊥
not-Λ-⇒ (⊢Λ d)    ()
not-Λ-⇒ (⊢<: d s) sub = not-Λ-⇒ d (transitivity s sub)

not-rcd-⇒ : ∀ {Γ : Ctx S} {re C B₁ B₂} →
  Γ ⊢ (RcdE re) ∶ C → Γ ⊢ C <: (B₁ ⇒ B₂) → ⊥
not-rcd-⇒ (⊢rcd d)  ()
not-rcd-⇒ (⊢<: d s) sub = not-rcd-⇒ d (transitivity s sub)

not-λ-∀ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (λx[ A ] e) ∶ C → Γ ⊢ C <: (∀[<: B₁ ] B₂) → ⊥
not-λ-∀ (⊢λ d)    ()
not-λ-∀ (⊢<: d s) sub = not-λ-∀ d (transitivity s sub)

not-rcd-∀ : ∀ {Γ : Ctx S} {re C B₁ B₂} →
  Γ ⊢ (RcdE re) ∶ C → Γ ⊢ C <: (∀[<: B₁ ] B₂) → ⊥
not-rcd-∀ (⊢rcd d)  ()
not-rcd-∀ (⊢<: d s) sub = not-rcd-∀ d (transitivity s sub)

not-λ-rcd : ∀ {Γ : Ctx S} {A e C rt} →
  Γ ⊢ (λx[ A ] e) ∶ C → Γ ⊢ C <: (RcdT rt) → ⊥
not-λ-rcd (⊢λ d)    ()
not-λ-rcd (⊢<: d s) sub = not-λ-rcd d (transitivity s sub)

not-Λ-rcd : ∀ {Γ : Ctx S} {A e C rt} →
  Γ ⊢ (Λα[<: A ] e) ∶ C → Γ ⊢ C <: (RcdT rt) → ⊥
not-Λ-rcd (⊢Λ d)    ()
not-Λ-rcd (⊢<: d s) sub = not-Λ-rcd d (transitivity s sub)

-- ─── matching: M-Var / M-Rcd meet P-Var / P-Rcd ─────────────────────

<:ᴿ-incl : ∀ {S} {Γ : Ctx S} (rt : S ⊢ rtype) {rs : S ⊢ rtype} →
  (∀ {l A} → Has rt l A → Has rs l A) → WfR rt → Γ ⊢ rs <:ᴿ rt
<:ᴿ-incl nilT           inc wf-nil         = <:ᴿ-nil
<:ᴿ-incl (consT l A rt) inc (wf-cons ni w) =
  <:ᴿ-cons (inc here) (<:-reflexive A)
           (<:ᴿ-incl rt (λ h → inc (there (notin-≢ ni h) h)) w)

ValsᴿE-Has : ∀ {S} {re : S ⊢ rexpr} {l e} → ValsᴿE re → HasE re l e → Val e
ValsᴿE-Has (vcons v vs) hereE        = v
ValsᴿE-Has (vcons v vs) (thereE _ h) = ValsᴿE-Has vs h

-- a match against a well-typed value yields well-typed values
⊢match  : ∀ {S n₁ n₂} {Γ : Ctx S} {p : S ⊢ pat n₁ n₂} {A Δ v vs} →
  p ⊢ᵖ A ⇒ Δ → Γ ⊢ v ∶ A → Match p v vs → AllTyped Γ Δ vs
⊢matchᴿ : ∀ {S n₁ n₂} {Γ : Ctx S} {ps : S ⊢ rpat n₁ n₂} {rt Δ re vs} →
  ps ⊢ʳ rt ⇒ Δ → WfR rt → Γ ⊢ (RcdE re) ∶ (RcdT rt) → Matchᴿ ps re vs →
  AllTyped Γ Δ vs
⊢match P-var        d M-var     = d ∷ []
⊢match (P-rcd w pt) d (M-rcd m) = ⊢matchᴿ pt w d m
⊢matchᴿ P-nil w d M-nil = []
⊢matchᴿ (P-cons pt₁ pt₂) (wf-cons ni w) d (M-cons hasE m₁ m₂)
  with inv-rcd d (<:-reflexive _) here
... | (e′ , hasE′ , de′) =
  AllTyped-++
    (⊢match pt₁ (subst (λ z → _ ⊢ z ∶ _) (HasE-unique hasE′ hasE) de′) m₁)
    (⊢matchᴿ pt₂ w
      (⊢<: d (<:-rcd (<:ᴿ-incl _ (λ h → there (notin-≢ ni h) h) w))) m₂)

-- and a match always succeeds on a well-typed value: this is what
-- progress needs for E-LetV
match-total  : ∀ {S n₁ n₂} {Γ : Ctx S} {p : S ⊢ pat n₁ n₂} {A Δ v} →
  p ⊢ᵖ A ⇒ Δ → Γ ⊢ v ∶ A → Val v → Σ[ vs ∈ Vals S n₁ n₂ ] Match p v vs
matchᴿ-total : ∀ {S n₁ n₂} {Γ : Ctx S} {ps : S ⊢ rpat n₁ n₂} {rt Δ re} →
  ps ⊢ʳ rt ⇒ Δ → WfR rt → Γ ⊢ (RcdE re) ∶ (RcdT rt) → ValsᴿE re →
  Σ[ vs ∈ Vals S n₁ n₂ ] Matchᴿ ps re vs
match-total P-var        d val      = _ , M-var
match-total (P-rcd w pt) d vλ       = ⊥-elim (not-λ-rcd d (<:-reflexive _))
match-total (P-rcd w pt) d vΛ       = ⊥-elim (not-Λ-rcd d (<:-reflexive _))
match-total (P-rcd w pt) d (vrcd vs) with matchᴿ-total pt w d vs
... | (ws , m) = ws , M-rcd m
matchᴿ-total P-nil w d vs = [] , M-nil
matchᴿ-total (P-cons pt₁ pt₂) (wf-cons ni w) d vs
  with inv-rcd d (<:-reflexive _) here
... | (e , hasE , de) with match-total pt₁ de (ValsᴿE-Has vs hasE)
...   | (ws , m₁) with matchᴿ-total pt₂ w
                       (⊢<: d (<:-rcd (<:ᴿ-incl _ (λ h → there (notin-≢ ni h) h) w))) vs
...     | (us , m₂) = (ws ++ᵛ us) , M-cons hasE m₁ m₂

-- ─── preservation ───────────────────────────────────────────────────

preservation  : ∀ {Γ : Ctx S} {e e′ : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → e ↪ e′ → Γ ⊢ e′ ∶ A
preservationᴿ : ∀ {Γ : Ctx S} {re re′ : S ⊢ rexpr} {rt} →
  Γ ⊢ re ∶ᴿ rt → re ↪ᴿ re′ → Γ ⊢ re′ ∶ᴿ rt

preservation (⊢` _)  ()
preservation (⊢λ _)  ()
preservation (⊢Λ _)  ()
preservation (⊢· {e₂ = e₂} d₁ d₂) (β-λ v) with inv-λ d₁ (<:-reflexive _)
... | (sub , body) = _⊢⋯ˢ_ {σ = e₂ ∙ˢ idˢ} body (⊢[] (⊢<: d₂ sub))
preservation (⊢· d₁ d₂) (ξ-·₁ st)   = ⊢· (preservation d₁ st) d₂
preservation (⊢· d₁ d₂) (ξ-·₂ v st) = ⊢· d₁ (preservation d₂ st)
preservation (⊢• {C = C} d₁ d₂) β-Λ with inv-Λ d₁ (<:-reflexive _)
... | (sub , body) = _⊢⋯ˢ_ {σ = C ∙ˢ idˢ} body (⊢[] d₂)
preservation (⊢• d₁ d₂) (ξ-• st) = ⊢• (preservation d₁ st) d₂
preservation (⊢rcd d) (ξ-rcd st) = ⊢rcd (preservationᴿ d st)
preservation (⊢# d h) (β-# vs m) with inv-rcd d (<:-reflexive _) h
... | (e , m′ , de) = subst (λ z → _ ⊢ z ∶ _) (HasE-unique m′ m) de
preservation (⊢# d h) (ξ-# st) = ⊢# (preservation d st) h
preservation {Γ = Γ} (⊢let {Δ = Δ} {e₂ = e₂} {B = B} d pt body) (β-let {vs = vs} v m)
  with ⊢match pt d m
... | at = subst (λ z → Γ ⊢ (e₂ [ (sub vs idᴿ) ]ˢ) ∶ z) (sub-wk at idᴿ B)
                 (_⊢⋯ˢ_ {σ = sub vs idᴿ} body (⊢sub idᴿ ⊢idᴿ at))
preservation (⊢let d pt body) (ξ-let st) = ⊢let (preservation d st) pt body
preservation (⊢<: d s) st      = ⊢<: (preservation d st) s

preservationᴿ (⊢ᴿ-cons d ds) (ξ-here st)   = ⊢ᴿ-cons (preservation d st) ds
preservationᴿ (⊢ᴿ-cons d ds) (ξ-tail v st) = ⊢ᴿ-cons d (preservationᴿ ds st)

-- ─── progress ───────────────────────────────────────────────────────

data Progress {S} (e : S ⊢ expr) : Set where
  step : ∀ {e′ : S ⊢ expr} → e ↪ e′ → Progress e
  done : Val e → Progress e

data ProgressᴿE {S} (re : S ⊢ rexpr) : Set where
  stepᴿ : ∀ {re′ : S ⊢ rexpr} → re ↪ᴿ re′ → ProgressᴿE re
  doneᴿ : ValsᴿE re → ProgressᴿE re

-- canonical forms, by matching on the value

app-step : ∀ {Γ : Ctx S} {e₁ e₂ : S ⊢ expr} {A B} →
  Γ ⊢ e₁ ∶ (A ⇒ B) → Val e₁ → Val e₂ → Progress (e₁ · e₂)
app-step d vλ       v₂ = step (β-λ v₂)
app-step d vΛ       v₂ = ⊥-elim (not-Λ-⇒ d (<:-reflexive _))
app-step d (vrcd _) v₂ = ⊥-elim (not-rcd-⇒ d (<:-reflexive _))

tapp-step : ∀ {Γ : Ctx S} {e : S ⊢ expr} {A B C} →
  Γ ⊢ e ∶ (∀[<: A ] B) → Val e → Progress (e • C)
tapp-step d vλ       = ⊥-elim (not-λ-∀ d (<:-reflexive _))
tapp-step d vΛ       = step β-Λ
tapp-step d (vrcd _) = ⊥-elim (not-rcd-∀ d (<:-reflexive _))

proj-step : ∀ {Γ : Ctx S} {e : S ⊢ expr} {rt l A} →
  Γ ⊢ e ∶ (RcdT rt) → Has rt l A → Val e → Progress (e # l)
proj-step d h vλ       = ⊥-elim (not-λ-rcd d (<:-reflexive _))
proj-step d h vΛ       = ⊥-elim (not-Λ-rcd d (<:-reflexive _))
proj-step d h (vrcd vs) with inv-rcd d (<:-reflexive _) h
... | (e , m , de) = step (β-# vs m)

progress  : ∀ {Γ : Ctx []} {e : [] ⊢ expr} {A} → Γ ⊢ e ∶ A → Progress e
progressᴿ : ∀ {Γ : Ctx []} {re : [] ⊢ rexpr} {rt} → Γ ⊢ re ∶ᴿ rt → ProgressᴿE re

progress (⊢` {x = ()} _)
progress (⊢λ _) = done vλ
progress (⊢Λ _) = done vΛ
progress (⊢· d₁ d₂) with progress d₁
... | step st = step (ξ-·₁ st)
... | done v₁ with progress d₂
...   | step st = step (ξ-·₂ v₁ st)
...   | done v₂ = app-step d₁ v₁ v₂
progress (⊢• d₁ d₂) with progress d₁
... | step st = step (ξ-• st)
... | done v  = tapp-step d₁ v
progress (⊢rcd d) with progressᴿ d
... | stepᴿ st = step (ξ-rcd st)
... | doneᴿ vs = done (vrcd vs)
progress (⊢# d h) with progress d
... | step st = step (ξ-# st)
... | done v  = proj-step d h v
progress (⊢let d pt body) with progress d
... | step st = step (ξ-let st)
... | done v with match-total pt d v
...   | (vs , m) = step (β-let v m)
progress (⊢<: d _) = progress d

progressᴿ ⊢ᴿ-nil = doneᴿ vnil
progressᴿ (⊢ᴿ-cons d ds) with progress d
... | step st = stepᴿ (ξ-here st)
... | done v with progressᴿ ds
...   | stepᴿ st = stepᴿ (ξ-tail v st)
...   | doneᴿ vs = doneᴿ (vcons v vs)

-- ═══ narrowing with A trailing ∆, challenge Lemma 3.2 in full ══════

data Tele (S : Scope) : Scope → Set where
  []  : Tele S S
  _◂_ : ∀ {S′ s} (A : S′ ∶⊢ s) → Tele S S′ → Tele S (s ∷ S′)

infixr 5 _◂_

_▸_ : ∀ {S S′} → Tele S S′ → Ctx S → Ctx S′
[]      ▸ Γ = Γ
(A ◂ Δ) ▸ Γ = A ∷ₜ (Δ ▸ Γ)

wk-tele : ∀ {S S′} → Tele S S′ → S ⊢ type → S′ ⊢ type
wk-tele []      A = A
wk-tele (B ◂ Δ) A = weaken (wk-tele Δ A)

narrow-tele : ∀ {S S′} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} (Δ : Tele S S′) →
  Narrowing Γ₂ Q Γ₁ → Narrowing (Δ ▸ Γ₂) (wk-tele Δ Q) (Δ ▸ Γ₁)
narrow-tele []                nr = nr
narrow-tele (_◂_ {s = s} A Δ) nr = narrow-ext (narrow-tele Δ nr) s A

size-wk-tele : ∀ {S S′} (Δ : Tele S S′) (A : S ⊢ type) →
  size (wk-tele Δ A) ≡ size A
size-wk-tele []      A = refl
size-wk-tele (B ◂ Δ) A =
  ≡-trans (size-ren (wk-tele Δ A) (wkᴿ _)) (size-wk-tele Δ A)

-- 3.2 Lemma [Narrowing], with records
narrowing∆ : ∀ {S S′} {Γ : Ctx S} {P Q : S ⊢ type} (Δ : Tele (type ∷ S) S′)
  {t : S′ ⊢ s} {A : S′ ∶⊢ s} →
  Γ ⊢ P <: Q → (Δ ▸ (Q ∷ₜ Γ)) ⊢ t ∶ A → (Δ ▸ (P ∷ₜ Γ)) ⊢ t ∶ A
narrowing∆ {Q = Q} Δ d =
  narrow (size Q)
    (subst (_≤ size Q)
      (sym (≡-trans (size-wk-tele Δ (weaken Q)) (size-ren Q (wkᴿ type))))
      ≤-refl)
    (narrow-tele Δ (narrow-here d))

narrowing′ : ∀ {Γ : Ctx S} {P Q : S ⊢ type} {t : (type ∷ S) ⊢ s} {A} →
  Γ ⊢ P <: Q → (Q ∷ₜ Γ) ⊢ t ∶ A → (P ∷ₜ Γ) ⊢ t ∶ A
narrowing′ = narrowing∆ []

-- ═══ eliminating the primitive reflexivity rule ═════════════════════
-- `_⊢_<:ᴿ°_` is SA-Rcd exactly: the challenge's two rules, with no
-- reflexivity rule.  Below: (i) `<:ᴿ-refl` is not admissible in
-- general; (ii) it is eliminable at every well-formed record body,
-- i.e. every record type the challenge's syntax denotes;
-- (iii) transitivity therefore transfers to SA-Rcd proper.

infix 3 _⊢_<:ᴿ°_
data _⊢_<:ᴿ°_ {S} (Γ : Ctx S) : S ⊢ rtype → S ⊢ rtype → Set where
  °nil  : ∀ {rt} → Γ ⊢ rt <:ᴿ° nilT
  °cons : ∀ {rt₁ rt₂ l A B} →
    Has rt₁ l A → Γ ⊢ A ∶ B → Γ ⊢ rt₁ <:ᴿ° rt₂ → Γ ⊢ rt₁ <:ᴿ° (consT l B rt₂)

-- (i) non-admissibility.  At a record body that is a variable -- a form
-- F<: does not have, but the syntax admits at every sort -- the only
-- derivation is `<:ᴿ-refl`.
<:ᴿ-var-forces-refl : ∀ {Γ : Ctx S} {rt} {x : S ∋ rtype} →
  Γ ⊢ rt <:ᴿ (` x) → rt ≡ (` x)
<:ᴿ-var-forces-refl <:ᴿ-refl = refl


-- (ii) reflexivity is derivable in sa-Rcd proper, for well-formed bodies
refl° : ∀ {Γ : Ctx S} (rt : S ⊢ rtype) {rs : S ⊢ rtype} →
  (∀ {l A} → Has rt l A → Has rs l A) → WfR rt → Γ ⊢ rs <:ᴿ° rt
refl° nilT           inc wf-nil          = °nil
refl° (consT l A rt) inc (wf-cons ni w)  =
  °cons (inc here) (<:-reflexive A)
        (refl° rt (λ h → inc (there (notin-≢ ni h) h)) w)

°→ : ∀ {Γ : Ctx S} {rt₁ rt₂} → Γ ⊢ rt₁ <:ᴿ° rt₂ → Γ ⊢ rt₁ <:ᴿ rt₂
°→ °nil          = <:ᴿ-nil
°→ (°cons h d r) = <:ᴿ-cons h d (°→ r)

-- the elimination: every derivation of my relation at a well-formed
-- record body is matched by an sa-Rcd derivation
→° : ∀ {Γ : Ctx S} {rt₁ rt₂} → WfR rt₂ → Γ ⊢ rt₁ <:ᴿ rt₂ → Γ ⊢ rt₁ <:ᴿ° rt₂
→° w              <:ᴿ-nil          = °nil
→° (wf-cons ni w) (<:ᴿ-cons h d r) = °cons h d (→° w r)
→° w              <:ᴿ-refl         = refl° _ (λ h → h) w

-- (iii) transitivity for sa-Rcd proper, no reflexivity rule involved
-- in the statement, at either end
transitivityᴿ° : ∀ {Γ : Ctx S} {rs rq rt : S ⊢ rtype} → WfR rt →
  Γ ⊢ rs <:ᴿ° rq → Γ ⊢ rq <:ᴿ° rt → Γ ⊢ rs <:ᴿ° rt
transitivityᴿ° {rq = rq} w d₁ d₂ =
  →° w (<:-transᴿ (sizeR rq) ≤-refl (°→ d₁) (°→ d₂))

-- ─── sanity: the pattern language is not vacuous ────────────────────

Γ₀ : Ctx []
Γ₀ _ ()

la lb : Label
la = 0
lb = 1

idTop : [] ⊢ expr
idTop = λx[ Top ] (` zero)

⊢idTop : Γ₀ ⊢ idTop ∶ (Top ⇒ Top)
⊢idTop = ⊢λ (⊢` refl)

-- the record type {a:Top→Top, b:Top→Top}, with distinct labels
rt₀ : [] ⊢ rtype
rt₀ = consT la (Top ⇒ Top) (consT lb (Top ⇒ Top) nilT)

wf-rt₀ : WfR rt₀
wf-rt₀ = wf-cons (ni-cons (λ ()) ni-nil) (wf-cons ni-nil wf-nil)

rec₀ : [] ⊢ expr
rec₀ = RcdE (consE la idTop (consE lb idTop nilE))

⊢rec₀ : Γ₀ ⊢ rec₀ ∶ (RcdT rt₀)
⊢rec₀ = ⊢rcd (⊢ᴿ-cons ⊢idTop (⊢ᴿ-cons ⊢idTop ⊢ᴿ-nil))

-- the record pattern {a = x:Top→Top, b = y:Top→Top}, binding two vars
pat₀ : [] ⊢ pat 0 2
pat₀ = prcd (consP la (pvar (Top ⇒ Top)) (consP lb (pvar (Top ⇒ Top)) nilP))

tel₀ : Tel [] 0 2
tel₀ = (Top ⇒ Top) ∷ ((Top ⇒ Top) ∷ [])

⊢pat₀ : pat₀ ⊢ᵖ (RcdT rt₀) ⇒ tel₀
⊢pat₀ = P-rcd wf-rt₀ (P-cons P-var (P-cons P-var P-nil))

-- let {a=x, b=y} = {a=id, b=id} in x   :  Top→Top
letexp : [] ⊢ expr
letexp = letP pat₀ rec₀ (` (suc zero))

⊢letexp : Γ₀ ⊢ letexp ∶ (Top ⇒ Top)
⊢letexp = ⊢let ⊢rec₀ ⊢pat₀ (⊢` refl)

-- it matches, and it steps
match₀ : Match pat₀ rec₀ (idTop ∷ (idTop ∷ []))
match₀ = M-rcd (M-cons hereE M-var
                (M-cons (thereE (λ ()) hereE) M-var M-nil))

step₀ : letexp ↪ ((`_ (suc zero)) [ (sub (idTop ∷ (idTop ∷ [])) idᴿ) ]ˢ)
step₀ = β-let (vrcd (vcons vλ (vcons vλ vnil))) match₀

-- preservation, run on that concrete reduction
⊢after : Γ₀ ⊢ ((`_ (suc zero)) [ (sub (idTop ∷ (idTop ∷ [])) idᴿ) ]ˢ) ∶ (Top ⇒ Top)
⊢after = preservation ⊢letexp step₀

-- ═══ challenge-referencing names (Parts 1B and 2B, full language) ═══

-- 3.1 Lemma [Transitivity], records and patterns
lemma-3-1-transitivity : ∀ {Γ : Ctx S} {A Q B : S ⊢ type} →
  Γ ⊢ A <: Q → Γ ⊢ Q <: B → Γ ⊢ A <: B
lemma-3-1-transitivity = transitivity

-- 3.1 again, for SA-Rcd proper (no reflexivity rule in the statement)
lemma-3-1-transitivity-SA-Rcd : ∀ {Γ : Ctx S} {rs rq rt : S ⊢ rtype} →
  WfR rt → Γ ⊢ rs <:ᴿ° rq → Γ ⊢ rq <:ᴿ° rt → Γ ⊢ rs <:ᴿ° rt
lemma-3-1-transitivity-SA-Rcd = transitivityᴿ°

-- 3.2 Lemma [Narrowing], with the trailing ∆
lemma-3-2-narrowing : ∀ {S S′} {Γ : Ctx S} {P Q : S ⊢ type}
  (Δ : Tele (type ∷ S) S′) {t : S′ ⊢ s} {A : S′ ∶⊢ s} →
  Γ ⊢ P <: Q → (Δ ▸ (Q ∷ₜ Γ)) ⊢ t ∶ A → (Δ ▸ (P ∷ₜ Γ)) ⊢ t ∶ A
lemma-3-2-narrowing = narrowing∆

-- 3.3 Theorem [Preservation], for F<: with records and patterns
theorem-3-3-preservation : ∀ {Γ : Ctx S} {e e′ : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → e ↪ e′ → Γ ⊢ e′ ∶ A
theorem-3-3-preservation = preservation

-- 3.4 Theorem [Progress], for F<: with records and patterns
theorem-3-4-progress : ∀ {Γ : Ctx []} {e : [] ⊢ expr} {A} →
  Γ ⊢ e ∶ A → Progress e
theorem-3-4-progress = progress
