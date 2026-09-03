{-# OPTIONS --rewriting --local-confluence-check #-}

-- Multi-sorted, intrinsically scoped System F with first-class renamings,
-- and its σ-calculus as a locally confluent Agda REWRITE system
-- (machine-checked with --local-confluence-check).
--
-- Renamings are a second kind of map that survives in normal forms,
-- rather than a termination device erased by `coincidence`.  That one
-- decision is what takes the rule set from 41 rules to 73.
--
-- The equational core is σ⇑ [Curien-Hardin-Levy JACM 1996; tables in
-- Hardin-Maranget-Pagano JFP 8(2) 1998, figs. 1-2], instantiated at the
-- four map-sort pairs; the bridge between the two worlds is Autosubst
-- 2's [Stark-Schaefer-Kaiser CPP 2019; Stark 2020].
--
-- The curation: first-class lifting, no η, composition pushes at mode V
-- and folds at mode T, and coincidence is oriented ˢ→ᴿ.
--
-- See trs/TRS.md for the full design record: why each of these
-- choices is forced, the rule-by-rule correspondence with σ⇑ and
-- Autosubst 2, and the gained/lost accounting.

module systemf where

--! E >

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_; drop)
open import Data.Nat using (ℕ; zero; suc)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

-- ─── syntax ─────────────────────────────────────────────────────────

--! MultiSorted {
data Sort : Set where
  expr type kind : Sort
Scope = List Sort
--! }

variable
  s s₁ s₂ s′ : Sort
  S S₁ S₂ S₃ : Scope

--! MultiSortedTm {
data Mode : Set where V T : Mode

data _⊢[_]_ : Scope → Mode → Sort → Set

_⊢_ = _⊢[ T ]_
_∋_ = _⊢[ V ]_

data _⊢[_]_ where
  zero    : (s ∷ S) ∋ s
  suc     : S ∋ s → (s′ ∷ S) ∋ s
  `_      : S ∋ s → S ⊢ s
  λx_     : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_     : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_ : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_     : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _•_     : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_     : S ⊢ type → S ⊢ type → S ⊢ type
  *       : S ⊢ kind
--! }

variable
  m          : Mode
  e e₁ e₂ e′ : S ⊢ expr
  k k′       : S ⊢ kind
  t t₁ t₂ t′ : S ⊢ s
  x x′       : S ∋ s
  x/t x/t′   : S ⊢[ m ] s

-- ─── maps ───────────────────────────────────────────────────────────

--! Ren {
_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s
--! }

--! Sub {
_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s
--! }

variable
  ξ ξ′ ξ₁ ξ₂ ξ₃ : S₁ →ᴿ S₂
  σ σ₁ σ₂ σ₃ τ : S₁ →ˢ S₂

-- ─── the renaming world ─────────────────────────────────────────────

-- Lifting is first-class in the renaming world too, and `_[_]ᴿ` is
-- mode-generic and mode-preserving: its V-instance is map application, so
-- there is no separate lookup operation and no V/T duplication.
--! RenOps {
opaque
  idᴿ : S →ᴿ S
  idᴿ _ x = x

  wkᴿ : ∀ s′ → S →ᴿ (s′ ∷ S)
  wkᴿ _ _ x = suc x

  _∙ᴿ_ : S₂ ∋ s → S₁ →ᴿ S₂ → (s ∷ S₁) →ᴿ S₂
  (x ∙ᴿ ξ) _ zero    = x
  (_ ∙ᴿ ξ) _ (suc x) = ξ _ x

  _↑ᴿ_ : S₁ →ᴿ S₂ → ∀ s → (s ∷ S₁) →ᴿ (s ∷ S₂)
  (ξ ↑ᴿ _) _ zero    = zero
  (ξ ↑ᴿ _) _ (suc x) = suc (ξ _ x)

  _[_]ᴿ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → S₂ ⊢[ m ] s
  _[_]ᴿ {m = V} x ξ   = ξ _ x
  (` x)         [ ξ ]ᴿ = ` (x [ ξ ]ᴿ)
  (λx e)        [ ξ ]ᴿ = λx (e [ (ξ ↑ᴿ _) ]ᴿ)
  (e₁ · e₂)     [ ξ ]ᴿ = (e₁ [ ξ ]ᴿ) · (e₂ [ ξ ]ᴿ)
  -- ...
--! [
  (Λα e)        [ ξ ]ᴿ = Λα (e [ (ξ ↑ᴿ _) ]ᴿ)
  (∀[α∶ k ] t)  [ ξ ]ᴿ = ∀[α∶ k [ ξ ]ᴿ ] (t [ (ξ ↑ᴿ _) ]ᴿ)
  (e • t)       [ ξ ]ᴿ = (e [ ξ ]ᴿ) • (t [ ξ ]ᴿ)
  (t₁ ⇒ t₂)     [ ξ ]ᴿ = (t₁ [ ξ ]ᴿ) ⇒ (t₂ [ ξ ]ᴿ)
  *             [ ξ ]ᴿ = *
--! ]
  _⨟ᴿ_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
  (ξ₁ ⨟ᴿ ξ₂) _ x = (ξ₁ _ x) [ ξ₂ ]ᴿ
--! }

-- ─── the substitution world ─────────────────────────────────────────

-- the σ-world's constants are embedded renamings: with the canonical
-- direction pointing at ᴿ, giving them their own symbols would only
-- create extra normal forms
--! SubT {
opaque
  ⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂
  ⟨ ξ ⟩ _ x = ` (x [ ξ ]ᴿ)

  _∙ˢ_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂
  (t ∙ˢ σ) _ zero    = t
  (t ∙ˢ σ) _ (suc x) = σ _ x

  _↑ˢ_  : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  (σ ↑ˢ _) _ zero    = ` zero
  (σ ↑ˢ _) _ (suc x) = (σ _ x) [ wkᴿ _ ]ᴿ

  _[_]ˢ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
  _[_]ˢ {m = V} x σ   = σ _ x
  (` x)         [ σ ]ˢ = σ _ x
  (λx e)        [ σ ]ˢ = λx (e [ (σ ↑ˢ _) ]ˢ)
  (e₁ · e₂)     [ σ ]ˢ = (e₁ [ σ ]ˢ) · (e₂ [ σ ]ˢ)
  -- ...
--! [
  (Λα e)        [ σ ]ˢ = Λα (e [ (σ ↑ˢ _) ]ˢ)
  (∀[α∶ k ] t)  [ σ ]ˢ = ∀[α∶ k [ σ ]ˢ ] (t [ (σ ↑ˢ _) ]ˢ)
  (e • t)       [ σ ]ˢ = (e [ σ ]ˢ) • (t [ σ ]ˢ)
  (t₁ ⇒ t₂)     [ σ ]ˢ = (t₁ [ σ ]ˢ) ⇒ (t₂ [ σ ]ˢ)
  *             [ σ ]ˢ = *
--! ]
  _⨟ˢ_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ⨟ˢ σ₂) _ x = (σ₁ _ x) [ σ₂ ]ˢ
--! }

--! SubIdWk {
idˢ : S →ˢ S
idˢ = ⟨ idᴿ ⟩

wkˢ : ∀ s′ → S →ˢ (s′ ∷ S)
wkˢ s′ = ⟨ wkᴿ s′ ⟩
--! }

--! Single {
_[_]₀ : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
t [ t′ ]₀ = t [ (t′ ∙ˢ idˢ) ]ˢ
--! }

-- ─── the two-world rewrite system ───────────────────────────────────

opaque
  unfolding idᴿ wkᴿ _∙ᴿ_ _↑ᴿ_ _[_]ᴿ _⨟ᴿ_ ⟨_⟩ _∙ˢ_ _[_]ˢ _↑ˢ_ _⨟ˢ_

  -- ══ Iᴿ. applied rules, renaming world ════════════════════════════
  def-wkᴿ     : x [ wkᴿ s′ ]ᴿ ≡ suc x
  def-∙ᴿ-zero : zero [ (x ∙ᴿ ξ) ]ᴿ ≡ x
  def-∙ᴿ-suc  : (suc {s′ = s′} x′) [ (x ∙ᴿ ξ) ]ᴿ ≡ x′ [ ξ ]ᴿ
  def-↑ᴿ-zero : zero [ (ξ ↑ᴿ s) ]ᴿ ≡ zero
  def-↑ᴿ-suc  : (suc x) [ (ξ ↑ᴿ s) ]ᴿ ≡ suc (x [ ξ ]ᴿ)

  -- ══ IIᴿ. traversal rules, renaming world ═════════════════════════
  instᴿ-x : (` x)        [ ξ ]ᴿ ≡ ` (x [ ξ ]ᴿ)
  instᴿ-λ : (λx e)       [ ξ ]ᴿ ≡ λx (e [ (ξ ↑ᴿ _) ]ᴿ)
  instᴿ-Λ : (Λα e)       [ ξ ]ᴿ ≡ Λα (e [ (ξ ↑ᴿ _) ]ᴿ)
  instᴿ-∀ : (∀[α∶ k ] t) [ ξ ]ᴿ ≡ ∀[α∶ k [ ξ ]ᴿ ] (t [ (ξ ↑ᴿ _) ]ᴿ)
  instᴿ-· : (e₁ · e₂)    [ ξ ]ᴿ ≡ (e₁ [ ξ ]ᴿ) · (e₂ [ ξ ]ᴿ)
  instᴿ-• : (e • t)      [ ξ ]ᴿ ≡ (e [ ξ ]ᴿ) • (t [ ξ ]ᴿ)
  instᴿ-⇒ : (t₁ ⇒ t₂)    [ ξ ]ᴿ ≡ (t₁ [ ξ ]ᴿ) ⇒ (t₂ [ ξ ]ᴿ)
  instᴿ-* : * {S = S}    [ ξ ]ᴿ ≡ *

  -- ══ IIIᴿ. map algebra, renaming world ════════════════════════════
  assocᴿ    : (ξ₁ ⨟ᴿ ξ₂) ⨟ᴿ ξ₃ ≡ ξ₁ ⨟ᴿ (ξ₂ ⨟ᴿ ξ₃)
  comp-idₗᴿ : idᴿ ⨟ᴿ ξ ≡ ξ
  comp-idᵣᴿ : ξ ⨟ᴿ idᴿ ≡ ξ
  -- distᴿ is a lemma, not a rule: its pair with compositionalityᴿᴿ-var
  -- (push) is non-joinable, because joining needs a case split on the
  -- variable that neither side can perform.  Measured: registering it
  -- costs 2 non-joinable pairs (with push and with ⟨⟩-split-⨟).
  distᴿ     : (x ∙ᴿ ξ₁) ⨟ᴿ ξ₂ ≡ (x [ ξ₂ ]ᴿ) ∙ᴿ (ξ₁ ⨟ᴿ ξ₂)
  interactᴿ : wkᴿ s ⨟ᴿ (x ∙ᴿ ξ) ≡ ξ

  -- ══ IVᴿ. lifting rules, renaming world ═══════════════════════════
  lift-idᴿ         : (idᴿ {S} ↑ᴿ s) ≡ idᴿ
  lift-dist-compᴿᴿ : ((ξ₁ ↑ᴿ s) ⨟ᴿ (ξ₂ ↑ᴿ s)) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s)
  lift-wkᴿ         : wkᴿ s ⨟ᴿ (ξ ↑ᴿ s) ≡ ξ ⨟ᴿ wkᴿ s
  lift-consᴿ       : (ξ ↑ᴿ s) ⨟ᴿ (x ∙ᴿ ξ′) ≡ x ∙ᴿ (ξ ⨟ᴿ ξ′)

  -- ══ Vᴿ. monad laws, renaming world ═══════════════════════════════
  -- both are mode-generic: on the renaming side the traversal
  -- preserves the mode, so each of these single rules is simultaneously
  -- σ⇑'s law on terms and its variable instance
  right-idᴿ : ∀ (x/t : S ⊢[ m ] s) → x/t [ idᴿ ]ᴿ ≡ x/t
  -- (Clos), split by mode: push at V, fold at T.  The halves point in
  -- opposite directions because a fold at V would overlap def-wkᴿ
  -- unjoinably.  trs/TRS.md, rules 22 and 23.
  compositionalityᴿᴿ-var : ∀ (x : S₁ ∋ s) {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    x [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ ≡ (x [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ
  compositionalityᴿᴿ : ∀ (t : S₁ ⊢ s) {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    (t [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ ≡ t [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ

  -- ══ VIᴿ. completion companions, renaming world ═══════════════════
  -- Push at V makes σ⇑'s VarShift2/FVarLift2/RVarLift2 unnecessary.
  -- What remains is the join of push with lift-dist-compᴿᴿ and with
  -- lift-consᴿ, and interact under a continuation.
  lift-dist-compᴿᴿ-var : (x [ (ξ₁ ↑ᴿ s) ]ᴿ) [ (ξ₂ ↑ᴿ s) ]ᴿ ≡ x [ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s) ]ᴿ
  lift-consᴿ-var       : (x [ (ξ ↑ᴿ s) ]ᴿ) [ (x′ ∙ᴿ ξ′) ]ᴿ ≡ x [ (x′ ∙ᴿ (ξ ⨟ᴿ ξ′)) ]ᴿ
  interactᴿ-⨟ᴿ         : wkᴿ s ⨟ᴿ ((x ∙ᴿ ξ) ⨟ᴿ ξ′) ≡ ξ ⨟ᴿ ξ′
  lift-wkᴿ-⨟ᴿ          : wkᴿ s ⨟ᴿ ((ξ ↑ᴿ s) ⨟ᴿ ξ′) ≡ ξ ⨟ᴿ (wkᴿ s ⨟ᴿ ξ′)
  lift-dist-compᴿᴿ-⨟ᴿ  : (ξ₁ ↑ᴿ s) ⨟ᴿ ((ξ₂ ↑ᴿ s) ⨟ᴿ ξ′) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s) ⨟ᴿ ξ′

  -- ══ Iˢ. applied rules, substitution world ════════════════════════
  -- (no def-id/def-wk: idˢ and wkˢ are embedded renamings, so their
  -- applied rules are instances of coincidence-var)
  --! DefLaws {
  coincidence-var : x [ ⟨ ξ ⟩ ]ˢ ≡ ` (x [ ξ ]ᴿ)
  def-∙ˢ-zero     : zero [ (t ∙ˢ σ) ]ˢ ≡ t
  def-∙ˢ-suc      : (suc {s′ = s′} x) [ (t ∙ˢ σ) ]ˢ ≡ x [ σ ]ˢ
  def-↑ˢ-zero     : zero [ (σ ↑ˢ s) ]ˢ ≡ ` zero
  def-↑ˢ-suc      : (suc x) [ (σ ↑ˢ s) ]ˢ ≡ x [ (σ ⨟ˢ ⟨ wkᴿ s ⟩) ]ˢ
  --! }

  -- ══ IIˢ. traversal rules, substitution world ═════════════════════
  --! TraversalLaws {
  inst-x : (` x)        [ σ ]ˢ ≡ x [ σ ]ˢ
  inst-λ : (λx e)       [ σ ]ˢ ≡ λx (e [ (σ ↑ˢ _) ]ˢ)
  inst-Λ : (Λα e)       [ σ ]ˢ ≡ Λα (e [ (σ ↑ˢ _) ]ˢ)
  inst-∀ : (∀[α∶ k ] t) [ σ ]ˢ ≡ ∀[α∶ k [ σ ]ˢ ] (t [ (σ ↑ˢ _) ]ˢ)
  inst-· : (e₁ · e₂)    [ σ ]ˢ ≡ (e₁ [ σ ]ˢ) · (e₂ [ σ ]ˢ)
  inst-• : (e • t)      [ σ ]ˢ ≡ (e [ σ ]ˢ) • (t [ σ ]ˢ)
  inst-⇒ : (t₁ ⇒ t₂)    [ σ ]ˢ ≡ (t₁ [ σ ]ˢ) ⇒ (t₂ [ σ ]ˢ)
  inst-* : * {S = S}    [ σ ]ˢ ≡ *
  --! }

  -- ══ VIˢ. completion companions, substitution world ═══════════════
  compositionalityᴿˢ-⨟-var : x [ (⟨ ξ ⟩ ⨟ˢ σ) ]ˢ ≡ (x [ ξ ]ᴿ) [ σ ]ˢ
  def-↑ˢ-zero-⨟            : zero [ ((σ ↑ˢ s) ⨟ˢ τ) ]ˢ ≡ zero [ τ ]ˢ
  def-↑ˢ-suc-⨟             : (suc x) [ ((σ ↑ˢ s) ⨟ˢ τ) ]ˢ ≡ x [ (σ ⨟ˢ (⟨ wkᴿ s ⟩ ⨟ˢ τ)) ]ˢ
  lift-wk-⨟                : ⟨ wkᴿ s ⟩ ⨟ˢ ((σ ↑ˢ s) ⨟ˢ τ) ≡ σ ⨟ˢ (⟨ wkᴿ s ⟩ ⨟ˢ τ)
  lift-dist-compˢˢ-⨟       : (σ₁ ↑ˢ s) ⨟ˢ ((σ₂ ↑ˢ s) ⨟ˢ τ) ≡ ((σ₁ ⨟ˢ σ₂) ↑ˢ s) ⨟ˢ τ

  -- ══ IIIˢ/IVˢ. map algebra and lifting, substitution world ════════
  --! InteractLaws {
  interact         : ⟨ wkᴿ s ⟩ ⨟ˢ (t ∙ˢ σ) ≡ σ
  comp-idₗ         : ⟨ idᴿ {S₁} ⟩ ⨟ˢ σ ≡ σ
  comp-idᵣ         : σ ⨟ˢ ⟨ idᴿ ⟩ ≡ σ
  lift-wk          : ⟨ wkᴿ s ⟩ ⨟ˢ (σ ↑ˢ s) ≡ σ ⨟ˢ ⟨ wkᴿ s ⟩
  assoc            : (σ₁ ⨟ˢ σ₂) ⨟ˢ σ₃ ≡ σ₁ ⨟ˢ (σ₂ ⨟ˢ σ₃)
  dist             : (t ∙ˢ σ₁) ⨟ˢ σ₂ ≡ (t [ σ₂ ]ˢ) ∙ˢ (σ₁ ⨟ˢ σ₂)
  lift-cons        : (σ ↑ˢ s) ⨟ˢ (t ∙ˢ τ) ≡ t ∙ˢ (σ ⨟ˢ τ)
  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ˢ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ˢ σ₂) ↑ˢ s)
  --! }

  -- ══ Vˢ. monad laws, substitution world ═══════════════════════════
  --! MonadLaws {
  compositionalityˢˢ : ∀ (x/t : S₁ ⊢[ m ] s)
    {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} →
    (x/t [ σ₁ ]ˢ) [ σ₂ ]ˢ ≡ x/t [ (σ₁ ⨟ˢ σ₂) ]ˢ
  --! }

  -- ══ the two mixed compositionality laws ══════════════════════════
  -- Autosubst's compRenSubst and compSubstRen.
  -- compositionalityᴿˢ is T-only: its V-instance is
  -- compositionalityᴿˢ-⨟-var read backwards, and registering both loops.
  compositionalityᴿˢ : ∀ (t : S₁ ⊢ s) {ξ₁ : S₁ →ᴿ S₂} {σ₂ : S₂ →ˢ S₃} →
    (t [ ξ₁ ]ᴿ) [ σ₂ ]ˢ ≡ t [ (⟨ ξ₁ ⟩ ⨟ˢ σ₂) ]ˢ
  -- mode-generic on the left: a ˢ-traversal accepts a variable as input
  compositionalityˢᴿ : ∀ (x/t : S₁ ⊢[ m ] s) {σ₁ : S₁ →ˢ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    (x/t [ σ₁ ]ˢ) [ ξ₂ ]ᴿ ≡ x/t [ (σ₁ ⨟ˢ ⟨ ξ₂ ⟩) ]ˢ

  -- the ⨟-companions of the two mixed fusions (same completion pattern
  -- as ShiftLift2/Lift2, one level up)
  lift-dist-compᴿˢ-⨟ : ∀ {S₄} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
    ⟨ ξ ↑ᴿ s ⟩ ⨟ˢ ((σ ↑ˢ s) ⨟ˢ τ) ≡ ((⟨ ξ ⟩ ⨟ˢ σ) ↑ˢ s) ⨟ˢ τ
  lift-dist-compˢᴿ-⨟ : ∀ {S₄} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
    (σ ↑ˢ s) ⨟ˢ (⟨ ξ ↑ᴿ s ⟩ ⨟ˢ τ) ≡ ((σ ⨟ˢ ⟨ ξ ⟩) ↑ˢ s) ⨟ˢ τ
  -- the variable-level mixed fusions: the join of compositionalityᴿˢ-⨟-var with
  -- lift-dist-compᴿˢ resp. of the σ-applied rules with lift-dist-compˢᴿ, at an
  -- abstract variable (neither side can case-split on it)
  lift-dist-compᴿˢ-var   : (x [ (ξ ↑ᴿ s) ]ᴿ) [ (σ ↑ˢ s) ]ˢ ≡ x [ ((⟨ ξ ⟩ ⨟ˢ σ) ↑ˢ s) ]ˢ
  lift-dist-compᴿˢ-⨟-var : ∀ {S₄} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
    (x [ (ξ ↑ᴿ s) ]ᴿ) [ ((σ ↑ˢ s) ⨟ˢ τ) ]ˢ ≡ x [ (((⟨ ξ ⟩ ⨟ˢ σ) ↑ˢ s) ⨟ˢ τ) ]ˢ

  -- cons absorbs a lifted embedded renaming, at the map and at the
  -- variable level (σ⇑'s LiftEnv, ⟨_⟩-flavoured)
  ⟨⟩-lift-cons     : ⟨ ξ ↑ᴿ s ⟩ ⨟ˢ (t ∙ˢ σ) ≡ t ∙ˢ (⟨ ξ ⟩ ⨟ˢ σ)
  ⟨⟩-lift-cons-var : (x [ (ξ ↑ᴿ s) ]ᴿ) [ (t ∙ˢ σ) ]ˢ ≡ x [ (t ∙ˢ (⟨ ξ ⟩ ⨟ˢ σ)) ]ˢ

  -- ⟨⟩-comp's C2 image ⟨ξ₁⟩ ⨟ (⟨ξ₂⟩ ⨟ τ) → ⟨ξ₁ ⨟ᴿ ξ₂⟩ ⨟ τ is the exact
  -- inverse of ⟨⟩-split-⨟ and loops with it, the one image in the system
  -- that cannot be taken.  What survives is that image restricted to the
  -- three ᴿ-rules whose firing makes progress, one rule for each.
  ⟨⟩-comp-⨟-lift-wkᴿ : ∀ {S₄} {ξ : S₁ →ᴿ S₂} {τ : (s ∷ S₂) →ˢ S₄} →
    ⟨ wkᴿ s ⟩ ⨟ˢ (⟨ ξ ↑ᴿ s ⟩ ⨟ˢ τ) ≡ ⟨ ξ ⟩ ⨟ˢ (⟨ wkᴿ s ⟩ ⨟ˢ τ)
  ⟨⟩-comp-⨟-interactᴿ : ∀ {ξ : S₁ →ᴿ S₂} {x : S₂ ∋ s} {τ : S₂ →ˢ S₃} →
    ⟨ wkᴿ s ⟩ ⨟ˢ (⟨ x ∙ᴿ ξ ⟩ ⨟ˢ τ) ≡ ⟨ ξ ⟩ ⨟ˢ τ
  ⟨⟩-comp-⨟-lift-dist-compᴿᴿ : ∀ {S₄} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
    ⟨ ξ₁ ↑ᴿ s ⟩ ⨟ˢ (⟨ ξ₂ ↑ᴿ s ⟩ ⨟ˢ τ) ≡ ⟨ (ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s ⟩ ⨟ˢ τ
  -- ⟨⟩-split-⨟ in tail position, where there is no continuation to
  -- match.  With one present it is derivable, so there is no
  -- ⟨⟩-split-tail-⨟.
  ⟨⟩-split-tail : ∀ {S₄} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} {ξ′ : (s ∷ S₃) →ᴿ S₄} →
    (σ ↑ˢ s) ⨟ˢ ⟨ (ξ ↑ᴿ s) ⨟ᴿ ξ′ ⟩ ≡ ((σ ⨟ˢ ⟨ ξ ⟩) ↑ˢ s) ⨟ˢ ⟨ ξ′ ⟩

  -- ══ the collapse family: ⟨_⟩ is pushed back into the ᴿ world ═════
  --! CoincidenceLaws {
  coincidence : ∀ (t : S ⊢ s) (ξ : S →ᴿ S₂) → t [ ⟨ ξ ⟩ ]ˢ ≡ t [ ξ ]ᴿ
  ⟨⟩-comp    : ⟨ ξ₁ ⟩ ⨟ˢ ⟨ ξ₂ ⟩ ≡ ⟨ ξ₁ ⨟ᴿ ξ₂ ⟩
  ⟨⟩-split-⨟ : ⟨ ξ₁ ⨟ᴿ ξ₂ ⟩ ⨟ˢ σ ≡ ⟨ ξ₁ ⟩ ⨟ˢ (⟨ ξ₂ ⟩ ⨟ˢ σ)
  ⟨⟩-lift    : (⟨ ξ ⟩ ↑ˢ s) ≡ ⟨ ξ ↑ᴿ s ⟩
  --! }

  -- ══ subsumed: σ⇑'s LiftId is a lemma, not a rule ═════════════════
  -- ⟨⟩-lift already sends its LHS to ⟨ idᴿ ↑ᴿ s ⟩, where lift-idᴿ
  -- finishes under the coercion.  A base rule subsumed by its own
  -- coercion image is redundant.  It still holds by refl for user code.
  lift-id : (⟨ idᴿ {S} ⟩ ↑ˢ s) ≡ ⟨ idᴿ ⟩

  -- ══ η: lemmas only, exactly as in the one-world file ═════════════
  η-idᴿ  : (zero {s = s} {S = S}) ∙ᴿ (wkᴿ s) ≡ idᴿ
  η-lawᴿ : (zero [ ξ ]ᴿ) ∙ᴿ (wkᴿ s ⨟ᴿ ξ) ≡ ξ
  η-id   : (` zero) ∙ˢ (wkˢ s) ≡ idˢ {S = s ∷ S}
  η-law  : (zero [ σ ]ˢ) ∙ˢ (wkˢ s ⨟ˢ σ) ≡ σ
  def-↑ᴿ : ξ ↑ᴿ s ≡ zero ∙ᴿ (ξ ⨟ᴿ wkᴿ s)
  def-↑ˢ : σ ↑ˢ s ≡ (` zero) ∙ˢ (σ ⨟ˢ wkˢ s)

  -- ── proofs ───────────────────────────────────────────────────────

  def-wkᴿ     = refl
  def-∙ᴿ-zero = refl
  def-∙ᴿ-suc  = refl
  def-↑ᴿ-zero = refl
  def-↑ᴿ-suc  = refl  -- ξ ⨟ᴿ wkᴿ s at a variable is suc (x [ ξ ]ᴿ)

  instᴿ-x = refl
  instᴿ-λ = refl
  instᴿ-Λ = refl
  instᴿ-∀ = refl
  instᴿ-· = refl
  instᴿ-• = refl
  instᴿ-⇒ = refl
  instᴿ-* = refl

  assocᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂} {ξ₃ = ξ₃} = ext λ x → sym (compositionalityᴿᴿ-var (ξ₁ _ x) {ξ₁ = ξ₂} {ξ₂ = ξ₃})
  comp-idₗᴿ = refl
  comp-idᵣᴿ = ext λ x → right-idᴿ _
  distᴿ     = ext λ { zero → refl ; (suc x) → refl }
  interactᴿ = refl

  lift-idᴿ     = ext λ { zero → refl ; (suc x) → refl }
  lift-dist-compᴿᴿ = ext λ { zero → refl ; (suc x) → refl }
  lift-wkᴿ     = refl
  lift-consᴿ   = ext λ { zero → refl ; (suc x) → refl }

  right-idᴿ {m = V} x    = refl
  right-idᴿ (` x)        = refl
  right-idᴿ (λx e)       = cong λx_ (trans (cong (e [_]ᴿ) lift-idᴿ) (right-idᴿ e))
  right-idᴿ (Λα e)       = cong Λα_ (trans (cong (e [_]ᴿ) lift-idᴿ) (right-idᴿ e))
  right-idᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idᴿ k)
                             (trans (cong (t [_]ᴿ) lift-idᴿ) (right-idᴿ t))
  right-idᴿ (e₁ · e₂)    = cong₂ _·_ (right-idᴿ e₁) (right-idᴿ e₂)
  right-idᴿ (e • t)      = cong₂ _•_ (right-idᴿ e) (right-idᴿ t)
  right-idᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idᴿ t₁) (right-idᴿ t₂)
  right-idᴿ *            = refl

  compositionalityᴿᴿ-var x           = refl
  compositionalityᴿᴿ (` x) {ξ₁ = ξ₁} {ξ₂ = ξ₂} = cong `_ (sym (compositionalityᴿᴿ-var x {ξ₁ = ξ₁} {ξ₂ = ξ₂}))
  compositionalityᴿᴿ (λx e)       = cong λx_ (trans (compositionalityᴿᴿ e) (cong (e [_]ᴿ) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (Λα e)       = cong Λα_ (trans (compositionalityᴿᴿ e) (cong (e [_]ᴿ) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿᴿ k)
                           (trans (compositionalityᴿᴿ t) (cong (t [_]ᴿ) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿᴿ e₁) (compositionalityᴿᴿ e₂)
  compositionalityᴿᴿ (e • t)      = cong₂ _•_ (compositionalityᴿᴿ e) (compositionalityᴿᴿ t)
  compositionalityᴿᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿᴿ t₁) (compositionalityᴿᴿ t₂)
  compositionalityᴿᴿ *            = refl

  lift-dist-compᴿᴿ-var {x = zero}  = refl
  lift-dist-compᴿᴿ-var {x = suc x} = refl
  lift-consᴿ-var {x = zero}  = refl
  lift-consᴿ-var {x = suc x} = refl
  interactᴿ-⨟ᴿ    = refl
  lift-wkᴿ-⨟ᴿ {s = s} {ξ = ξ} {ξ′ = ξ′} =
    trans (sym (assocᴿ {ξ₁ = wkᴿ s} {ξ₂ = ξ ↑ᴿ s} {ξ₃ = ξ′}))
          (trans (cong (_⨟ᴿ ξ′) (lift-wkᴿ {s = s}))
                 (assocᴿ {ξ₁ = ξ} {ξ₂ = wkᴿ s} {ξ₃ = ξ′}))
  lift-dist-compᴿᴿ-⨟ᴿ {ξ₁ = ξ₁} {s = s} {ξ₂ = ξ₂} {ξ′ = ξ′} =
    trans (sym (assocᴿ {ξ₁ = ξ₁ ↑ᴿ s} {ξ₂ = ξ₂ ↑ᴿ s} {ξ₃ = ξ′}))
          (cong (_⨟ᴿ ξ′) (lift-dist-compᴿᴿ {ξ₁ = ξ₁} {s = s} {ξ₂ = ξ₂}))

  coincidence-var = refl
  def-∙ˢ-zero  = refl
  def-∙ˢ-suc   = refl
  def-↑ˢ-zero  = refl
  def-↑ˢ-suc {x = x} {σ = σ} {s = s} = sym (coincidence (σ _ x) (wkᴿ s))
  compositionalityᴿˢ-⨟-var     = refl
  def-↑ˢ-zero-⨟ = refl
  def-↑ˢ-suc-⨟ {x = x} {σ = σ} {s = s} {τ = τ} =
    trans (compositionalityᴿˢ (σ _ x)) (cong ((σ _ x) [_]ˢ) (ext λ y → refl))
  interact  = refl
  comp-idₗ  = refl
  comp-idᵣ {σ = σ} = ext λ y → trans (coincidence (σ _ y) idᴿ) (right-idᴿ (σ _ y))
  lift-wk {s = s} {σ = σ} = ext λ y → sym (coincidence (σ _ y) (wkᴿ s))
  lift-id   = ext λ { zero → refl ; (suc x) → refl }
  lift-wk-⨟ {s = s} {σ = σ} {τ = τ} =
    trans (sym (assoc {σ₁ = ⟨ wkᴿ s ⟩} {σ₂ = σ ↑ˢ s} {σ₃ = τ}))
          (trans (cong (_⨟ˢ τ) (lift-wk {s = s} {σ = σ}))
                 (assoc {σ₁ = σ} {σ₂ = ⟨ wkᴿ s ⟩} {σ₃ = τ}))
  lift-dist-compˢˢ-⨟ {σ₁ = σ₁} {s = s} {σ₂ = σ₂} {τ = τ} =
    trans (sym (assoc {σ₁ = σ₁ ↑ˢ s} {σ₂ = σ₂ ↑ˢ s} {σ₃ = τ}))
          (cong (_⨟ˢ τ) (lift-dist-compˢˢ {σ₁ = σ₁} {s = s} {σ₂ = σ₂}))

  inst-x = refl
  inst-λ = refl
  inst-Λ = refl
  inst-∀ = refl
  inst-· = refl
  inst-• = refl
  inst-⇒ = refl
  inst-* = refl

  -- the stratified mixed lemmas, in the classical order:
  -- compositionalityᴿˢ needs only ᴿ-facts, compositionalityˢᴿ needs compositionalityᴿᴿ, and the
  -- σ-fusion needs both
  lift-dist-compᴿˢ : ∀ {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
    (⟨ ξ ↑ᴿ s ⟩ ⨟ˢ (σ ↑ˢ s)) ≡ ((⟨ ξ ⟩ ⨟ˢ σ) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl ; (suc x) → refl }

  compositionalityᴿˢ (` x)        = refl
  compositionalityᴿˢ (λx e)       = cong λx_ (trans (compositionalityᴿˢ e) (cong (e [_]ˢ) lift-dist-compᴿˢ))
  compositionalityᴿˢ (Λα e)       = cong Λα_ (trans (compositionalityᴿˢ e) (cong (e [_]ˢ) lift-dist-compᴿˢ))
  compositionalityᴿˢ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿˢ k)
                           (trans (compositionalityᴿˢ t) (cong (t [_]ˢ) lift-dist-compᴿˢ))
  compositionalityᴿˢ (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿˢ e₁) (compositionalityᴿˢ e₂)
  compositionalityᴿˢ (e • t)      = cong₂ _•_ (compositionalityᴿˢ e) (compositionalityᴿˢ t)
  compositionalityᴿˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿˢ t₁) (compositionalityᴿˢ t₂)
  compositionalityᴿˢ *            = refl

  lift-dist-compˢᴿ : ∀ {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
    ((σ ↑ˢ s) ⨟ˢ ⟨ ξ ↑ᴿ s ⟩) ≡ ((σ ⨟ˢ ⟨ ξ ⟩) ↑ˢ s)
  lift-dist-compˢᴿ {s = s} {σ = σ} {ξ = ξ} = ext λ where
    zero    → refl
    (suc x) → let t = σ _ x in
      trans (coincidence (t [ wkᴿ s ]ᴿ) (ξ ↑ᴿ s))
      (trans (compositionalityᴿᴿ t {ξ₁ = wkᴿ s} {ξ₂ = ξ ↑ᴿ s})
      (trans (cong (t [_]ᴿ) (lift-wkᴿ {s = s}))
      (trans (sym (compositionalityᴿᴿ t {ξ₁ = ξ} {ξ₂ = wkᴿ s}))
             (cong (_[ wkᴿ s ]ᴿ) (sym (coincidence t ξ))))))

  compositionalityˢᴿ {m = V} x {σ₁ = σ₁} {ξ₂ = ξ₂} = sym (coincidence (σ₁ _ x) ξ₂)
  compositionalityˢᴿ (` x) {σ₁ = σ₁} {ξ₂ = ξ₂}     = sym (coincidence (σ₁ _ x) ξ₂)
  compositionalityˢᴿ (λx e)       = cong λx_ (trans (compositionalityˢᴿ e) (cong (e [_]ˢ) lift-dist-compˢᴿ))
  compositionalityˢᴿ (Λα e)       = cong Λα_ (trans (compositionalityˢᴿ e) (cong (e [_]ˢ) lift-dist-compˢᴿ))
  compositionalityˢᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢᴿ k)
                           (trans (compositionalityˢᴿ t) (cong (t [_]ˢ) lift-dist-compˢᴿ))
  compositionalityˢᴿ (e₁ · e₂)    = cong₂ _·_ (compositionalityˢᴿ e₁) (compositionalityˢᴿ e₂)
  compositionalityˢᴿ (e • t)      = cong₂ _•_ (compositionalityˢᴿ e) (compositionalityˢᴿ t)
  compositionalityˢᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢᴿ t₁) (compositionalityˢᴿ t₂)
  compositionalityˢᴿ *            = refl

  lift-dist-compˢˢ {σ₁ = σ₁} {s = s} {σ₂ = σ₂} = ext λ where
    zero    → refl
    (suc x) → let t = σ₁ _ x in
      trans (compositionalityᴿˢ t)
      (trans (cong (t [_]ˢ) (ext λ y → sym (coincidence (σ₂ _ y) (wkᴿ s))))
             (sym (compositionalityˢᴿ t)))

  compositionalityˢˢ {m = V} x    = refl
  compositionalityˢˢ (` x)        = refl
  compositionalityˢˢ (λx e)       = cong λx_ (trans (compositionalityˢˢ e) (cong (e [_]ˢ) lift-dist-compˢˢ))
  compositionalityˢˢ (Λα e)       = cong Λα_ (trans (compositionalityˢˢ e) (cong (e [_]ˢ) lift-dist-compˢˢ))
  compositionalityˢˢ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢˢ k)
                           (trans (compositionalityˢˢ t) (cong (t [_]ˢ) lift-dist-compˢˢ))
  compositionalityˢˢ (e₁ · e₂)    = cong₂ _·_ (compositionalityˢˢ e₁) (compositionalityˢˢ e₂)
  compositionalityˢˢ (e • t)      = cong₂ _•_ (compositionalityˢˢ e) (compositionalityˢˢ t)
  compositionalityˢˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢˢ t₁) (compositionalityˢˢ t₂)
  compositionalityˢˢ *            = refl

  assoc {σ₁ = σ₁} {σ₂ = σ₂} {σ₃ = σ₃} = ext λ x → compositionalityˢˢ (σ₁ _ x) {σ₁ = σ₂} {σ₂ = σ₃}
  dist            = ext λ { zero → refl ; (suc x) → refl }
  lift-cons {σ = σ} {t = t} {τ = τ} = ext λ where
    zero    → refl
    (suc x) → trans (compositionalityᴿˢ (σ _ x)) (cong ((σ _ x) [_]ˢ) (ext λ y → refl))

  coincidence (` x)        ξ = refl
  coincidence (λx e)       ξ = cong λx_
    (trans (cong (e [_]ˢ) ⟨⟩-lift) (coincidence e (ξ ↑ᴿ _)))
  coincidence (Λα e)       ξ = cong Λα_
    (trans (cong (e [_]ˢ) ⟨⟩-lift) (coincidence e (ξ ↑ᴿ _)))
  coincidence (∀[α∶ k ] t) ξ = cong₂ ∀[α∶_]_ (coincidence k ξ)
    (trans (cong (t [_]ˢ) ⟨⟩-lift) (coincidence t (ξ ↑ᴿ _)))
  coincidence (e₁ · e₂)    ξ = cong₂ _·_ (coincidence e₁ ξ) (coincidence e₂ ξ)
  coincidence (e • t)      ξ = cong₂ _•_ (coincidence e ξ) (coincidence t ξ)
  coincidence (t₁ ⇒ t₂)    ξ = cong₂ _⇒_ (coincidence t₁ ξ) (coincidence t₂ ξ)
  coincidence *            ξ = refl

  lift-dist-compᴿˢ-⨟ {s = s} {ξ = ξ} {σ = σ} {τ = τ} =
    trans (sym (assoc {σ₁ = ⟨ ξ ↑ᴿ s ⟩} {σ₂ = σ ↑ˢ s} {σ₃ = τ}))
          (cong (_⨟ˢ τ) (lift-dist-compᴿˢ {s = s}))
  lift-dist-compˢᴿ-⨟ {s = s} {σ = σ} {ξ = ξ} {τ = τ} =
    trans (sym (assoc {σ₁ = σ ↑ˢ s} {σ₂ = ⟨ ξ ↑ᴿ s ⟩} {σ₃ = τ}))
          (cong (_⨟ˢ τ) (lift-dist-compˢᴿ {s = s}))
  lift-dist-compᴿˢ-var {x = zero}  = refl
  lift-dist-compᴿˢ-var {x = suc x} = refl
  lift-dist-compᴿˢ-⨟-var {x = zero}  = refl
  lift-dist-compᴿˢ-⨟-var {x = suc x} = refl
  ⟨⟩-comp-⨟-lift-wkᴿ    = ext λ x → refl
  ⟨⟩-comp-⨟-interactᴿ    = ext λ x → refl
  ⟨⟩-comp-⨟-lift-dist-compᴿᴿ  = ext λ { zero → refl ; (suc x) → refl }
  ⟨⟩-split-tail {s = s} {σ = σ} {ξ = ξ} {ξ′ = ξ′} = ext λ where
    zero    → refl
    (suc x) → let t = σ _ x in begin
        (t [ wkᴿ s ]ᴿ) [ ⟨ (ξ ↑ᴿ s) ⨟ᴿ ξ′ ⟩ ]ˢ
      ≡⟨ coincidence (t [ wkᴿ s ]ᴿ) ((ξ ↑ᴿ s) ⨟ᴿ ξ′) ⟩
        (t [ wkᴿ s ]ᴿ) [ ((ξ ↑ᴿ s) ⨟ᴿ ξ′) ]ᴿ
      ≡⟨ compositionalityᴿᴿ t {ξ₁ = wkᴿ s} {ξ₂ = (ξ ↑ᴿ s) ⨟ᴿ ξ′} ⟩
        t [ (wkᴿ s ⨟ᴿ ((ξ ↑ᴿ s) ⨟ᴿ ξ′)) ]ᴿ
      ≡⟨ cong (t [_]ᴿ) (lift-wkᴿ-⨟ᴿ {s = s} {ξ′ = ξ′}) ⟩
        t [ (ξ ⨟ᴿ (wkᴿ s ⨟ᴿ ξ′)) ]ᴿ
      ≡⟨ sym (compositionalityᴿᴿ t {ξ₁ = ξ} {ξ₂ = wkᴿ s ⨟ᴿ ξ′}) ⟩
        (t [ ξ ]ᴿ) [ (wkᴿ s ⨟ᴿ ξ′) ]ᴿ
      ≡⟨ cong (_[ wkᴿ s ⨟ᴿ ξ′ ]ᴿ) (sym (coincidence t ξ)) ⟩
        (t [ ⟨ ξ ⟩ ]ˢ) [ (wkᴿ s ⨟ᴿ ξ′) ]ᴿ
      ≡⟨ sym (compositionalityᴿᴿ (t [ ⟨ ξ ⟩ ]ˢ) {ξ₁ = wkᴿ s} {ξ₂ = ξ′}) ⟩
        ((t [ ⟨ ξ ⟩ ]ˢ) [ wkᴿ s ]ᴿ) [ ξ′ ]ᴿ
      ≡⟨ sym (coincidence ((t [ ⟨ ξ ⟩ ]ˢ) [ wkᴿ s ]ᴿ) ξ′) ⟩
        ((t [ ⟨ ξ ⟩ ]ˢ) [ wkᴿ s ]ᴿ) [ ⟨ ξ′ ⟩ ]ˢ
      ∎
  ⟨⟩-lift-cons  = ext λ { zero → refl ; (suc x) → refl }
  ⟨⟩-lift-cons-var {x = zero}  = refl
  ⟨⟩-lift-cons-var {x = suc x} = refl
  ⟨⟩-comp    = ext λ x → refl
  ⟨⟩-split-⨟ = ext λ x → refl
  ⟨⟩-lift    = ext λ { zero → refl ; (suc x) → refl }

  η-idᴿ  = ext λ { zero → refl ; (suc x) → refl }
  η-lawᴿ = ext λ { zero → refl ; (suc x) → refl }
  η-id   = ext λ { zero → refl ; (suc x) → refl }
  η-law  = ext λ { zero → refl ; (suc x) → refl }
  def-↑ᴿ = ext λ { zero → refl ; (suc x) → refl }
  def-↑ˢ {σ = σ} {s = s} = ext λ { zero → refl ; (suc x) → sym (coincidence (σ _ x) (wkᴿ s)) }

-- ─── the completed two-world system ─────────────────────────────────

--! RewriteSys {
{-# REWRITE
  def-wkᴿ def-∙ᴿ-zero def-∙ᴿ-suc def-↑ᴿ-zero def-↑ᴿ-suc
  instᴿ-x instᴿ-λ instᴿ-Λ instᴿ-∀ instᴿ-· instᴿ-• instᴿ-⇒ instᴿ-*
  assocᴿ comp-idₗᴿ comp-idᵣᴿ interactᴿ
  lift-idᴿ lift-dist-compᴿᴿ lift-wkᴿ
  right-idᴿ compositionalityᴿᴿ-var compositionalityᴿᴿ
  lift-dist-compᴿᴿ-var lift-consᴿ-var interactᴿ-⨟ᴿ lift-wkᴿ-⨟ᴿ lift-dist-compᴿᴿ-⨟ᴿ
  coincidence-var def-∙ˢ-zero def-∙ˢ-suc def-↑ˢ-zero def-↑ˢ-suc
  compositionalityᴿˢ-⨟-var def-↑ˢ-zero-⨟ def-↑ˢ-suc-⨟
  inst-x inst-λ inst-Λ inst-∀ inst-· inst-• inst-⇒ inst-*
  assoc dist interact comp-idₗ comp-idᵣ
  lift-wk lift-cons lift-dist-compˢˢ lift-wk-⨟ lift-dist-compˢˢ-⨟
  compositionalityˢˢ compositionalityᴿˢ compositionalityˢᴿ lift-dist-compᴿˢ lift-dist-compˢᴿ lift-dist-compᴿˢ-⨟ lift-dist-compˢᴿ-⨟
  lift-dist-compᴿˢ-var lift-dist-compᴿˢ-⨟-var ⟨⟩-lift-cons-var
  coincidence ⟨⟩-comp ⟨⟩-split-⨟ ⟨⟩-lift ⟨⟩-lift-cons
  ⟨⟩-comp-⨟-lift-wkᴿ ⟨⟩-comp-⨟-interactᴿ ⟨⟩-comp-⨟-lift-dist-compᴿᴿ ⟨⟩-split-tail
#-}
--! }

-- ─── the theory is definitional, in both worlds ─────────────────────

weaken : S ⊢ s → (s′ ∷ S) ⊢ s
weaken t = t [ wkᴿ _ ]ᴿ

var-zero : ∀ {t′ : S ⊢ s′} → (` zero) [ t′ ]₀ ≡ t′
var-zero = refl
var-suc : ∀ {x : S ∋ s} {t′ : S ⊢ s′} → (` suc x) [ t′ ]₀ ≡ ` x
var-suc = refl
wk-comm : ∀ {t : S₁ ⊢ s} {σ : S₁ →ˢ S₂} →
  (weaken {s′ = s′} t) [ (σ ↑ˢ s′) ]ˢ ≡ weaken (t [ σ ]ˢ)
wk-comm = refl
--! LawsUsed {
wk-cancel : ∀ {t : S ⊢ s} {t′ : S ⊢ s′} → (weaken t) [ t′ ]₀ ≡ t
wk-cancel = refl
subst-commute : ∀ {t : (s′ ∷ S₁) ⊢ s} {t′ : S₁ ⊢ s′}
  {σ : S₁ →ˢ S₂} →
  (t [ (σ ↑ˢ s′) ]ˢ) [ t′ [ σ ]ˢ ]₀ ≡ (t [ t′ ]₀) [ σ ]ˢ
subst-commute = refl
--! }
subst-subst : ∀ {t : (s₁ ∷ s₂ ∷ S) ⊢ s} {t′ : (s₂ ∷ S) ⊢ s₁} {t₂ : S ⊢ s₂} →
  (t [ t′ ]₀) [ t₂ ]₀ ≡ (t [ ((t₂ ∙ˢ idˢ) ↑ˢ s₁) ]ˢ) [ t′ [ t₂ ]₀ ]₀
subst-subst = refl
lift-comp : ∀ {t : (s′ ∷ S₁) ⊢ s} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} →
  (t [ (σ₁ ↑ˢ s′) ]ˢ) [ (σ₂ ↑ˢ s′) ]ˢ ≡ t [ ((σ₁ ⨟ˢ σ₂) ↑ˢ s′) ]ˢ
lift-comp = refl

renᴿ-id : ∀ {x/t : S ⊢[ m ] s} → x/t [ idᴿ ]ᴿ ≡ x/t
renᴿ-id = refl
renᴿ-comp : ∀ {t : S₁ ⊢ s} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
  (t [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ ≡ t [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ
renᴿ-comp = refl
renᴿ-lift : ∀ {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
  ((ξ₁ ↑ᴿ s) ⨟ᴿ (ξ₂ ↑ᴿ s)) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s)
renᴿ-lift = refl
mixed-RS : ∀ {t : S₁ ⊢ s} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
  (t [ ξ ]ᴿ) [ σ ]ˢ ≡ t [ (⟨ ξ ⟩ ⨟ˢ σ) ]ˢ
mixed-RS = refl
mixed-SR : ∀ {t : S₁ ⊢ s} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
  (t [ σ ]ˢ) [ ξ ]ᴿ ≡ t [ (σ ⨟ˢ ⟨ ξ ⟩) ]ˢ
mixed-SR = refl
emb-collapse : ∀ {t : S₁ ⊢ s} {ξ : S₁ →ᴿ S₂} → t [ ⟨ ξ ⟩ ]ˢ ≡ t [ ξ ]ᴿ
emb-collapse = refl

-- ─── subject reduction ──────────────────────────────────────────────
-- Every substitution equation arising in preservation is discharged
-- definitionally.  The rule that makes the ⊢•-case work is lift-cons
-- (group IVˢ); a system that eliminates ⇑ instead reduces the same goal
-- via def-↑ˢ, which is what drags the η-family into the rewrite system.

↑ˢᵗ_ : Sort → Sort
↑ˢᵗ expr = type
↑ˢᵗ type = kind
↑ˢᵗ kind = kind

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

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {x : S ∋ s} {t} →
    Γ ∋ x ∶ t →
    Γ ⊢ (` x) ∶ t
  --! TyLam {
  ⊢λ :
    (t₁ ∷ₜ Γ) ⊢ e ∶ (weaken t₂) →
    Γ ⊢ (λx e) ∶ (t₁ ⇒ t₂)
  --! }
  ⊢Λ :
    (k ∷ₜ Γ) ⊢ e ∶ t →
    Γ ⊢ (Λα e) ∶ (∀[α∶ k ] t)
  ⊢· :
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ (e₁ · e₂) ∶ t₂
  --! TyTApp {
  ⊢• :
    Γ ⊢ e ∶ (∀[α∶ k ] t′) →
    Γ ⊢ t ∶ k →
    (k ∷ₜ Γ) ⊢ t′ ∶ k′ →
    Γ ⊢ (e • t) ∶ (t′ [ t ]₀)
  --! }
  ⊢* : {t : S ⊢ type} →
    Γ ⊢ t ∶ *

-- one notion of well-typed map
--! WTS {
record _∶_→ˢ_ {S₁ S₂} (σ : S₁ →ˢ S₂) (Γ₁ : Ctx S₁) (Γ₂ : Ctx S₂) : Set where
  constructor mkˢ
  field at : ∀ s (x : S₁ ∋ s) (t : S₁ ∶⊢ s) →
               Γ₁ ∋ x ∶ t → Γ₂ ⊢ (x [ σ ]ˢ) ∶ (t [ σ ]ˢ)
open _∶_→ˢ_ public
--! }

-- Phase 1 of the preservation lemma.  With renamings first class this
-- is a plain judgment on ᴿ-maps: _[_]ᴿ preserves the mode, so a typed
-- renaming sends a variable to a variable by construction and ⊢` is a
-- direct application.  Without them phase 1 is a Σ-predicate on
-- substitutions and extracting the variable costs a transport.
_∶_→ᴿ_ : S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ᴿ_ {S₁} ξ Γ₁ Γ₂ = ∀ s (x : S₁ ∋ s) (t : S₁ ∶⊢ s) →
  Γ₁ ∋ x ∶ t → Γ₂ ∋ (x [ ξ ]ᴿ) ∶ (t [ ξ ]ᴿ)

⊢wkᴿ : (t′ : S ∶⊢ s′) → wkᴿ s′ ∶ Γ →ᴿ (t′ ∷ₜ Γ)
⊢wkᴿ t′ _ x _ refl = refl

⊢↑ᴿ : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} → ξ ∶ Γ₁ →ᴿ Γ₂ →
  (t : S₁ ∶⊢ s) → (ξ ↑ᴿ s) ∶ (t ∷ₜ Γ₁) →ᴿ ((t [ ξ ]ᴿ) ∷ₜ Γ₂)
⊢↑ᴿ ⊢ξ t _ zero    _ refl = refl
⊢↑ᴿ ⊢ξ t _ (suc x) _ refl = cong weaken (⊢ξ _ x _ refl)

--! RenPres {
ren-pres : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
  Γ₁ ⊢ e ∶ t → ξ ∶ Γ₁ →ᴿ Γ₂ →
  Γ₂ ⊢ (e [ ξ ]ᴿ) ∶ (t [ ξ ]ᴿ)
ren-pres (⊢` ⊢x) ⊢ξ = ⊢` (⊢ξ _ _ _ ⊢x)
--! }
ren-pres (⊢λ ⊢e) ⊢ξ = ⊢λ (ren-pres ⊢e (⊢↑ᴿ ⊢ξ _))
ren-pres (⊢Λ ⊢e) ⊢ξ = ⊢Λ (ren-pres ⊢e (⊢↑ᴿ ⊢ξ _))
ren-pres (⊢· ⊢e₁ ⊢e₂) ⊢ξ = ⊢· (ren-pres ⊢e₁ ⊢ξ) (ren-pres ⊢e₂ ⊢ξ)
ren-pres (⊢• ⊢e ⊢t ⊢t′) ⊢ξ = ⊢• (ren-pres ⊢e ⊢ξ) (ren-pres ⊢t ⊢ξ) (ren-pres ⊢t′ (⊢↑ᴿ ⊢ξ _))
ren-pres ⊢*             ⊢ξ = ⊢*

-- Phase 2.  The entry typings go through ren-pres, so this stays
-- structural.  _∶_→ˢ_ is a record with the map as a parameter, which is
-- what lets every recursive call infer it: the rewritten type index in
-- the goal does not determine σ, but the record type constructor is
-- rigid, so the unifier reads σ off the argument's own type.
--! SubPresSig {
sub-pres : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
  Γ₁ ⊢ e ∶ t → σ ∶ Γ₁ →ˢ Γ₂ →
  Γ₂ ⊢ (e [ σ ]ˢ) ∶ (t [ σ ]ˢ)
--! }
--! LiftWT {
⊢↑ˢ : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} →
  σ ∶ Γ₁ →ˢ Γ₂ → (t : S₁ ∶⊢ s) →
  (σ ↑ˢ s) ∶ (t ∷ₜ Γ₁) →ˢ ((t [ σ ]ˢ) ∷ₜ Γ₂)
--! }
⊢↑ˢ {σ = σ} ⊢σ t = mkˢ λ where
  _ zero    _ refl → ⊢` refl
  _ (suc x) _ refl → ren-pres (at ⊢σ _ x _ refl) (⊢wkᴿ (t [ σ ]ˢ))
sub-pres (⊢` ⊢x)                     ⊢σ = at ⊢σ _ _ _ ⊢x
-- the induction hypothesis types the body at (weaken t′) [ σ ↑ˢ _ ]ˢ,
-- while ⊢λ demands weaken (t′ [ σ ]ˢ).  Discharged by wk-comm.
--! CaseLam {
sub-pres (⊢λ ⊢e)                     ⊢σ = ⊢λ (sub-pres ⊢e (⊢↑ˢ ⊢σ _))
--! }
-- ⊢Λ and ⊢· use no substitution law: neither typing rule moves a
-- substitution past a binder in its conclusion.
sub-pres (⊢Λ ⊢e)                     ⊢σ = ⊢Λ (sub-pres ⊢e (⊢↑ˢ ⊢σ _))
sub-pres (⊢· ⊢e₁ ⊢e₂)                ⊢σ = ⊢· (sub-pres ⊢e₁ ⊢σ) (sub-pres ⊢e₂ ⊢σ)
-- ⊢• concludes at t′ [ t ]₀, so the two sides are
-- (t′ [ σ ↑ˢ _ ]ˢ) [ t [ σ ]ˢ ]₀  and  (t′ [ t ]₀) [ σ ]ˢ.
-- Discharged by subst-commute.
--! CaseTApp {
sub-pres (⊢• ⊢e ⊢t ⊢t′) ⊢σ =
  ⊢• (sub-pres ⊢e ⊢σ) (sub-pres ⊢t ⊢σ) (sub-pres ⊢t′ (⊢↑ˢ ⊢σ _))
--! }
sub-pres ⊢*                          ⊢σ = ⊢*

--! SingleWT {
⊢[] : ∀ {Γ : Ctx S} {e : S ⊢ s} {t : S ∶⊢ s} →
  Γ ⊢ e ∶ t → (e ∙ˢ idˢ) ∶ (t ∷ₜ Γ) →ˢ Γ
--! }
⊢[] ⊢e = mkˢ λ where
  _ zero    _ refl → ⊢e
  _ (suc x) _ refl → ⊢` refl

data Val : S ⊢ expr → Set where
  vλ : Val (λx e)
  vΛ : Val (Λα e)

data _↪_ : S ⊢ expr → S ⊢ expr → Set where
  --! BetaLam {
  β-λ :
    Val e₂ →
    ((λx e₁) · e₂) ↪ (e₁ [ e₂ ]₀)
  --! }
  β-Λ :
    ((Λα e) • t) ↪ (e [ t ]₀)
  ξ-·₁ :
    e₁ ↪ e →
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-• :
    e ↪ e′ →
    (e • t) ↪ (e′ • t)

--! SRSig {
sr : Γ ⊢ e ∶ t → e ↪ e′ → Γ ⊢ e′ ∶ t
--! }
-- ⊢λ stores the result type weakened, so the redex is typed at
-- (weaken t₂) [ e₂ ]₀ where the goal is t₂.  Discharged by wk-cancel.
--! CaseBeta {
sr (⊢· (⊢λ ⊢e₁) ⊢e₂) (β-λ v₂) = sub-pres ⊢e₁ (⊢[] ⊢e₂)
--! }
-- the type-application β-case uses no law: t′ [ t ]₀ is t′ [ t ∙ˢ idˢ ]ˢ.
sr (⊢• (⊢Λ ⊢e) ⊢t ⊢t′) β-Λ      = sub-pres ⊢e (⊢[] ⊢t)
sr (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ st)       = ⊢· (sr ⊢e₁ st) ⊢e₂
sr (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ st v₁)    = ⊢· ⊢e₁ (sr ⊢e₂ st)
sr (⊢• ⊢e ⊢t ⊢t′) (ξ-• st)      = ⊢• (sr ⊢e st) ⊢t ⊢t′
