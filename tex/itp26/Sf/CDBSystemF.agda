{-# OPTIONS --rewriting --local-confluence-check #-}
-- ============================================================================
-- System F, co-de-Bruijn, single SORTED syntax over the generic infra (CDBsigG).
-- One uniform substitution handles type- and term-variables; the type-into-term
-- commutation that makes de-Bruijn System F hard never appears, because the lift
-- under EVERY binder (∀, λ, Λ) is the same o'-based wkSub.
-- ============================================================================
module CDBSystemF where
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst)
open import Agda.Builtin.Equality.Rewrite

data Sort : Set where ty tm : Sort
open import CDBsigG Sort public
variable r : Sort

-- sort-agnostic co-de-Bruijn structure (over Scope → Set predicates)
record _×ᴿ_ (S T : Scope → Set)(Γ : Scope) : Set where
  constructor pair
  field {sₗ sᵣ} : Scope
        outl : S sₗ
        outr : T sᵣ
        cvr  : Cover sₗ sᵣ Γ
data Bind (b : Sort)(T : Scope → Set) : Scope → Set where
  use  : T (b ∷ Γ) → Bind b T Γ
  drop : T Γ        → Bind b T Γ
record _↑_ (T : Scope → Set)(Δ : Scope) : Set where
  constructor _⇑_
  field {sup} : Scope
        thing : T sup
        thn   : sup ⊑ Δ
open _↑_ public
infix 4 _↑_

-- System F: types and terms in one sorted family
data Exp : Scope → Sort → Set where
  var   : Exp (r ∷ []) r
  -- types
  _`→_  : ((λ Γ → Exp Γ ty) ×ᴿ (λ Γ → Exp Γ ty)) Γ → Exp Γ ty
  `∀    : Bind ty (λ Γ → Exp Γ ty) Γ → Exp Γ ty
  -- terms
  `app  : ((λ Γ → Exp Γ tm) ×ᴿ (λ Γ → Exp Γ tm)) Γ → Exp Γ tm
  `lam  : ((λ Γ → Exp Γ ty) ×ᴿ Bind tm (λ Γ → Exp Γ tm)) Γ → Exp Γ tm
  `Lam  : Bind ty (λ Γ → Exp Γ tm) Γ → Exp Γ tm
  `App  : ((λ Γ → Exp Γ tm) ×ᴿ (λ Γ → Exp Γ ty)) Γ → Exp Γ tm   -- e [A]

Exp^ : Sort → Scope → Set
Exp^ s Γ = Exp Γ s

-- generic functor / smart constructors on things-with-thinnings
_<$>_ : ∀ {S T Δ} → (∀ {Γ} → S Γ → T Γ) → (S ↑ Δ) → (T ↑ Δ)
f <$> (t ⇑ θ) = f t ⇑ θ
infixl 4 _<$>_
pairUp : ∀ {S T Δ} → (S ↑ Δ) → (T ↑ Δ) → ((S ×ᴿ T) ↑ Δ)
pairUp (a ⇑ θ) (b ⇑ φ) = pair a b (cov (cop θ φ)) ⇑ out (cop θ φ)
bindUp : ∀ {b T Δ} → (T ↑ (b ∷ Δ)) → (Bind b T ↑ Δ)
bindUp (t ⇑ os θ) = use t  ⇑ θ
bindUp (t ⇑ o' θ) = drop t ⇑ θ

-- sorted substitution: each Γ-variable of sort s ↦ a thing of sort s in Δ
data Sub (Δ : Scope) : Scope → Set where
  []   : Sub Δ []
  _,-_ : ∀ {s Γ} → Sub Δ Γ → (Exp^ s ↑ Δ) → Sub Δ (s ∷ Γ)
infixl 5 _,-_

opaque
  oe : ∀ {Δ} → [] ⊑ Δ
  oe {[]}    = oz
  oe {_ ∷ Δ} = o' oe

selL : ∀ {Γₗ Γᵣ Γ Δ} → Cover Γₗ Γᵣ Γ → Sub Δ Γ → Sub Δ Γₗ
selL czz     []       = []
selL (css c) (σ ,- u) = selL c σ ,- u
selL (cs' c) (σ ,- u) = selL c σ ,- u
selL (c's c) (σ ,- u) = selL c σ
selR : ∀ {Γₗ Γᵣ Γ Δ} → Cover Γₗ Γᵣ Γ → Sub Δ Γ → Sub Δ Γᵣ
selR czz     []       = []
selR (css c) (σ ,- u) = selR c σ ,- u
selR (cs' c) (σ ,- u) = selR c σ
selR (c's c) (σ ,- u) = selR c σ ,- u
wkSub : ∀ {s Γ Δ} → Sub Δ Γ → Sub (s ∷ Δ) Γ
wkSub []             = []
wkSub (σ ,- (t ⇑ θ)) = wkSub σ ,- (t ⇑ o' θ)

-- the uniform substitution (mutual with subBind for the three binders)
sub     : ∀ {s Γ Δ} → Exp Γ s → Sub Δ Γ → Exp^ s ↑ Δ
subBind : ∀ {b s Γ Δ} → Bind b (Exp^ s) Γ → Sub Δ Γ → (Bind b (Exp^ s)) ↑ Δ
sub var                       ([] ,- u) = u
sub (_`→_ (pair a₁ a₂ cv))    σ = _`→_  <$> pairUp (sub a₁ (selL cv σ)) (sub a₂ (selR cv σ))
sub (`∀ bnd)                  σ = `∀    <$> subBind bnd σ
sub (`app (pair e₁ e₂ cv))    σ = `app  <$> pairUp (sub e₁ (selL cv σ)) (sub e₂ (selR cv σ))
sub (`lam (pair a bnd cv))    σ = `lam  <$> pairUp (sub a (selL cv σ)) (subBind bnd (selR cv σ))
sub (`Lam bnd)                σ = `Lam  <$> subBind bnd σ
sub (`App (pair e a cv))      σ = `App  <$> pairUp (sub e (selL cv σ)) (sub a (selR cv σ))
subBind (use t)  σ = bindUp (sub t (wkSub σ ,- (var ⇑ os oe)))
subBind (drop t) σ = drop <$> sub t σ

-- smoke test: the polymorphic identity Λα. λ(x:α). x   (closed, support [])
polyId : Exp [] tm
polyId = `Lam (use (`lam (pair var (use var) (cs' czz))))

-- the uniform sorted substitution applies to a real polymorphic term and computes
subTest : Exp^ tm ↑ []
subTest = sub polyId []
