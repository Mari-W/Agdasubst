{-# OPTIONS --rewriting --local-confluence-check #-}
-- PROVEN *and* CONFLUENT type-level σ, now WITH a renaming layer:
--   • Ty is concrete data (eliminable);
--   • module M is the transparent model — substitutions are real functions,
--     _[_] is defined (renamings-first), every σ-law is a THEOREM (no postulates but funext);
--   • the `opaque` block aliases the operators to M and re-proves the laws, so OUTSIDE
--     they are opaque symbols with PROVEN laws ⇒ a genuinely confluent rewrite system.
module SigmaTyProvenConfluent where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Agda.Builtin.Equality.Rewrite
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate funext : ∀ {a b} → Extensionality a b

variable l m n k : ℕ

data Ty : ℕ → Set where
  `_  : Fin n → Ty n
  _⇒_ : Ty n → Ty n → Ty n
  ∀'_ : Ty (suc n) → Ty n

Ren : ℕ → ℕ → Set     -- transparent: renamings ARE Fin-maps (only the ops are opaque)
Ren m n = Fin m → Fin n

------------------------------------------------------------------------
module M where   -- transparent model: everything computes, all laws proven
  _↑ᴿ : Ren m n → Ren (suc m) (suc n)
  (ρ ↑ᴿ) zero = zero
  (ρ ↑ᴿ) (suc x) = suc (ρ x)
  ren : Ty m → Ren m n → Ty n
  ren (` x) ρ = ` (ρ x)
  ren (A ⇒ B) ρ = ren A ρ ⇒ ren B ρ
  ren (∀' A) ρ = ∀' (ren A (ρ ↑ᴿ))

  Sub : ℕ → ℕ → Set
  Sub m n = Fin m → Ty n
  id : Sub n n
  id = `_
  wk : Sub n (suc n)
  wk x = ` (suc x)
  _∙_ : Ty n → Sub m n → Sub (suc m) n
  (A ∙ σ) zero = A
  (A ∙ σ) (suc x) = σ x
  _↑ˢ : Sub m n → Sub (suc m) (suc n)
  (σ ↑ˢ) zero = ` zero
  (σ ↑ˢ) (suc x) = ren (σ x) suc
  sub : Ty m → Sub m n → Ty n
  sub (` x) σ = σ x
  sub (A ⇒ B) σ = sub A σ ⇒ sub B σ
  sub (∀' A) σ = ∀' (sub A (σ ↑ˢ))
  _⨟_ : Sub m k → Sub k n → Sub m n
  (σ ⨟ τ) x = sub (σ x) τ

  ren-ren : (A : Ty m)(ρ₁ : Ren m k)(ρ₂ : Ren k n) → ren (ren A ρ₁) ρ₂ ≡ ren A (λ x → ρ₂ (ρ₁ x))
  ren-ren (` x) ρ₁ ρ₂ = refl
  ren-ren (A ⇒ B) ρ₁ ρ₂ = cong₂ _⇒_ (ren-ren A ρ₁ ρ₂) (ren-ren B ρ₁ ρ₂)
  ren-ren (∀' A) ρ₁ ρ₂ = cong ∀'_ (trans (ren-ren A (ρ₁ ↑ᴿ) (ρ₂ ↑ᴿ)) (cong (ren A) (funext λ { zero → refl ; (suc x) → refl })))
  sub-ren : (A : Ty m)(ρ : Ren m k)(σ : Sub k n) → sub (ren A ρ) σ ≡ sub A (λ x → σ (ρ x))
  sub-ren (` x) ρ σ = refl
  sub-ren (A ⇒ B) ρ σ = cong₂ _⇒_ (sub-ren A ρ σ) (sub-ren B ρ σ)
  sub-ren (∀' A) ρ σ = cong ∀'_ (trans (sub-ren A (ρ ↑ᴿ) (σ ↑ˢ)) (cong (sub A) (funext λ { zero → refl ; (suc x) → refl })))
  ren-sub : (A : Ty m)(σ : Sub m k)(ρ : Ren k n) → ren (sub A σ) ρ ≡ sub A (λ x → ren (σ x) ρ)
  ren-sub (` x) σ ρ = refl
  ren-sub (A ⇒ B) σ ρ = cong₂ _⇒_ (ren-sub A σ ρ) (ren-sub B σ ρ)
  ren-sub (∀' A) σ ρ = cong ∀'_ (trans (ren-sub A (σ ↑ˢ) (ρ ↑ᴿ)) (cong (sub A) (funext λ { zero → refl ; (suc x) → trans (ren-ren (σ x) suc (ρ ↑ᴿ)) (sym (ren-ren (σ x) ρ suc)) })))
  ⨟∘↑ˢ : (σ : Sub m k)(τ : Sub k n) → (λ x → sub ((σ ↑ˢ) x) (τ ↑ˢ)) ≡ ((λ x → sub (σ x) τ) ↑ˢ)
  ⨟∘↑ˢ σ τ = funext λ { zero → refl ; (suc x) → trans (sub-ren (σ x) suc (τ ↑ˢ)) (sym (ren-sub (σ x) τ suc)) }

  compositionality : (A : Ty m)(σ : Sub m k)(τ : Sub k n) → sub (sub A σ) τ ≡ sub A (σ ⨟ τ)
  compositionality (` x) σ τ = refl
  compositionality (A ⇒ B) σ τ = cong₂ _⇒_ (compositionality A σ τ) (compositionality B σ τ)
  compositionality (∀' A) σ τ = cong ∀'_ (trans (compositionality A (σ ↑ˢ) (τ ↑ˢ)) (cong (sub A) (⨟∘↑ˢ σ τ)))
  sub-id : (A : Ty n) → sub A id ≡ A
  sub-id (` x) = refl
  sub-id (A ⇒ B) = cong₂ _⇒_ (sub-id A) (sub-id B)
  sub-id (∀' A) = cong ∀'_ (trans (cong (sub A) (funext λ { zero → refl ; (suc x) → refl })) (sub-id A))
  ren-is-sub : (A : Ty m)(ρ : Ren m n) → ren A ρ ≡ sub A (λ x → ` (ρ x))
  ren-is-sub (` x) ρ = refl
  ren-is-sub (A ⇒ B) ρ = cong₂ _⇒_ (ren-is-sub A ρ) (ren-is-sub B ρ)
  ren-is-sub (∀' A) ρ = cong ∀'_ (trans (ren-is-sub A (ρ ↑ᴿ)) (cong (sub A) (funext λ { zero → refl ; (suc x) → refl })))
  -- renaming algebra (mirrors the substitution one)
  idᴿ : Ren n n
  idᴿ x = x
  wkᴿ : Ren n (suc n)
  wkᴿ = suc
  _∙ᴿ_ : Fin n → Ren m n → Ren (suc m) n
  (x ∙ᴿ ρ) zero = x
  (x ∙ᴿ ρ) (suc y) = ρ y
  _∘_ : Ren m k → Ren k n → Ren m n
  (ρ₁ ∘ ρ₂) x = ρ₂ (ρ₁ x)
  ⟨_⟩ : Ren m n → Sub m n
  ⟨ ρ ⟩ x = ` (ρ x)
  ren-id : (A : Ty n) → ren A idᴿ ≡ A
  ren-id (` x) = refl
  ren-id (A ⇒ B) = cong₂ _⇒_ (ren-id A) (ren-id B)
  ren-id (∀' A) = cong ∀'_ (trans (cong (ren A) (funext λ { zero → refl ; (suc x) → refl })) (ren-id A))

------------------------------------------------------------------------
opaque
  Sub : ℕ → ℕ → Set
  Sub = M.Sub
  _[_] : Ty m → Sub m n → Ty n
  A [ σ ] = M.sub A σ
  _⨟_ : Sub m k → Sub k n → Sub m n
  σ ⨟ τ = σ M.⨟ τ
  id : Sub n n
  id = M.id
  wk : Sub n (suc n)
  wk = M.wk
  _∙_ : Ty n → Sub m n → Sub (suc m) n
  A ∙ σ = A M.∙ σ

  infixr 5 _⇒_
  infixl 6 _⨟_
  infixr 7 _∙_
  infixl 8 _[_]

  variable A B : Ty n
  variable σ τ υ : Sub m n

  Clos      : (A [ σ ]) [ τ ] ≡ A [ σ ⨟ τ ]
  Clos {A = A} {σ = σ} {τ = τ} = M.compositionality A σ τ
  IdSubst   : A [ id ] ≡ A
  IdSubst {A = A} = M.sub-id A
  VarCons-z : (` zero) [ A ∙ σ ] ≡ A
  VarCons-z = refl
  VarCons-s : ∀ {x} → (` (suc x)) [ A ∙ σ ] ≡ (` x) [ σ ]
  VarCons-s = refl
  Var-wk    : ∀ {x : Fin n} → (` x) [ wk ] ≡ ` (suc x)
  Var-wk = refl
  IdL       : id ⨟ σ ≡ σ
  IdL = refl
  IdR       : σ ⨟ id ≡ σ
  IdR {σ = σ} = funext λ x → M.sub-id (σ x)
  ShiftCons : wk ⨟ (A ∙ σ) ≡ σ
  ShiftCons = funext λ x → refl
  Map       : (A ∙ σ) ⨟ τ ≡ (A [ τ ]) ∙ (σ ⨟ τ)
  Map = funext λ { zero → refl ; (suc x) → refl }
  Ass       : (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
  Ass {σ = σ} {τ = τ} {υ = υ} = funext λ x → M.compositionality (σ x) τ υ
  IdCons    : (` zero {n}) ∙ wk ≡ id
  IdCons = funext λ { zero → refl ; (suc x) → refl }
  SCons     : ((` zero) [ σ ]) ∙ (wk ⨟ σ) ≡ σ
  SCons = funext λ { zero → refl ; (suc x) → refl }
  Inst-⇒    : (A ⇒ B) [ σ ] ≡ (A [ σ ]) ⇒ (B [ σ ])
  Inst-⇒ = refl
  Inst-∀    : (∀' A) [ σ ] ≡ ∀' (A [ (` zero) ∙ (σ ⨟ wk) ])
  Inst-∀ {A = A} {σ = σ} = cong ∀'_ (cong (M.sub A) (funext λ { zero → refl ; (suc x) → M.ren-is-sub (σ x) suc }))

  -- renaming layer (separate _⟨_⟩), exposed opaquely, laws proven via M
  _⟨_⟩ : Ty m → Ren m n → Ty n
  A ⟨ ρ ⟩ = M.ren A ρ
  idᴿ : Ren n n
  idᴿ = M.idᴿ
  wkᴿ : Ren n (suc n)
  wkᴿ = M.wkᴿ
  _∙ᴿ_ : Fin n → Ren m n → Ren (suc m) n
  x ∙ᴿ ρ = x M.∙ᴿ ρ
  _∘_ : Ren m k → Ren k n → Ren m n
  ρ₁ ∘ ρ₂ = ρ₁ M.∘ ρ₂

  variable ρ ρ′ : Ren m n

  ⌜_⌝ : Ren m n → Sub m n        -- embed a renaming as a substitution
  ⌜ ρ ⌝ = M.⟨ ρ ⟩

  -- renaming ELIMINATES into substitution; the renaming laws then hold derivably
  -- through the (confluent) substitution layer.  No rule applies an opaque renaming.
  coincidence : A ⟨ ρ ⟩ ≡ A [ ⌜ ρ ⌝ ]
  coincidence {A = A} {ρ = ρ} = M.ren-is-sub A ρ
  embed-id   : ⌜ idᴿ ⌝ ≡ id {n}
  embed-id = funext λ x → refl
  embed-wk   : ⌜ wkᴿ ⌝ ≡ wk {n}
  embed-wk = funext λ x → refl
  embed-cons : ∀ {x} → ⌜ x ∙ᴿ ρ ⌝ ≡ (` x) ∙ ⌜ ρ ⌝
  embed-cons = funext λ { zero → refl ; (suc y) → refl }
  embed-comp : ∀ {ρ₁ : Ren m k}{ρ₂ : Ren k n} → ⌜ ρ₁ ∘ ρ₂ ⌝ ≡ ⌜ ρ₁ ⌝ ⨟ ⌜ ρ₂ ⌝
  embed-comp = funext λ x → refl

{-# REWRITE Clos IdSubst VarCons-z IdL IdR ShiftCons Map Ass IdCons SCons Inst-⇒ Inst-∀
            coincidence embed-id embed-wk embed-cons embed-comp #-}
