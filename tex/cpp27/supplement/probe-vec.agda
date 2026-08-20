{-# OPTIONS --safe #-}
-- PROBE: is any law of the σ-calculus UNPROVABLE when maps are vectors?
--
-- Maps are inductive data (extension is a constructor); identity,
-- weakening, lifting and composition are ordinary recursive functions
-- over them.  No postulates -- in particular NO funext, which the
-- function model needs for the η-laws.
module probe-vec where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

private variable n m k l : ℕ

data Var : ℕ → Set where
  zero : Var (suc n)
  suc  : Var n → Var (suc n)

data Tm (n : ℕ) : Set where
  `_   : Var n → Tm n
  lam  : Tm (suc n) → Tm n
  _·_  : Tm n → Tm n → Tm n

-- ── renamings as vectors ───────────────────────────────────────────
data Ren : ℕ → ℕ → Set where
  []   : Ren zero m
  _∙ᴿ_ : Var m → Ren n m → Ren (suc n) m
infixr 5 _∙ᴿ_

_[_]ᵛ : Var n → Ren n m → Var m
zero  [ x ∙ᴿ ξ ]ᵛ = x
suc y [ x ∙ᴿ ξ ]ᵛ = y [ ξ ]ᵛ

sucᴿ : Ren n m → Ren n (suc m)
sucᴿ []        = []
sucᴿ (x ∙ᴿ ξ)  = suc x ∙ᴿ sucᴿ ξ

idᴿ : Ren n n
idᴿ {zero}  = []
idᴿ {suc n} = zero ∙ᴿ sucᴿ idᴿ

wkᴿ : Ren n (suc n)
wkᴿ = sucᴿ idᴿ

_↑ᴿ : Ren n m → Ren (suc n) (suc m)
ξ ↑ᴿ = zero ∙ᴿ sucᴿ ξ

_[_]ᴿ : Tm n → Ren n m → Tm m
(` x)     [ ξ ]ᴿ = ` (x [ ξ ]ᵛ)
(lam t)   [ ξ ]ᴿ = lam (t [ ξ ↑ᴿ ]ᴿ)
(t₁ · t₂) [ ξ ]ᴿ = (t₁ [ ξ ]ᴿ) · (t₂ [ ξ ]ᴿ)

_⨟ᴿ_ : Ren n m → Ren m k → Ren n k
[]        ⨟ᴿ ξ₂ = []
(x ∙ᴿ ξ₁) ⨟ᴿ ξ₂ = (x [ ξ₂ ]ᵛ) ∙ᴿ (ξ₁ ⨟ᴿ ξ₂)

-- ── substitutions as vectors ───────────────────────────────────────
data Sub : ℕ → ℕ → Set where
  []   : Sub zero m
  _∙ˢ_ : Tm m → Sub n m → Sub (suc n) m
infixr 5 _∙ˢ_

⟨_⟩ : Ren n m → Sub n m
⟨ [] ⟩       = []
⟨ x ∙ᴿ ξ ⟩   = (` x) ∙ˢ ⟨ ξ ⟩

idˢ : Sub n n
idˢ = ⟨ idᴿ ⟩

_[_]ᵛˢ : Var n → Sub n m → Tm m
zero  [ t ∙ˢ σ ]ᵛˢ = t
suc y [ t ∙ˢ σ ]ᵛˢ = y [ σ ]ᵛˢ

renˢ : Sub n m → Ren m k → Sub n k
renˢ []        ξ = []
renˢ (t ∙ˢ σ)  ξ = (t [ ξ ]ᴿ) ∙ˢ renˢ σ ξ

_↑ˢ : Sub n m → Sub (suc n) (suc m)
σ ↑ˢ = (` zero) ∙ˢ renˢ σ wkᴿ

_[_]ˢ : Tm n → Sub n m → Tm m
(` x)     [ σ ]ˢ = x [ σ ]ᵛˢ
(lam t)   [ σ ]ˢ = lam (t [ σ ↑ˢ ]ˢ)
(t₁ · t₂) [ σ ]ˢ = (t₁ [ σ ]ˢ) · (t₂ [ σ ]ˢ)

_⨟_ : Sub n m → Sub m k → Sub n k
[]        ⨟ σ₂ = []
(t ∙ˢ σ₁) ⨟ σ₂ = (t [ σ₂ ]ˢ) ∙ˢ (σ₁ ⨟ σ₂)

wkˢ : Sub n (suc n)
wkˢ = ⟨ wkᴿ ⟩

compᴿˢ : Ren n m → Sub m k → Sub n k
compᴿˢ []        σ = []
compᴿˢ (x ∙ᴿ ξ)  σ = (x [ σ ]ᵛˢ) ∙ˢ compᴿˢ ξ σ

-- ══ renaming world ════════════════════════════════════════════════
def-∙-zeroᴿ : ∀ {x : Var m} {ξ : Ren n m} → zero [ x ∙ᴿ ξ ]ᵛ ≡ x
def-∙-zeroᴿ = refl

def-∙-sucᴿ : ∀ {y : Var n} {x : Var m} {ξ : Ren n m} → (suc y) [ x ∙ᴿ ξ ]ᵛ ≡ y [ ξ ]ᵛ
def-∙-sucᴿ = refl

def-sucᴿ : ∀ (x : Var n) (ξ : Ren n m) → x [ sucᴿ ξ ]ᵛ ≡ suc (x [ ξ ]ᵛ)
def-sucᴿ zero    (y ∙ᴿ ξ) = refl
def-sucᴿ (suc x) (y ∙ᴿ ξ) = def-sucᴿ x ξ

def-idᴿ : ∀ (x : Var n) → x [ idᴿ ]ᵛ ≡ x
def-idᴿ zero    = refl
def-idᴿ (suc x) = trans (def-sucᴿ x idᴿ) (cong suc (def-idᴿ x))

def-wkᴿ : ∀ (x : Var n) → x [ wkᴿ ]ᵛ ≡ suc x
def-wkᴿ x = trans (def-sucᴿ x idᴿ) (cong suc (def-idᴿ x))

def-⨟ᴿ : ∀ (x : Var n) (ξ₁ : Ren n m) (ξ₂ : Ren m k) → x [ ξ₁ ⨟ᴿ ξ₂ ]ᵛ ≡ (x [ ξ₁ ]ᵛ) [ ξ₂ ]ᵛ
def-⨟ᴿ zero    (y ∙ᴿ ξ₁) ξ₂ = refl
def-⨟ᴿ (suc x) (y ∙ᴿ ξ₁) ξ₂ = def-⨟ᴿ x ξ₁ ξ₂

sucᴿ-⨟ᴿ : ∀ (ξ₁ : Ren n m) (y : Var k) (ξ₂ : Ren m k) → sucᴿ ξ₁ ⨟ᴿ (y ∙ᴿ ξ₂) ≡ ξ₁ ⨟ᴿ ξ₂
sucᴿ-⨟ᴿ []        y ξ₂ = refl
sucᴿ-⨟ᴿ (x ∙ᴿ ξ₁) y ξ₂ = cong (_ ∙ᴿ_) (sucᴿ-⨟ᴿ ξ₁ y ξ₂)

⨟ᴿ-sucᴿ : ∀ (ξ₁ : Ren n m) (ξ₂ : Ren m k) → ξ₁ ⨟ᴿ sucᴿ ξ₂ ≡ sucᴿ (ξ₁ ⨟ᴿ ξ₂)
⨟ᴿ-sucᴿ []        ξ₂ = refl
⨟ᴿ-sucᴿ (x ∙ᴿ ξ₁) ξ₂ = cong₂ _∙ᴿ_ (def-sucᴿ x ξ₂) (⨟ᴿ-sucᴿ ξ₁ ξ₂)

left-idᴿ : ∀ (ξ : Ren n m) → idᴿ ⨟ᴿ ξ ≡ ξ
left-idᴿ []       = refl
left-idᴿ (x ∙ᴿ ξ) = cong (x ∙ᴿ_) (trans (sucᴿ-⨟ᴿ idᴿ x ξ) (left-idᴿ ξ))

right-idᴿ : ∀ (ξ : Ren n m) → ξ ⨟ᴿ idᴿ ≡ ξ
right-idᴿ []       = refl
right-idᴿ (x ∙ᴿ ξ) = cong₂ _∙ᴿ_ (def-idᴿ x) (right-idᴿ ξ)

assocᴿ : ∀ (ξ₁ : Ren n m) (ξ₂ : Ren m k) (ξ₃ : Ren k l)
       → (ξ₁ ⨟ᴿ ξ₂) ⨟ᴿ ξ₃ ≡ ξ₁ ⨟ᴿ (ξ₂ ⨟ᴿ ξ₃)
assocᴿ []        ξ₂ ξ₃ = refl
assocᴿ (x ∙ᴿ ξ₁) ξ₂ ξ₃ = cong₂ _∙ᴿ_ (sym (def-⨟ᴿ x ξ₂ ξ₃)) (assocᴿ ξ₁ ξ₂ ξ₃)

interactᴿ : ∀ (x : Var m) (ξ : Ren n m) → wkᴿ ⨟ᴿ (x ∙ᴿ ξ) ≡ ξ
interactᴿ x ξ = trans (sucᴿ-⨟ᴿ idᴿ x ξ) (left-idᴿ ξ)

distᴿ : ∀ (x : Var m) (ξ₁ : Ren n m) (ξ₂ : Ren m k)
      → (x ∙ᴿ ξ₁) ⨟ᴿ ξ₂ ≡ (x [ ξ₂ ]ᵛ) ∙ᴿ (ξ₁ ⨟ᴿ ξ₂)
distᴿ x ξ₁ ξ₂ = refl

⨟ᴿ-wkᴿ : ∀ (ξ : Ren n m) → ξ ⨟ᴿ wkᴿ ≡ sucᴿ ξ
⨟ᴿ-wkᴿ ξ = trans (⨟ᴿ-sucᴿ ξ idᴿ) (cong sucᴿ (right-idᴿ ξ))

lift-distᴿ : ∀ (ξ₁ : Ren n m) (ξ₂ : Ren m k) → (ξ₁ ↑ᴿ) ⨟ᴿ (ξ₂ ↑ᴿ) ≡ (ξ₁ ⨟ᴿ ξ₂) ↑ᴿ
lift-distᴿ ξ₁ ξ₂ = cong (zero ∙ᴿ_) (trans (sucᴿ-⨟ᴿ ξ₁ zero (sucᴿ ξ₂)) (⨟ᴿ-sucᴿ ξ₁ ξ₂))

-- ══ η, renaming world ═════════════════════════════════════════════
η-idᴿ : zero ∙ᴿ wkᴿ ≡ idᴿ {suc n}
η-idᴿ = refl

η-lawᴿ : ∀ (ξ : Ren (suc n) m) → (zero [ ξ ]ᵛ) ∙ᴿ (wkᴿ ⨟ᴿ ξ) ≡ ξ
η-lawᴿ (x ∙ᴿ ξ) = cong (x ∙ᴿ_) (interactᴿ x ξ)

-- ══ traversal, renaming world ═════════════════════════════════════
identityᴿ : ∀ (t : Tm n) → t [ idᴿ ]ᴿ ≡ t
identityᴿ (` x)     = cong `_ (def-idᴿ x)
identityᴿ (lam t)   = cong lam (identityᴿ t)
identityᴿ (t₁ · t₂) = cong₂ _·_ (identityᴿ t₁) (identityᴿ t₂)

compᴿᴿ : ∀ (t : Tm n) (ξ₁ : Ren n m) (ξ₂ : Ren m k) → (t [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ ≡ t [ ξ₁ ⨟ᴿ ξ₂ ]ᴿ
compᴿᴿ (` x)     ξ₁ ξ₂ = cong `_ (sym (def-⨟ᴿ x ξ₁ ξ₂))
compᴿᴿ (lam t)   ξ₁ ξ₂ = cong lam (trans (compᴿᴿ t (ξ₁ ↑ᴿ) (ξ₂ ↑ᴿ)) (cong (t [_]ᴿ) (lift-distᴿ ξ₁ ξ₂)))
compᴿᴿ (t₁ · t₂) ξ₁ ξ₂ = cong₂ _·_ (compᴿᴿ t₁ ξ₁ ξ₂) (compᴿᴿ t₂ ξ₁ ξ₂)

-- ══ substitution world ════════════════════════════════════════════
def-⟨⟩ : ∀ (x : Var n) (ξ : Ren n m) → x [ ⟨ ξ ⟩ ]ᵛˢ ≡ ` (x [ ξ ]ᵛ)
def-⟨⟩ zero    (y ∙ᴿ ξ) = refl
def-⟨⟩ (suc x) (y ∙ᴿ ξ) = def-⟨⟩ x ξ

def-renˢ : ∀ (x : Var n) (σ : Sub n m) (ξ : Ren m k) → x [ renˢ σ ξ ]ᵛˢ ≡ (x [ σ ]ᵛˢ) [ ξ ]ᴿ
def-renˢ zero    (t ∙ˢ σ) ξ = refl
def-renˢ (suc x) (t ∙ˢ σ) ξ = def-renˢ x σ ξ

renˢ-renˢ : ∀ (σ : Sub n m) (ξ₁ : Ren m k) (ξ₂ : Ren k l) → renˢ (renˢ σ ξ₁) ξ₂ ≡ renˢ σ (ξ₁ ⨟ᴿ ξ₂)
renˢ-renˢ []       ξ₁ ξ₂ = refl
renˢ-renˢ (t ∙ˢ σ) ξ₁ ξ₂ = cong₂ _∙ˢ_ (compᴿᴿ t ξ₁ ξ₂) (renˢ-renˢ σ ξ₁ ξ₂)

renˢ-⟨⟩ : ∀ (ξ₁ : Ren n m) (ξ₂ : Ren m k) → renˢ ⟨ ξ₁ ⟩ ξ₂ ≡ ⟨ ξ₁ ⨟ᴿ ξ₂ ⟩
renˢ-⟨⟩ []         ξ₂ = refl
renˢ-⟨⟩ (x ∙ᴿ ξ₁)  ξ₂ = cong (_ ∙ˢ_) (renˢ-⟨⟩ ξ₁ ξ₂)

⟨⟩-↑ : ∀ (ξ : Ren n m) → ⟨ ξ ⟩ ↑ˢ ≡ ⟨ ξ ↑ᴿ ⟩
⟨⟩-↑ ξ = cong (_ ∙ˢ_) (trans (renˢ-⟨⟩ ξ wkᴿ) (cong ⟨_⟩ (⨟ᴿ-wkᴿ ξ)))

coincidence : ∀ (t : Tm n) (ξ : Ren n m) → t [ ⟨ ξ ⟩ ]ˢ ≡ t [ ξ ]ᴿ
coincidence (` x)     ξ = def-⟨⟩ x ξ
coincidence (lam t)   ξ = cong lam (trans (cong (t [_]ˢ) (⟨⟩-↑ ξ)) (coincidence t (ξ ↑ᴿ)))
coincidence (t₁ · t₂) ξ = cong₂ _·_ (coincidence t₁ ξ) (coincidence t₂ ξ)

identityˢ : ∀ (t : Tm n) → t [ idˢ ]ˢ ≡ t
identityˢ t = trans (coincidence t idᴿ) (identityᴿ t)

-- mixed fusion ─────────────────────────────────────────────────────
compᴿˢ-sucᴿ : ∀ (ξ : Ren n m) (t : Tm k) (σ : Sub m k) → compᴿˢ (sucᴿ ξ) (t ∙ˢ σ) ≡ compᴿˢ ξ σ
compᴿˢ-sucᴿ []       t σ = refl
compᴿˢ-sucᴿ (x ∙ᴿ ξ) t σ = cong (_ ∙ˢ_) (compᴿˢ-sucᴿ ξ t σ)

compᴿˢ-idᴿ : ∀ (σ : Sub n m) → compᴿˢ idᴿ σ ≡ σ
compᴿˢ-idᴿ []       = refl
compᴿˢ-idᴿ (t ∙ˢ σ) = cong (t ∙ˢ_) (trans (compᴿˢ-sucᴿ idᴿ t σ) (compᴿˢ-idᴿ σ))

compᴿˢ-renˢ : ∀ (ξ : Ren n m) (σ : Sub m k) (ξ′ : Ren k l)
            → compᴿˢ ξ (renˢ σ ξ′) ≡ renˢ (compᴿˢ ξ σ) ξ′
compᴿˢ-renˢ []       σ ξ′ = refl
compᴿˢ-renˢ (x ∙ᴿ ξ) σ ξ′ = cong₂ _∙ˢ_ (def-renˢ x σ ξ′) (compᴿˢ-renˢ ξ σ ξ′)

lift-compᴿˢ : ∀ (ξ : Ren n m) (σ : Sub m k) → compᴿˢ (ξ ↑ᴿ) (σ ↑ˢ) ≡ (compᴿˢ ξ σ) ↑ˢ
lift-compᴿˢ ξ σ = cong (_ ∙ˢ_)
  (trans (compᴿˢ-sucᴿ ξ (` zero) (renˢ σ wkᴿ)) (compᴿˢ-renˢ ξ σ wkᴿ))

lift-renˢ : ∀ (σ : Sub n m) (ξ : Ren m k) → renˢ (σ ↑ˢ) (ξ ↑ᴿ) ≡ (renˢ σ ξ) ↑ˢ
lift-renˢ σ ξ = cong (_ ∙ˢ_)
  (trans (renˢ-renˢ σ wkᴿ (ξ ↑ᴿ))
    (trans (cong (renˢ σ) (trans (interactᴿ zero (sucᴿ ξ)) (sym (⨟ᴿ-wkᴿ ξ))))
           (sym (renˢ-renˢ σ ξ wkᴿ))))

fusionᴿˢ : ∀ (t : Tm n) (ξ : Ren n m) (σ : Sub m k) → (t [ ξ ]ᴿ) [ σ ]ˢ ≡ t [ compᴿˢ ξ σ ]ˢ
fusionᴿˢ (` x)     ξ σ = go x ξ σ
  where go : ∀ (x : Var n) (ξ : Ren n m) (σ : Sub m k) → (x [ ξ ]ᵛ) [ σ ]ᵛˢ ≡ x [ compᴿˢ ξ σ ]ᵛˢ
        go zero    (y ∙ᴿ ξ) σ = refl
        go (suc x) (y ∙ᴿ ξ) σ = go x ξ σ
fusionᴿˢ (lam t)   ξ σ = cong lam (trans (fusionᴿˢ t (ξ ↑ᴿ) (σ ↑ˢ)) (cong (t [_]ˢ) (lift-compᴿˢ ξ σ)))
fusionᴿˢ (t₁ · t₂) ξ σ = cong₂ _·_ (fusionᴿˢ t₁ ξ σ) (fusionᴿˢ t₂ ξ σ)

fusionˢᴿ : ∀ (t : Tm n) (σ : Sub n m) (ξ : Ren m k) → (t [ σ ]ˢ) [ ξ ]ᴿ ≡ t [ renˢ σ ξ ]ˢ
fusionˢᴿ (` x)     σ ξ = sym (def-renˢ x σ ξ)
fusionˢᴿ (lam t)   σ ξ = cong lam (trans (fusionˢᴿ t (σ ↑ˢ) (ξ ↑ᴿ)) (cong (t [_]ˢ) (lift-renˢ σ ξ)))
fusionˢᴿ (t₁ · t₂) σ ξ = cong₂ _·_ (fusionˢᴿ t₁ σ ξ) (fusionˢᴿ t₂ σ ξ)

compᴿˢ-wkᴿ : ∀ (σ : Sub n m) → compᴿˢ wkᴿ (σ ↑ˢ) ≡ renˢ σ wkᴿ
compᴿˢ-wkᴿ σ = trans (compᴿˢ-sucᴿ idᴿ (` zero) (renˢ σ wkᴿ)) (compᴿˢ-idᴿ (renˢ σ wkᴿ))

renˢ-⨟-↑ : ∀ (σ₁ : Sub n m) (σ₂ : Sub m k) → renˢ σ₁ wkᴿ ⨟ (σ₂ ↑ˢ) ≡ renˢ (σ₁ ⨟ σ₂) wkᴿ
renˢ-⨟-↑ []        σ₂ = refl
renˢ-⨟-↑ (u ∙ˢ σ₁) σ₂ = cong₂ _∙ˢ_
  (trans (fusionᴿˢ u wkᴿ (σ₂ ↑ˢ))
    (trans (cong (u [_]ˢ) (compᴿˢ-wkᴿ σ₂)) (sym (fusionˢᴿ u σ₂ wkᴿ))))
  (renˢ-⨟-↑ σ₁ σ₂)

lift-⨟ : ∀ (σ₁ : Sub n m) (σ₂ : Sub m k) → (σ₁ ↑ˢ) ⨟ (σ₂ ↑ˢ) ≡ (σ₁ ⨟ σ₂) ↑ˢ
lift-⨟ σ₁ σ₂ = cong ((` zero) ∙ˢ_) (renˢ-⨟-↑ σ₁ σ₂)

compositionalityˢˢ : ∀ (t : Tm n) (σ₁ : Sub n m) (σ₂ : Sub m k) → (t [ σ₁ ]ˢ) [ σ₂ ]ˢ ≡ t [ σ₁ ⨟ σ₂ ]ˢ
compositionalityˢˢ (` x)     σ₁ σ₂ = go x σ₁ σ₂
  where go : ∀ (x : Var n) (σ₁ : Sub n m) (σ₂ : Sub m k) → (x [ σ₁ ]ᵛˢ) [ σ₂ ]ˢ ≡ x [ σ₁ ⨟ σ₂ ]ᵛˢ
        go zero    (t ∙ˢ σ₁) σ₂ = refl
        go (suc x) (t ∙ˢ σ₁) σ₂ = go x σ₁ σ₂
compositionalityˢˢ (lam t)   σ₁ σ₂ =
  cong lam (trans (compositionalityˢˢ t (σ₁ ↑ˢ) (σ₂ ↑ˢ)) (cong (t [_]ˢ) (lift-⨟ σ₁ σ₂)))
compositionalityˢˢ (t₁ · t₂) σ₁ σ₂ = cong₂ _·_ (compositionalityˢˢ t₁ σ₁ σ₂) (compositionalityˢˢ t₂ σ₁ σ₂)

-- ── map algebra, substitution world ────────────────────────────────
⟨⟩-⨟ : ∀ (ξ : Ren n m) (σ : Sub m k) → ⟨ ξ ⟩ ⨟ σ ≡ compᴿˢ ξ σ
⟨⟩-⨟ []       σ = refl
⟨⟩-⨟ (x ∙ᴿ ξ) σ = cong (_ ∙ˢ_) (⟨⟩-⨟ ξ σ)

⨟-⟨⟩ : ∀ (σ : Sub n m) (ξ : Ren m k) → σ ⨟ ⟨ ξ ⟩ ≡ renˢ σ ξ
⨟-⟨⟩ []       ξ = refl
⨟-⟨⟩ (t ∙ˢ σ) ξ = cong₂ _∙ˢ_ (coincidence t ξ) (⨟-⟨⟩ σ ξ)

left-idˢ : ∀ (σ : Sub n m) → idˢ ⨟ σ ≡ σ
left-idˢ σ = trans (⟨⟩-⨟ idᴿ σ) (compᴿˢ-idᴿ σ)

right-idˢ : ∀ (σ : Sub n m) → σ ⨟ idˢ ≡ σ
right-idˢ []       = refl
right-idˢ (t ∙ˢ σ) = cong₂ _∙ˢ_ (identityˢ t) (right-idˢ σ)

assocˢ : ∀ (σ₁ : Sub n m) (σ₂ : Sub m k) (σ₃ : Sub k l)
       → (σ₁ ⨟ σ₂) ⨟ σ₃ ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)
assocˢ []        σ₂ σ₃ = refl
assocˢ (t ∙ˢ σ₁) σ₂ σ₃ = cong₂ _∙ˢ_ (compositionalityˢˢ t σ₂ σ₃) (assocˢ σ₁ σ₂ σ₃)

interactˢ : ∀ (t : Tm m) (σ : Sub n m) → wkˢ ⨟ (t ∙ˢ σ) ≡ σ
interactˢ t σ = trans (⟨⟩-⨟ wkᴿ (t ∙ˢ σ))
                      (trans (compᴿˢ-sucᴿ idᴿ t σ) (compᴿˢ-idᴿ σ))

distˢ : ∀ (t : Tm m) (σ₁ : Sub n m) (σ₂ : Sub m k)
      → (t ∙ˢ σ₁) ⨟ σ₂ ≡ (t [ σ₂ ]ˢ) ∙ˢ (σ₁ ⨟ σ₂)
distˢ t σ₁ σ₂ = refl

def-↑ˢ : ∀ (σ : Sub n m) → σ ↑ˢ ≡ (` zero) ∙ˢ (σ ⨟ wkˢ)
def-↑ˢ σ = cong ((` zero) ∙ˢ_) (sym (⨟-⟨⟩ σ wkᴿ))

-- ══ THE η-LAWS.  In the function model these need funext. ═════════
η-id : (` zero) ∙ˢ wkˢ ≡ idˢ {suc n}
η-id = refl

η-law : ∀ (σ : Sub (suc n) m) → (zero [ σ ]ᵛˢ) ∙ˢ (wkˢ ⨟ σ) ≡ σ
η-law (t ∙ˢ σ) = cong (t ∙ˢ_) (interactˢ t σ)
