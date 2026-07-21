{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.Typing — STLC typing + `sub-pres`, on THINNING-POSITIONS + STRUCTURAL ctx.
-- Subst-free, funext-only, NO ⊢-ren.  The structural-context machinery (Cx/rest/
-- splitL/cohL/…) is identical to the Var rep; only WtSub changes — its head is the
-- position `os oe`, its tail `o' p` (positions are thinnings now, not vz/vs).
-- ════════════════════════════════════════════════════════════════════════════
module Clean.Typing where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite
open import Clean.Sub   -- Tm, sub, Sub, selL/selR, var₀, lift, wkSub, + Pos (positions, oe-⨾, thinL/out/cop/Cover, oi/oe, _⨾_)

infixr 7 _⇒_
data Ty : Set where ι : Ty ; _⇒_ : Ty → Ty → Ty

-- ── STRUCTURAL context (Var-free; identical to the Var rep) ──
data Cx : Scope → Set where
  ε    : Cx []
  _,-_ : ∀ {Γ} → Cx Γ → Ty → Cx (tt ∷ Γ)
infixl 5 _,-_

rest : ∀ {sup Δ} → sup ⊑ Δ → Cx Δ → Cx sup
rest oz     ε        = ε
rest (os θ) (Φ ,- A) = rest θ Φ ,- A
rest (o' θ) (Φ ,- A) = rest θ Φ

splitL : ∀ {Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Cx Γ → Cx Γₗ
splitL czz     ε        = ε
splitL (css c) (Φ ,- A) = splitL c Φ ,- A
splitL (cs' c) (Φ ,- A) = splitL c Φ ,- A
splitL (c's c) (Φ ,- A) = splitL c Φ
splitR : ∀ {Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Cx Γ → Cx Γᵣ
splitR czz     ε        = ε
splitR (css c) (Φ ,- A) = splitR c Φ ,- A
splitR (cs' c) (Φ ,- A) = splitR c Φ
splitR (c's c) (Φ ,- A) = splitR c Φ ,- A

opaque
  unfolding oi
  rest-oi : ∀ {Δ}(Ψ : Cx Δ) → rest oi Ψ ≡ Ψ
  rest-oi ε        = refl
  rest-oi (Ψ ,- A) = cong (_,- A) (rest-oi Ψ)
{-# REWRITE rest-oi #-}

opaque
  unfolding oe
  rest-oe : ∀ {Δ}(Ψ : Cx Δ) → rest oe Ψ ≡ ε
  rest-oe ε        = refl
  rest-oe (Ψ ,- A) = rest-oe Ψ
{-# REWRITE rest-oe #-}

opaque
  unfolding covL covR full
  splitL-covL : ∀ {Γ Δ}(φ : Γ ⊑ Δ)(Ψ : Cx Δ) → splitL (covL φ) Ψ ≡ Ψ
  splitL-covL oz     ε        = refl
  splitL-covL (os φ) (Ψ ,- A) = cong (_,- A) (splitL-covL φ Ψ)
  splitL-covL (o' φ) (Ψ ,- A) = cong (_,- A) (splitL-covL φ Ψ)
  splitR-covL : ∀ {Γ Δ}(φ : Γ ⊑ Δ)(Ψ : Cx Δ) → splitR (covL φ) Ψ ≡ rest φ Ψ
  splitR-covL oz     ε        = refl
  splitR-covL (os φ) (Ψ ,- A) = cong (_,- A) (splitR-covL φ Ψ)
  splitR-covL (o' φ) (Ψ ,- A) = splitR-covL φ Ψ
  splitL-covR : ∀ {Γ Δ}(θ : Γ ⊑ Δ)(Ψ : Cx Δ) → splitL (covR θ) Ψ ≡ rest θ Ψ
  splitL-covR oz     ε        = refl
  splitL-covR (os θ) (Ψ ,- A) = cong (_,- A) (splitL-covR θ Ψ)
  splitL-covR (o' θ) (Ψ ,- A) = splitL-covR θ Ψ
  splitR-covR : ∀ {Γ Δ}(θ : Γ ⊑ Δ)(Ψ : Cx Δ) → splitR (covR θ) Ψ ≡ Ψ
  splitR-covR oz     ε        = refl
  splitR-covR (os θ) (Ψ ,- A) = cong (_,- A) (splitR-covR θ Ψ)
  splitR-covR (o' θ) (Ψ ,- A) = cong (_,- A) (splitR-covR θ Ψ)
  splitL-full : ∀ {Γ}(Ψ : Cx Γ) → splitL full Ψ ≡ Ψ
  splitL-full ε        = refl
  splitL-full (Ψ ,- A) = cong (_,- A) (splitL-full Ψ)
  splitR-full : ∀ {Γ}(Ψ : Cx Γ) → splitR full Ψ ≡ Ψ
  splitR-full ε        = refl
  splitR-full (Ψ ,- A) = cong (_,- A) (splitR-full Ψ)
{-# REWRITE splitL-covL splitR-covL splitL-covR splitR-covR splitL-full splitR-full #-}

opaque
  unfolding cop
  cohL : ∀ {sₗ sᵣ Δ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(Ψ : Cx Δ)
       → splitL (cov (cop θ φ)) (rest (out (cop θ φ)) Ψ) ≡ rest θ Ψ
  cohL oz     oz     ε        = refl
  cohL (os θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohL θ φ Ψ)
  cohL (os θ) (o' φ) (Ψ ,- A) = cong (_,- A) (cohL θ φ Ψ)
  cohL (o' θ) (os φ) (Ψ ,- A) = cohL θ φ Ψ
  cohL (o' θ) (o' φ) (Ψ ,- A) = cohL θ φ Ψ
  cohR : ∀ {sₗ sᵣ Δ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(Ψ : Cx Δ)
       → splitR (cov (cop θ φ)) (rest (out (cop θ φ)) Ψ) ≡ rest φ Ψ
  cohR oz     oz     ε        = refl
  cohR (os θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohR θ φ Ψ)
  cohR (os θ) (o' φ) (Ψ ,- A) = cohR θ φ Ψ
  cohR (o' θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohR θ φ Ψ)
  cohR (o' θ) (o' φ) (Ψ ,- A) = cohR θ φ Ψ
{-# REWRITE cohL cohR #-}

-- ── typing ──
data _⊢_∶_ : ∀ {Γ} → Cx Γ → Tm Γ → Ty → Set where
  ⊢var  : ∀ {A} → (ε ,- A) ⊢ var ∶ A
  ⊢app  : ∀ {Γ Γₗ Γᵣ}{Φ : Cx Γ}{cv : Cover Γₗ Γᵣ Γ}{l r}{A B}
        → splitL cv Φ ⊢ l ∶ (A ⇒ B) → splitR cv Φ ⊢ r ∶ A → Φ ⊢ app (pair l r cv) ∶ B
  ⊢lam  : ∀ {Γ}{Φ : Cx Γ}{t}{A B} → (Φ ,- A) ⊢ t ∶ B → Φ ⊢ lam (use t) ∶ (A ⇒ B)
  ⊢lamᵈ : ∀ {Γ}{Φ : Cx Γ}{t}{A B} → Φ ⊢ t ∶ B → Φ ⊢ lam (drop t) ∶ (A ⇒ B)
infix 4 _⊢_∶_

_⊢↑_∶_ : ∀ {Δ} → Cx Δ → Tm ↑ Δ → Ty → Set
Φ ⊢↑ (t ⇑ θ) ∶ A = rest θ Φ ⊢ t ∶ A
infix 4 _⊢↑_∶_

⊢app↑ : ∀ {Δ}{Ψ : Cx Δ}{A B}{L R : Tm ↑ Δ} → Ψ ⊢↑ L ∶ (A ⇒ B) → Ψ ⊢↑ R ∶ A → Ψ ⊢↑ app↑ L R ∶ B
⊢app↑ {L = a ⇑ α}{R = b ⇑ β} ⊢L ⊢R = ⊢app ⊢L ⊢R
⊢lam↑ : ∀ {Δ}{Ψ : Cx Δ}{A B}{X : Tm ↑ (tt ∷ Δ)} → (Ψ ,- A) ⊢↑ X ∶ B → Ψ ⊢↑ lam↑ X ∶ (A ⇒ B)
⊢lam↑ {X = t ⇑ os θ} ⊢t = ⊢lam  ⊢t
⊢lam↑ {X = t ⇑ o' θ} ⊢t = ⊢lamᵈ ⊢t
⊢fresh : ∀ {Δ}{Ψ : Cx Δ}{A} → (Ψ ,- A) ⊢↑ var₀ ∶ A
⊢fresh = ⊢var

-- ── well-typed substitution — DATA, structural on the source context ──
-- a Sub is a function of POSITIONS: its head is the slot `os oe`, its tail `o' p`.
data WtSub {Δ} : ∀ {Γ} → Sub Δ Γ → Cx Γ → Cx Δ → Set where
  ⟨⟩  : ∀ {σ}{Ψ : Cx Δ} → WtSub σ ε Ψ
  _◂_ : ∀ {Γ}{σ : Sub Δ (tt ∷ Γ)}{Φ : Cx Γ}{Ψ : Cx Δ}{A}
      → WtSub (λ p → σ (o' p)) Φ Ψ → Ψ ⊢↑ σ (os oe) ∶ A → WtSub σ (Φ ,- A) Ψ
infixl 5 _◂_

-- env split preserves typing — structural recursion (oe-⨾ + unfolding thinL make
-- the head position `(os oe) ⨾ thinL cv` compute back to `os oe`)
opaque
  unfolding thinL thinR _⨾_
  selL-pres : ∀ {Γₗ Γᵣ Γ Δ}{σ : Sub Δ Γ}{Φ}{Ψ}(cv : Cover Γₗ Γᵣ Γ) → WtSub σ Φ Ψ → WtSub (selL cv σ) (splitL cv Φ) Ψ
  selL-pres czz     ⟨⟩        = ⟨⟩
  selL-pres (css c) (wt ◂ ⊢u) = selL-pres c wt ◂ ⊢u
  selL-pres (cs' c) (wt ◂ ⊢u) = selL-pres c wt ◂ ⊢u
  selL-pres (c's c) (wt ◂ ⊢u) = selL-pres c wt
  selR-pres : ∀ {Γₗ Γᵣ Γ Δ}{σ : Sub Δ Γ}{Φ}{Ψ}(cv : Cover Γₗ Γᵣ Γ) → WtSub σ Φ Ψ → WtSub (selR cv σ) (splitR cv Φ) Ψ
  selR-pres czz     ⟨⟩        = ⟨⟩
  selR-pres (css c) (wt ◂ ⊢u) = selR-pres c wt ◂ ⊢u
  selR-pres (cs' c) (wt ◂ ⊢u) = selR-pres c wt
  selR-pres (c's c) (wt ◂ ⊢u) = selR-pres c wt ◂ ⊢u

-- a renamed-by-(o' oi) thing keeps its type (ξ ⨾ o' oi = o' ξ; rest (o' ξ) drops the head)
opaque
  unfolding _⨾_
  wk⟨⟩-pres : ∀ {Δ}{Ψ : Cx Δ}{A B}(u : Tm ↑ Δ) → Ψ ⊢↑ u ∶ B → (Ψ ,- A) ⊢↑ u ⟨ o' oi ⟩ ∶ B
  wk⟨⟩-pres (t ⇑ ξ) ⊢u = ⊢u

opaque
  unfolding wkSub
  wkSub-pres : ∀ {Γ Δ}{σ : Sub Δ Γ}{Φ}{Ψ : Cx Δ}{A} → WtSub σ Φ Ψ → WtSub (wkSub σ) Φ (Ψ ,- A)
  wkSub-pres ⟨⟩                       = ⟨⟩
  wkSub-pres {σ = σ}{A = A} (wt ◂ ⊢u) = wkSub-pres {A = A} wt ◂ wk⟨⟩-pres {A = A} (σ (os oe)) ⊢u

opaque
  unfolding lift _∙_
  lift-pres : ∀ {Γ Δ}{σ : Sub Δ Γ}{Φ}{Ψ : Cx Δ}{A} → WtSub σ Φ Ψ → WtSub (lift σ) (Φ ,- A) (Ψ ,- A)
  lift-pres {Ψ = Ψ}{A = A} wt = wkSub-pres wt ◂ ⊢fresh {Ψ = Ψ}{A = A}

-- ── THE SUBSTITUTION LEMMA — the only preservation theorem, subst-free, NO ⊢-ren ──
opaque
  unfolding sub _⟪_⟫ oi oe
  sub-pres : ∀ {Γ Δ}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{e A} → WtSub σ Φ Ψ → Φ ⊢ e ∶ A → Ψ ⊢↑ (sub e σ) ∶ A
  sub-pres (⟨⟩ ◂ ⊢u) ⊢var = ⊢u
  sub-pres {σ = σ} wt (⊢app {cv = cv}{l = l}{r = r} ⊢l ⊢r) =
    ⊢app↑ {L = sub l (selL cv σ)}{R = sub r (selR cv σ)}
          (sub-pres (selL-pres cv wt) ⊢l) (sub-pres (selR-pres cv wt) ⊢r)
  sub-pres {σ = σ} wt (⊢lam {t = t} ⊢t) =
    ⊢lam↑ {X = sub t (lift σ)} (sub-pres (lift-pres wt) ⊢t)
  sub-pres {σ = σ} wt (⊢lamᵈ {t = t} ⊢t) =
    ⊢lam↑ {X = wk↑ tt (sub t σ)} (sub-pres wt ⊢t)
