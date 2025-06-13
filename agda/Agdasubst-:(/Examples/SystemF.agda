{-# OPTIONS --rewriting #-}
module Examples.SystemF where

-- Imports ---------------------------------------------------------------------

open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; ∃-syntax; proj₂)
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookupWith)
open import Data.List.Membership.Propositional public using (_∈_)

open import Agda.Builtin.Equality.Rewrite

open import Prelude

data Sort : SORT where
  expr : Sort Bind
  type : Sort Bind
  kind : Sort NoBind

open WithSort Sort
open SortsMeta 

data _⊢_ : SCOPED where
  `_        : S ∋ s → S ⊢ s     
  λx_     : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_     : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_ : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_     : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _∙_     : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_     : S ⊢ type → S ⊢ type → S ⊢ type
  ★       : S ⊢ kind


open import Derive

unquoteDecl syn = deriveSyntax Sort _⊢_ `_ syn
  
open Syntax syn hiding (_⊢_; `_)

_⋯_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (x & ϕ)
(λx e)          ⋯ ϕ = λx (e ⋯ (ϕ ↑ₖ⋆ _))
(e₁ · e₂)       ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
 
opaque
  unfolding all_kit_definitions
    
  ⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s) → t ⋯ id ⦃ K ⦄ ≡ t
  ⋯-id ⦃ K ⦄ (` x)     = `/`-is-` ⦃ K ⦄ x
  ⋯-id (λx t)          = cong λx_ (
    t ⋯ (id ↑ₖ expr)   ≡⟨ cong (t ⋯_) (~-ext id↑ₖ~id) ⟩
    t ⋯ id             ≡⟨ ⋯-id t ⟩
    t                  ∎)
  ⋯-id (t₁ · t₂)       = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (t₁ ⇒ t₂)       = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)

traversal : Traversal
traversal = record
  { _⋯_ = _⋯_ 
  ; ⋯-id = ⋯-id 
  ; ⋯-var = λ x ϕ → refl 
  }

open Traversal traversal hiding (_⋯_; ⋯-id; ⋯-var)

opaque
  unfolding all_kit_and_compose_definitions

  ⋯-fusion′ :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ C : ComposeKit K₁ K₂ ⦄ 
      (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
      (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ _⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t (ϕ₁ ⨟[ C ] ϕ₂)
  ⋯-fusion′ (` x)          ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
  ⋯-fusion′ ⦃ K₁ = K₁ ⦄ ⦃ K₂ = K₂ ⦄ ⦃ C = C ⦄ (λx t)         ϕ₁ ϕ₂ = cong λx_ (
    (_⋯_ ⦃ K = K₁ ⦄ t (ϕ₁ ↑ₖ expr)) ⋯ (ϕ₂ ↑ₖ expr)       ≡⟨ ⋯-fusion′ t (ϕ₁ ↑ₖ expr) (ϕ₂ ↑ₖ expr) ⟩
    _⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t ((ϕ₁ ↑ₖ expr) ⨟ (ϕ₂ ↑ₖ expr))   
      ≡⟨ cong (_⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t) (sym (Kit.~-ext (K₁ ⊔ K₂) (dist-↑ₖ-⨟ expr ϕ₁ ϕ₂))) ⟩
     _⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t ((Kit._↑ₖ_ (K₁ ⊔ K₂) (ϕ₁ ⨟ ϕ₂) expr))           ∎) 
  ⋯-fusion′ (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)
  ⋯-fusion′ (t₁ ⇒ t₂)      ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)  

compose : ComposeTraversal 
compose = record { ⋯-fusion = ⋯-fusion′ }

open ComposeTraversal compose hiding (⋯-fusion)

⋯-fusion : 
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ _⋯_ ⦃ K₁ ⊔ K₂ ⦄ t (ϕ₁ ⨟[ K₁ ⨟ₖ K₂ ] ϕ₂)
⋯-fusion ⦃ K₁ ⦄ ⦃ K₂ ⦄ = ⋯-fusion′ ⦃ C = K₁ ⨟ₖ K₂ ⦄

⋯id : ⦃ K : Kit _∋/⊢_ ⦄ (T : S ⊢ s) → T ⋯ id ⦃ K ⦄ ≡ T 
⋯id _ = ⋯-id _ 

{-# REWRITE 
  &-def₁ &-def₂ id-def ∷-def₁ ∷-def₂ wk-def

  interact
  left-id right-id
  η-id η-law

  distributivity
  associativity
  
  ⋯id 
  ⋯-fusion 

-- Typing ----------------------------------------------------------------------

⤊_ : Sort st → ∃[ st' ] Sort st'
⤊ expr = _ , type
⤊ type = _ , kind
⤊ kind = _ , kind

_∶⊢_ : List (Sort Var) → Sort st → Set
S ∶⊢ s = S ⊢ (proj₂ (⤊ s))

depth : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → x ∈ xs → ℕ
depth (here refl) = zero
depth (there x)   = suc (depth x)

drop-∈ :  ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} →
          x ∈ xs → List A → List A
drop-∈ e xs = drop (suc (depth e)) xs

Ctx : List (Sort Var) → Set
Ctx S = ∀ s → (x : s ∈ S) → drop-∈ x S ∶⊢ s

∅ : Ctx []
∅ _ ()

_،_ : Ctx S → S ∶⊢ s → Ctx (s ∷ S)
(Γ ، t) _ (here refl) = t
(Γ ، t) _ (there x)   = Γ _ x

wk-drop-∈ : (x : s ∈ S) → drop-∈ x S ⊢ s' → S ⊢ s'
wk-drop-∈ (here refl) t = wk t 
wk-drop-∈ (there x)   t = wk (wk-drop-∈ x t) 

wk-telescope : Ctx S → s ∈ S → S ∶⊢ s
wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

_∶_∈_ : s ∈ S → S ∶⊢ s → Ctx S → Set
x ∶ t ∈ Γ = wk-telescope Γ x ≡ t

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx S

data _⊢_∶_ : {s : Sort st} → Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {s : Sort Var} {x : s ∈ S} {T} → 
    x ∶ T ∈ Γ →
    -------------
    Γ ⊢ (` x) ∶ T
  ⊢λ : 
    (Γ ، t) ⊢ e ∶ (wk t') → 
    ------------------------
    Γ ⊢ (λx e) ∶ (t ⇒ t')
  ⊢Λ :
    (Γ ، k) ⊢ e ∶ t →  
    -------------------------
    Γ ⊢ (Λα e) ∶ (∀[α∶ k ] t)
  ⊢· : 
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    --------------------
    Γ ⊢ (e₁ · e₂) ∶ t₂
  ⊢∙ : 
    Γ ⊢ e ∶ (∀[α∶ k ] t') →
    Γ ⊢ t ∶ k →
    (Γ ، k) ⊢ t' ∶ k' →
    ------------------------
    Γ ⊢ (e ∙ t) ∶ (t' [ t ])
  ⊢★ : 
    ---------
    Γ ⊢ t ∶ ★

_∶_→ᵣ_ : S₁ →ᵣ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ᵣ_ {S₁} {S₂} ρ Γ₁ Γ₂ = ∀ (s : Sort Var) (x : s ∈ S₁) (T : S₁ ∶⊢ s) → x ∶ T ∈ Γ₁ → (ρ ⍟ᵣ x) ∶ T ⋯ᵣ ρ ∈ Γ₂ 

_∶_→ₛ_ : S₁ →ₛ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ₛ_ {S₁} {S₂} σ Γ₁ Γ₂ = ∀ (s : Sort Var) (x : s ∈ S₁) (T : S₁ ∶⊢ s) → x ∶ T ∈ Γ₁ → Γ₂ ⊢ (σ ⍟ₛ x) ∶ (T ⋯ₛ σ)

-- Semantics -------------------------------------------------------------------

data Val : S ⊢ expr → Set where
  vλ : Val (λx e)
  vΛ : Val (Λα e)

data _↪_ : S ⊢ expr → S ⊢ expr → Set where
  β-λ :
    Val e₂ →
    ----------------------------
    ((λx e₁) · e₂) ↪ (e₁ [ e₂ ])
  β-Λ :
    ------------------------
    ((Λα e) ∙ t) ↪ (e [ t ])
  ξ-·₁ :
    e₁ ↪ e →
    --------------------
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    --------------------
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-∙ :
    e ↪ e' →
    ------------------
    (e ∙ t) ↪ (e' ∙ t)

-- Subject Reduction ----------------------------------------------------------- 

⊢wkᵣ : ∀ {s' : Sort st} {s : Sort Var} (Γ : Ctx S) (x : s ∈ S) T (T' : S ∶⊢ s') → x ∶ T ∈ Γ → (there x) ∶ (wk T) ∈ (Γ ، T')
⊢wkᵣ _ _ _ _ refl = refl

⊢↑ₖᵣ : ρ ∶ Γ₁ →ᵣ Γ₂ → (T : S₁ ∶⊢ s) → (ρ ↑ₖᵣ s) ∶ Γ₁ ، T →ᵣ (Γ₂ ، (T ⋯ᵣ ρ))
⊢↑ₖᵣ ⊢ρ T _ (here refl) _ refl = refl
⊢↑ₖᵣ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ T _ (there x) _ refl =  ⊢wkᵣ Γ₂ (ρ ⍟ᵣ x) (wk-drop-∈ x (Γ₁ _ x) ⋯ᵣ ρ) (T ⋯ᵣ ρ) (⊢ρ _ x _ refl)

⊢ρ-preserves : ∀ {t : S₁ ⊢ s} {T : S₁ ∶⊢ s} →
  ρ ∶ Γ₁ →ᵣ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (t ⋯ᵣ ρ) ∶ (T ⋯ᵣ ρ)
⊢ρ-preserves ⊢ρ (⊢` ⊢x)        = ⊢` (⊢ρ _ _ _ ⊢x) 
⊢ρ-preserves ⊢ρ (⊢λ ⊢e)        = ⊢λ (⊢ρ-preserves (⊢↑ₖᵣ ⊢ρ _) ⊢e)
⊢ρ-preserves ⊢ρ (⊢Λ ⊢e)        = ⊢Λ ((⊢ρ-preserves (⊢↑ₖᵣ ⊢ρ _) ⊢e))
⊢ρ-preserves ⊢ρ (⊢· ⊢e₁ ⊢e₂)   = ⊢· (⊢ρ-preserves ⊢ρ ⊢e₁) (⊢ρ-preserves ⊢ρ ⊢e₂)
⊢ρ-preserves ⊢ρ (⊢∙ ⊢e ⊢t ⊢t') = ⊢∙ (⊢ρ-preserves ⊢ρ ⊢e) (⊢ρ-preserves ⊢ρ ⊢t) ((⊢ρ-preserves (⊢↑ₖᵣ ⊢ρ _) ⊢t'))
⊢ρ-preserves ⊢ρ ⊢★             = ⊢★

⊢wkₛ : ∀ (Γ : Ctx S) (t : S ⊢ s) (T : S ∶⊢ s) (T' : S ∶⊢ s') → Γ ⊢ t ∶ T → (Γ ، T') ⊢ wk t ∶ wk T 
⊢wkₛ Γ _ _ T' ⊢T = ⊢ρ-preserves (λ s x T ⊢x → ⊢wkᵣ Γ x T T' ⊢x) ⊢T

⊢↑ₖₛ : σ ∶ Γ₁ →ₛ Γ₂ → (T : S ∶⊢ s) → (σ ↑ₖₛ s) ∶ Γ₁ ، T →ₛ (Γ₂ ، (T ⋯ₛ σ))
⊢↑ₖₛ ⊢σ T _ (here refl) _ refl = ⊢` refl
⊢↑ₖₛ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢σ T _ (there x) _ refl = ⊢wkₛ Γ₂ (σ ⍟ₛ x) (wk-drop-∈ x (Γ₁ _ x) ⋯ₛ σ) (T ⋯ₛ σ) (⊢σ _ x _ refl)

⊢σ-preserves : ∀ {σ : S₁ →ₛ S₂} {t : S₁ ⊢ s} {T : S₁ ∶⊢ s} →
  σ ∶ Γ₁ →ₛ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (t ⋯ₛ σ) ∶ (T ⋯ₛ σ)
⊢σ-preserves ⊢σ (⊢` ⊢x)        = ⊢σ _ _ _ ⊢x
⊢σ-preserves {σ = σ} ⊢σ (⊢λ ⊢e)        = ⊢λ (⊢σ-preserves {σ = σ ↑ₖₛ _} (⊢↑ₖₛ {σ = σ} ⊢σ _) ⊢e)
⊢σ-preserves {σ = σ}  ⊢σ (⊢Λ ⊢e)       = ⊢Λ (⊢σ-preserves {σ = σ ↑ₖₛ _} (⊢↑ₖₛ {σ = σ} ⊢σ _) ⊢e)
⊢σ-preserves {σ = σ} ⊢σ (⊢· ⊢e₁ ⊢e₂)   = ⊢· (⊢σ-preserves {σ = σ} ⊢σ ⊢e₁) (⊢σ-preserves {σ = σ} ⊢σ ⊢e₂)
⊢σ-preserves {σ = σ} ⊢σ (⊢∙ ⊢e ⊢t ⊢t') = ⊢∙ (⊢σ-preserves {σ = σ} ⊢σ ⊢e) (⊢σ-preserves {σ = σ} ⊢σ ⊢t) (⊢σ-preserves {σ = σ ↑ₖₛ _} (⊢↑ₖₛ {σ = σ} ⊢σ _) ⊢t')
⊢σ-preserves ⊢σ ⊢★             = ⊢★

⊢[] : ∀ {Γ : Ctx S} {t : S ⊢ s} {T : S ∶⊢ s} → Γ ⊢ t ∶ T → (t ∷ₛ idₛ) ∶ (Γ ، T) →ₛ Γ
⊢[] ⊢t _ (here refl) _ refl = ⊢t
⊢[] ⊢t _ (there x)   _ refl = ⊢` refl

subject-reduction : 
  Γ ⊢ e ∶ t →   
  e ↪ e' → 
  Γ ⊢ e' ∶ t 
subject-reduction (⊢· {e₂ = e₂} (⊢λ ⊢e₁) ⊢e₂) (β-λ v₂)      = ⊢σ-preserves {σ = e₂ ∷ₛ idₛ} (⊢[] ⊢e₂) ⊢e₁
subject-reduction (⊢· ⊢e₁ ⊢e₂)                (ξ-·₁ e₁↪e)   = ⊢· (subject-reduction ⊢e₁ e₁↪e) ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)                (ξ-·₂ e₂↪e x) = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e)       
subject-reduction (⊢∙ {t = t} (⊢Λ ⊢e) ⊢t ⊢t') β-Λ           = ⊢σ-preserves {σ = t ∷ₛ idₛ} (⊢[] ⊢t) ⊢e        
subject-reduction (⊢∙ ⊢e ⊢t ⊢t')              (ξ-∙ e↪e')    = ⊢∙ (subject-reduction ⊢e e↪e') ⊢t ⊢t'                                                   