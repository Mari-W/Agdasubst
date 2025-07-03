module Examples.SystemF.SubjectReduction where

--Typing ----------------------------------------------------------------------

open import Examples.SystemF.Definitions

instance _ = mkLib Sort syn traversal compose  
open import Extensions.StandardTyping

types : Types
types = record
  { ↑ᵗ = λ { expr → _ , type ; type → _ , kind ; kind → _ , kind } } 

open Types types

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ′ Γ₁′ Γ₂′ Γ₃′ : Ctx S

data _⊢_∶_ : {s : Sort m} → Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {s : Sort Bind} {x : S ∋ s} {t} → 
    Γ ∋ x ∶ t →
    -------------
    Γ ⊢ (` x) ∶ t
  ⊢λ : 
    (t ∷ₜ Γ) ⊢ e ∶ (weaken t′) → 
    ------------------------
    Γ ⊢ (λx e) ∶ (t ⇒ t′)
  ⊢Λ :
    (★ₖ ∷ₜ Γ) ⊢ e ∶ t →  
    -------------------------
    Γ ⊢ (Λα e) ∶ (∀[α∶ ★ₖ ] t)
  ⊢· : 
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    --------------------
    Γ ⊢ (e₁ · e₂) ∶ t₂
  ⊢• : 
    Γ ⊢ e ∶ (∀[α∶ ★ₖ ] t′) →
    Γ ⊢ t ∶ ★ₖ →
    (★ₖ ∷ₜ Γ) ⊢ t′ ∶ ★ₖ′ →
    ------------------------
    Γ ⊢ (e • t) ∶ (t′ [ t ])
  ⊢★ : 
    ---------
    Γ ⊢ t ∶ ★
 
typing : Typing
typing = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }

open Typing typing hiding (_⊢_∶_; ⊢`) 

_⊢⋯_ :
  ∀ {{K : Kit k}} {{TK : TypingKit K}}
    {S₁ S₂ m} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort m}
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ (e ⋯ ϕ) ∶ (t ⋯ ϕ)
⊢` ⊢x        ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ⊢x)
⊢λ ⊢e        ⊢⋯ ⊢ϕ = ⊢λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢Λ ⊢e        ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢· ⊢e₁ ⊢e₂   ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢• ⊢e ⊢t ⊢t′ ⊢⋯ ⊢ϕ = ⊢• (⊢e ⊢⋯ ⊢ϕ) (⊢t ⊢⋯ ⊢ϕ) (⊢t′ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢★           ⊢⋯ ⊢ϕ = ⊢★ 

open TypingTraversal record { _⊢⋯_ = _⊢⋯_ } hiding (_⊢⋯_)

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
    ((Λα e) • t) ↪ (e [ t ])
  ξ-·₁ :
    e₁ ↪ e →
    --------------------
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    --------------------
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-• :
    e ↪ e′ →
    ------------------
    (e • t) ↪ (e′ • t) 

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e′ →
  Γ ⊢ e′ ∶ t
subject-reduction (⊢· (⊢λ ⊢e₁) ⊢e₂)     (β-λ _)         = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ
subject-reduction (⊢• (⊢Λ ⊢e) ⊢t ⊢t′) β-Λ               = ⊢e ⊢⋯ₛ ⊢⦅ ⊢t ⦆ₛ
subject-reduction (⊢· ⊢e₁ ⊢e₂)          (ξ-·₁ e₁↪e₁′)   = ⊢· (subject-reduction ⊢e₁ e₁↪e₁′) ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)          (ξ-·₂ e₂↪e₂′ _) = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂′)
subject-reduction (⊢• ⊢e ⊢t ⊢t′)        (ξ-• e₁↪e₁′)    = ⊢• (subject-reduction ⊢e e₁↪e₁′) ⊢t ⊢t′ 