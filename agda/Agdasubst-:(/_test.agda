module _test where 

open import Data.Bool

record K (A : Set) : Set where
  field
    b : Bool

open K ⦃ … ⦄  

data X : Set where
  x : X
data Y : Set where
  y : Y

instance
  R : K X
  R = record { b = true }

  S : K Y
  S = record { b = false }


f′ : ∀ {A₁ A₂ : Set} → K A₁ → K A₂ → Set
f′ {A₁ = A₁} {A₂ = A₂} record { b = false } record { b = false } = A₁
f′ {A₁ = A₁} {A₂ = A₂} record { b = false } record { b = true }  = A₂
f′ {A₁ = A₁} {A₂ = A₂} record { b = true }  record { b = false } = A₂
f′ {A₁ = A₁} {A₂ = A₂} record { b = true }  record { b = true }  = A₂

f : ∀ {A₁ A₂ : Set} → (K₁ : K A₁) → (K₂ : K A₂) → K (f′ K₁ K₂) 
f K₁@record { b = false } K₂@record { b = false } = K₁
f K₁@record { b = false } K₂@record { b = true }  = K₂
f K₁@record { b = true }  K₂@record { b = false } = K₂
f K₁@record { b = true }  K₂@record { b = true }  = K₂

g : ∀{A : Set} → K A → Set
g {A = A} K = A

record C {A₁ A₂ : Set} (K₁ : K A₁) (K₂ : K A₂) : Set where
  private instance _ = K₁; _ = K₂
  field
    c : g K₁ → g K₂ → g (f K₁ K₂)

open C ⦃ … ⦄

instance 
  CR : {A : Set} ⦃ k : K A ⦄ → C R k
  CR ⦃ k = record { b = false } ⦄ = record { c = λ _ a → a }
  CR ⦃ k = record { b = true } ⦄  = record { c = λ _ a → a } 

  CS : {A : Set} ⦃ k : K A ⦄ ⦃ c : C k R ⦄ → C S k
  CS ⦃ k = record { b = false } ⦄ = record { c = λ _ a → y }
  CS ⦃ k = record { b = true } ⦄  = record { c = λ _ a → a }

