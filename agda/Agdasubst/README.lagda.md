```
Sort : Set 
  ... 

Scope : Set
Scope = List Sort

_∋_ : Scope → Sort → Set -- intrinsically scoped variables
_⊢_ : Scope → Sort → Set -- intrinsically scoped terms

Kᵢ be Kits (either R or S)
Sᵢ be Scopes,
Xᵢ be S ∋ s
tᵢ be S ⊢ s

language:
  `_        : S ∋ s → S ⊢ s
  ...

symbols: 
  _⊔_   : Kit → Kit → Kit 
  id`_  : S ∋ s → S ∋/⊢[ K ] s
  `id_  : S ∋/⊢[ K ] s → S ⊢ s

  _&_   : S₁ ∋ s → S₁ –[ K ]→ S₂ → S₂ ∋/⊢[ K ] s
  _⋯_   : S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
  _∙_   : S₂ ∋/⊢[ K ] s → S₁ –[ K ]→ S₂ → (s ∷ S₁) –[ K ]→ S₂
  id    : S –[ K ]→ S
  wk    : S –[ K ]→ (s ∷ S)
  _;_   : S₁ –[ K₁ ]→ S₂ → S₂ –[ K₂ ]→ S₃ → S₁ –[ K₁ ⊔ K₂ ]→ S₃
  _&/⋯_ : S₁ ∋/⊢[ K₁ ] s → S₁ –[ K₂ ]→ S₂ → S₂ ∋/⊢[ K₁ ⊔ K₂ ] s 


shorthands: 
  _↑_      : S₁ –[ K ]→ S₂ → ∀ s → (s ∷ S₁) –[ K ]→ (s ∷ S₂)
  ϕ ↑ s    = id[ K ]` zero ∙ (ϕ ; wk[K = R])

rules:
  -- bounded join-semilattice? (without commutativity)
  K ⊔ K               ≡ K               -- lub-idem
  K ⊔ R               ≡ K               -- lub-ren-bot-right
  R ⊔ K               ≡ K               -- lub-ren-bot-left
  K ⊔ S               ≡ S               -- lub-sub-top-right
  S ⊔ K               ≡ S               -- lub-sub-top-left
  (K₁ ⊔ K₂) ⊔ K₃      ≡ K₁ ⊔ (K₂ ⊔ K₃)  -- lub-assoc

  S ∋/⊢[ R ] s        ≡ _∋_             -- scoped-ren
  S ∋/⊢[ S ] s        ≡ _⊢_             -- scoped-sub

  id`[K = R] x        ≡ id            -- id`-def-ren
  id`[K = S] x        ≡ `_            -- id`-def-sub

  `id[K = R] x        ≡ `_            -- `id-def-ren
  `id[K = S] x        ≡ id            -- `id-def-sub

  x & id[K = K]       ≡ id`[K = K] x    -- id-def

  zero & (x/t ∙ ϕ)    ≡ x/t           -- ext-def-zero
  suc x′ & (x/t ∙ ϕ)  ≡ x′ & ϕ        -- ext-def-suc
  x & wk              ≡ id/` (suc x)  -- wk-def

  t ⋯ id              ≡ t             -- id-law
  (t ⋯ ϕ₁) ⋯ ϕ₂       ≡ t ⋯ (ϕ₁ ; ϕ₂) -- compositionality 

  x & (ϕ₁ ; ϕ₂)       ≡ (x & ϕ₁) &/⋯ ϕ₂ -- compose-def  

  t &/⋯ ϕ             ≡ t ⋯ ϕ           -- look-comp-term
  x &/⋯ ϕ             ≡ x & ϕ           -- look-comp-var
  
  id/` x &/⋯ ϕ        ≡ x & ϕ           -- look-comp-id/`
  id/`
  `/id (id/` x)       ≡ ` x             -- cancel-`/`


  ... traversal laws, language dependent (insert example for system f)


```