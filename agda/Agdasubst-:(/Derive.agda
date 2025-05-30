-- Author: Marius Weidner
{-# OPTIONS --allow-unsolved-metas --rewriting -v tc.unquote.decl:10 -v tc.unquote.def:10 #-}
module Derive where

open import DeBruijn
open import Sorts
open import Kits

open import Level
open import Agda.Builtin.Reflection
open import Reflection hiding (_≟_)
open import Reflection.AST.Name using (_≟_) 
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; [])
open import Data.String using (String)
open import Relation.Nullary.Decidable using (isYes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ′ ℓ₁′ ℓ₂′ ℓ₃′ ℓ₄′ : Level

defineA : String → (A : Set ℓ) → (Name → TC ⊤) → TC A 
defineA s A by = do
  nm ← freshName s
  by nm
  unquoteTC {A = A} (def nm []) 

visA : ∀ {ℓ} {A : Set ℓ} → A → Arg A
visA {ℓ = ℓ} = arg {a = ℓ} (arg-info visible (modality relevant quantity-ω))

declareTy : Name → (A : Set ℓ) → TC ⊤
declareTy nm A = do
  ty ← quoteTC {A = _} A
  declareDef (visA nm) ty 

getConstructors : Name → TC (List Name)
getConstructors nm = do
  definition ← getDefinition nm
  cstrs definition
  where cstrs : Definition → TC (List Name)
        cstrs (data-type _ cons) = returnTC cons
        cstrs _ = typeError ([ strErr "impossible!" ])

mapM : {A : Set ℓ} {B : Set ℓ′} → (A → TC B) -> List A -> TC (List B)
mapM f [] = returnTC []
mapM f (x ∷ xs) = do
  y ← f x 
  ys ← mapM f xs
  returnTC (y ∷ ys)

term→name : Term → TC Name
term→name (def nm args) = returnTC nm
term→name (con nm args) = returnTC nm
term→name t = typeError ([ strErr "impossible!" ])

quoteNameTC : {A : Set ℓ} → A → TC Name
quoteNameTC a = do
  t ← quoteTC a
  term→name t

conRefl : Term
conRefl = con (quote refl) []

patRefl : Pattern 
patRefl = con (quote refl) []

module _ (Sort : SORT) where
  open SortsWithSort Sort
  open SortsMeta
  open KitsWithSort Sort
  
  module _ (_⊢_ : SCOPED) where
    VAR = ∀ {S} {s} → S ∋ s → S ⊢ s

    traverseSyntax : {A : Set ℓ} → (Name → TC A) → TC (List A)
    traverseSyntax {A = A} f = do 
      ⊢nm ← quoteNameTC {A = SCOPED} _⊢_
      cstrs ← getConstructors ⊢nm

      mapM f cstrs

    module _ (`_ : VAR) where

      module _ (syn : Syntax) where
        open Syntax syn hiding (_⊢_; `_)

        isVarConstructor : Name → TC Bool
        isVarConstructor nm = do 
          `_-nm ←  quoteNameTC {A = VAR} `_ 
          returnTC (isYes (`_-nm ≟ nm))

        deriveTraversal : Name → TC ⊤
        deriveTraversal nm = do 
          declareTy nm (∀ {m} {S₁ S₂} {s : Sort m} {_∋/⊢_} ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s)
          clauses ← traverseSyntax deriveClause
          defineFun nm clauses
          where 
            deriveClause : Name → TC Clause
            deriveClause nm = do 
              isVarCstr ← isVarConstructor nm
              if isVarCstr then returnTC (clause {!   !} {!   !} {!   !})
                else do 
                  {!  !}

      deriveSyntax : Name → TC ⊤
      deriveSyntax nm = do
        declareTy nm Syntax
        injection-proof ← unquoteTC {A = ∀ {S} {s} {x₁ x₂ : S ∋ s} → (` x₁) ≡ (` x₂) → x₁ ≡ x₂} deriveInjectionProof 
        rec ← quoteTC (mkSyntax _⊢_ `_ injection-proof)
        defineFun nm [ clause [] [] rec ]
        where 
          deriveInjectionProof : Term
          deriveInjectionProof = pat-lam  [ clause [] [ visA patRefl ] conRefl ] [] 

      derive : TC ⊤ 
      derive = do
        syn ← defineA "syn" Syntax deriveSyntax
        returnTC tt