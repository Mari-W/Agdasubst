{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLmark Challenge, Part 3, test 5 of 7 ═══════════════════════
-- "two times three, step 5", from the challenge's own graded test terms
-- `step.poplmark` (challenge-03.zip at
-- https://www.seas.upenn.edu/~plclub/poplmark/).  The named binders are
-- transcribed to de Bruijn indices into the one Scope list that carries
-- both term and type binders, which absorbs the α-renaming the expected
-- outputs perform.  Nothing else is changed.
--
--   test "n" = t ---> t'   output : b    is   isYes (t ⟶? t') ≡ b
--   test "n" = t ---> ?    output : u    is   reduct t ≡ just u
--
-- The first form is task 1 and needs the decision procedure: the test
-- whose output is `false` can only be answered by refuting a reduction.
-- The second form is task 3.
--
-- The statement is at the end of this file.

module Challenge.Test5 where

open import Languages.FsubRecords
open import Challenge.Records
open import Challenge.Animation

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (isYes)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)

-- test 'two times three, step 5'
t5L : [] ⊢ expr
t5L = ((λx[ (∀[<: Top ] (∀[<: (` zero) ] (∀[<: (` (suc zero)) ] (((` (suc (suc zero))) ⇒ (` (suc zero))) ⇒ ((` zero) ⇒ (` (suc zero))))))) ] (Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (((((Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((` (suc zero)) · (` zero))))))) • (` (suc (suc (suc zero))))) • (` (suc (suc zero)))) • (` (suc zero))) · (((((` (suc (suc (suc (suc zero))))) • (` (suc (suc (suc zero))))) • (` (suc (suc zero)))) • (` (suc (suc (suc zero))))) · (` zero)))))))) · (Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((((((Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((` (suc zero)) · (` zero))))))) • (` (suc (suc (suc (suc zero)))))) • (` (suc (suc (suc zero))))) • (` (suc (suc (suc zero))))) · (` (suc zero))) · ((((((Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((` (suc zero)) · (` zero))))))) • (` (suc (suc (suc (suc zero)))))) • (` (suc (suc (suc zero))))) • (` (suc (suc zero)))) · (` (suc zero))) · (` zero)))))))))

t5R : [] ⊢ expr
t5R = (Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (((((Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((` (suc zero)) · (` zero))))))) • (` (suc (suc (suc zero))))) • (` (suc (suc zero)))) • (` (suc zero))) · (((((Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((((((Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((` (suc zero)) · (` zero))))))) • (` (suc (suc (suc (suc zero)))))) • (` (suc (suc (suc zero))))) • (` (suc (suc (suc zero))))) · (` (suc zero))) · ((((((Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((` (suc zero)) · (` zero))))))) • (` (suc (suc (suc (suc zero)))))) • (` (suc (suc (suc zero))))) • (` (suc (suc zero)))) · (` (suc zero))) · (` zero)))))))) • (` (suc (suc (suc zero))))) • (` (suc (suc zero)))) • (` (suc (suc (suc zero))))) • (` (suc (suc (suc zero))))))))))

step-5 : isYes (t5L ⟶? t5R) ≡ false
step-5 = refl

-- test 5 of 7, discharged by `refl`.
