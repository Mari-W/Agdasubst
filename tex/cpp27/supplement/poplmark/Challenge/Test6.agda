{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLmark Challenge, Part 3, test 6 of 7 ═══════════════════════
-- "one + one, step 1", from the challenge's own graded test terms
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

module Challenge.Test6 where

open import Languages.FsubRecords
open import Challenge.Records
open import Challenge.Animation

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (isYes)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)

-- test 'one + one, step 1'
t6L : [] ⊢ expr
t6L = (((λx[ (∀[<: Top ] (∀[<: (` zero) ] (∀[<: (` (suc zero)) ] (((` (suc (suc zero))) ⇒ (` (suc zero))) ⇒ ((` zero) ⇒ (` (suc zero))))))) ] (λx[ (∀[<: Top ] (∀[<: (` zero) ] (∀[<: (` (suc zero)) ] (((` (suc (suc zero))) ⇒ (` (suc zero))) ⇒ ((` zero) ⇒ (` (suc zero))))))) ] (Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((((((` (suc (suc (suc (suc (suc (suc zero))))))) • (` (suc (suc (suc (suc zero)))))) • (` (suc (suc (suc zero))))) • (` (suc (suc (suc zero))))) · (` (suc zero))) · ((((((` (suc (suc (suc (suc (suc zero)))))) • (` (suc (suc (suc (suc zero)))))) • (` (suc (suc (suc zero))))) • (` (suc (suc zero)))) · (` (suc zero))) · (` zero)))))))))) · (Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((` (suc zero)) · (` zero)))))))) · (Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((` (suc zero)) · (` zero))))))))

t6O : [] ⊢ expr
t6O = ((λx[ (∀[<: Top ] (∀[<: (` zero) ] (∀[<: (` (suc zero)) ] (((` (suc (suc zero))) ⇒ (` (suc zero))) ⇒ ((` zero) ⇒ (` (suc zero))))))) ] (Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((((((Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((` (suc zero)) · (` zero))))))) • (` (suc (suc (suc (suc zero)))))) • (` (suc (suc (suc zero))))) • (` (suc (suc (suc zero))))) · (` (suc zero))) · ((((((` (suc (suc (suc (suc (suc zero)))))) • (` (suc (suc (suc (suc zero)))))) • (` (suc (suc (suc zero))))) • (` (suc (suc zero)))) · (` (suc zero))) · (` zero))))))))) · (Λα[<: Top ] (Λα[<: (` zero) ] (Λα[<: (` (suc zero)) ] (λx[ ((` (suc (suc zero))) ⇒ (` (suc zero))) ] (λx[ (` (suc zero)) ] ((` (suc zero)) · (` zero))))))))

step-6 : reduct t6L ≡ just t6O
step-6 = refl

-- test 6 of 7, discharged by `refl`.
