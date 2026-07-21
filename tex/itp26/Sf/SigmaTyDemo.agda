{-# OPTIONS --rewriting --local-confluence-check #-}
-- Demonstration that SigmaTy actually computes (everything below holds by refl,
-- i.e. by the rewrite rules) — including the critical pair that is NON-confluent
-- in the function-based encodings.
module SigmaTyDemo where
open import SigmaTy
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- The η/dist critical pair that broke every function-based encoding now JOINS:
witness : ((vz [ s ]) ∙ (wk ⨟ s)) ⨟ t  ≡  s ⨟ t
witness = refl

-- and the σ laws compute as rewrites:
ex-clos : (A [ s ]) [ t ] ≡ A [ s ⨟ t ]            ; ex-clos = refl   -- closure fusion
ex-id   : A [ id ] ≡ A                              ; ex-id   = refl   -- identity
ex-var  : vz [ A ∙ s ] ≡ A                          ; ex-var  = refl   -- variable lookup
ex-arr  : (A ⇒ B) [ s ] ≡ (A [ s ]) ⇒ (B [ s ])     ; ex-arr  = refl   -- traversal (⇒)
ex-all  : (∀' A) [ s ] ≡ ∀' (A [ vz ∙ (s ⨟ wk) ])   ; ex-all  = refl   -- traversal (∀, lift)
