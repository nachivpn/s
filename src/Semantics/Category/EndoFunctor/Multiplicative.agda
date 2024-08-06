{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Multiplicative where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

record IsMultiplicative {C : Category} (F : EndoFunctor C) : Set₂ where
  open Category C
  open EndoFunctor F

  field
    ℱ'-mult[_]      : (P : Obj) → (ℱ' (ℱ' P) →̇ ℱ' P)
    ℱ'-mult-natural : {P Q : Obj} → (t :  P →̇  Q) → ℱ'-mult[ Q ] ∘ (ℱ'-map (ℱ'-map t)) ≈̇ (ℱ'-map t) ∘ ℱ'-mult[ P ]
    ℱ'-mult-assoc   : {P : Obj} → ℱ'-mult[ P ] ∘ (ℱ'-map ℱ'-mult[ P ]) ≈̇ ℱ'-mult[ P ] ∘ ℱ'-mult[ ℱ' P ]
