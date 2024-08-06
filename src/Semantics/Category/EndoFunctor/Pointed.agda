{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Pointed where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

record IsPointed {C : Category} (F : EndoFunctor C) : Set₂ where
  open Category C
  open EndoFunctor F

  field
    ℱ'-point[_]      : (P : Obj) → (P →̇ ℱ' P)
    ℱ'-point-natural : {P Q : Obj} → (t : P →̇ Q) → ℱ'-point[ Q ] ∘ t ≈̇ ℱ'-map t ∘ ℱ'-point[ P ]
    

