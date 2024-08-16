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
    point[_]      : (P : Obj) → (P →̇ ℱ' P)
    point-natural : {P Q : Obj} → (t : P →̇ Q) → point[ Q ] ∘ t ≈̇ map t ∘ point[ P ]
    
  point : {P : Obj} → P →̇ ℱ' P
  point = point[ _ ]

  return' : {P Q : Obj} → P →̇ Q → P →̇ ℱ' Q
  return' = point ∘_
