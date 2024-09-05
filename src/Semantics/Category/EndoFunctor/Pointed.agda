{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Pointed where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Level using (0ℓ ; suc)

record IsPointedₗ {ℓ} {C : Categoryₗ ℓ} (F : EndoFunctorₗ C) : Set (suc ℓ) where
  open Categoryₗ C
  open EndoFunctorₗ F

  field
    point[_]      : (P : Obj) → (P →̇ ℱ' P)
    point-natural : {P Q : Obj} → (t : P →̇ Q) → point[ Q ] ∘ t ≈̇ map t ∘ point[ P ]
    
  point : {P : Obj} → P →̇ ℱ' P
  point = point[ _ ]

  return' : {P Q : Obj} → P →̇ Q → P →̇ ℱ' Q
  return' = point ∘_

  return'-pres-≈̇ : {P Q : Obj} → {f g : P →̇ Q}
    → f ≈̇ g → return' f ≈̇ return' g
  return'-pres-≈̇ = ∘-pres-≈̇-right _

  return'-nat : {P Q R : Obj} (g : Q →̇ R) (f : P →̇ Q)
    → return' (g ∘ f) ≈̇ return' g ∘ f
  return'-nat g f = ≈̇-sym (∘-assoc _ g f)

IsPointed = IsPointedₗ {ℓ = suc 0ℓ}
module IsPointed = IsPointedₗ
