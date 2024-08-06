{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Monad where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Pointed
open import Semantics.Category.EndoFunctor.Multiplicative

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

record IsMonad {C : Category} {F : EndoFunctor C} (isPointed : IsPointed F) (isMultiplicative : IsMultiplicative F) : Set₂ where
  open Category C
  open EndoFunctor F
  open IsPointed isPointed
  open IsMultiplicative isMultiplicative

  ℱ'-return[_] = ℱ'-point[_]
  ℱ'-join[_]   = ℱ'-mult[_]

  field
    ℱ'-return-unit-right : {P : Obj} → ℱ'-join[ P ] ∘ ℱ'-return[ ℱ' P ] ≈̇ id'[ ℱ' P ]
    ℱ'-return-unit-left  : {P : Obj} → ℱ'-join[ P ] ∘ (ℱ'-map ℱ'-return[ P ]) ≈̇ id'[ ℱ' P ]
