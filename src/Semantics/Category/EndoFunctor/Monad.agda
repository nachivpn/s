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
  open IsPointed isPointed public
  open IsMultiplicative isMultiplicative public

  field
    join-unit-left : {P : Obj} → join[ P ] ∘ point[ ℱ' P ] ≈̇ id'[ ℱ' P ]
    join-unit-right  : {P : Obj} → join[ P ] ∘ (map point[ P ]) ≈̇ id'[ ℱ' P ]
