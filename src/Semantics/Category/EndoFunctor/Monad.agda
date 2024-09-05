{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Monad where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Pointed
open import Semantics.Category.EndoFunctor.Multiplicative

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Level using (0ℓ ; suc)

record IsMonadₗ {ℓ} {C : Categoryₗ ℓ} {F : EndoFunctorₗ C} (isPointed : IsPointedₗ F) (isMultiplicative : IsMultiplicativeₗ F) : Set (suc ℓ) where
  open Categoryₗ C
  open EndoFunctorₗ F
  open IsPointedₗ isPointed public
  open IsMultiplicativeₗ isMultiplicative public

  field
    join-unit-left : {P : Obj} → join[ P ] ∘ point[ ℱ' P ] ≈̇ id'[ ℱ' P ]
    join-unit-right  : {P : Obj} → join[ P ] ∘ (map point[ P ]) ≈̇ id'[ ℱ' P ]

IsMonad = IsMonadₗ {ℓ = suc 0ℓ}
module IsMonad = IsMonadₗ
