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

record IsLMonad ℓ {C : LCategory ℓ} {F : LEndoFunctor ℓ C} (isPointed : IsLPointed ℓ F) (isMultiplicative : IsLMultiplicative ℓ F) : Set (suc ℓ) where
  open LCategory C
  open LEndoFunctor F
  open IsLPointed isPointed public
  open IsLMultiplicative isMultiplicative public

  field
    join-unit-left : {P : Obj} → join[ P ] ∘ point[ ℱ' P ] ≈̇ id'[ ℱ' P ]
    join-unit-right  : {P : Obj} → join[ P ] ∘ (map point[ P ]) ≈̇ id'[ ℱ' P ]

IsMonad = IsLMonad (suc 0ℓ)
module IsMonad = IsLMonad
