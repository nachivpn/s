{-# OPTIONS --safe --without-K #-}

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.CartesianClosed
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Strong.Base

module SFC.Evaluation
  (𝒞             : Category)
  (𝒞-is-CC       : IsCartesian 𝒞)
  (𝒞-is-CCC      : IsCartesianClosed 𝒞 𝒞-is-CC)
  (ℱ'            : EndoFunctor 𝒞)
  (ℱ'-is-strong  : IsStrong 𝒞-is-CC ℱ')
  (ι'            : Category.Obj 𝒞)
  where

open import SFC.Evaluation.Base 𝒞 𝒞-is-CC 𝒞-is-CCC ℱ' ℱ'-is-strong public
open import SFC.Evaluation.Properties 𝒞 𝒞-is-CC 𝒞-is-CCC ℱ' ℱ'-is-strong ι' public
