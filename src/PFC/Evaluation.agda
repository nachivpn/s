{-# OPTIONS --safe --without-K #-}

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.CartesianClosed
open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Pointed
open import Semantics.Category.EndoFunctor.Strong.Base
open import Semantics.Category.EndoFunctor.Strong.Pointed

module PFC.Evaluation
  (𝒞                   : Category)
  {𝒞-is-CC             : IsCartesian 𝒞}
  (𝒞-is-CCC            : IsCartesianClosed 𝒞 𝒞-is-CC)
  (◇'                  : EndoFunctor 𝒞)
  {◇'-is-strong        : IsStrong 𝒞-is-CC ◇'}
  {◇'-is-pointed       : IsPointed ◇'}
  (◇'-is-strong-point  : IsStrongPointed ◇' ◇'-is-strong ◇'-is-pointed)
  (ι'            : Category.Obj 𝒞)
  where

open import PFC.Evaluation.Base 𝒞 𝒞-is-CCC ◇' ◇'-is-strong-point public
open import PFC.Evaluation.Properties 𝒞 𝒞-is-CCC ◇' ◇'-is-strong-point ι' public
