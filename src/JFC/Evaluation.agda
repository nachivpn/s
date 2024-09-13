{-# OPTIONS --safe --without-K #-}

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.CartesianClosed
open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Pointed
open import Semantics.Category.EndoFunctor.Multiplicative
open import Semantics.Category.EndoFunctor.Monad
open import Semantics.Category.EndoFunctor.Strong.Base
open import Semantics.Category.EndoFunctor.Strong.Pointed
open import Semantics.Category.EndoFunctor.Strong.Multiplicative
open import Semantics.Category.EndoFunctor.Strong.Monad

module JFC.Evaluation
  (𝒞                     : Category)
  {𝒞-is-CC               : IsCartesian 𝒞}
  (𝒞-is-CCC              : IsCartesianClosed 𝒞 𝒞-is-CC)
  (◇'                    : EndoFunctor 𝒞)
  {◇'-is-strong          : IsStrong 𝒞-is-CC ◇'}
  {◇'-is-pointed         : IsPointed ◇'}
  {◇'-is-joinable        : IsMultiplicative ◇'}
  {◇'-is-monad           : IsMonad ◇'-is-pointed ◇'-is-joinable}
  {◇'-is-strong-point    : IsStrongPointed ◇' ◇'-is-strong ◇'-is-pointed}
  (◇'-is-strong-joinable : IsStrongMultiplicative ◇' ◇'-is-strong ◇'-is-joinable)
  (ι'                    : Category.Obj 𝒞)
  where

open import JFC.Evaluation.Base 𝒞 𝒞-is-CCC ◇' ◇'-is-strong-joinable public
open import JFC.Evaluation.Properties 𝒞 𝒞-is-CCC ◇' ◇'-is-strong-joinable ι' public
