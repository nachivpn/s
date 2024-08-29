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

module Semantics.Category.Evaluation.MLC
  (𝒞                   : Category)
  {𝒞-is-CC             : IsCartesian 𝒞}
  (𝒞-is-CCC            : IsCartesianClosed 𝒞 𝒞-is-CC)
  (◇'                  : EndoFunctor 𝒞)
  {◇'-is-strong        : IsStrong 𝒞-is-CC ◇'}
  {◇'-is-pointed       : IsPointed ◇'}
  {◇'-is-mult          : IsMultiplicative ◇'}
  {◇'-is-monad         : IsMonad ◇'-is-pointed ◇'-is-mult}
  {◇'-is-strong-point  : IsStrongPointed ◇' ◇'-is-strong ◇'-is-pointed}
  {◇'-is-strong-mult   : IsStrongMultiplicative ◇' ◇'-is-strong ◇'-is-mult}
  (◇'-is-strong-monad  : IsStrongMonad ◇' ◇'-is-strong-point ◇'-is-strong-mult ◇'-is-monad)
  (ι'            : Category.Obj 𝒞)
  where

open import MLC.Evaluation.Base 𝒞 𝒞-is-CCC ◇' ◇'-is-strong-monad public
open import MLC.Evaluation.Properties 𝒞 𝒞-is-CCC ◇' ◇'-is-strong-monad ι' public
