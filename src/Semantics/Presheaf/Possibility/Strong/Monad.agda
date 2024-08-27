{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame

module Semantics.Presheaf.Possibility.Strong.Monad
  {C    : Set}
  {_⊆_  : (Γ Δ : C) → Set}
  {IF   : IFrame C _⊆_}
  {_R_  : (Γ Δ : C) → Set}
  (MF   : MFrame IF _R_)
  (IMF  : InclusiveMFrame MF)
  {RMF  : ReflexiveMFrame MF}
  {TMF  : TransitiveMFrame MF}
  (RTMF : ReflexiveTransitiveMFrame MF RMF TMF)
  (IRMF : InclusiveReflexiveMFrame MF IMF RMF)
  (ITMF : InclusiveTransitiveMFrame MF IMF TMF)
  where

open MFrame MF
open InclusiveMFrame IMF
open TransitiveMFrame TMF
open ReflexiveMFrame RMF
open ReflexiveTransitiveMFrame RTMF
open InclusiveReflexiveMFrame IRMF
open InclusiveTransitiveMFrame ITMF

open import Semantics.Presheaf.Base IF
open import Semantics.Presheaf.CartesianClosure IF
open import Semantics.Presheaf.Possibility.Base MF
open import Semantics.Presheaf.Possibility.Monad MF RMF TMF RTMF public
open import Semantics.Presheaf.Possibility.Strong.Pointed MF IRMF public
open import Semantics.Presheaf.Possibility.Strong.Multiplicative MF ITMF public
open import Semantics.Category.EndoFunctor.Strong.Monad

◇'-is-strong-monad : IsStrongMonad ◇'-is-PshFunctor ◇'-is-strong-pointed ◇'-is-strong-multiplicative ◇'-is-monad
◇'-is-strong-monad = record {}
