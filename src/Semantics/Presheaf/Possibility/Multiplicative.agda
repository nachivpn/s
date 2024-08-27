{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame ; MFrame ; TransitiveMFrame)

module Semantics.Presheaf.Possibility.Multiplicative
  {C      : Set}
  {_⊆_    : (Γ Δ : C) → Set}
  {IF     : IFrame C _⊆_}
  {_R_    : (Γ Δ : C) → Set}
  (MF     : MFrame IF _R_)
  (TMF    : TransitiveMFrame MF)
  (let open MFrame MF)
  (let open TransitiveMFrame TMF)
  where

open import Semantics.Presheaf.Base IF
open import Semantics.Presheaf.Possibility.Base MF
open import Semantics.Presheaf.Possibility.Multiplicative.Magma MF TMF public
open import Semantics.Presheaf.Possibility.Multiplicative.Semigroup MF TMF public

open import Semantics.Category.EndoFunctor.Multiplicative

◇'-is-multiplicative : IsMultiplicative ◇'-is-PshFunctor
◇'-is-multiplicative = record
  { mult[_]      = mult'[_]
  ; mult-natural = mult'-natural
  ; mult-assoc = mult'-assoc
  }
