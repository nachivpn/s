{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame

module Semantics.Presheaf.Strong.Monad
  {C    : Set}
  {_⊆_  : (Γ Δ : C) → Set}
  {IF   : IFrame C _⊆_}
  {_R_  : (Γ Δ : C) → Set}
  (MF   : MFrame IF _R_)
  (IMF  : InclusiveMFrame MF)
  (RMF  : ReflexiveMFrame MF)
  (TMF  : TransitiveMFrame MF)
  (IRMF : InclusiveReflexiveMFrame MF IMF RMF)
  (ITMF : InclusiveTransitiveMFrame MF IMF TMF)
  (let open MFrame MF)
  (let open InclusiveMFrame IMF)
  (let open TransitiveMFrame TMF)
  (let open ReflexiveMFrame RMF)
  (let open InclusiveReflexiveMFrame IRMF)
  (let open InclusiveTransitiveMFrame ITMF)
  where

open import Semantics.Presheaf.Base IF
open import Semantics.Presheaf.CartesianClosure IF
open import Semantics.Presheaf.Possibility MF
open import Semantics.Presheaf.Monad MF RMF TMF
open import Semantics.Presheaf.Strong.Pointed MF IRMF
open import Semantics.Presheaf.Strong.Multiplicative MF ITMF
