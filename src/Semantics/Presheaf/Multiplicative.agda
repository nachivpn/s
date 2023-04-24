{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (MFrame ; TransitiveMFrame)

module Semantics.Presheaf.Multiplicative
  {C      : Set}
  {_⊆_    : (Γ Δ : C) → Set}
  {_R_    : (Γ Δ : C) → Set}
  (MF     : MFrame C _⊆_ _R_)
  (TMF    : TransitiveMFrame MF)
  (let open MFrame MF)
  (let open TransitiveMFrame TMF)
  (R-trans-assoc : {Γ Δ Δ' Θ : C} → (r : Γ R Δ) (r' : Δ R Δ') (r'' : Δ' R Θ) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r''))
  where

open import Semantics.Presheaf.Multiplicative.Magma MF TMF public
open import Semantics.Presheaf.Multiplicative.Semigroup MF TMF R-trans-assoc public
