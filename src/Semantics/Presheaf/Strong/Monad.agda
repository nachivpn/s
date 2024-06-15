{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame ; MFrame ; InclusiveMFrame ; ReflexiveMFrame ; TransitiveMFrame)

module Semantics.Presheaf.Strong.Monad
  {C      : Set}
  {_⊆_    : (Γ Δ : C) → Set}
  {IF     : IFrame C _⊆_}
  {_R_    : (Γ Δ : C) → Set}
  (MF     : MFrame IF _R_)
  (IMF    : InclusiveMFrame MF)
  (RMF    : ReflexiveMFrame MF)
  (TMF    : TransitiveMFrame MF)
  (let open MFrame MF)
  (let open InclusiveMFrame IMF)
  (let open TransitiveMFrame TMF)
  (let open ReflexiveMFrame RMF)
  (R-to-⊆-pres-refl  : {Γ : C} → R-to-⊆ R-refl[ Γ ] ≡ ⊆-refl)
  (R-trans-assoc : {Γ Δ Δ' Θ : C} → (r : Γ R Δ) (r' : Δ R Δ') (r'' : Δ' R Θ) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r''))
  (R-to-⊆-pres-trans : ∀ {Γ Δ Θ} → (r : Γ R Δ) →  (r' : Δ R Θ) → R-to-⊆ (R-trans r r') ≡ ⊆-trans (R-to-⊆ r) (R-to-⊆ r'))
  where

open import Semantics.Presheaf.Base IF
open import Semantics.Presheaf.CartesianClosure IF
open import Semantics.Presheaf.Possibility MF
open import Semantics.Presheaf.Strong.Pointed MF IMF RMF
open import Semantics.Presheaf.Strong.Multiplicative MF IMF TMF R-trans-assoc R-to-⊆-pres-trans
