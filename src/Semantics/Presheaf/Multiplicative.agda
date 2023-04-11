{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.IFrame using (IFrame)

module Semantics.Presheaf.Multiplicative
  (C             : Set)
  (_⊆_           : (Γ Δ : C) → Set)
  (_R_           : (Γ Δ : C) → Set)
  (IF            : IFrame C _⊆_)
  (R-trans       : ∀ {Γ Δ Θ} → Γ R Δ →  Δ R Θ → Γ R Θ)
  (R-trans-assoc : ∀ {Γ Δ Δ' Θ} → (r : Γ R Δ) (r' : Δ R Δ') (r'' : Δ' R Θ) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r''))
  where

open import Semantics.Presheaf.Multiplicative.Magma C _⊆_ _R_ IF R-trans public
open import Semantics.Presheaf.Multiplicative.Semigroup C _⊆_ _R_ IF R-trans public
