{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame)

module Semantics.Presheaf.Strong.Monad
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (_R_               : (Γ Δ : C) → Set)
  (IF                : IFrame C _⊆_)
  (let open IFrame IF)
  (R-refl            : ∀ {Γ} → Γ R Γ)
  (let R-refl[_]     : ∀ Γ → Γ R Γ ; R-refl[ Γ ] = R-refl {Γ})
  (R-trans           : ∀ {Γ Δ Θ} → Γ R Δ →  Δ R Θ → Γ R Θ)
  (R-trans-assoc     : ∀ {Γ Δ Δ' Θ} → (r : Γ R Δ) (r' : Δ R Δ') (r'' : Δ' R Θ) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r''))
  (R-to-⊆            : ∀ {Γ Δ : C} → Γ R Δ → Γ ⊆ Δ)
  (R-to-⊆-pres-refl  : ∀ {Γ} → R-to-⊆ R-refl[ Γ ] ≡ ⊆-refl)
  (R-to-⊆-pres-trans : ∀ {Γ Δ Θ} → (r : Γ R Δ) →  (r' : Δ R Θ) → R-to-⊆ (R-trans r r') ≡ ⊆-trans (R-to-⊆ r) (R-to-⊆ r'))
  where

open import Semantics.Presheaf.Monad C _⊆_ _R_ IF R-refl R-trans
open import Semantics.Presheaf.Strong.Pointed C _⊆_ _R_ IF R-refl R-to-⊆ R-to-⊆-pres-refl
open import Semantics.Presheaf.Strong.Multiplicative C _⊆_ _R_ IF R-trans R-trans-assoc R-to-⊆ R-to-⊆-pres-trans 
