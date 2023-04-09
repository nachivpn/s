{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong ; cong₂)

module Semantics.Presheaf.StrongMonad
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (⊆-trans           : ∀ {Γ Γ' Γ'' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  (⊆-trans-assoc     : ∀ {Γ Γ' Γ'' Γ''' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (w'' : Γ'' ⊆ Γ''') → ⊆-trans (⊆-trans w w') w'' ≡ ⊆-trans w (⊆-trans w' w''))
  (⊆-refl            : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-refl-unit-left  : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans w ⊆-refl ≡ w)
  (⊆-refl-unit-right : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans ⊆-refl w ≡ w)
  (_R_               : (Γ Δ : C) → Set)
  (R-refl            : ∀ {Γ} → Γ R Γ)
  (let R-refl[_]     : ∀ Γ → Γ R Γ ; R-refl[ Γ ] = R-refl {Γ})
  (R-trans           : ∀ {Γ Δ Θ} → Γ R Δ →  Δ R Θ → Γ R Θ)
  (R-trans-assoc     : ∀ {Γ Δ Δ' Θ} → (r : Γ R Δ) (r' : Δ R Δ') (r'' : Δ' R Θ) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r''))
  (R-to-⊆            : ∀ {Γ Δ : C} → Γ R Δ → Γ ⊆ Δ)
  (R-to-⊆-pres-refl  : ∀ {Γ} → R-to-⊆ R-refl[ Γ ] ≡ ⊆-refl)
  (R-to-⊆-pres-trans : ∀ {Γ Δ Θ} → (r : Γ R Δ) →  (r' : Δ R Θ) → R-to-⊆ (R-trans r r') ≡ ⊆-trans (R-to-⊆ r) (R-to-⊆ r'))
  where

open import Semantics.Presheaf.Monad C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-refl R-trans
open import Semantics.Presheaf.StrongPointed C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-refl R-to-⊆ R-to-⊆-pres-refl
open import Semantics.Presheaf.StrongMultiplicative C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-trans R-trans-assoc R-to-⊆ R-to-⊆-pres-trans
