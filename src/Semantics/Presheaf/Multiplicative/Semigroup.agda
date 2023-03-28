{-# OPTIONS --safe --without-K #-}
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

module Semantics.Presheaf.Multiplicative.Semigroup
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (⊆-trans           : ∀ {Γ Γ' Γ'' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  (⊆-trans-assoc     : ∀ {Γ Γ' Γ'' Γ''' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (w'' : Γ'' ⊆ Γ''') → ⊆-trans (⊆-trans w w') w'' ≡ ⊆-trans w (⊆-trans w' w''))
  (⊆-refl            : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-refl-unit-left  : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans w ⊆-refl ≡ w)
  (⊆-refl-unit-right : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans ⊆-refl w ≡ w)
  (_R_               : (Γ Δ : C) → Set)
  (R-trans           : ∀ {Γ Δ Θ} → Γ R Δ →  Δ R Θ → Γ R Θ)
  (R-trans-assoc     : ∀ {Γ Δ Δ' Θ} → (r : Γ R Δ) (r' : Δ R Δ') (r'' : Δ' R Θ) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r''))
  where

open import Semantics.Presheaf.Base C _⊆_ ⊆-refl ⊆-trans
open import Semantics.Presheaf.LaxLax C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_
open import Semantics.Presheaf.Multiplicative.Magma C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-trans

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

import Semantics.Presheaf.LaxLax as LL

mult-horizontal-comp : mult'[ 𝒫 ] ∘ (◯'-map mult'[ 𝒫 ]) ≈̇ mult'[ 𝒫 ] ∘ mult'[ ◯' 𝒫 ]
mult-horizontal-comp {𝒫} = record { proof = λ p → proof (λ w → proof
  (refl
  , sym (R-trans-assoc _ _ _)
  , ≋[ 𝒫 ]-refl)) }
