{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong ; cong₂)

module Semantics.Presheaf.StrongPointed
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (⊆-trans           : ∀ {Γ Γ' Γ'' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  (⊆-trans-assoc     : ∀ {Γ Γ' Γ'' Γ''' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (w'' : Γ'' ⊆ Γ''') → ⊆-trans (⊆-trans w w') w'' ≡ ⊆-trans w (⊆-trans w' w''))
  (⊆-refl            : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-refl-unit-left  : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans w ⊆-refl ≡ w)
  (⊆-refl-unit-right : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans ⊆-refl w ≡ w)
  (_R_               : (Γ Δ : C) → Set)
  (R-to-⊆            : ∀ {Γ Δ : C} → Γ R Δ → Γ ⊆ Δ)
  (R-refl[_]         : ∀ Γ → Γ R Γ)
  (let R-refl        = λ {Γ} → R-refl[ Γ ])
  (R-to-⊆-pres-refl : ∀ {Γ} → R-to-⊆ R-refl[ Γ ] ≡ ⊆-refl)
  where

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base C _⊆_ ⊆-refl ⊆-trans
open import Semantics.Presheaf.CartesianClosure C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right
open import Semantics.Presheaf.LaxLax C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_
open import Semantics.Presheaf.Strong C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-to-⊆
open import Semantics.Presheaf.Pointed C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-to-⊆ R-refl[_]

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

abstract
  ◯'-strength-point : ◯'-strength 𝒫 𝒬  ∘ id'[ 𝒫 ] ×'-map point'[ 𝒬 ] ≈̇ point'[ 𝒫 ×' 𝒬 ]
  ◯'-strength-point {𝒫} {𝒬} = record { proof = λ p → proof (λ w → proof
        ( refl
        , refl
        , proof
          ((let open EqReasoning ≋[ 𝒫 ]-setoid in begin
            wk[ 𝒫 ] (R-to-⊆ R-refl) _ ≡⟨ cong₂ wk[ 𝒫 ] R-to-⊆-pres-refl refl ⟩
            wk[ 𝒫 ] (⊆-refl) _        ≈⟨ wk[ 𝒫 ]-pres-refl _ ⟩
            wk[ 𝒫 ] w _ ∎)
          , ≋[ 𝒬 ]-refl))) }
