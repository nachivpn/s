{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong₂)

module Semantics.Presheaf.Multiplicative.Magma
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (⊆-trans           : ∀ {Γ Γ' Γ'' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  (⊆-trans-assoc     : ∀ {Γ Γ' Γ'' Γ''' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (w'' : Γ'' ⊆ Γ''') → ⊆-trans (⊆-trans w w') w'' ≡ ⊆-trans w (⊆-trans w' w''))
  (⊆-refl            : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-refl-unit-left  : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans w ⊆-refl ≡ w)
  (⊆-refl-unit-right : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans ⊆-refl w ≡ w)
  (_R_               : (Γ Δ : C) → Set)
  (R-trans           : ∀ {Γ Δ Θ} → Γ R Δ →  Δ R Θ → Γ R Θ)
  where

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base C _⊆_ ⊆-refl ⊆-trans
open import Semantics.Presheaf.LaxLax C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

◇'-pres-R⁻¹ : Γ R Δ → ◇'-Fam 𝒫 Δ → ◇'-Fam 𝒫 Γ
◇'-pres-R⁻¹ ΓRΔ (elem (Δ' , ΔRΔ' , p)) = elem (Δ' , (R-trans ΓRΔ ΔRΔ' , p))

◇'-◯'-squash : ◇'-Fam (◯' 𝒫) Γ  → ◇'-Fam 𝒫 Γ
◇'-◯'-squash (elem (Δ , ΓRΔ , f)) = ◇'-pres-R⁻¹ ΓRΔ (f .apply-◯ ⊆-refl)

abstract
  --
  ◇'-pres-R⁻¹-pres-≋ : {p p' : ◇'-Fam 𝒫 Δ} {r : Γ R Δ} 
    → p ◇'-≋[ 𝒫 ] p'
    → ◇'-pres-R⁻¹ r p ◇'-≋[ 𝒫 ] ◇'-pres-R⁻¹ r p'
  ◇'-pres-R⁻¹-pres-≋ (proof (refl , refl , p≋p')) = proof (refl , refl , p≋p')

  --
  ◇'-◯'-squash-pres-≋ : {p p' : ◇'-Fam (◯' 𝒫) Γ}
        →  p ◇'-≋[ ◯' 𝒫 ] p' → ◇'-◯'-squash p ◇'-≋[ 𝒫 ] ◇'-◯'-squash p' 
  ◇'-◯'-squash-pres-≋ (proof (refl , refl , f)) = ◇'-pres-R⁻¹-pres-≋ (f .pw ⊆-refl)

mult'[_] : ∀ 𝒫 → (◯' ◯' 𝒫 →̇ ◯' 𝒫)
mult'[ 𝒫 ] = record
  { fun     = λ p → elem λ w → ◇'-◯'-squash (p .apply-◯ w) 
  ; pres-≋  = λ p≋p' → proof (λ w → ◇'-◯'-squash-pres-≋ (p≋p' .pw w) ) 
  ; natural = λ w p → proof λ w' → proof (refl , (refl , ≋[ 𝒫 ]-refl ))
  }

abstract
-- mult' is a natural transformation from the composition of functors ◯' ∘ ◯' to ◯'
  mult'-natural : (t :  𝒫 →̇  𝒬) → mult'[ 𝒬 ] ∘ (◯'-map (◯'-map t)) ≈̇ (◯'-map t) ∘ mult'[ 𝒫 ]
  mult'-natural {𝒫} {𝒬} t = record { proof = λ p → proof λ w → proof (refl , refl , ≋[ 𝒬 ]-refl ) } 
  
mult' = λ {𝒫} → mult'[ 𝒫 ]
