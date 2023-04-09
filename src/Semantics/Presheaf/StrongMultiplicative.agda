{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong ; cong₂)

module Semantics.Presheaf.StrongMultiplicative
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
  (R-to-⊆            : ∀ {Γ Δ : C} → Γ R Δ → Γ ⊆ Δ)
  (R-to-⊆-pres-trans : ∀ {Γ Δ Θ} → (r : Γ R Δ) →  (r' : Δ R Θ) → R-to-⊆ (R-trans r r') ≡ ⊆-trans (R-to-⊆ r) (R-to-⊆ r'))
  where

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base C _⊆_ ⊆-refl ⊆-trans
open import Semantics.Presheaf.CartesianClosure C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right
open import Semantics.Presheaf.LaxLax C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_
open import Semantics.Presheaf.Strong C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-to-⊆
open import Semantics.Presheaf.Multiplicative C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-trans R-trans-assoc

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

-- c.f. https://en.wikipedia.org/wiki/Strong_monad#/media/File:Strong_monad_multiplication.svg
◯'-strong-mult' : (mult'[ 𝒫 ×' 𝒬 ]) ∘ (◯'-map (◯'-strength 𝒫 𝒬)) ∘ ◯'-strength 𝒫 (◯' 𝒬) ≈̇ ◯'-strength 𝒫 𝒬 ∘ (id'[ 𝒫 ] ×'-map mult'[ 𝒬 ])
◯'-strong-mult' {𝒫} {𝒬} = record { proof = λ p → proof (λ w → proof
  (refl
  , refl
  , proof
    ((let open EqReasoning ≋[ 𝒫 ]-setoid in
      begin
      wk[ 𝒫 ] (R-to-⊆ _) (wk[ 𝒫 ] ⊆-refl (wk[ 𝒫 ] (R-to-⊆ _) (wk[ 𝒫 ] w _)))
        ≈⟨ wk[ 𝒫 ]-pres-≋ _ (wk[ 𝒫 ]-pres-refl _) ⟩
      wk[ 𝒫 ] (R-to-⊆ _) (wk[ 𝒫 ] (R-to-⊆ _) (wk[ 𝒫 ] w _))
        ≈˘⟨ wk[ 𝒫 ]-pres-trans _ _ _ ⟩
      wk[ 𝒫 ] (⊆-trans (R-to-⊆ _) (R-to-⊆ _)) (wk[ 𝒫 ] w _)
        ≡⟨ cong (λ z → wk[ 𝒫 ] z (wk[ 𝒫 ] w _)) (sym (R-to-⊆-pres-trans _ _)) ⟩
      wk[ 𝒫 ] (R-to-⊆ (R-trans _ _)) (wk[ 𝒫 ] w _) ∎)
    , ≋[ 𝒬 ]-refl))) }


