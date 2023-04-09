{-# OPTIONS --safe --without-K #-}
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Semantics.Presheaf.Monad
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (⊆-trans           : ∀ {Γ Γ' Γ'' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  (⊆-trans-assoc     : ∀ {Γ Γ' Γ'' Γ''' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (w'' : Γ'' ⊆ Γ''') → ⊆-trans (⊆-trans w w') w'' ≡ ⊆-trans w (⊆-trans w' w''))
  (⊆-refl            : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-refl-unit-left  : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans w ⊆-refl ≡ w)
  (⊆-refl-unit-right : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans ⊆-refl w ≡ w)
  (_R_               : (Γ Δ : C) → Set)
  (R-refl            : ∀ {Γ} → Γ R Γ)
  (R-trans           : ∀ {Γ Δ Θ} → Γ R Δ →  Δ R Θ → Γ R Θ)
  (R-trans-assoc     : ∀ {Γ Δ Δ' Θ} → (r : Γ R Δ) (r' : Δ R Δ') (r'' : Δ' R Θ) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r''))
  (R-refl-unit-left  : ∀ {Γ Δ : C} (r : Γ R Δ) → R-trans r R-refl ≡ r)
  (R-refl-unit-right : ∀ {Γ Δ : C} (r : Γ R Δ) → R-trans R-refl r ≡ r) 
  where

open import Semantics.Presheaf.Base C _⊆_ ⊆-refl ⊆-trans
open import Semantics.Presheaf.LaxLax C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_
open import Semantics.Presheaf.Pointed C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-refl
  renaming (point'[_] to return'[_] ; point' to return')
open import Semantics.Presheaf.Multiplicative C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-trans R-trans-assoc
  renaming (mult'[_] to join'[_]; mult' to join'; mult'-assoc to join'-assoc)

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

return'-unit-right : join'[ 𝒫 ] ∘ return'[ ◯' 𝒫 ] ≈̇ id'[ ◯' 𝒫 ]
return'-unit-right {𝒫} = record { proof = λ {Γ} p → proof (λ w → auxproof p w) }
  where
  auxproof : (p : ◯' 𝒫 ₀ Γ) (w : Γ ⊆ Γ') → (join'[ 𝒫 ] ∘ return'[ ◯' 𝒫 ]) .apply p .apply-◯ w ◇'-≋[ 𝒫 ] id'[ ◯' 𝒫 ] .apply p .apply-◯ w
  auxproof p w rewrite (⊆-refl-unit-left w) = proof (refl , (R-refl-unit-right _ , ≋[ 𝒫 ]-refl))

return'-unit-left : join'[ 𝒫 ] ∘ (◯'-map return'[ 𝒫 ]) ≈̇ id'[ ◯' 𝒫 ]
return'-unit-left {𝒫} = record { proof = λ p → proof (λ w → proof
  (refl
  , R-refl-unit-left _
  , wk[ 𝒫 ]-pres-refl _)) }

