{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

module Semantics.Presheaf.Pointed
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
  where

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base C _⊆_ ⊆-refl ⊆-trans
open import Semantics.Presheaf.LaxLax C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_
open import Semantics.Presheaf.Strong C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right _R_ R-to-⊆

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

point'[_] : ∀ 𝒫 → 𝒫 →̇ ◯' 𝒫
point'[_] 𝒫 = record
  { fun     = λ p → elem λ {Γ'} w → elem (Γ' , (R-refl[ _ ] , wk[ 𝒫 ] w p))
  ; pres-≋  = λ p≋p' → proof λ w → proof (refl , (refl , (wk[ 𝒫 ]-pres-≋ w p≋p')))
  ; natural = λ w p → proof (λ w' → proof (refl , (refl , wk[ 𝒫 ]-pres-trans w w' p)))
  }

abstract
  -- point' is a natural transformation from the identity functor to ◯'
  point'-natural : (t : 𝒫 →̇ 𝒬) → point'[ 𝒬 ] ∘ t ≈̇ (◯'-map t) ∘ point'[ 𝒫 ]
  point'-natural t = record { proof = λ p → proof (λ w → proof (refl , (refl , t .natural w p))) }

  -- obs: point' need not be well-pointed
  -- point'-well-pointed : (t : 𝒫 →̇ ◯' 𝒬) → ◯'-map point'[ 𝒫 ] ≈̇ point'[ ◯' 𝒫 ]

  -- obs: "The pointed endofunctor underlying a monad T is
  -- well-pointed if and only if T is idempotent."  [Proposition 3.1.,
  -- https://ncatlab.org/nlab/show/pointed+endofunctor]

point' = λ {𝒫} → point'[ 𝒫 ]