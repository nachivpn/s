{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong ; cong₂)
open import Semantics.Kripke.IFrame using (IFrame)

module Semantics.Presheaf.Strong.Pointed
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (_R_               : (Γ Δ : C) → Set)
  (IF                : IFrame C _⊆_)
  (let open IFrame IF)
  (R-refl            : ∀ {Γ} → Γ R Γ)
  (let R-refl[_]     : ∀ Γ → Γ R Γ ; R-refl[ Γ ] = R-refl {Γ})
  (R-to-⊆            : ∀ {Γ Δ : C} → Γ R Δ → Γ ⊆ Δ)
  (R-to-⊆-pres-refl  : ∀ {Γ} → R-to-⊆ R-refl[ Γ ] ≡ ⊆-refl)
  where

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base C _⊆_ IF
open import Semantics.Presheaf.CartesianClosure C _⊆_ IF
open import Semantics.Presheaf.LaxLax C _⊆_ _R_ IF
open import Semantics.Presheaf.Strong C _⊆_ _R_ IF R-to-⊆
open import Semantics.Presheaf.Pointed C _⊆_ _R_ IF R-refl

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
