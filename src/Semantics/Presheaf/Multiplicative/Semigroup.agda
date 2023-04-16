{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame)

module Semantics.Presheaf.Multiplicative.Semigroup
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (_R_               : (Γ Δ : C) → Set)
  (IF                : IFrame C _⊆_)
  (let open IFrame IF)
  (R-trans           : ∀ {Γ Δ Θ} → Γ R Δ →  Δ R Θ → Γ R Θ)
  (R-trans-assoc     : ∀ {Γ Δ Δ' Θ} → (r : Γ R Δ) (r' : Δ R Δ') (r'' : Δ' R Θ) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r''))
  where

open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Semantics.Presheaf.Base C _⊆_ IF
open import Semantics.Presheaf.LaxLax C _⊆_ _R_ IF
open import Semantics.Presheaf.Multiplicative.Magma C _⊆_ _R_ IF R-trans

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

mult'-assoc : mult'[ 𝒫 ] ∘ (◯'-map mult'[ 𝒫 ]) ≈̇ mult'[ 𝒫 ] ∘ mult'[ ◯' 𝒫 ]
mult'-assoc {𝒫} = record { proof = λ p → proof (λ w → proof
  (≡-refl
  , ≡-sym (R-trans-assoc _ _ _)
  , ≋[ 𝒫 ]-refl)) }
