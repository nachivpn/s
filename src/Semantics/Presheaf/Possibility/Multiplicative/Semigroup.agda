{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame ; MFrame ; TransitiveMFrame)

module Semantics.Presheaf.Possibility.Multiplicative.Semigroup
  {C      : Set}
  {_⊆_    : (Γ Δ : C) → Set}
  {IF     : IFrame C _⊆_}
  {_R_    : (Γ Δ : C) → Set}
  (MF     : MFrame IF _R_)
  (TMF    : TransitiveMFrame MF)
  (let open MFrame MF)
  (let open TransitiveMFrame TMF)
  where

open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Semantics.Presheaf.Base IF
open import Semantics.Presheaf.Possibility.Base MF
open import Semantics.Presheaf.Possibility.Multiplicative.Magma MF TMF

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

mult'-assoc : mult'[ 𝒫 ] ∘ (◇'-map mult'[ 𝒫 ]) ≈̇ mult'[ 𝒫 ] ∘ mult'[ ◇' 𝒫 ]
mult'-assoc {𝒫} = record { proof = λ p → proof (≡-refl , ≡-sym (R-trans-assoc _ _ _) , ≋[ 𝒫 ]-refl) }
