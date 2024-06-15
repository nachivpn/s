{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame ; MFrame ; ReflexiveMFrame ; TransitiveMFrame)

module Semantics.Presheaf.Monad
  {C      : Set}
  {_⊆_    : (Γ Δ : C) → Set}
  {IF     : IFrame C _⊆_}
  {_R_    : (Γ Δ : C) → Set}
  (MF     : MFrame IF _R_)
  (RMF    : ReflexiveMFrame MF)
  (TMF    : TransitiveMFrame MF)
  (let open MFrame MF)
  (let open ReflexiveMFrame RMF)
  (let open TransitiveMFrame TMF)
  (R-trans-assoc     : {Γ Δ Δ' Θ : C} (r : Γ R Δ) (r' : Δ R Δ') (r'' : Δ' R Θ) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r''))
  (R-refl-unit-left  : {Γ Δ : C} (r : Γ R Δ) → R-trans r R-refl ≡ r)
  (R-refl-unit-right : {Γ Δ : C} (r : Γ R Δ) → R-trans R-refl r ≡ r) 
  where

open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Semantics.Presheaf.Base IF
open import Semantics.Presheaf.Possibility MF
open import Semantics.Presheaf.Pointed MF RMF 
  renaming (point'[_] to return'[_] ; point' to return')
open import Semantics.Presheaf.Multiplicative MF TMF R-trans-assoc
  renaming (mult'[_] to join'[_]; mult' to join'; mult'-assoc to join'-assoc)

private
  variable
    𝒫 : Psh

return'-unit-right : join'[ 𝒫 ] ∘ return'[ ◇' 𝒫 ] ≈̇ id'[ ◇' 𝒫 ]
return'-unit-right {𝒫} = record { proof = λ p → proof
  (≡-refl
  , R-refl-unit-right _
  , ≋[ 𝒫 ]-refl) }

return'-unit-left : join'[ 𝒫 ] ∘ (◇'-map return'[ 𝒫 ]) ≈̇ id'[ ◇' 𝒫 ]
return'-unit-left {𝒫} = record { proof = λ p → proof
  (≡-refl
  , R-refl-unit-left _
  , ≋[ 𝒫 ]-refl) }
