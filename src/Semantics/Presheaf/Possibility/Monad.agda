{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame ; MFrame ; ReflexiveMFrame ; TransitiveMFrame ; ReflexiveTransitiveMFrame)

module Semantics.Presheaf.Possibility.Monad
  {C      : Set}
  {_⊆_    : (Γ Δ : C) → Set}
  {IF     : IFrame C _⊆_}
  {_R_    : (Γ Δ : C) → Set}
  (MF     : MFrame IF _R_)
  (RMF    : ReflexiveMFrame MF)
  (TMF    : TransitiveMFrame MF)
  (RTMF   : ReflexiveTransitiveMFrame MF RMF TMF)
  (let open MFrame MF)
  (let open ReflexiveMFrame RMF)
  (let open TransitiveMFrame TMF)
  (let open ReflexiveTransitiveMFrame RTMF)
  where

open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Semantics.Presheaf.Base IF
open import Semantics.Presheaf.Possibility.Base MF
open import Semantics.Presheaf.Possibility.Pointed MF RMF
  renaming (point'[_] to return'[_] ; point' to return') public
open import Semantics.Presheaf.Possibility.Multiplicative MF TMF
  renaming (mult'[_] to join'[_]; mult' to join'; mult'-assoc to join'-assoc) public

open import Semantics.Category.EndoFunctor.Monad

private
  variable
    𝒫 : Psh

join'-unit-left : join'[ 𝒫 ] ∘ return'[ ◇' 𝒫 ] ≈̇ id'[ ◇' 𝒫 ]
join'-unit-left {𝒫} = record { proof = λ p → proof
  (≡-refl
  , R-refl-unit-right _
  , ≋[ 𝒫 ]-refl) }

join'-unit-right : join'[ 𝒫 ] ∘ (◇'-map return'[ 𝒫 ]) ≈̇ id'[ ◇' 𝒫 ]
join'-unit-right {𝒫} = record { proof = λ p → proof
  (≡-refl
  , R-refl-unit-left _
  , ≋[ 𝒫 ]-refl) }

◇'-is-monad : IsMonad ◇'-is-pointed ◇'-is-multiplicative
◇'-is-monad = record { join-unit-left = join'-unit-left ; join-unit-right = join'-unit-right }
