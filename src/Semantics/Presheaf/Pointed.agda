{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame)

module Semantics.Presheaf.Pointed
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (_R_               : (Γ Δ : C) → Set)
  (IF                : IFrame C _⊆_)
  (let open IFrame IF)
  (R-refl            : ∀ {Γ} → Γ R Γ)
  (let R-refl[_]     : ∀ Γ → Γ R Γ ; R-refl[ Γ ] = R-refl {Γ})
  where

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base C _⊆_ IF
open import Semantics.Presheaf.LaxLax C _⊆_ _R_ IF

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

◇'-point' : 𝒫 ₀ Γ → ◇'-Fam 𝒫 Γ
◇'-point' x = elem (_ , (R-refl , x))

◇'-point'-pres-≋ : {x y : 𝒫 ₀ Γ} → x ≋[ 𝒫 ] y → ◇'-point' {𝒫} x ◇'-≋ ◇'-point' y
◇'-point'-pres-≋ x≋y = proof (refl , refl , x≋y)

point'[_] : ∀ 𝒫 → 𝒫 →̇ ◯' 𝒫
point'[_] 𝒫 = record
  { fun     = λ p → elem λ {Γ'} w → ◇'-point' (wk[ 𝒫 ] w p)
  ; pres-≋  = λ p≋p' → proof λ w → ◇'-point'-pres-≋ (wk[ 𝒫 ]-pres-≋ w p≋p')
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
