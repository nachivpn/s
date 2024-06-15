{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame ; MFrame ; TransitiveMFrame)

module Semantics.Presheaf.Multiplicative.Magma
  {C      : Set}
  {_⊆_    : (Γ Δ : C) → Set}
  {IF     : IFrame C _⊆_}
  {_R_    : (Γ Δ : C) → Set}
  (MF     : MFrame IF _R_)
  (TMF    : TransitiveMFrame MF)
  (let open MFrame MF)
  (let open TransitiveMFrame TMF)
  where

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong₂)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base IF
open import Semantics.Presheaf.Possibility MF

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

mult'[_] : ∀ 𝒫 → (◇' ◇' 𝒫 →̇ ◇' 𝒫)
mult'[ 𝒫 ] = record
  { fun     = ◇'-mult'-fun 
  ; pres-≋  = ◇'-mult'-fun-pres-≋  
  ; natural = ◇'-mult'-natural
  }
  where
  ◇'-mult'-fun : ◇'-Fam (◇' 𝒫) Γ  → ◇'-Fam 𝒫 Γ
  ◇'-mult'-fun (elem (Δ , ΓRΔ , (elem (Δ' , ΔRΔ' , p)))) = elem (Δ' , R-trans ΓRΔ ΔRΔ' , p)

  abstract
    ◇'-mult'-fun-pres-≋ : {p p' : ◇'-Fam (◇' 𝒫) Γ} 
      → p ◇'-≋[ ◇' 𝒫 ] p'
      → ◇'-mult'-fun p ◇'-≋[ 𝒫 ] ◇'-mult'-fun p'
    ◇'-mult'-fun-pres-≋ (proof (refl , refl , (proof (refl , refl , p≋p')))) = proof (refl , refl , p≋p')

    ◇'-mult'-natural : (w : Γ ⊆ Γ') (p : (◇' (◇' 𝒫)) ₀ Γ) →
      (wk[ ◇' 𝒫 ] w (◇'-mult'-fun p)) ≋[ ◇' 𝒫 ] (◇'-mult'-fun (wk[ ◇' (◇' 𝒫) ] w p))
    ◇'-mult'-natural w (elem (Δ , ΓRΔ , (elem (Δ' , ΔRΔ' , p)))) rewrite factor-pres-R-trans w ΓRΔ ΔRΔ' = ≋[ ◇' 𝒫 ]-refl

abstract
-- mult' is a natural transformation from the composition of functors ◇' ∘ ◇' to ◇'
  mult'-natural : (t :  𝒫 →̇  𝒬) → mult'[ 𝒬 ] ∘ (◇'-map (◇'-map t)) ≈̇ (◇'-map t) ∘ mult'[ 𝒫 ]
  mult'-natural {𝒫} {𝒬} t = record { proof = λ _p → ≋[ ◇' 𝒬 ]-refl } 
  
mult' = λ {𝒫} → mult'[ 𝒫 ]
