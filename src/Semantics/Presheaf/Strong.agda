{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame ; MFrame ; InclusiveMFrame)

module Semantics.Presheaf.Strong
  {C      : Set}
  {_⊆_    : (Γ Δ : C) → Set}
  {IF     : IFrame C _⊆_}
  {_R_    : (Γ Δ : C) → Set}
  (MF     : MFrame IF _R_)
  (IMF    : InclusiveMFrame MF)
  (let open MFrame MF)
  (let open InclusiveMFrame IMF)
  where

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Strong.Base

open import Semantics.Presheaf.Base IF
open import Semantics.Presheaf.CartesianClosure IF
open import Semantics.Presheaf.Possibility MF

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    Θ Θ' Θ'' : C
    𝒫 𝒫'  : Psh
    𝒬 𝒬'  : Psh
    ℛ ℛ' : Psh

◇'-strength : (𝒫 𝒬 : Psh) → 𝒫 ×' (◇' 𝒬) →̇ ◇' (𝒫 ×' 𝒬)
◇'-strength 𝒫 𝒬 = record
  { fun     = λ p×◇q → ◇'-strength-fun (π₁' .apply p×◇q) (π₂' .apply p×◇q)
  ; pres-≋  = λ r≋r' → ◇'-strength-fun-pres-≋ (π₁' .apply-≋ r≋r') (π₂' .apply-≋ r≋r')
  ; natural = λ w p×◇q → ◇'-strength-fun-natural w (π₁' .apply p×◇q) (π₂' .apply p×◇q)
  }
  where
  
  ◇'-strength-fun : 𝒫 ₀ Γ → ◇'-Fam 𝒬 Γ → ◇'-Fam (𝒫 ×' 𝒬) Γ
  ◇'-strength-fun p (elem (Δ , r , q)) = elem (Δ , r , elem (wk[ 𝒫 ] (R-to-⊆ r) p , q))

  abstract
    ◇'-strength-fun-pres-≋ : {p p' : 𝒫 ₀ Γ'} {q q' : ◇'-Fam 𝒬 Γ'}
        → p ≋[ 𝒫 ] p' → q ◇'-≋[ 𝒬 ] q'
        → (◇'-strength-fun p q) ◇'-≋[ 𝒫 ×' 𝒬 ] (◇'-strength-fun p' q')
    ◇'-strength-fun-pres-≋ p≋p' (proof (refl , refl , q≋q')) = proof (refl , refl , proof (wk[ 𝒫 ]-pres-≋ _ p≋p' , q≋q'))

    ◇'-strength-fun-natural : (w : Γ ⊆ Γ') (p : 𝒫 ₀ Γ) (q : ◇'-Fam 𝒬 Γ)
      →  wk[ ◇' (𝒫 ×' 𝒬) ] w (◇'-strength-fun p q) ≋[ ◇' (𝒫 ×' 𝒬) ] ◇'-strength-fun (wk[ 𝒫 ] w p) (wk[ ◇' 𝒬 ] w q)
    ◇'-strength-fun-natural w p q = let open EqReasoning ≋[ 𝒫 ]-setoid in
      proof (refl , (refl , (proof
        ((begin
          wk[ 𝒫 ] (factor⊆ w _) (wk[ 𝒫 ] (R-to-⊆ _) p)
            ≈˘⟨ wk[ 𝒫 ]-pres-trans (R-to-⊆ _) (factor⊆ w _) p ⟩
          wk[ 𝒫 ] (⊆-trans (R-to-⊆ _) (factor⊆ w _)) p
            ≡˘⟨ cong (λ w → wk[ 𝒫 ] w p) (factor-pres-R-to-⊆ w _) ⟩
          wk[ 𝒫 ] (⊆-trans w (R-to-⊆ (factorR w _))) p
            ≈⟨  wk[ 𝒫 ]-pres-trans w (R-to-⊆ (factorR w _)) p ⟩
          wk[ 𝒫 ] (R-to-⊆ (factorR w _)) (wk[ 𝒫 ] w p)          
           ∎)
        , ≋[ 𝒬 ]-refl))))
        
◇'-is-strong : IsStrong PshCat-is-CC ◇'-is-PshFunctor
◇'-is-strong = record
  { strength[_,_]     = ◇'-strength
  ; strength-natural₁ = ◇'-strength-natural₁
  ; strength-natural₂ = ◇'-strength-natural₂
  ; strength-assoc    = ◇'-strength-assoc
  ; strength-unit     = ◇'-strength-unit
  }
  where
  abstract
    ◇'-strength-natural₁ : (t : 𝒫 →̇ 𝒫') → ◇'-strength 𝒫' 𝒬 ∘ (t ×'-map id') ≈̇ (◇'-map (t ×'-map id')) ∘ ◇'-strength 𝒫 𝒬
    ◇'-strength-natural₁ {𝒬 = 𝒬} t = record { proof = λ _p → proof (refl , refl , proof (t .natural _ _ , ≋[ 𝒬 ]-refl)) }

    ◇'-strength-natural₂ : (t : 𝒬 →̇ 𝒬') → ◇'-strength 𝒫 𝒬' ∘ (id' ×'-map (◇'-map t)) ≈̇ (◇'-map (id' ×'-map t)) ∘ ◇'-strength 𝒫 𝒬
    ◇'-strength-natural₂ {𝒬' = 𝒬'} {𝒫 = 𝒫} t = record { proof = λ _p → proof (refl , refl , ≋[ 𝒫 ×' 𝒬' ]-refl) }

    ◇'-strength-assoc : ◇'-map assoc' ∘ ◇'-strength (𝒫 ×' 𝒬) ℛ ≈̇ (◇'-strength 𝒫 (𝒬 ×' ℛ) ∘ (id' ×'-map (◇'-strength 𝒬 ℛ)) ∘ assoc')
    ◇'-strength-assoc {𝒫 = 𝒫} {𝒬 = 𝒬} {ℛ = ℛ} = record { proof = λ _p → ≋[ ◇' (𝒫 ×' (𝒬 ×' ℛ)) ]-refl }

    ◇'-strength-unit :  ◇'-map π₂' ∘ ◇'-strength []' 𝒫 ≈̇ π₂'
    ◇'-strength-unit {𝒫} = record { proof = λ _p → ≋[ ◇' 𝒫 ]-refl }
