{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (IFrame)

module Semantics.Presheaf.Strong
  (C      : Set)
  (_⊆_    : (Γ Δ : C) → Set)
  (_R_    : (Γ Δ : C) → Set)
  (IF     : IFrame C _⊆_)
  (let open IFrame IF)
  (R-to-⊆ : ∀ {Γ Δ : C} → Γ R Δ → Γ ⊆ Δ)
  where

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.StrongFunctor

open import Semantics.Presheaf.Base C _⊆_ IF
open import Semantics.Presheaf.CartesianClosure C _⊆_ IF
open import Semantics.Presheaf.LaxLax C _⊆_ _R_ IF 

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    Θ Θ' Θ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'    : Psh
    𝒬 𝒬'     : Psh
    ℛ ℛ' ℛ'' : Psh
    s s'       : 𝒫 →̇ 𝒬
    t t'       : 𝒫 →̇ 𝒬
    u u'       : 𝒫 →̇ 𝒬

module _ where

  ◇'-transport : 𝒫 ₀ Γ → ◇'-Fam 𝒬 Γ → ◇'-Fam (𝒫 ×' 𝒬) Γ
  ◇'-transport {𝒫} p (elem (Δ , r , q)) = elem (Δ , r , elem (wk[ 𝒫 ] (R-to-⊆ r) p , q))

  abstract
    ◇'-transport-pres-≋ : {p p' : 𝒫 ₀ Γ'} {q q' : ◇'-Fam 𝒬 Γ'}
        → p ≋[ 𝒫 ] p' → q ◇'-≋[ 𝒬 ] q'
        → (◇'-transport p q) ◇'-≋[ 𝒫 ×' 𝒬 ] (◇'-transport p' q')
    ◇'-transport-pres-≋ {𝒫} p≋p' (proof (refl , refl , q≋q')) = proof (refl , refl , proof (wk[ 𝒫 ]-pres-≋ _ p≋p' , q≋q'))

    ◇'-transport-square₁ : (t : 𝒫 →̇ 𝒫') {p : 𝒫 ₀ Γ} {q : ◇'-Fam 𝒬 Γ}
     → ◇'-transport (t .apply p) q ◇'-≋[ 𝒫' ×' 𝒬 ] ◇'-map-fun (t ×'-map id') (◇'-transport p q)
    ◇'-transport-square₁ {𝒫} {𝒫'} {𝒬 = 𝒬} t = proof (refl , refl , proof (t .natural _ _ , ≋[ 𝒬 ]-refl))

    ◇'-transport-square₂ : (t : 𝒬 →̇ 𝒬') {p : 𝒫 ₀ Γ} {q : ◇'-Fam 𝒬 Γ}
     → ◇'-transport p (◇'-map-fun t q) ◇'-≋[ 𝒫 ×' 𝒬' ] ◇'-map-fun (id' ×'-map t) (◇'-transport p q)
    ◇'-transport-square₂ {𝒬} {𝒬'} {𝒫 = 𝒫} t = proof (refl , refl , ≋[ 𝒫 ×' 𝒬' ]-refl)

-- Refer to `https://ncatlab.org/nlab/show/tensorial+strength`
◯'-strength : (𝒫 𝒬 : Psh) → 𝒫 ×' (◯' 𝒬) →̇ ◯' (𝒫 ×' 𝒬)
◯'-strength 𝒫 𝒬 = record
  { fun     = λ p×◯q → elem λ w →
              let p   = π₁' .apply p×◯q
                  ◯q  = π₂' . apply p×◯q
                  ◇q  = ◯q .apply-◯ w
                  p'  = wk[ 𝒫 ] w p
              in ◇'-transport p' ◇q
  ; pres-≋  = λ p×◯q≋p'×◯q' → proof λ w →
              let p≋p'   = π₁' .apply-≋ p×◯q≋p'×◯q'
                  ◯q≋◯q' = π₂' .apply-≋ p×◯q≋p'×◯q'
                  ◇q≋◇q' = ◯q≋◯q' .pw w
              in ◇'-transport-pres-≋ (wk[ 𝒫 ]-pres-≋ _ p≋p') ◇q≋◇q'
  ; natural = λ w _p×◯q → proof λ w' → ◇'-transport-pres-≋ (wk[ 𝒫 ]-pres-trans w w' _) ◇'-≋-refl
  }

abstract
  ◯'-strength-natural₁ : (t : 𝒫 →̇ 𝒫') → ◯'-strength 𝒫' 𝒬 ∘ (t ×'-map id') ≈̇ (◯'-map (t ×'-map id')) ∘ ◯'-strength 𝒫 𝒬
  ◯'-strength-natural₁ t = record
    { proof = λ _p → proof λ w →
                ◇'-≋-trans
                  (◇'-transport-pres-≋ (t .natural w _) ◇'-≋-refl)
                  (◇'-transport-square₁ t)
    }

  ◯'-strength-natural₂ : (t : 𝒬 →̇ 𝒬') → ◯'-strength 𝒫 𝒬' ∘ (id' ×'-map (◯'-map t)) ≈̇ (◯'-map (id' ×'-map t)) ∘ ◯'-strength 𝒫 𝒬
  ◯'-strength-natural₂ t = record { proof = λ _p → proof λ _w → ◇'-transport-square₂ t }

  ◯'-strength-assoc : ◯'-map assoc' ∘ ◯'-strength (𝒫 ×' 𝒬) ℛ ≈̇ (◯'-strength 𝒫 (𝒬 ×' ℛ) ∘ (id' ×'-map (◯'-strength 𝒬 ℛ)) ∘ assoc')
  ◯'-strength-assoc = record { proof = λ _p → proof λ _w → ◇'-≋-refl }

  ◯'-strength-unit :  ◯'-map π₂' ∘ ◯'-strength []' 𝒫 ≈̇ π₂'
  ◯'-strength-unit = record { proof = λ _p → proof λ _w → ◇'-≋-refl }

-- derived categorical laws
abstract
  ◯'-strength-π₂ : {𝒫 𝒬 : Psh} → ◯'-map π₂' ∘ ◯'-strength 𝒫 𝒬 ≈̇ π₂'
  ◯'-strength-π₂ {𝒫} {𝒬} = let open EqReasoning (→̇-setoid (𝒫 ×' (◯' 𝒬)) (◯' 𝒬)) in begin
    ◯'-map π₂' ∘ ◯'-strength 𝒫 𝒬
      ≈⟨ ∘-pres-≈̇-left (≈̇-sym (◯'-map-pres-≈̇ (≈̇-trans (×'-beta-right π₂') (id'-unit-left 𝒬 π₂')))) (◯'-strength 𝒫 𝒬) ⟩
    ◯'-map (π₂' ∘ (unit' ×'-map id')) ∘ ◯'-strength 𝒫 𝒬
      ≈⟨ ∘-pres-≈̇-left (◯'-map-pres-∘ π₂' (unit' ×'-map id')) (◯'-strength 𝒫 𝒬) ⟩
    (◯'-map π₂' ∘ ◯'-map (unit' ×'-map id')) ∘ ◯'-strength 𝒫 𝒬
      ≈⟨ ∘-assoc (◯'-map π₂') ( ◯'-map (unit' ×'-map id')) (◯'-strength 𝒫 𝒬) ⟩
    ◯'-map π₂' ∘ ◯'-map (unit' ×'-map id') ∘ ◯'-strength 𝒫 𝒬
       ≈⟨ ∘-pres-≈̇-right (◯'-map π₂') (≈̇-sym (◯'-strength-natural₁ unit')) ⟩
    ◯'-map π₂' ∘ (◯'-strength []' 𝒬) ∘ (unit' ×'-map id')
       ≈˘⟨ ∘-assoc (◯'-map π₂') (◯'-strength []' 𝒬) (unit' ×'-map id') ⟩
    (◯'-map π₂' ∘ ◯'-strength []' 𝒬) ∘ unit' ×'-map id'
       ≈⟨ ∘-pres-≈̇-left ◯'-strength-unit (unit' ×'-map id') ⟩
    π₂' ∘ (unit' ×'-map id')
      ≈⟨ ≈̇-trans (×'-beta-right π₂') (id'-unit-left (◯' 𝒬) π₂') ⟩
    π₂' ∎

letin' : (t : 𝒫 →̇ ◯' 𝒬) → (u : (𝒫 ×' 𝒬) →̇ ℛ) → 𝒫 →̇ ◯' ℛ
letin' t u = (◯'-map u ∘ ◯'-strength _ _) ∘ pr' id' t

abstract
  ◯'-beta : {t : 𝒫 →̇ ◯' 𝒬} → {u : (𝒫 ×' 𝒬) →̇ ℛ} {u' : (𝒫 ×' ℛ →̇ ℛ')}
    → letin' (letin' t u) u' ≈̇ letin' t (u' [ pr' π₁' u ]' )
  ◯'-beta = record { proof = λ _p → proof λ _w → ◇'-≋-refl }

  ◯'-eta : {t : 𝒫 →̇ ◯' 𝒬} → t ≈̇ letin' t π₂'
  ◯'-eta {t = t} = ≈̇-sym (≈̇-trans (∘-pres-≈̇-left ◯'-strength-π₂ (pr' id' t)) (×'-beta-right t))

◯'-is-strong : StrongFunctor PshCat-is-CC ◯'-is-PshFunctor
◯'-is-strong = record
               { ◯'-strength[_,_] = ◯'-strength
               ; ◯'-strength-natural₁ = ◯'-strength-natural₁
               ; ◯'-strength-natural₂ = ◯'-strength-natural₂
               ; ◯'-strength-assoc = ◯'-strength-assoc
               ; ◯'-strength-unit = ◯'-strength-unit
               }
