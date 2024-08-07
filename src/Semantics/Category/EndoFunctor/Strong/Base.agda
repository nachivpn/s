{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Strong.Base where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

record IsStrong {C : Category} (isCartesian : IsCartesian C) (F : EndoFunctor C) : Set₂ where
  open Category C
  open IsCartesian isCartesian
  open EndoFunctor F

  -- tensorial strength taking the tensor product as the cartesian product
  field
    ℱ'-strength[_,_] : (P Q : Obj) → P ×' (ℱ' Q) →̇ ℱ' (P ×' Q)
    ℱ'-strength-natural₁ : {P P' Q : Obj} (φ : P →̇ P') → ℱ'-strength[ P' , Q ] ∘ (φ ×'-map id'[ ℱ' Q ]) ≈̇ (ℱ'-map (φ ×'-map id'[ Q ])) ∘ ℱ'-strength[ P , Q ]
    ℱ'-strength-natural₂ : {P Q Q' : Obj} (t : Q →̇ Q') → ℱ'-strength[ P , Q' ] ∘ (id'[ P ] ×'-map (ℱ'-map t)) ≈̇ (ℱ'-map (id'[ P ] ×'-map t)) ∘ ℱ'-strength[ P , Q ]
    ℱ'-strength-assoc    : {P Q R : Obj} → ℱ'-map ×'-assoc ∘ ℱ'-strength[ (P ×' Q) , R ] ≈̇ ℱ'-strength[ P , Q ×' R ] ∘ (id'[ P ] ×'-map ℱ'-strength[ Q , R ] ∘ ×'-assoc)
    ℱ'-strength-unit     : {P : Obj} → ℱ'-map π₂' ∘ ℱ'-strength[ []' , P ] ≈̇ π₂'

  ℱ'-strength : {P Q : Obj} → P ×' (ℱ' Q) →̇ ℱ' (P ×' Q)
  ℱ'-strength = ℱ'-strength[ _ , _ ]

  -- derived constructs and laws
  letin' : {P Q R : Obj} (φ : P →̇ ℱ' Q) → (ψ : (P ×' Q) →̇ R) → P →̇ ℱ' R
  letin' φ ψ = (ℱ'-map ψ ∘ ℱ'-strength) ∘ pr' id' φ

  abstract

    letin'-pres-≈̇ : ∀ {P Q R : Obj} {φ φ' : P →̇ ℱ' Q} {ψ ψ' : (P ×' Q) →̇ R} → (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → letin' φ ψ ≈̇ letin' φ' ψ'
    letin'-pres-≈̇  {P} {Q} φ≈̇φ' ψ≈̇ψ' = ∘-pres-≈̇ (∘-pres-≈̇-left (ℱ'-map-pres-≈̇ ψ≈̇ψ') ℱ'-strength) (⟨,⟩'-pres-≈̇-right _ φ≈̇φ')

    letin'-pres-≈̇-left : ∀ {P Q R : Obj} {φ φ' : P →̇ ℱ' Q} (φ≈̇φ' : φ ≈̇ φ') (ψ : (P ×' Q) →̇ R) → letin' φ ψ ≈̇ letin' φ' ψ
    letin'-pres-≈̇-left φ≈̇φ' ψ = letin'-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

    letin'-pres-≈̇-right : ∀ {P Q R : Obj} (φ : P →̇ ℱ' Q) {ψ ψ' : (P ×' Q) →̇ R} (ψ≈̇ψ' : ψ ≈̇ ψ')→ letin' φ ψ ≈̇ letin' φ ψ'
    letin'-pres-≈̇-right φ ψ≈̇ψ' = letin'-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

    letin'-nat : ∀ {P P' Q R : Obj} (φ : P →̇ ℱ' Q) → (ψ : (P ×' Q) →̇ R) (ω : P' →̇ P) → letin' φ ψ ∘ ω ≈̇ letin' (φ ∘ ω) (ψ ∘ (ω ×'-map id'[ Q ]))
    letin'-nat {P} {P'} {Q} {R} φ ψ ω =  let open EqReasoning (→̇-setoid P' (ℱ' R)) in begin
      ((ℱ'-map ψ ∘ ℱ'-strength[ P , Q ]) ∘ pr' id' φ) ∘ ω
        ≈⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right  _ (≈̇-trans (⟨,⟩'-nat id' φ ω) (⟨,⟩'-pres-≈̇-left (id'-unit-left P ω) _))) ⟩
      (ℱ'-map ψ ∘ ℱ'-strength[ P , Q ]) ∘ (pr' ω (φ ∘ ω))
        ≈⟨ ∘-assoc _ _ _ ⟩
      ℱ'-map ψ ∘ ℱ'-strength[ P , Q ] ∘ (pr' ω (φ ∘ ω))
       ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (≈̇-sym (≈̇-trans
            (×'-map-∘-⟨,⟩' _ _ _ _)
            (⟨,⟩'-pres-≈̇ (id'-unit-right _ _) (id'-unit-left _ _))))) ⟩
      ℱ'-map ψ ∘ (ℱ'-strength[ P , Q ] ∘ ((ω ×'-map id') ∘ pr' id' (φ ∘ ω)))
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩
      ℱ'-map ψ ∘ (ℱ'-strength[ P , Q ] ∘ (ω ×'-map id')) ∘ pr' id' (φ ∘ ω)
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (ℱ'-strength-natural₁ ω) _) ⟩
      ℱ'-map ψ ∘ ((ℱ'-map (ω ×'-map id') ∘ ℱ'-strength[ P' , Q ]) ∘ pr' id' (φ ∘ ω))
        ≈⟨ ≈̇-trans (≈̇-sym (∘-assoc _ _ _)) (∘-pres-≈̇-left (≈̇-sym (∘-assoc _ _ _)) _) ⟩
      ((ℱ'-map ψ ∘ ℱ'-map (ω ×'-map id')) ∘ ℱ'-strength[ P' , Q ]) ∘ pr' id' (φ ∘ ω)
        ≈˘⟨ ∘-pres-≈̇-left (∘-pres-≈̇-left (ℱ'-map-pres-∘ _ _) _) _ ⟩
      (ℱ'-map (ψ ∘ (ω ×'-map id')) ∘ ℱ'-strength[ P' , Q ]) ∘ pr' id' (φ ∘ ω) ∎

  abstract
    ℱ'-strength-π₂ : {P Q : Obj} → ℱ'-map π₂' ∘ ℱ'-strength[ P , Q ] ≈̇ π₂'[ P ]
    ℱ'-strength-π₂ {P} {Q} = let open EqReasoning (→̇-setoid (P ×' (ℱ' Q)) (ℱ' Q)) in begin
      ℱ'-map π₂' ∘ ℱ'-strength[ P , Q ]
        ≈˘⟨ ∘-pres-≈̇-left (ℱ'-map-pres-≈̇ (≈̇-trans (×'-beta-right _) (id'-unit-left _ _))) _ ⟩
      ℱ'-map (π₂' ∘ (unit' ×'-map id')) ∘ ℱ'-strength[ P , Q ]
        ≈⟨ ∘-pres-≈̇-left (ℱ'-map-pres-∘ _ _) _ ⟩
      (ℱ'-map π₂' ∘ ℱ'-map (unit' ×'-map id')) ∘ ℱ'-strength[ P , Q ]
        ≈⟨ ∘-assoc _ _ _ ⟩
      ℱ'-map π₂' ∘ ℱ'-map (unit' ×'-map id') ∘ ℱ'-strength[ P , Q ]
        ≈˘⟨ ∘-pres-≈̇-right _ (ℱ'-strength-natural₁ unit') ⟩
      ℱ'-map π₂' ∘ ℱ'-strength[ []' , Q ] ∘ (unit' ×'-map id')
        ≈˘⟨ ∘-assoc _ _ _ ⟩
      (ℱ'-map π₂' ∘ ℱ'-strength[ []' , Q ]) ∘ unit' ×'-map id'
        ≈⟨ ∘-pres-≈̇-left ℱ'-strength-unit _ ⟩
      π₂' ∘ (unit' ×'-map id')
        ≈⟨ ≈̇-trans (×'-beta-right _) (id'-unit-left _ _) ⟩
      π₂' ∎

    ℱ'-eta : {P Q : Obj} (φ : P →̇ ℱ' Q) → φ ≈̇ letin' φ π₂'
    ℱ'-eta {P} {Q} φ = ≈̇-sym (≈̇-trans (∘-pres-≈̇-left ℱ'-strength-π₂ (pr' id' φ)) (×'-beta-right id'[ P ]))

    ℱ'-beta : ∀ {P Q R R' : Obj} (φ : P →̇ ℱ' Q) (ψ : (P ×' Q) →̇ R) (ψ' : (P ×' R →̇ R')) → letin' (letin' φ ψ) ψ' ≈̇ letin' φ (ψ' ∘ ⟨ π₁'[ Q ] , ψ ⟩' )
    ℱ'-beta {P} {Q} {R} {R'} φ ψ ψ' = let open EqReasoning (→̇-setoid _ _) in begin
      (ℱ'-map ψ' ∘ ℱ'-strength[ P , R ]) ∘ ⟨ id' , ((ℱ'-map ψ) ∘ ℱ'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩' ⟩'
        ≈⟨ ∘-assoc _ _ _ ⟩
      ℱ'-map ψ' ∘ ℱ'-strength[ P , R ] ∘ ⟨ id' , ((ℱ'-map ψ) ∘ ℱ'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩' ⟩'
        ≈⟨ ∘-pres-≈̇-right _ step1-with-ℱ'-strength-natural₂ ⟩
      ℱ'-map ψ' ∘ ℱ'-map (id' ×'-map ψ) ∘ ℱ'-strength[ P , P ×' Q ] ∘ ⟨ id' , ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ step2-with-ℱ'-strength-assoc) ⟩
      ℱ'-map ψ' ∘ ℱ'-map (id' ×'-map ψ) ∘ ℱ'-map ×'-assoc ∘ ℱ'-strength[ P ×' P , Q ] ∘ ⟨ ⟨ id' , id' ⟩' , φ ⟩'
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (∘-pres-≈̇-right _ step3-with-ℱ'-strength-natural₁)) ⟩
      ℱ'-map ψ' ∘ ℱ'-map (id' ×'-map ψ) ∘ ℱ'-map ×'-assoc ∘ ℱ'-map (⟨ id' , id' ⟩' ×'-map id') ∘ ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩'
        ≈˘⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (∘-assoc _ _ _)))) ⟩
      (ℱ'-map ψ' ∘ ℱ'-map (id' ×'-map ψ) ∘ ℱ'-map ×'-assoc ∘ ℱ'-map (⟨ id' , id' ⟩' ×'-map id')) ∘ ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩'
        ≈⟨ ∘-pres-≈̇-left step4-with-ℱ'-map-pres-∘ _ ⟩
      ℱ'-map (ψ' ∘ ⟨ π₁' , ψ ⟩') ∘ (ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩')
          ≈˘⟨ ∘-assoc _ _ _ ⟩
      (ℱ'-map (ψ' ∘ ⟨ π₁' , ψ ⟩') ∘ ℱ'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩' ∎
      where
      step1-with-ℱ'-strength-natural₂ : ℱ'-strength[ P , R ] ∘ ⟨ id' , (ℱ'-map ψ ∘ ℱ'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩' ⟩'
            ≈̇ ℱ'-map (id' ×'-map ψ) ∘ ℱ'-strength[ P , P ×' Q ] ∘ ⟨ id' , ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
      step1-with-ℱ'-strength-natural₂ = let open EqReasoning (→̇-setoid _ _) in begin
        ℱ'-strength[ P , R ] ∘ ⟨ id' , (ℱ'-map ψ ∘ ℱ'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩' ⟩'
          ≈⟨ ∘-pres-≈̇-right _ (⟨,⟩'-pres-≈̇-right _ (∘-assoc _ _ _)) ⟩
        ℱ'-strength[ P , R ] ∘ ⟨ id' , (ℱ'-map ψ) ∘ ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
          ≈˘⟨ ∘-pres-≈̇-right _ (≈̇-trans (×'-map-∘-⟨,⟩' _ _ _ _) (⟨,⟩'-pres-≈̇-left (id'-unit-left _ _) _)) ⟩
        ℱ'-strength[ P , R ] ∘ (id' ×'-map (ℱ'-map ψ)) ∘ ⟨ id' , ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
          ≈⟨ ≈̇-trans (≈̇-sym (∘-assoc _ _ _)) (≈̇-trans (∘-pres-≈̇-left (ℱ'-strength-natural₂ ψ) _) (∘-assoc _ _ _)) ⟩
        _ ∎

      step2-with-ℱ'-strength-assoc : ℱ'-strength[ P , P ×' Q ] ∘ ⟨ id' , ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
            ≈̇ ℱ'-map ×'-assoc ∘ ℱ'-strength[ P ×' P , Q ] ∘ ⟨ ⟨ id' , id' ⟩' , φ ⟩'
      step2-with-ℱ'-strength-assoc = let open EqReasoning (→̇-setoid _ _) in begin
        ℱ'-strength[ P , P ×' Q ] ∘ ⟨ id' , ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
          ≈˘⟨ ∘-pres-≈̇-right _ (⟨,⟩'-pres-≈̇-left (id'-unit-left P id') _) ⟩
        ℱ'-strength[ P , P ×' Q ] ∘ ⟨ id' ∘ id' , ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
          ≈˘⟨ ∘-pres-≈̇-right _ (×'-map-∘-⟨,⟩' _ _ _ _) ⟩
        ℱ'-strength[ P , P ×' Q ] ∘ (id' ×'-map ℱ'-strength[ P , Q ] ∘ ⟨ id' , ⟨ id' , φ ⟩' ⟩')
          ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (×'-assoc-∘-⟨⟨,⟩',⟩' _ _ _)) ⟩
        ℱ'-strength[ P , P ×' Q ] ∘ (id' ×'-map ℱ'-strength[ P , Q ] ∘ ×'-assoc ∘ ⟨ ⟨ id' , id' ⟩'  , φ ⟩')
          ≈˘⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (∘-assoc _ _ _)) ⟩
        (ℱ'-strength[ P , P ×' Q ] ∘ id' ×'-map ℱ'-strength[ P , Q ] ∘ ×'-assoc) ∘ ⟨ ⟨ id' , id' ⟩'  , φ ⟩'
          ≈˘⟨ ∘-pres-≈̇-left ℱ'-strength-assoc _ ⟩
        (ℱ'-map ×'-assoc ∘ ℱ'-strength[ P ×' P , Q ]) ∘ ⟨ ⟨ id' , id' ⟩'  , φ ⟩'
          ≈⟨ ∘-assoc _ _ _ ⟩
        _ ∎

      step3-with-ℱ'-strength-natural₁ : ℱ'-strength[ P ×' P , Q ] ∘ ⟨ ⟨ id' , id' ⟩' , φ ⟩'
            ≈̇ ℱ'-map (⟨ id' , id' ⟩' ×'-map id') ∘ ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩'
      step3-with-ℱ'-strength-natural₁ = let open EqReasoning (→̇-setoid _ _) in begin
        ℱ'-strength[ P ×' P , Q ] ∘ ⟨ ⟨ id' , id' ⟩' , φ ⟩'
          ≈˘⟨ ∘-pres-≈̇-right _ (≈̇-trans (×'-map-∘-⟨,⟩' _ _ _ _) (⟨,⟩'-pres-≈̇ (id'-unit-right _ _) (id'-unit-left _ _))) ⟩
        ℱ'-strength[ P ×' P , Q ] ∘ (⟨ id' , id' ⟩' ×'-map id'[ ℱ' Q ]) ∘ ⟨ id' , φ ⟩'
          ≈˘⟨ ∘-assoc _ _ _ ⟩
        (ℱ'-strength[ P ×' P , Q ] ∘ (⟨ id' , id' ⟩' ×'-map id'[ ℱ' Q ])) ∘ ⟨ id' , φ ⟩'
          ≈⟨ ∘-pres-≈̇-left (ℱ'-strength-natural₁ ⟨ id' , id' ⟩') _ ⟩
        (ℱ'-map (⟨ id' , id' ⟩' ×'-map id') ∘ ℱ'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩'
          ≈⟨ ∘-assoc _ _ _ ⟩
        _ ∎

      step4-with-ℱ'-map-pres-∘ : ℱ'-map ψ' ∘ ℱ'-map (id' ×'-map ψ) ∘ ℱ'-map ×'-assoc ∘ ℱ'-map (⟨ id' , id' ⟩' ×'-map id')
            ≈̇ ℱ'-map (ψ' ∘ ⟨ π₁' , ψ ⟩')
      step4-with-ℱ'-map-pres-∘ = let open EqReasoning (→̇-setoid _ _) in begin
        ℱ'-map ψ' ∘ ℱ'-map (id' ×'-map ψ) ∘ ℱ'-map ×'-assoc ∘ ℱ'-map (⟨ id' , id' ⟩' ×'-map id')
            ≈˘⟨ ∘-pres-≈̇-right _ (≈̇-trans (ℱ'-map-pres-∘ _ _) (∘-pres-≈̇-right _ (ℱ'-map-pres-∘ _ _))) ⟩
        ℱ'-map ψ' ∘ ℱ'-map (id' ×'-map ψ ∘ (×'-assoc ∘ ⟨ id' , id' ⟩' ×'-map id'))
           ≈⟨ ∘-pres-≈̇-right _ (ℱ'-map-pres-≈̇ (∘-pres-≈̇-right _ step4a)) ⟩
        ℱ'-map ψ' ∘ ℱ'-map (id' ×'-map ψ ∘ ⟨ π₁' , id' ⟩'  )
            ≈⟨ ∘-pres-≈̇-right _ (ℱ'-map-pres-≈̇ (×'-map-∘-⟨,⟩' _ _ _ _)) ⟩
        ℱ'-map ψ' ∘ ℱ'-map ⟨ id' ∘ π₁' , ψ ∘ id' ⟩'
            ≈⟨ ∘-pres-≈̇-right _ (ℱ'-map-pres-≈̇ (⟨,⟩'-pres-≈̇ (id'-unit-left _ _) (id'-unit-right _ _))) ⟩
        ℱ'-map ψ' ∘ ℱ'-map ⟨ π₁' , ψ ⟩'
            ≈˘⟨ ℱ'-map-pres-∘ _ _ ⟩
        _ ∎
        where
        step4a : ×'-assoc[ P , P , Q ] ∘ ⟨ id' , id' ⟩' ×'-map id' ≈̇ ⟨ π₁' , id' ⟩'
        step4a = let open EqReasoning (→̇-setoid _ _) in begin
          ×'-assoc ∘ ⟨ id' , id' ⟩' ×'-map id'
            ≈⟨ ∘-pres-≈̇-right _ (⟨,⟩'-pres-≈̇-right _ (id'-unit-left _ _)) ⟩
          ×'-assoc ∘ ⟨ ⟨ id' , id' ⟩' ∘ π₁' , π₂' ⟩'
            ≈⟨ ∘-pres-≈̇-right _ (⟨,⟩'-pres-≈̇-left (≈̇-trans (⟨,⟩'-nat _ _ _) (⟨,⟩'-pres-≈̇ (id'-unit-left _ _) (id'-unit-left _ _))) _) ⟩
          ×'-assoc ∘ ⟨ ⟨ π₁' , π₁' ⟩' , π₂' ⟩'
            ≈⟨ ×'-assoc-∘-⟨⟨,⟩',⟩' _ _ _ ⟩
          ⟨ π₁' , ⟨ π₁' , π₂' ⟩' ⟩'
            ≈˘⟨ ⟨,⟩'-pres-≈̇-right _ (≈̇-trans ×'-eta (⟨,⟩'-pres-≈̇ (id'-unit-right _ _) (id'-unit-right _ _))) ⟩
          _ ∎
