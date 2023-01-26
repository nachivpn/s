{-# OPTIONS --without-K #-}

module Semantics.Category.StrongFunctor where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.CartesianClosed

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

record HasStrongFunctor (C : Category) (isCartesian : IsCartesian C) : Set₂ where
  open Category C
  open IsCartesian isCartesian

  -- endofunctor
  field
    ◯'_     : (P : Obj) → Obj
    ◯'-map_ : {P Q : Obj} (φ : P →̇ Q) → (◯' P →̇ ◯' Q)
    ◯'-map-pres-≈̇  : {P Q : Obj} {φ φ' : P →̇ Q} → φ ≈̇ φ' → ◯'-map φ ≈̇ ◯'-map φ'
    ◯'-map-pres-id : {P : Obj} → ◯'-map id'[ P ] ≈̇ id'
    ◯'-map-pres-∘  : {P Q R : Obj} → (ψ : Q →̇ R) (φ : P →̇ Q) → ◯'-map (ψ ∘ φ) ≈̇ ◯'-map ψ ∘ ◯'-map φ

  -- strength
  field
    ◯'-strength[_,_] : (P Q : Obj) → P ×' (◯' Q) →̇ ◯' (P ×' Q)
    ◯'-strength-natural₁ : {P P' Q : Obj} (φ : P →̇ P') → ◯'-strength[ P' , Q ] ∘ (φ ×'-map id'[ ◯' Q ]) ≈̇ (◯'-map (φ ×'-map id'[ Q ])) ∘ ◯'-strength[ P , Q ]
    ◯'-strength-natural₂ : {P Q Q' : Obj} (t : Q →̇ Q') → ◯'-strength[ P , Q' ] ∘ (id'[ P ] ×'-map (◯'-map t)) ≈̇ (◯'-map (id'[ P ] ×'-map t)) ∘ ◯'-strength[ P , Q ]
    ◯'-strength-assoc    : {P Q R : Obj} → ◯'-map ×'-assoc ∘ ◯'-strength[ (P ×' Q) , R ] ≈̇ ◯'-strength[ P , Q ×' R ] ∘ (id'[ P ] ×'-map ◯'-strength[ Q , R ] ∘ ×'-assoc)
    ◯'-strength-unit     : {P : Obj} → ◯'-map π₂' ∘ ◯'-strength[ []' , P ] ≈̇ π₂'

  ◯'-strength : {P Q : Obj} → P ×' (◯' Q) →̇ ◯' (P ×' Q)
  ◯'-strength = ◯'-strength[ _ , _ ]

  -- derived constructs and laws
  letin' : {P Q R : Obj} (φ : P →̇ ◯' Q) → (ψ : (P ×' Q) →̇ R) → P →̇ ◯' R
  letin' φ ψ = (◯'-map ψ ∘ ◯'-strength) ∘ pr' id' φ

  abstract

    letin'-pres-≈̇ : ∀ {P Q R : Obj} {φ φ' : P →̇ ◯' Q} {ψ ψ' : (P ×' Q) →̇ R} → (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → letin' φ ψ ≈̇ letin' φ' ψ'
    letin'-pres-≈̇  {P} {Q} φ≈̇φ' ψ≈̇ψ' = ∘-pres-≈̇ (∘-pres-≈̇-left (◯'-map-pres-≈̇ ψ≈̇ψ') ◯'-strength) (⟨,⟩'-pres-≈̇-right _ φ≈̇φ')

    letin'-pres-≈̇-left : ∀ {P Q R : Obj} {φ φ' : P →̇ ◯' Q} (φ≈̇φ' : φ ≈̇ φ') (ψ : (P ×' Q) →̇ R) → letin' φ ψ ≈̇ letin' φ' ψ
    letin'-pres-≈̇-left φ≈̇φ' ψ = letin'-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

    letin'-pres-≈̇-right : ∀ {P Q R : Obj} (φ : P →̇ ◯' Q) {ψ ψ' : (P ×' Q) →̇ R} (ψ≈̇ψ' : ψ ≈̇ ψ')→ letin' φ ψ ≈̇ letin' φ ψ'
    letin'-pres-≈̇-right φ ψ≈̇ψ' = letin'-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

    letin'-nat : ∀ {P P' Q R : Obj} (φ : P →̇ ◯' Q) → (ψ : (P ×' Q) →̇ R) (ω : P' →̇ P) → letin' φ ψ ∘ ω ≈̇ letin' (φ ∘ ω) (ψ ∘ (ω ×'-map id'[ Q ]))
    letin'-nat {P} {P'} {Q} {R} φ ψ ω =  let open EqReasoning (→̇-setoid P' (◯' R)) in begin
      ((◯'-map ψ ∘ ◯'-strength[ P , Q ]) ∘ pr' id' φ) ∘ ω
        ≈⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right  _ (≈̇-trans (⟨,⟩'-nat id' φ ω) (⟨,⟩'-pres-≈̇-left (id'-unit-left P ω) _))) ⟩
      (◯'-map ψ ∘ ◯'-strength[ P , Q ]) ∘ (pr' ω (φ ∘ ω))
        ≈⟨ ∘-assoc _ _ _ ⟩
      ◯'-map ψ ∘ ◯'-strength[ P , Q ] ∘ (pr' ω (φ ∘ ω))
       ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (≈̇-sym (≈̇-trans
            (×'-map-∘-⟨,⟩' _ _ _ _)
            (⟨,⟩'-pres-≈̇ (id'-unit-right _ _) (id'-unit-left _ _))))) ⟩
      ◯'-map ψ ∘ (◯'-strength[ P , Q ] ∘ ((ω ×'-map id') ∘ pr' id' (φ ∘ ω)))
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩
      ◯'-map ψ ∘ (◯'-strength[ P , Q ] ∘ (ω ×'-map id')) ∘ pr' id' (φ ∘ ω)
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (◯'-strength-natural₁ ω) _) ⟩
      ◯'-map ψ ∘ ((◯'-map (ω ×'-map id') ∘ ◯'-strength[ P' , Q ]) ∘ pr' id' (φ ∘ ω))
        ≈⟨ ≈̇-trans (≈̇-sym (∘-assoc _ _ _)) (∘-pres-≈̇-left (≈̇-sym (∘-assoc _ _ _)) _) ⟩
      ((◯'-map ψ ∘ ◯'-map (ω ×'-map id')) ∘ ◯'-strength[ P' , Q ]) ∘ pr' id' (φ ∘ ω)
        ≈˘⟨ ∘-pres-≈̇-left (∘-pres-≈̇-left (◯'-map-pres-∘ _ _) _) _ ⟩
      (◯'-map (ψ ∘ (ω ×'-map id')) ∘ ◯'-strength[ P' , Q ]) ∘ pr' id' (φ ∘ ω) ∎

  abstract
    ◯'-strength-π₂ : {P Q : Obj} → ◯'-map π₂' ∘ ◯'-strength[ P , Q ] ≈̇ π₂'[ P ]
    ◯'-strength-π₂ {P} {Q} = let open EqReasoning (→̇-setoid (P ×' (◯' Q)) (◯' Q)) in begin
      ◯'-map π₂' ∘ ◯'-strength[ P , Q ]
        ≈˘⟨ ∘-pres-≈̇-left (◯'-map-pres-≈̇ (≈̇-trans (×'-beta-right _) (id'-unit-left _ _))) _ ⟩
      ◯'-map (π₂' ∘ (unit' ×'-map id')) ∘ ◯'-strength[ P , Q ]
        ≈⟨ ∘-pres-≈̇-left (◯'-map-pres-∘ _ _) _ ⟩
      (◯'-map π₂' ∘ ◯'-map (unit' ×'-map id')) ∘ ◯'-strength[ P , Q ]
        ≈⟨ ∘-assoc _ _ _ ⟩
      ◯'-map π₂' ∘ ◯'-map (unit' ×'-map id') ∘ ◯'-strength[ P , Q ]
        ≈˘⟨ ∘-pres-≈̇-right _ (◯'-strength-natural₁ unit') ⟩
      ◯'-map π₂' ∘ ◯'-strength[ []' , Q ] ∘ (unit' ×'-map id')
        ≈˘⟨ ∘-assoc _ _ _ ⟩
      (◯'-map π₂' ∘ ◯'-strength[ []' , Q ]) ∘ unit' ×'-map id'
        ≈⟨ ∘-pres-≈̇-left ◯'-strength-unit _ ⟩
      π₂' ∘ (unit' ×'-map id')
        ≈⟨ ≈̇-trans (×'-beta-right _) (id'-unit-left _ _) ⟩
      π₂' ∎

    ◯'-eta : {P Q : Obj} (φ : P →̇ ◯' Q) → φ ≈̇ letin' φ π₂'
    ◯'-eta {P} {Q} φ = ≈̇-sym (≈̇-trans (∘-pres-≈̇-left ◯'-strength-π₂ (pr' id' φ)) (×'-beta-right id'[ P ]))

    ◯'-beta : ∀ {P Q R R' : Obj} (φ : P →̇ ◯' Q) (ψ : (P ×' Q) →̇ R) (ψ' : (P ×' R →̇ R')) → letin' (letin' φ ψ) ψ' ≈̇ letin' φ (ψ' ∘ ⟨ π₁'[ Q ] , ψ ⟩' )
    ◯'-beta {P} {Q} {R} {R'} φ ψ ψ' = let open EqReasoning (→̇-setoid _ _) in begin
      (◯'-map ψ' ∘ ◯'-strength[ P , R ]) ∘ ⟨ id' , ((◯'-map ψ) ∘ ◯'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩' ⟩'
        ≈⟨ ∘-assoc _ _ _ ⟩
      ◯'-map ψ' ∘ ◯'-strength[ P , R ] ∘ ⟨ id' , ((◯'-map ψ) ∘ ◯'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩' ⟩'
        ≈⟨ ∘-pres-≈̇-right _ step1-with-◯'-strength-natural₂ ⟩
      ◯'-map ψ' ∘ ◯'-map (id' ×'-map ψ) ∘ ◯'-strength[ P , P ×' Q ] ∘ ⟨ id' , ◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ step2-with-◯'-strength-assoc) ⟩
      ◯'-map ψ' ∘ ◯'-map (id' ×'-map ψ) ∘ ◯'-map ×'-assoc ∘ ◯'-strength[ P ×' P , Q ] ∘ ⟨ ⟨ id' , id' ⟩' , φ ⟩'
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (∘-pres-≈̇-right _ step3-with-◯'-strength-natural₁)) ⟩
      ◯'-map ψ' ∘ ◯'-map (id' ×'-map ψ) ∘ ◯'-map ×'-assoc ∘ ◯'-map (⟨ id' , id' ⟩' ×'-map id') ∘ ◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩'
        ≈˘⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (∘-assoc _ _ _)))) ⟩
      (◯'-map ψ' ∘ ◯'-map (id' ×'-map ψ) ∘ ◯'-map ×'-assoc ∘ ◯'-map (⟨ id' , id' ⟩' ×'-map id')) ∘ ◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩'
        ≈⟨ ∘-pres-≈̇-left step4-with-◯'-map-pres-∘ _ ⟩
      ◯'-map (ψ' ∘ ⟨ π₁' , ψ ⟩') ∘ (◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩')
          ≈˘⟨ ∘-assoc _ _ _ ⟩
      (◯'-map (ψ' ∘ ⟨ π₁' , ψ ⟩') ∘ ◯'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩' ∎
      where
      step1-with-◯'-strength-natural₂ : ◯'-strength[ P , R ] ∘ ⟨ id' , (◯'-map ψ ∘ ◯'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩' ⟩'
            ≈̇ ◯'-map (id' ×'-map ψ) ∘ ◯'-strength[ P , P ×' Q ] ∘ ⟨ id' , ◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
      step1-with-◯'-strength-natural₂ = let open EqReasoning (→̇-setoid _ _) in begin
        ◯'-strength[ P , R ] ∘ ⟨ id' , (◯'-map ψ ∘ ◯'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩' ⟩'
          ≈⟨ ∘-pres-≈̇-right _ (⟨,⟩'-pres-≈̇-right _ (∘-assoc _ _ _)) ⟩
        ◯'-strength[ P , R ] ∘ ⟨ id' , (◯'-map ψ) ∘ ◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
          ≈˘⟨ ∘-pres-≈̇-right _ (≈̇-trans (×'-map-∘-⟨,⟩' _ _ _ _) (⟨,⟩'-pres-≈̇-left (id'-unit-left _ _) _)) ⟩
        ◯'-strength[ P , R ] ∘ (id' ×'-map (◯'-map ψ)) ∘ ⟨ id' , ◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
          ≈⟨ ≈̇-trans (≈̇-sym (∘-assoc _ _ _)) (≈̇-trans (∘-pres-≈̇-left (◯'-strength-natural₂ ψ) _) (∘-assoc _ _ _)) ⟩
        _ ∎

      step2-with-◯'-strength-assoc : ◯'-strength[ P , P ×' Q ] ∘ ⟨ id' , ◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
            ≈̇ ◯'-map ×'-assoc ∘ ◯'-strength[ P ×' P , Q ] ∘ ⟨ ⟨ id' , id' ⟩' , φ ⟩'
      step2-with-◯'-strength-assoc = let open EqReasoning (→̇-setoid _ _) in begin
        ◯'-strength[ P , P ×' Q ] ∘ ⟨ id' , ◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
          ≈˘⟨ ∘-pres-≈̇-right _ (⟨,⟩'-pres-≈̇-left (id'-unit-left P id') _) ⟩
        ◯'-strength[ P , P ×' Q ] ∘ ⟨ id' ∘ id' , ◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩' ⟩'
          ≈˘⟨ ∘-pres-≈̇-right _ (×'-map-∘-⟨,⟩' _ _ _ _) ⟩
        ◯'-strength[ P , P ×' Q ] ∘ (id' ×'-map ◯'-strength[ P , Q ] ∘ ⟨ id' , ⟨ id' , φ ⟩' ⟩')
          ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (×'-assoc-∘-⟨⟨,⟩',⟩' _ _ _)) ⟩
        ◯'-strength[ P , P ×' Q ] ∘ (id' ×'-map ◯'-strength[ P , Q ] ∘ ×'-assoc ∘ ⟨ ⟨ id' , id' ⟩'  , φ ⟩')
          ≈˘⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (∘-assoc _ _ _)) ⟩
        (◯'-strength[ P , P ×' Q ] ∘ id' ×'-map ◯'-strength[ P , Q ] ∘ ×'-assoc) ∘ ⟨ ⟨ id' , id' ⟩'  , φ ⟩'
          ≈˘⟨ ∘-pres-≈̇-left ◯'-strength-assoc _ ⟩
        (◯'-map ×'-assoc ∘ ◯'-strength[ P ×' P , Q ]) ∘ ⟨ ⟨ id' , id' ⟩'  , φ ⟩'
          ≈⟨ ∘-assoc _ _ _ ⟩
        _ ∎

      step3-with-◯'-strength-natural₁ : ◯'-strength[ P ×' P , Q ] ∘ ⟨ ⟨ id' , id' ⟩' , φ ⟩'
            ≈̇ ◯'-map (⟨ id' , id' ⟩' ×'-map id') ∘ ◯'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩'
      step3-with-◯'-strength-natural₁ = let open EqReasoning (→̇-setoid _ _) in begin
        ◯'-strength[ P ×' P , Q ] ∘ ⟨ ⟨ id' , id' ⟩' , φ ⟩'
          ≈˘⟨ ∘-pres-≈̇-right _ (≈̇-trans (×'-map-∘-⟨,⟩' _ _ _ _) (⟨,⟩'-pres-≈̇ (id'-unit-right _ _) (id'-unit-left _ _))) ⟩
        ◯'-strength[ P ×' P , Q ] ∘ (⟨ id' , id' ⟩' ×'-map id'[ ◯' Q ]) ∘ ⟨ id' , φ ⟩'
          ≈˘⟨ ∘-assoc _ _ _ ⟩
        (◯'-strength[ P ×' P , Q ] ∘ (⟨ id' , id' ⟩' ×'-map id'[ ◯' Q ])) ∘ ⟨ id' , φ ⟩'
          ≈⟨ ∘-pres-≈̇-left (◯'-strength-natural₁ ⟨ id' , id' ⟩') _ ⟩
        (◯'-map (⟨ id' , id' ⟩' ×'-map id') ∘ ◯'-strength[ P , Q ]) ∘ ⟨ id' , φ ⟩'
          ≈⟨ ∘-assoc _ _ _ ⟩
        _ ∎

      step4-with-◯'-map-pres-∘ : ◯'-map ψ' ∘ ◯'-map (id' ×'-map ψ) ∘ ◯'-map ×'-assoc ∘ ◯'-map (⟨ id' , id' ⟩' ×'-map id')
            ≈̇ ◯'-map (ψ' ∘ ⟨ π₁' , ψ ⟩')
      step4-with-◯'-map-pres-∘ = let open EqReasoning (→̇-setoid _ _) in begin
        ◯'-map ψ' ∘ ◯'-map (id' ×'-map ψ) ∘ ◯'-map ×'-assoc ∘ ◯'-map (⟨ id' , id' ⟩' ×'-map id')
            ≈˘⟨ ∘-pres-≈̇-right _ (≈̇-trans (◯'-map-pres-∘ _ _) (∘-pres-≈̇-right _ (◯'-map-pres-∘ _ _))) ⟩
        ◯'-map ψ' ∘ ◯'-map (id' ×'-map ψ ∘ (×'-assoc ∘ ⟨ id' , id' ⟩' ×'-map id'))
           ≈⟨ ∘-pres-≈̇-right _ (◯'-map-pres-≈̇ (∘-pres-≈̇-right _ step4a)) ⟩
        ◯'-map ψ' ∘ ◯'-map (id' ×'-map ψ ∘ ⟨ π₁' , id' ⟩'  )
            ≈⟨ ∘-pres-≈̇-right _ (◯'-map-pres-≈̇ (×'-map-∘-⟨,⟩' _ _ _ _)) ⟩
        ◯'-map ψ' ∘ ◯'-map ⟨ id' ∘ π₁' , ψ ∘ id' ⟩'
            ≈⟨ ∘-pres-≈̇-right _ (◯'-map-pres-≈̇ (⟨,⟩'-pres-≈̇ (id'-unit-left _ _) (id'-unit-right _ _))) ⟩
        ◯'-map ψ' ∘ ◯'-map ⟨ π₁' , ψ ⟩'
            ≈˘⟨ ◯'-map-pres-∘ _ _ ⟩
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


  module _ (isCartesianClosed : IsCartesianClosed C isCartesian) where

    open IsCartesianClosed isCartesianClosed

    fmap : {P Q R : Obj} (φ : P →̇ (Q ⇒' R)) (ψ : P →̇ ◯' Q) → (P →̇ ◯' R)
    fmap {P} {Q} {R} φ ψ = letin' ψ (app' (φ [ π₁' ]') π₂')
