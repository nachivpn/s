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

  field
    ◯'_     : (P : Obj) → Obj
    ◯'-map_ : {P Q : Obj} (φ : P →̇ Q) → (◯' P →̇ ◯' Q)
    ◯'-map-pres-≈̇  : {P Q : Obj} {φ φ' : P →̇ Q} → φ ≈̇ φ' → ◯'-map φ ≈̇ ◯'-map φ'
    ◯'-map-pres-id : {P : Obj} → ◯'-map id'[ P ] ≈̇ id'
    ◯'-map-pres-∘  : {P Q R : Obj} → (ψ : Q →̇ R) (φ : P →̇ Q) → ◯'-map (ψ ∘ φ) ≈̇ ◯'-map ψ ∘ ◯'-map φ

  field
    ◯'-strength : (P Q : Obj) → P ×' (◯' Q) →̇ ◯' (P ×' Q)
    ◯'-strength-natural₁ : {P P' Q : Obj} (φ : P →̇ P') → ◯'-strength P' Q ∘ (φ ×'-map id'[ ◯' Q ]) ≈̇ (◯'-map (φ ×'-map id'[ Q ])) ∘ ◯'-strength P Q
    ◯'-strength-natural₂ : {P Q Q' : Obj} (t : Q →̇ Q') → ◯'-strength P Q' ∘ (id'[ P ] ×'-map (◯'-map t)) ≈̇ (◯'-map (id'[ P ] ×'-map t)) ∘ ◯'-strength P Q
    ◯'-strength-assoc    : {P Q R : Obj} → ◯'-map assoc' ∘ ◯'-strength (P ×' Q) R ≈̇ (◯'-strength P (Q ×' R) ∘ (id'[ P ] ×'-map (◯'-strength Q R)) ∘ assoc')
    ◯'-strength-unit     : {P : Obj} → ◯'-map π₂' ∘ ◯'-strength []' P ≈̇ π₂'

  abstract
    ◯'-strength-π₂ : {P Q : Obj} → ◯'-map π₂' ∘ ◯'-strength P Q ≈̇ π₂'[ P ]
    ◯'-strength-π₂ {P} {Q} = let open EqReasoning (→̇-setoid (P ×' (◯' Q)) (◯' Q)) in begin
      ◯'-map π₂' ∘ ◯'-strength P Q
        ≈⟨ ∘-pres-≈̇-left (≈̇-sym (◯'-map-pres-≈̇ ((≈̇-trans (×'-beta-right (unit' ∘ π₁')) (id'-unit-left Q π₂'))))) (◯'-strength P Q)⟩
      ◯'-map (π₂' ∘ (unit' ×'-map id')) ∘ ◯'-strength P Q
        ≈⟨ ∘-pres-≈̇-left (◯'-map-pres-∘ π₂' (unit' ×'-map id')) (◯'-strength P Q) ⟩
      (◯'-map π₂' ∘ ◯'-map (unit' ×'-map id')) ∘ ◯'-strength P Q
        ≈⟨ ∘-assoc (◯'-map π₂') ( ◯'-map (unit' ×'-map id')) (◯'-strength P Q) ⟩
      ◯'-map π₂' ∘ ◯'-map (unit' ×'-map id') ∘ ◯'-strength P Q
        ≈⟨ ∘-pres-≈̇-right (◯'-map π₂') (≈̇-sym (◯'-strength-natural₁ unit')) ⟩
      ◯'-map π₂' ∘ (◯'-strength []' Q) ∘ (unit' ×'-map id')
        ≈˘⟨ ∘-assoc (◯'-map π₂') (◯'-strength []' Q) (unit' ×'-map id') ⟩
      (◯'-map π₂' ∘ ◯'-strength []' Q) ∘ unit' ×'-map id'
        ≈⟨ ∘-pres-≈̇-left ◯'-strength-unit (unit' ×'-map id') ⟩
      π₂' ∘ (unit' ×'-map id')
        ≈⟨ ≈̇-trans (×'-beta-right (unit' ∘ π₁')) (id'-unit-left (◯' Q) π₂') ⟩
      π₂' ∎

  letin' : {P Q R : Obj} (t : P →̇ ◯' Q) → (u : (P ×' Q) →̇ R) → P →̇ ◯' R
  letin' {P} {Q} t u = (◯'-map u ∘ ◯'-strength P Q) ∘ pr' id' t

  abstract

    letin'-pres-≈̇ : ∀ {P Q R : Obj} {φ φ' : P →̇ ◯' Q} {ψ ψ' : (P ×' Q) →̇ R} → (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → letin' φ ψ ≈̇ letin' φ' ψ'
    letin'-pres-≈̇  {P} {Q} φ≈̇φ' ψ≈̇ψ' = ∘-pres-≈̇ (∘-pres-≈̇-left (◯'-map-pres-≈̇ ψ≈̇ψ') (◯'-strength P Q)) (pr'-pres-≈̇-right _ φ≈̇φ')

    letin'-pres-≈̇-left : ∀ {P Q R : Obj} {φ φ' : P →̇ ◯' Q} (φ≈̇φ' : φ ≈̇ φ') (ψ : (P ×' Q) →̇ R) → letin' φ ψ ≈̇ letin' φ' ψ
    letin'-pres-≈̇-left φ≈̇φ' ψ = letin'-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

    letin'-pres-≈̇-right : ∀ {P Q R : Obj} (φ : P →̇ ◯' Q) {ψ ψ' : (P ×' Q) →̇ R} (ψ≈̇ψ' : ψ ≈̇ ψ')→ letin' φ ψ ≈̇ letin' φ ψ'
    letin'-pres-≈̇-right φ ψ≈̇ψ' = letin'-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

    letin'-nat : ∀ {P P' Q R : Obj} (φ : P →̇ ◯' Q) → (ψ : (P ×' Q) →̇ R) (ω : P' →̇ P) → letin' φ ψ ∘ ω ≈̇ letin' (φ ∘ ω) (ψ ∘ (ω ×'-map id'[ Q ]))
    letin'-nat {P} {P'} {Q} {R} φ ψ ω =  let open EqReasoning (→̇-setoid P' (◯' R)) in begin
      ((◯'-map ψ ∘ ◯'-strength P Q) ∘ pr' id' φ) ∘ ω
        ≈⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right  _ (≈̇-trans (pr'-nat id' φ ω) (pr'-pres-≈̇-left (id'-unit-left P ω) _))) ⟩
      (◯'-map ψ ∘ ◯'-strength P Q) ∘ (pr' ω (φ ∘ ω))
        ≈⟨ ∘-assoc _ _ _ ⟩
      ◯'-map ψ ∘ (◯'-strength P Q) ∘ (pr' ω (φ ∘ ω))
       ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (≈̇-sym (≈̇-trans
            (×'-map-∘-⟨,⟩' _ _ _ _)
            (pr'-pres-≈̇ (id'-unit-right _ _) (id'-unit-left _ _))))) ⟩
      ◯'-map ψ ∘ (◯'-strength P Q ∘ ((ω ×'-map id') ∘ pr' id' (φ ∘ ω)))
        ≈⟨ ∘-pres-≈̇-right _ (≈̇-sym (∘-assoc _ _ _)) ⟩
      ◯'-map ψ ∘ (◯'-strength P Q ∘ (ω ×'-map id')) ∘ pr' id' (φ ∘ ω)
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (◯'-strength-natural₁ ω) _) ⟩
      ◯'-map ψ ∘ ((◯'-map (ω ×'-map id') ∘ ◯'-strength P' Q) ∘ pr' id' (φ ∘ ω))
        ≈⟨ ≈̇-trans (≈̇-sym (∘-assoc _ _ _)) (∘-pres-≈̇-left (≈̇-sym (∘-assoc _ _ _)) _) ⟩
      ((◯'-map ψ ∘ ◯'-map (ω ×'-map id')) ∘ ◯'-strength P' Q) ∘ pr' id' (φ ∘ ω)
        ≈⟨ ∘-pres-≈̇-left (∘-pres-≈̇-left (≈̇-sym (◯'-map-pres-∘ _ _)) _) _ ⟩
      (◯'-map (ψ ∘ (ω ×'-map id')) ∘ ◯'-strength P' Q) ∘ pr' id' (φ ∘ ω) ∎

    ◯'-eta : {P Q : Obj} (φ : P →̇ ◯' Q) → φ ≈̇ letin' φ π₂'
    ◯'-eta {P} {Q} φ = ≈̇-sym (≈̇-trans (∘-pres-≈̇-left ◯'-strength-π₂ (pr' id' φ)) (×'-beta-right id'[ P ]))

  postulate
    ◯'-beta : ∀ {P Q R R' : Obj} (t : P →̇ ◯' Q) (u : (P ×' Q) →̇ R) (u' : (P ×' R →̇ R')) → letin' (letin' t u) u' ≈̇ letin' t (u' ∘ ⟨ π₁'[ Q ] , u ⟩' )
