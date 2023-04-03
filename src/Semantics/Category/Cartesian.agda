{-# OPTIONS --safe --without-K #-}
module Semantics.Category.Cartesian where

open import Semantics.Category.Base

open import Relation.Binary using (IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

record IsCartesian (C : Category) : Set₂ where
  open Category C

  -- terminal object
  field
    []'     : Obj
    unit'   : {P : Obj} → P →̇ []'
    []'-eta : ∀ {P : Obj} {φ : P →̇ []'} → φ ≈̇ unit'

  -- products
  field
    _×'_    : (P Q : Obj) → Obj
    ⟨_,_⟩'        : {R P Q : Obj} → (φ : R →̇ P) → (ψ : R →̇ Q) → R →̇ P ×' Q
    ⟨,⟩'-pres-≈̇   : ∀ {R P Q : Obj} {φ φ' : R →̇ P} {ψ ψ' : R →̇ Q} (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ' , ψ' ⟩'
    π₁'[_]        : {P : Obj} → (Q : Obj) → P ×' Q →̇ P
    π₂'[_]        : (P : Obj) → {Q : Obj} → P ×' Q →̇ Q

  pr'        = ⟨_,_⟩'

  π₁' : {P Q : Obj} → P ×' Q →̇ P
  π₁' = π₁'[ _ ]

  π₂' : {P Q : Obj} → P ×' Q →̇ Q
  π₂' = π₂'[ _ ]

  fst'[_]_ : {R P : Obj} (Q : Obj) (φ : R →̇ (P ×' Q)) → R →̇ P
  fst'[_]_ {R} {P} Q = π₁'[ Q ] ∘_

  snd'[_]_ : {R : Obj} (P : Obj) {Q : Obj} (φ : R →̇ (P ×' Q)) → R →̇ Q
  snd'[_]_ {R} P {Q} = π₂'[ P ] ∘_

  fst' : {R P Q : Obj} (φ : R →̇ (P ×' Q)) → R →̇ P
  fst' {R} {P} {Q} = fst'[ Q ]_

  snd' : {R P Q : Obj} (φ : R →̇ (P ×' Q)) → R →̇ Q
  snd' {R} {P} {Q} = snd'[ P ]_

  _×'-map_ : {P P' Q Q' : Obj} (t : P →̇ P') → (u : Q →̇ Q') → P ×' Q →̇ P' ×' Q'
  _×'-map_ {P} {P'} {Q} {Q'} φ ψ = ⟨ φ ∘ π₁'[ Q ] , ψ ∘ π₂'[ P ] ⟩'

  ×'-assoc[_,_,_] : (P Q R : Obj) → (P ×' Q) ×' R →̇ P ×' (Q ×' R)
  ×'-assoc[ _ , _ , _ ] = ⟨ π₁' ∘ π₁' , ⟨ π₂' ∘ π₁' , π₂' ⟩' ⟩'

  ×'-assoc : {P Q R : Obj} → (P ×' Q) ×' R →̇ P ×' (Q ×' R)
  ×'-assoc = ×'-assoc[ _ , _ , _ ]

  field
    ×'-beta-left  : ∀ {R P Q : Obj} {φ : R →̇ P} (ψ : R →̇ Q) → π₁'[ Q ] ∘ ⟨ φ , ψ ⟩' ≈̇ φ
    ×'-beta-right : ∀ {R P Q : Obj} (φ : R →̇ P) {ψ : R →̇ Q} → π₂'[ P ] ∘ ⟨ φ , ψ ⟩' ≈̇ ψ
    ×'-eta        : ∀ {R P Q : Obj} {φ : R →̇ P ×' Q} → φ ≈̇ ⟨ π₁'[ Q ] ∘ φ , π₂'[ P ] ∘ φ ⟩'

  private
    variable
      P Q R P' Q' R' : Obj
      φ φ' : P →̇ Q
      ψ ψ' : P →̇ Q
      ω ω' : P →̇ Q

  abstract
    ⟨,⟩'-pres-≈̇-left : {φ φ' : R →̇ P} (φ≈̇φ' : φ ≈̇ φ') (ψ : R →̇ Q) → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ' , ψ ⟩'
    ⟨,⟩'-pres-≈̇-left ψ≈̇ψ' φ = ⟨,⟩'-pres-≈̇ ψ≈̇ψ' (≈̇-refl {φ = φ})

    ⟨,⟩'-pres-≈̇-right : (φ : R →̇ P) {ψ ψ' : R →̇ Q} (ψ≈̇ψ' : ψ ≈̇ ψ') → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ , ψ' ⟩'
    ⟨,⟩'-pres-≈̇-right ψ φ≈̇φ' = ⟨,⟩'-pres-≈̇ (≈̇-refl {φ = ψ}) φ≈̇φ'

    ⟨,⟩'-nat : (φ : R →̇ P) (ψ : R →̇ Q) (ω : R' →̇ R) → ⟨ φ , ψ ⟩' ∘ ω ≈̇ ⟨ φ ∘ ω , ψ ∘ ω ⟩'
    ⟨,⟩'-nat φ ψ ω = let open EqReasoning (→̇-setoid _ _) in begin
      ⟨ φ , ψ ⟩' ∘ ω
        ≈⟨ ×'-eta ⟩
      ⟨ π₁' ∘ ⟨ φ , ψ ⟩' ∘ ω , π₂' ∘ ⟨ φ , ψ ⟩' ∘ ω ⟩'
        ≈⟨ ⟨,⟩'-pres-≈̇ (≈̇-sym (∘-assoc _ _ _)) (≈̇-sym (∘-assoc _ _ _)) ⟩
      ⟨ (π₁' ∘ ⟨ φ , ψ ⟩') ∘ ω , (π₂' ∘ ⟨ φ , ψ ⟩') ∘ ω ⟩'
        ≈⟨ ⟨,⟩'-pres-≈̇ (∘-pres-≈̇-left (×'-beta-left _) _) (∘-pres-≈̇-left (×'-beta-right _) _) ⟩
      ⟨ φ ∘ ω , ψ ∘ ω ⟩' ∎

    ×'-map-pres-≈̇ : {φ φ' : P →̇ P'} (φ≈̇φ' : φ ≈̇ φ') {ψ ψ' : Q →̇ Q'} (ψ≈̇ψ' : ψ ≈̇ ψ') → φ ×'-map ψ ≈̇ φ' ×'-map ψ'
    ×'-map-pres-≈̇ {φ = φ} {φ'} φ≈̇φ' {ψ} {ψ'} ψ≈̇ψ' = let open EqReasoning (→̇-setoid _ _) in begin
      φ ×'-map ψ                ≡⟨⟩
      ⟨ φ  ∘ π₁' , ψ  ∘ π₂' ⟩'  ≈⟨ ⟨,⟩'-pres-≈̇ (∘-pres-≈̇-left φ≈̇φ' π₁') (∘-pres-≈̇-left ψ≈̇ψ' π₂') ⟩
      ⟨ φ' ∘ π₁' , ψ' ∘ π₂' ⟩'  ∎

    ×'-map-pres-≈̇-left : {φ φ' : P →̇ P'} (φ≈̇φ' : φ ≈̇ φ') (ψ : Q →̇ Q) → φ ×'-map ψ ≈̇ φ' ×'-map ψ
    ×'-map-pres-≈̇-left = λ φ≈̇φ' ψ → ×'-map-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

    ×'-map-pres-≈̇-right : (φ : P →̇ P) {ψ ψ' : Q →̇ Q'} (ψ≈̇ψ' : ψ ≈̇ ψ') → φ ×'-map ψ ≈̇ φ ×'-map ψ'
    ×'-map-pres-≈̇-right = λ φ ψ≈̇ψ' → ×'-map-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

    ×'-map-pres-id' : {P Q : Obj} → id'[ P ] ×'-map id'[ Q ] ≈̇ id'[ P ×' Q ]
    ×'-map-pres-id' {P} {Q} = let open EqReasoning (→̇-setoid _ _) in begin
      id' ×'-map id'              ≡⟨⟩
      ⟨ id' ∘ π₁' , id' ∘ π₂' ⟩'  ≈⟨ ⟨,⟩'-pres-≈̇ (id'-unit-left P π₁') (id'-unit-left Q π₂') ⟩
      ⟨ π₁'       , π₂'       ⟩'  ≈˘⟨ ⟨,⟩'-pres-≈̇ (id'-unit-right (P ×' Q) π₁') (id'-unit-right (P ×' Q) π₂') ⟩
      ⟨ π₁' ∘ id' , π₂' ∘ id' ⟩'  ≈˘⟨ ×'-eta ⟩
      id'                         ∎

    ×'-map-∘-⟨,⟩' : (φ : Q →̇ Q') (ψ : R →̇  R') (ω : P →̇ Q) (ω' : P →̇ R) → φ ×'-map ψ ∘ ⟨ ω , ω' ⟩' ≈̇ ⟨ φ ∘ ω , ψ ∘ ω' ⟩'
    ×'-map-∘-⟨,⟩' φ ψ ω ω' = let open EqReasoning (→̇-setoid _ _) in begin
      φ ×'-map ψ ∘ ⟨ ω , ω' ⟩'
        ≈⟨ ⟨,⟩'-nat _ _ _  ⟩
      ⟨ (φ ∘ π₁') ∘ ⟨ ω , ω' ⟩' , (ψ ∘ π₂') ∘ ⟨ ω , ω' ⟩' ⟩'
        ≈⟨ ⟨,⟩'-pres-≈̇ (∘-assoc _ _ _) (∘-assoc _ _ _) ⟩
      ⟨ φ ∘ π₁' ∘ ⟨ ω , ω' ⟩' , ψ ∘ π₂' ∘ ⟨ ω , ω' ⟩' ⟩'
        ≈⟨ ⟨,⟩'-pres-≈̇ (∘-pres-≈̇-right _ (×'-beta-left _)) (∘-pres-≈̇-right _ (×'-beta-right _)) ⟩
      ⟨ φ ∘ ω , ψ ∘ ω' ⟩' ∎

    ×'-assoc-∘-⟨⟨,⟩',⟩' : {P' P Q R : Obj} → (φ : P' →̇ P) (ψ : P' →̇ Q) (ω : P' →̇ R)
      → ×'-assoc ∘ ⟨ ⟨ φ , ψ ⟩' , ω ⟩' ≈̇ ⟨ φ , ⟨ ψ , ω ⟩' ⟩'
    ×'-assoc-∘-⟨⟨,⟩',⟩' φ ψ ω = let open EqReasoning (→̇-setoid _ _) in begin
      ⟨ π₁' ∘ π₁' , ⟨ π₂' ∘ π₁' , π₂' ⟩' ⟩' ∘ ⟨ ⟨ φ , ψ ⟩' , ω ⟩'
        ≈⟨ ⟨,⟩'-nat _ _ _ ⟩
      ⟨ (π₁' ∘ π₁') ∘ ⟨ ⟨ φ , ψ ⟩' , ω ⟩' ,  ⟨ π₂' ∘ π₁' , π₂' ⟩' ∘  ⟨ ⟨ φ , ψ ⟩' , ω ⟩' ⟩'
        ≈⟨ ⟨,⟩'-pres-≈̇-right _ (⟨,⟩'-nat _ _ _) ⟩
      ⟨ (π₁' ∘ π₁') ∘ ⟨ ⟨ φ , ψ ⟩' , ω ⟩' , ⟨ (π₂' ∘ π₁') ∘ ⟨ ⟨ φ , ψ ⟩' , ω ⟩' , π₂' ∘ ⟨ ⟨ φ , ψ ⟩' , ω ⟩' ⟩' ⟩'
        ≈⟨ ⟨,⟩'-pres-≈̇ (∘-assoc _ _ _) (⟨,⟩'-pres-≈̇-left (∘-assoc _ _ _) _) ⟩
      ⟨ π₁' ∘ π₁' ∘ ⟨ ⟨ φ , ψ ⟩' , ω ⟩' , ⟨ π₂' ∘ π₁' ∘ ⟨ ⟨ φ , ψ ⟩' , ω ⟩' , π₂' ∘ ⟨ ⟨ φ , ψ ⟩' , ω ⟩' ⟩' ⟩'
        ≈⟨ ⟨,⟩'-pres-≈̇ (∘-pres-≈̇-right _ (×'-beta-left _)) (⟨,⟩'-pres-≈̇ (∘-pres-≈̇-right _ (×'-beta-left _)) (×'-beta-right _)) ⟩
      ⟨ π₁' ∘ ⟨ φ , ψ ⟩' , ⟨ π₂' ∘ ⟨ φ , ψ ⟩' , ω ⟩' ⟩'
        ≈⟨ ⟨,⟩'-pres-≈̇ (×'-beta-left _) (⟨,⟩'-pres-≈̇-left (×'-beta-right _) _) ⟩
      ⟨ φ , ⟨ ψ , ω ⟩' ⟩' ∎
