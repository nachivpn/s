{-# OPTIONS --safe --without-K #-}
module Semantics.Category.Cartesian where

open import Semantics.Category.Base

open import Relation.Binary using (IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

record IsCartesian (C : Category) : Set₂ where
  open Category C
  field
    []'     : Obj
    unit'   : {P : Obj} → P →̇ []'
    []'-eta : ∀ {P : Obj} {φ : P →̇ []'} → φ ≈̇ unit'
    _×'_    : (P Q : Obj) → Obj
    ⟨_,_⟩'        : {R P Q : Obj} → (φ : R →̇ P) → (ψ : R →̇ Q) → R →̇ P ×' Q
    ⟨,⟩'-pres-≈̇   : ∀ {R P Q : Obj} {φ φ' : R →̇ P} {ψ ψ' : R →̇ Q} (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ' , ψ' ⟩'
    π₁'[_]        : {P : Obj} → (Q : Obj) → P ×' Q →̇ P
    π₂'[_]        : (P : Obj) → {Q : Obj} → P ×' Q →̇ Q

  pr'        = ⟨_,_⟩'
  pr'-pres-≈̇ = ⟨,⟩'-pres-≈̇

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

  field
    ×'-beta-left  : ∀ {R P Q : Obj} {φ : R →̇ P} (ψ : R →̇ Q) → π₁'[ Q ] ∘ ⟨ φ , ψ ⟩' ≈̇ φ
    ×'-beta-right : ∀ {R P Q : Obj} (φ : R →̇ P) {ψ : R →̇ Q} → π₂'[ P ] ∘ ⟨ φ , ψ ⟩' ≈̇ ψ
    ×'-eta        : ∀ {R P Q : Obj} {φ : R →̇ P ×' Q} → φ ≈̇ ⟨ π₁'[ Q ] ∘ φ , π₂'[ P ] ∘ φ ⟩'
    ⟨,⟩'-nat       : ∀ {R' R P Q : Obj} (φ : R →̇ P) (ψ : R →̇ Q) (ω : R' →̇ R) → ⟨ φ , ψ ⟩' ∘ ω ≈̇ ⟨ φ ∘ ω , ψ ∘ ω ⟩'

  pr'-nat = ⟨,⟩'-nat

  assoc' : ∀ {P Q R : Obj} → (P ×' Q) ×' R →̇ P ×' (Q ×' R)
  assoc' = ⟨ π₁' ∘ π₁' , ⟨ π₂' ∘ π₁' , π₂' ⟩' ⟩'

  private
    variable
      P Q R P' Q' R' : Obj
      φ φ' : P →̇ Q
      ψ ψ' : P →̇ Q
      ω ω' : P →̇ Q

  abstract
    ⟨,⟩'-pres-≈̇-left : ∀ {R P Q : Obj} {φ φ' : R →̇ P} (φ≈̇φ' : φ ≈̇ φ') (ψ : R →̇ Q) → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ' , ψ ⟩'
    ⟨,⟩'-pres-≈̇-left ψ≈̇ψ' φ = ⟨,⟩'-pres-≈̇ ψ≈̇ψ' (≈̇-refl {φ = φ})

    ⟨,⟩'-pres-≈̇-right : ∀ {R P Q : Obj} (φ : R →̇ P) {ψ ψ' : R →̇ Q} (ψ≈̇ψ' : ψ ≈̇ ψ') → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ , ψ' ⟩'
    ⟨,⟩'-pres-≈̇-right ψ φ≈̇φ' = ⟨,⟩'-pres-≈̇ (≈̇-refl {φ = ψ}) φ≈̇φ'

  pr'-pres-≈̇-left  = ⟨,⟩'-pres-≈̇-left
  pr'-pres-≈̇-right = ⟨,⟩'-pres-≈̇-right

  abstract
    ×'-map-pres-≈̇ : {P Q P' Q' : Obj} {φ φ' : P →̇ P'} (φ≈̇φ' : φ ≈̇ φ') {ψ ψ' : Q →̇ Q'} (ψ≈̇ψ' : ψ ≈̇ ψ') → φ ×'-map ψ ≈̇ φ' ×'-map ψ'
    ×'-map-pres-≈̇ {φ = φ} {φ'} φ≈̇φ' {ψ} {ψ'} ψ≈̇ψ' = let open EqReasoning (→̇-setoid _ _) in begin
      φ ×'-map ψ                ≡⟨⟩
      ⟨ φ  ∘ π₁' , ψ  ∘ π₂' ⟩'  ≈⟨ ⟨,⟩'-pres-≈̇ (∘-pres-≈̇-left φ≈̇φ' π₁') (∘-pres-≈̇-left ψ≈̇ψ' π₂') ⟩
      ⟨ φ' ∘ π₁' , ψ' ∘ π₂' ⟩'  ∎

    ×'-map-pres-≈̇-left : {P Q P' : Obj} {φ φ' : P →̇ P'} (φ≈̇φ' : φ ≈̇ φ') (ψ : Q →̇ Q) → φ ×'-map ψ ≈̇ φ' ×'-map ψ
    ×'-map-pres-≈̇-left = λ φ≈̇φ' ψ → ×'-map-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

    ×'-map-pres-≈̇-right : {P Q Q' : Obj} (φ : P →̇ P) {ψ ψ' : Q →̇ Q'} (ψ≈̇ψ' : ψ ≈̇ ψ') → φ ×'-map ψ ≈̇ φ ×'-map ψ'
    ×'-map-pres-≈̇-right = λ φ ψ≈̇ψ' → ×'-map-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

    ×'-map-pres-id' : {P Q : Obj} → id'[ P ] ×'-map id'[ Q ] ≈̇ id'[ P ×' Q ]
    ×'-map-pres-id' {P} {Q} = let open EqReasoning (→̇-setoid _ _) in begin
      id' ×'-map id'              ≡⟨⟩
      ⟨ id' ∘ π₁' , id' ∘ π₂' ⟩'  ≈⟨ ⟨,⟩'-pres-≈̇ (id'-unit-left P π₁') (id'-unit-left Q π₂') ⟩
      ⟨ π₁'       , π₂'       ⟩'  ≈˘⟨ ⟨,⟩'-pres-≈̇ (id'-unit-right (P ×' Q) π₁') (id'-unit-right (P ×' Q) π₂') ⟩
      ⟨ π₁' ∘ id' , π₂' ∘ id' ⟩'  ≈˘⟨ ×'-eta ⟩
      id'                         ∎


    ×'-map-∘-⟨,⟩' : (φ : Q →̇ Q') (ψ : R →̇  R') (ω : P →̇ Q) (ω' : P →̇ R) → φ ×'-map ψ ∘ ⟨ ω , ω' ⟩' ≈̇ ⟨ φ ∘ ω , ψ ∘ ω' ⟩'
    ×'-map-∘-⟨,⟩' _ _ _ _ = ≈̇-trans (⟨,⟩'-nat _ _ _)
      (⟨,⟩'-pres-≈̇
        (≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (×'-beta-left _)))
        (≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (×'-beta-right _))))
