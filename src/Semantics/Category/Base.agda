{-# OPTIONS --safe --without-K #-}
module Semantics.Category.Base where

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Level using (0ℓ ; suc)

record Categoryₗ ℓ : Set (suc ℓ) where

  infixr 19 _→̇_

  field
    Obj     : Set ℓ
    _→̇_     : (P Q : Obj) → Set
    _≈̇_     : {P Q : Obj} → (φ ψ : P →̇ Q) → Set
    _∘_     : {P Q R : Obj} → (ψ : Q →̇ R) → (φ : P →̇ Q) → (P →̇ R)
    id'[_]  : (P : Obj) → P →̇ P

  infix 18 _≈̇_
  infixr 19 _∘_

  field
    ≈̇-refl   : ∀ {P Q : Obj} {φ : P →̇ Q} → φ ≈̇ φ
    ≈̇-sym    : ∀ {P Q : Obj} {φ ψ : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → ψ ≈̇ φ
    ≈̇-trans  : ∀ {P Q : Obj} {φ ψ ω : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → (ψ≈̇ω : ψ ≈̇ ω) → φ ≈̇ ω
    ∘-pres-≈̇ : ∀ {P Q R : Obj} {ψ ψ' : Q →̇ R} {φ φ' : P →̇ Q} (ψ≈̇ψ' : ψ ≈̇ ψ') (φ≈̇φ' : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ' ∘ φ'

  field
    ∘-unit-left  : ∀ {P : Obj} (Q : Obj) (φ : P →̇ Q) → id'[ Q ] ∘ φ ≈̇ φ
    ∘-unit-right : ∀ (P : Obj) {Q : Obj} (φ : P →̇ Q) → φ ∘ id'[ P ] ≈̇ φ
    ∘-assoc        : {P Q R S : Obj} → (ω : R →̇ S) → (ψ : Q →̇ R) → (φ : P →̇ Q) → (ω ∘ ψ) ∘ φ ≈̇ ω ∘ ψ ∘ φ

  _[_]' = _∘_

  private
    variable
      P Q R : Obj
      φ φ' : P →̇ Q
      ψ ψ' : P →̇ Q
      ω ω' : P →̇ Q

  id' : P →̇ P
  id' = id'[ _ ]

  ≈̇-equiv : IsEquivalence {A = P →̇ Q} _≈̇_
  ≈̇-equiv = record
    { refl  = ≈̇-refl
    ; sym   = ≈̇-sym
    ; trans = ≈̇-trans
    }

  →̇-setoid : (P Q : Obj) → Setoid 0ℓ 0ℓ
  →̇-setoid P Q = record
    { Carrier       = P →̇ Q
    ; _≈_           = _≈̇_
    ; isEquivalence = ≈̇-equiv
    }

  abstract
    ∘-pres-≈̇-left : ∀ (_ : ψ ≈̇ ψ') (φ : P →̇ Q) → ψ ∘ φ ≈̇ ψ' ∘ φ
    ∘-pres-≈̇-left ψ≈̇ψ' φ = ∘-pres-≈̇ ψ≈̇ψ' (≈̇-refl {φ = φ})

    ∘-pres-≈̇-right : ∀ (ψ : Q →̇ R) (_ : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ ∘ φ'
    ∘-pres-≈̇-right ψ φ≈̇φ' = ∘-pres-≈̇ (≈̇-refl {φ = ψ}) φ≈̇φ'

-- aliases
Category₀ = Categoryₗ 0ℓ
Category₁ = Categoryₗ (suc 0ℓ)

-- legacy use
Category = Category₁
module Category = Categoryₗ

