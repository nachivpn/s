{-# OPTIONS --safe --without-K #-}
module Semantics.Category.CartesianClosed where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian

record IsCartesianClosed (C : Category) (isCartesian : IsCartesian C) : Set₂ where
  open Category C
  open IsCartesian isCartesian

  field
    _⇒'_  : (P Q : Obj) → Obj
    lam'        : {R P Q : Obj} → (φ : R ×' P →̇ Q) → R →̇ P ⇒' Q
    lam'-pres-≈̇ : ∀ {R P Q : Obj} {φ φ' : R ×' P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → lam' φ ≈̇ lam' φ'
    app'        : {R P Q : Obj} → (φ : R →̇ P ⇒' Q) → (ψ : R →̇ P) → R →̇ Q
    app'-pres-≈̇ : ∀ {R P Q : Obj} {φ φ' : R →̇ P ⇒' Q} {ψ ψ' : R →̇ P} (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → app' φ ψ ≈̇ app' φ' ψ'
    ⇒'-beta     : ∀ {R P Q : Obj} (φ : R ×' P →̇ Q) (ψ : R →̇ P) → app' (lam' φ) ψ ≈̇ φ [ ⟨ id'[ R ] , ψ ⟩' ]'
    ⇒'-eta      : ∀ {R P Q : Obj} (φ : R →̇ P ⇒' Q) → φ ≈̇ lam' (app' (φ [ π₁'[ P ] ]') π₂'[ R ])
    lam'-nat    : ∀ {R' R P Q : Obj} (φ : R ×' P →̇ Q) (ψ : R' →̇ R) → lam' φ ∘ ψ ≈̇ lam' (φ ∘ ψ ×'-map id'[ P ])
    app'-nat    : ∀ {R' R P Q : Obj} (φ : R →̇ P ⇒' Q) (ψ : R →̇ P) (ω : R' →̇ R) → app' φ ψ ∘ ω ≈̇ app' (φ ∘ ω) (ψ ∘ ω)

  abstract
    app'-pres-≈̇-left : ∀ {R : Obj} {P Q : Obj} {φ φ' : R →̇ P ⇒' Q} (φ≈̇φ' : φ ≈̇ φ') (ψ : R →̇ P) → app' φ ψ ≈̇ app' φ' ψ
    app'-pres-≈̇-left φ≈̇φ' ψ = app'-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

    app'-pres-≈̇-right : ∀ {R : Obj} {P Q : Obj} (φ : R →̇ P ⇒' Q) {ψ ψ' : R →̇ P} (ψ≈̇ψ' : ψ ≈̇ ψ') → app' φ ψ ≈̇ app' φ ψ'
    app'-pres-≈̇-right φ ψ≈̇ψ' = app'-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'
