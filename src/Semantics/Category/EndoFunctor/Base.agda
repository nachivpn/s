{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Base where

open import Semantics.Category.Base

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

record EndoFunctor (C : Category)  : Set₂ where
  open Category C

  -- endofunctor
  field
    ℱ'_     : (P : Obj) → Obj
    ℱ'-map_ : {P Q : Obj} (φ : P →̇ Q) → (ℱ' P →̇ ℱ' Q)
    ℱ'-map-pres-≈̇  : {P Q : Obj} {φ φ' : P →̇ Q} → φ ≈̇ φ' → ℱ'-map φ ≈̇ ℱ'-map φ'
    ℱ'-map-pres-id : {P : Obj} → ℱ'-map id'[ P ] ≈̇ id'
    ℱ'-map-pres-∘  : {P Q R : Obj} → (ψ : Q →̇ R) (φ : P →̇ Q) → ℱ'-map (ψ ∘ φ) ≈̇ ℱ'-map ψ ∘ ℱ'-map φ
