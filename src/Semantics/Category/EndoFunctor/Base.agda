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
    map_ : {P Q : Obj} (φ : P →̇ Q) → (ℱ' P →̇ ℱ' Q)
    map-pres-≈̇  : {P Q : Obj} {φ φ' : P →̇ Q} → φ ≈̇ φ' → map φ ≈̇ map φ'
    map-pres-id : {P : Obj} → map id'[ P ] ≈̇ id'
    map-pres-∘  : {P Q R : Obj} → (ψ : Q →̇ R) (φ : P →̇ Q) → map (ψ ∘ φ) ≈̇ map ψ ∘ map φ
