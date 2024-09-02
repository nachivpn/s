{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Strong.Pointed where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Pointed
open import Semantics.Category.EndoFunctor.Strong.Base

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

record IsStrongPointed {C : Category} {isCartesian : IsCartesian C}
  (F : EndoFunctor C) (isStrong : IsStrong isCartesian F) (isPointed : IsPointed F) : Set₂ where
  open Category C
  open IsCartesian isCartesian
  open EndoFunctor F
  open IsStrong isStrong renaming (red-dia' to red-dia1')
  open IsPointed isPointed

  field
    strength-point : {P Q : Obj} → strength[ P , Q ] ∘ id'[ P ] ×'-map point[ Q ] ≈̇ point[ P ×' Q ]

  red-dia2' : {P Q R : Obj} → (φ : P →̇ Q) (ψ : P ×' Q →̇ R) → letin' (return' φ) ψ ≈̇  return' (ψ ∘ ⟨ id' , φ ⟩' )
  red-dia2' φ ψ = let open EqReasoning (→̇-setoid _ _) in begin
    (map ψ ∘ strength) ∘ ⟨ id' , point ∘ φ ⟩'
      ≈⟨ ∘-assoc _ _ _ ⟩
    map ψ ∘ strength ∘ ⟨ id' , point ∘ φ ⟩'
      ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (⟨,⟩'-pres-≈̇-left (∘-unit-left _ _) _)) ⟩
    map ψ ∘ strength ∘ ⟨ id' ∘ id' , point ∘ φ ⟩'
      ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (×'-map-∘-⟨,⟩' _ _ _ _)) ⟩
    map ψ ∘ strength ∘ ((id' ×'-map point) ∘ ⟨ id' , φ ⟩')
      ≈˘⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩
    map ψ ∘ (strength ∘ (id' ×'-map point)) ∘ ⟨ id' , φ ⟩'
      ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left strength-point _) ⟩
    map ψ ∘ point ∘ ⟨ id' , φ ⟩'
      ≈˘⟨ ∘-assoc _ _ _ ⟩
    (map ψ ∘ point) ∘ ⟨ id' , φ ⟩'
      ≈˘⟨ ∘-pres-≈̇-left (point-natural ψ) _ ⟩
    (point ∘ ψ) ∘ ⟨ id' , φ ⟩'
      ≈⟨ ∘-assoc _ _ _ ⟩
    point ∘ ψ ∘ ⟨ id' , φ ⟩' ∎
