{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Strong.Multiplicative where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Multiplicative
open import Semantics.Category.EndoFunctor.Strong.Base

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

record IsStrongMultiplicative {C : Category} {isCartesian : IsCartesian C}
  (F : EndoFunctor C) (isStrong : IsStrong isCartesian F) (isMultiplicative : IsMultiplicative F) : Set₂ where
  open Category C
  open IsCartesian isCartesian
  open EndoFunctor F
  open IsStrong isStrong
  open IsMultiplicative isMultiplicative

  field
    ℱ'-strength-mult :{P Q : Obj} → ℱ'-mult[ P ×' Q ] ∘ (ℱ'-map (ℱ'-strength[ P , Q ])) ∘ ℱ'-strength[ P , ℱ' Q ] ≈̇ ℱ'-strength[ P , Q ] ∘ (id'[ P ] ×'-map ℱ'-mult[ Q ])
