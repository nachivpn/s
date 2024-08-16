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
  open IsStrong isStrong
  open IsPointed isPointed

  field
    strength-point : {P Q : Obj} → strength[ P , Q ] ∘ id'[ P ] ×'-map point[ Q ] ≈̇ point[ P ×' Q ]

