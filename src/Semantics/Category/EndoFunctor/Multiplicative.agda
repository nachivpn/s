{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Multiplicative where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

record IsMultiplicative {C : Category} (F : EndoFunctor C) : Set₂ where
  open Category C
  open EndoFunctor F

  field
    mult[_]      : (P : Obj) → (ℱ' (ℱ' P) →̇ ℱ' P)
    mult-natural : {P Q : Obj} → (t :  P →̇  Q) → mult[ Q ] ∘ (map (map t)) ≈̇ (map t) ∘ mult[ P ]
    mult-assoc   : {P : Obj} → mult[ P ] ∘ (map mult[ P ]) ≈̇ mult[ P ] ∘ mult[ ℱ' P ]

  mult : {P : Obj} → (ℱ' (ℱ' P) →̇ ℱ' P)
  mult = mult[ _ ]

  join[_]   = mult[_]
  
  join : {P : Obj} → ℱ' (ℱ' P) →̇ ℱ' P
  join = mult[ _ ]
  
