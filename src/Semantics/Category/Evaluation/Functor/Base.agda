{-# OPTIONS --safe --without-K #-}

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.CartesianClosed
open import Semantics.Category.StrongFunctor

module Semantics.Category.Evaluation.Functor.Base
  (C     : Category)
  (isCC  : IsCartesian C)
  (isCCC : IsCartesianClosed C isCC)
  (hasSF : HasStrongFunctor C isCC)
  where

open Category C
open IsCartesian isCC
open IsCartesianClosed isCCC
open HasStrongFunctor hasSF

Ty'  = Obj
Ctx' = Obj

open import Level using (0ℓ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Functor.Term

module Eval (ι' : Ty') where
  evalTy : (a : Ty) → Ty'
  evalTy ι       = ι'
  evalTy (a ⇒ b) = evalTy a ⇒' evalTy b
  evalTy (◯ a)   = ◯' evalTy a

  evalCtx : (Γ : Ctx) → Ty'
  evalCtx []       = []'
  evalCtx (Γ `, a) = evalCtx Γ ×' evalTy a

  evalWk : (w : Γ ⊆ Δ) → evalCtx Δ →̇ evalCtx Γ
  evalWk base             = unit'
  evalWk (drop {a = a} w) = evalWk w ∘ π₁'[ evalTy a ]
  evalWk (keep {a = a} w) = evalWk w ×'-map id'[ evalTy a ]

  evalVar : (v : Var Γ a) → evalCtx Γ →̇ evalTy a
  evalVar (zero {Γ})       = π₂'[ evalCtx Γ ]
  evalVar (succ {b = b} v) = evalVar v ∘ π₁'[ evalTy b ]

  evalTm : (t : Tm Γ a) → evalCtx Γ →̇ evalTy a
  evalTm (var v)     = evalVar v
  evalTm (lam t)     = lam' (evalTm t)
  evalTm (app t u)   = app' (evalTm t) (evalTm u)
  evalTm (letin t u) = letin' (evalTm t) (evalTm u)

  evalSub : (σ : Sub Δ Γ) → evalCtx Δ →̇ evalCtx Γ
  evalSub []         = unit'
  evalSub (σ `, t)   = ⟨ evalSub σ , evalTm t ⟩'

  Tm'        = λ Γ a → evalCtx Γ →̇ evalTy a
  Tm'-setoid = λ Γ a → →̇-setoid (evalCtx Γ) (evalTy a)

  Sub'        = λ Δ Γ → evalCtx Δ →̇ evalCtx Γ
  Sub'-setoid = λ Δ Γ → →̇-setoid (evalCtx Δ) (evalCtx Γ)
