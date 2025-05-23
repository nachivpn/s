{-# OPTIONS --safe --without-K #-}

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.CartesianClosed
open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Pointed
open import Semantics.Category.EndoFunctor.Multiplicative
open import Semantics.Category.EndoFunctor.Strong.Base
open import Semantics.Category.EndoFunctor.Strong.Pointed
open import Semantics.Category.EndoFunctor.Strong.Multiplicative

module JFC.Evaluation.Base
  (𝒞                     : Category)
  {𝒞-is-CC               : IsCartesian 𝒞}
  (𝒞-is-CCC              : IsCartesianClosed 𝒞 𝒞-is-CC)
  (◇'                    : EndoFunctor 𝒞)
  {◇'-is-strong          : IsStrong 𝒞-is-CC ◇'}
  {◇'-is-mult            : IsMultiplicative ◇'}
  (◇'-is-strong-joinable : IsStrongMultiplicative ◇' ◇'-is-strong ◇'-is-mult)
  where

open Category 𝒞
open IsCartesianClosed 𝒞-is-CCC
open IsStrong ◇'-is-strong renaming (letin' to sletin')
open EndoFunctor ◇' renaming (ℱ'_ to ℱ'₀_)
open IsStrongMultiplicative ◇'-is-strong-joinable renaming (letin' to jletin')

private
  Ty'  = Obj
  Ctx' = Obj

open import Level using (0ℓ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import JFC.Term

module Eval (ι' : Ty') where
  evalTy : (a : Ty) → Ty'
  evalTy ι       = ι'
  evalTy 𝟙       = []'
  evalTy (a × b) = evalTy a ×' evalTy b
  evalTy (a ⇒ b) = evalTy a ⇒' evalTy b
  evalTy (◇ a)   = ℱ'₀ evalTy a

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
  evalTm (var v)      = evalVar v
  evalTm unit         = unit'
  evalTm (pair t u)   = pr' (evalTm t) (evalTm u)
  evalTm (fst t)      = fst' (evalTm t)
  evalTm (snd t)      = snd' (evalTm t)
  evalTm (lam t)      = lam' (evalTm t)
  evalTm (app t u)    = app' (evalTm t) (evalTm u)
  evalTm (sletin t u) = sletin' (evalTm t) (evalTm u)
  evalTm (jletin t u) = jletin' (evalTm t) (evalTm u)

  evalSub : (σ : Sub Δ Γ) → evalCtx Δ →̇ evalCtx Γ
  evalSub []         = unit'
  evalSub (σ `, t)   = ⟨ evalSub σ , evalTm t ⟩'

  Tm'        = λ Γ a → evalCtx Γ →̇ evalTy a
  Tm'-setoid = λ Γ a → →̇-setoid (evalCtx Γ) (evalTy a)

  Sub'        = λ Δ Γ → evalCtx Δ →̇ evalCtx Γ
  Sub'-setoid = λ Δ Γ → →̇-setoid (evalCtx Δ) (evalCtx Γ)
