{-# OPTIONS --safe --without-K #-}

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.CartesianClosed
open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Pointed
open import Semantics.Category.EndoFunctor.Multiplicative
open import Semantics.Category.EndoFunctor.Monad
open import Semantics.Category.EndoFunctor.Strong.Base
open import Semantics.Category.EndoFunctor.Strong.Pointed
open import Semantics.Category.EndoFunctor.Strong.Multiplicative
open import Semantics.Category.EndoFunctor.Strong.Monad

open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module JFC.Evaluation.Properties
  (𝒞                     : Category)
  {𝒞-is-CC               : IsCartesian 𝒞}
  (𝒞-is-CCC              : IsCartesianClosed 𝒞 𝒞-is-CC)
  (◇'                    : EndoFunctor 𝒞)
  {◇'-is-strong          : IsStrong 𝒞-is-CC ◇'}
  {◇'-is-mult            : IsMultiplicative ◇'}
  (◇'-is-strong-joinable : IsStrongMultiplicative ◇' ◇'-is-strong ◇'-is-mult)
  (ι'                    : Category.Obj 𝒞)
  where

open Category 𝒞
open IsCartesianClosed 𝒞-is-CCC
open IsStrong ◇'-is-strong renaming (letin' to sletin'
      ; letin'-pres-≈̇ to sletin'-pres-≈̇
      ; letin'-pres-≈̇-left to sletin'-pres-≈̇-left
      ; letin'-pres-≈̇-right to sletin'-pres-≈̇-right
      ; letin'-nat₁ to sletin'-nat₁
      ; red-dia' to red-dia1')
open EndoFunctor ◇' renaming (ℱ'_ to ℱ'₀_)
open IsStrongMultiplicative ◇'-is-strong-joinable renaming  (letin' to jletin'
      ; letin'-pres-≈̇ to jletin'-pres-≈̇
      ; letin'-pres-≈̇-left to jletin'-pres-≈̇-left
      ; letin'-pres-≈̇-right to jletin'-pres-≈̇-right
      ; letin'-nat₁ to jletin'-nat₁
      )

private
  Ty'  = Obj
  Ctx' = Obj

open import Level using (0ℓ)

open import Relation.Binary using (IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import JFC.Term
open import JFC.Term.Conversion

open import JFC.Evaluation.Base
   𝒞 𝒞-is-CCC ◇' ◇'-is-strong-joinable
  renaming (module Eval to JFCBaseEval)

open JFCBaseEval ι'

abstract
  evalWk-pres-id : ∀ (Γ : Ctx) → evalWk ⊆-refl[ Γ ] ≈̇ id'
  evalWk-pres-id []          = ≈̇-sym []'-eta
  evalWk-pres-id Γ@(Γ' `, a) = let open EqReasoning (Sub'-setoid Γ Γ) in begin
    evalWk (keep[ a ] ⊆-refl[ Γ' ])             ≈⟨ ×'-map-pres-≈̇-left (evalWk-pres-id Γ') id'[ evalTy a ] ⟩
    id'[ evalCtx Γ' ] ×'-map id'[ evalTy a ]  ≈⟨ ×'-map-pres-id' ⟩
    id'[ evalCtx Γ ]                          ∎

  evalWk-pres-∘-π₁ : evalWk (drop[ a ] w) ≈̇ evalWk w ∘ π₁'[ evalTy a ]
  evalWk-pres-∘-π₁ = ≈̇-refl

  evalWk-pres-×-map-id : evalWk (keep[ a ] w) ≈̇ evalWk w ×'-map id'[ evalTy a ]
  evalWk-pres-×-map-id = ≈̇-refl

  evalWk-pres-π₁ : ∀ (Γ : Ctx) (a : Ty) → evalWk (freshWk {Γ} {a}) ≈̇ π₁'[ evalTy a ]
  evalWk-pres-π₁ Γ a = let open EqReasoning (Sub'-setoid (Γ `, a) Γ) in begin
    evalWk (freshWk {Γ} {a})              ≈⟨ ∘-pres-≈̇-left (evalWk-pres-id Γ) π₁'[ evalTy a ] ⟩
    id'[ evalCtx Γ ] ∘ π₁'[ evalTy a ]  ≈⟨ ∘-unit-left (evalCtx Γ) π₁'[ evalTy a ] ⟩
    π₁'[ evalTy a ]                     ∎

module _ {a : Ty} where
  abstract
    evalVar-pres-∘ : ∀ (w : Γ ⊆ Δ) (n : Var Γ a) → evalVar (wkVar w n) ≈̇ evalVar n ∘ evalWk w
    evalVar-pres-∘ (drop {Δ = Δ} {b} w) v = let open EqReasoning (Tm'-setoid (Δ `, b) a) in begin
      evalVar (wkVar (drop[ b ] w) v)                     ≈⟨ ∘-pres-≈̇-left (evalVar-pres-∘ w v) π₁'[ evalTy b ] ⟩
      (evalVar v ∘ evalWk w) ∘ π₁'[ evalTy b ]            ≈⟨ ∘-assoc (evalVar v) (evalWk w) π₁'[ evalTy b ] ⟩
      evalVar v ∘ evalWk (drop[ b ] w)                    ∎
    evalVar-pres-∘ (keep {Δ = Δ} {a} w) (zero {Γ}) = let open EqReasoning (Tm'-setoid (Δ `, a) a) in begin
      evalVar (wkVar (keep[ a ] w) (zero {Γ}))            ≈˘⟨ ∘-unit-left (evalTy a) π₂'[ evalCtx Δ ] ⟩
      id'[ evalTy a ] ∘ π₂'[ evalCtx Δ ]                  ≈˘⟨ ×'-beta-right (evalWk w ∘ π₁'[ evalTy a ]) ⟩
      evalVar (zero {Γ} {a}) ∘ evalWk (keep[ a ] w)       ∎
    evalVar-pres-∘ (keep {Δ = Δ} {b} w) (succ {Γ} {a} {b} n) = let open EqReasoning (Tm'-setoid (Δ `, b) a) in begin
      evalVar (wkVar (keep[ b ] w) (succ {Γ} {a} {b} n))  ≈⟨ ∘-pres-≈̇-left (evalVar-pres-∘ w n) π₁'[ evalTy b ] ⟩
      (evalVar n ∘ evalWk w) ∘ π₁'[ evalTy b ]            ≈⟨ ∘-assoc (evalVar n) (evalWk w) π₁'[ evalTy b ] ⟩
      evalVar n ∘ evalWk w ∘ π₁'[ evalTy b ]              ≈˘⟨ ∘-pres-≈̇-right (evalVar n) (×'-beta-left (id' ∘ π₂')) ⟩
      evalVar n ∘ π₁'[ evalTy b ] ∘ evalWk (keep[ b ] w)  ≈˘⟨ ∘-assoc (evalVar n) π₁'[ evalTy b ] (evalWk (keep[ b ] w)) ⟩
      evalVar (succ {Γ} {a} {b} n) ∘ evalWk (keep[ b ] w) ∎

abstract
  evalTm-pres-∘' : ∀ (w : Γ ⊆ Δ) (t : Tm Γ a) → evalTm (wkTm w t) ≈̇ evalTm t [ evalWk w ]'
  evalTm-pres-∘' w (var v) = evalVar-pres-∘ w v
  evalTm-pres-∘' w unit       = ≈̇-sym []'-eta
  evalTm-pres-∘' {Δ = Δ} {a} w (pair t u) = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (pair t u))
      ≈⟨ ⟨,⟩'-pres-≈̇ (evalTm-pres-∘' w t) (evalTm-pres-∘' w u) ⟩
    pr' (evalTm t [ evalWk w ]') (evalTm u [ evalWk w ]')
      ≈˘⟨ ⟨,⟩'-nat (evalTm t) (evalTm u) (evalWk w) ⟩
    evalTm (pair t u) [ evalWk w ]'
      ∎
  evalTm-pres-∘' {Δ = Δ} {a} w (fst t)    = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (fst t))
      ≈⟨ fst'-pres-≈̇ (evalTm-pres-∘' w t) ⟩
    fst' (evalTm t [ evalWk w ]')
      ≈˘⟨ fst'-nat (evalTm t) (evalWk w) ⟩
    evalTm (fst t) [ evalWk w ]'
      ∎
  evalTm-pres-∘' {Δ = Δ} {a} w (snd t)    = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (snd t))
      ≈⟨ snd'-pres-≈̇ (evalTm-pres-∘' w t) ⟩
    snd' (evalTm t [ evalWk w ]')
      ≈˘⟨ snd'-nat (evalTm t) (evalWk w) ⟩
    evalTm (snd t) [ evalWk w ]'
      ∎
  evalTm-pres-∘' {Δ = Δ} {a} w (lam {a = a'} t) = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (lam t))
      ≈⟨ lam'-pres-≈̇ (evalTm-pres-∘' (keep[ a' ] w) t) ⟩
    lam' (evalTm t ∘ evalWk (keep[ a' ] w))
      ≈˘⟨ lam'-nat (evalTm t) (evalWk w) ⟩
    evalTm (lam t) [ evalWk w ]'
      ∎
  evalTm-pres-∘' {Δ = Δ} {a} w (app t u) = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (app t u))
      ≈⟨ app'-pres-≈̇ (evalTm-pres-∘' w t) (evalTm-pres-∘' w u) ⟩
    app' (evalTm t ∘ evalWk w) (evalTm u ∘ evalWk w)
      ≈˘⟨ app'-nat (evalTm t) (evalTm u) (evalWk w) ⟩
    evalTm (app t u) [ evalWk w ]'
      ∎
  evalTm-pres-∘' {Δ = Δ} {a} w (sletin {a = a'} t u) = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (sletin t u))
      ≈⟨ sletin'-pres-≈̇ (evalTm-pres-∘' w t) (evalTm-pres-∘' (keep w) u) ⟩
    sletin' (evalTm t [ evalWk w ]') (evalTm u [ evalWk (keep[ a' ] w) ]')
      ≈˘⟨ sletin'-nat₁ (evalTm t) (evalTm u) (evalWk w) ⟩
    evalTm (sletin t u) [ evalWk w ]'
      ∎
  evalTm-pres-∘' {Δ = Δ} {a} w (jletin {a = a'} t u) = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (jletin t u))
      ≈⟨ jletin'-pres-≈̇ (evalTm-pres-∘' w t) (evalTm-pres-∘' (keep w) u) ⟩
    jletin' (evalTm t [ evalWk w ]') (evalTm u [ evalWk (keep[ a' ] w) ]')
      ≈˘⟨ jletin'-nat₁ (evalTm t) (evalTm u) (evalWk w) ⟩
    evalTm (jletin t u) [ evalWk w ]'
      ∎

abstract
  evalSub-pres-∘' : ∀ (σ : Sub Δ Γ) (w : Δ ⊆ Δ') → evalSub (wkSub w σ) ≈̇ evalSub σ ∘ evalWk w
  evalSub-pres-∘' []         w = ≈̇-sym []'-eta
  evalSub-pres-∘' {Γ = Γ} {Δ'} (σ `, t)   w = let open EqReasoning (Sub'-setoid Δ' Γ) in begin
    evalSub (wkSub w (σ `, t))
      ≈⟨ ⟨,⟩'-pres-≈̇ (evalSub-pres-∘' σ w) (evalTm-pres-∘' w t) ⟩
    ⟨ evalSub σ ∘ evalWk w , evalTm t ∘ evalWk w ⟩'
      ≈˘⟨ ⟨,⟩'-nat (evalSub σ) (evalTm t) (evalWk w) ⟩
    evalSub (σ `, t) ∘ evalWk w
      ∎
abstract
  evalSub-pres-∘-π₁ : ∀ (σ : Sub Δ Γ) (a : Ty) → evalSub (dropₛ {Δ} {Γ} {a} σ) ≈̇ evalSub σ ∘ π₁'[ evalTy a ]
  evalSub-pres-∘-π₁ {Δ} {Γ} σ a = let open EqReasoning (Sub'-setoid (Δ `, a) Γ) in begin
    evalSub (dropₛ {Δ} {Γ} {a} σ)       ≈⟨ evalSub-pres-∘' σ (freshWk {Δ} {a}) ⟩
    evalSub σ ∘ evalWk (freshWk {Δ} {a})  ≈⟨ ∘-pres-≈̇-right (evalSub σ) (evalWk-pres-π₁ Δ a) ⟩
    evalSub σ ∘ π₁'[ evalTy a ]         ∎

abstract
  evalSub-pres-×-map-id : ∀ (σ : Sub Δ Γ) (a : Ty) → evalSub (keepₛ {Δ} {Γ} {a} σ) ≈̇ evalSub σ ×'-map id'[ evalTy a ]
  evalSub-pres-×-map-id {Δ} {Γ} σ a = let open EqReasoning (Sub'-setoid (Δ `, a) (Γ `, a)) in begin
    evalSub (keepₛ {Δ} {Γ} {a} σ)    ≈⟨ ⟨,⟩'-pres-≈̇ (evalSub-pres-∘-π₁ σ a) (≈̇-sym (∘-unit-left (evalTy a) π₂'[ evalCtx Δ ])) ⟩
    evalSub σ ×'-map id'[ evalTy a ]  ∎

abstract
  evalSub-pres-wk : ∀ (w : Γ ⊆ Γ') → evalSub (embWk w) ≈̇ evalWk w
  evalSub-pres-wk base = []'-eta
  evalSub-pres-wk {Γ} (drop {Δ = Γ'} {a} w) = let open EqReasoning (Sub'-setoid (Γ' `, a) Γ) in begin
    evalSub (embWk (drop[ a ] w))                ≈⟨ evalSub-pres-∘' (embWk w) (freshWk {Γ'} {a}) ⟩
    evalSub (embWk w) ∘ evalWk (freshWk {Γ'} {a})  ≈⟨ ∘-pres-≈̇ (evalSub-pres-wk w) (evalWk-pres-π₁ Γ' a) ⟩
    evalWk (drop[ a ] w)                         ∎
  evalSub-pres-wk {Γ} (keep {Δ = Γ'} {a} w) = let open EqReasoning (Sub'-setoid (Γ' `, a) Γ) in begin
    evalSub (embWk (keep[ a ] w))                ≈⟨ evalSub-pres-×-map-id (embWk w) a ⟩
    evalSub (embWk w) ×'-map id'[ evalTy a ]     ≈⟨ ×'-map-pres-≈̇-left (evalSub-pres-wk w) id' ⟩
    evalWk (keep[ a ] w)                         ∎

abstract
  evalSub-pres-id : ∀ (Γ : Ctx) → evalSub idₛ[ Γ ] ≈̇ id'
  evalSub-pres-id Γ = let open EqReasoning (Sub'-setoid Γ Γ) in begin
    evalSub idₛ[ Γ ]  ≈⟨ evalSub-pres-wk ⊆-refl[ Γ ] ⟩
    evalWk ⊆-refl[ Γ ]  ≈⟨ evalWk-pres-id Γ ⟩
    id'                ∎

module _ {a : Ty} {Δ : Ctx} where
  abstract
    evalTm-pres-∘'' : ∀ (v : Var Γ a) (σ : Sub Δ Γ) → evalTm (substVar σ v) ≈̇ evalVar v [ evalSub σ ]'
    evalTm-pres-∘'' zero             (σ `, t) = ≈̇-sym (×'-beta-right (evalSub σ))
    evalTm-pres-∘'' (succ {b = b} v) (σ `, t) = let open EqReasoning (Tm'-setoid Δ a) in begin
      evalTm (substVar (σ `, t) (succ {b = b} v))     ≈⟨ evalTm-pres-∘'' v σ ⟩
      evalVar v [ evalSub σ ]'                        ≈˘⟨ ∘-pres-≈̇-right (evalVar v) (×'-beta-left (evalTm t)) ⟩
      evalVar v ∘ π₁'[ evalTy b ] ∘ evalSub (σ `, t)  ≈˘⟨ ∘-assoc (evalVar v) π₁'[ evalTy b ] (evalSub (σ `, t)) ⟩
      evalVar (succ {b = b} v) [ evalSub (σ `, t) ]'  ∎

abstract
  evalTm-pres-∘ : ∀ (t : Tm Γ a) → (σ : Sub Δ Γ) → evalTm (substTm σ t) ≈̇ evalTm t [ evalSub σ ]'
  evalTm-pres-∘ (var v)    σ = evalTm-pres-∘'' v σ
  evalTm-pres-∘ unit       σ = ≈̇-sym ([]'-eta)
  evalTm-pres-∘ {a = a} {Δ} (pair t u) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (pair t u))
      ≈⟨ ⟨,⟩'-pres-≈̇ (evalTm-pres-∘ t σ) (evalTm-pres-∘ u σ) ⟩
    pr' (evalTm t [ evalSub σ ]') (evalTm u [ evalSub σ ]')
      ≈˘⟨ ⟨,⟩'-nat (evalTm t) (evalTm u) (evalSub σ) ⟩
    evalTm (pair t u) [ evalSub σ ]'
      ∎
  evalTm-pres-∘ {a = a} {Δ} (fst t)    σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (fst t))
      ≈⟨ fst'-pres-≈̇ (evalTm-pres-∘ t σ) ⟩
    fst' (evalTm t [ evalSub σ ]')
      ≈˘⟨ fst'-nat (evalTm t) (evalSub σ) ⟩
    evalTm (fst t) [ evalSub σ ]'
      ∎
  evalTm-pres-∘ {a = a} {Δ} (snd t)    σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (snd t))
      ≈⟨ snd'-pres-≈̇ (evalTm-pres-∘ t σ) ⟩
    snd' (evalTm t [ evalSub σ ]')
      ≈˘⟨ snd'-nat (evalTm t) (evalSub σ) ⟩
    evalTm (snd t) [ evalSub σ ]'
      ∎
  evalTm-pres-∘ {a = a} {Δ} (lam {a = a'} t) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (lam t))
      ≈⟨ lam'-pres-≈̇ (evalTm-pres-∘ t (wkSub (freshWk {Δ} {a'}) σ `, var zero)) ⟩
    lam' (evalTm t [ evalSub (wkSub (freshWk {Δ} {a'}) σ `, var zero) ]')
      ≈⟨ lam'-pres-≈̇ (∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-left (evalSub-pres-∘' σ (freshWk {Δ} {a'})) π₂'[ evalCtx Δ ])) ⟩
    lam' (evalTm t [ ⟨ evalSub σ ∘ evalWk (freshWk {Δ} {a'}) , π₂'[ evalCtx Δ ] ⟩' ]' )
      ≈⟨ lam'-pres-≈̇ (∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-left (∘-pres-≈̇-right (evalSub σ) (evalWk-pres-π₁ Δ a')) π₂'[ evalCtx Δ ])) ⟩
    lam' (evalTm t [ ⟨ evalSub σ ∘ π₁'[ evalTy a' ] , π₂'[ evalCtx Δ ] ⟩' ]')
      ≈˘⟨ lam'-pres-≈̇ (∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-right (evalSub σ ∘ π₁'[ evalTy a' ]) (∘-unit-left (evalTy a') π₂'[ evalCtx Δ ]))) ⟩
    lam' (evalTm t ∘ evalSub σ ×'-map id'[ evalTy a' ])
      ≈˘⟨ lam'-nat (evalTm t) (evalSub σ) ⟩
    evalTm (lam t) [ evalSub σ ]'
      ∎
  evalTm-pres-∘ {a = a} {Δ} (app t u) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (app t u))
      ≈⟨ app'-pres-≈̇ (evalTm-pres-∘ t σ) (evalTm-pres-∘ u σ) ⟩
    app' (evalTm t [ evalSub σ ]') (evalTm u [ evalSub σ ]')
      ≈˘⟨ app'-nat (evalTm t) (evalTm u) (evalSub σ) ⟩
    evalTm (app t u) [ evalSub σ ]'
      ∎
  evalTm-pres-∘ {a = a} {Δ} (sletin {a = a'} t u) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (sletin t u))
      ≡⟨⟩
    sletin' (evalTm (substTm σ t)) (evalTm (substTm (keepₛ σ) u))
      ≈⟨ sletin'-pres-≈̇ (evalTm-pres-∘ t σ) (evalTm-pres-∘ u (keepₛ σ)) ⟩
    sletin' (evalTm t [ evalSub σ ]') (evalTm u [ evalSub (keepₛ {a = a'} σ) ]')
      ≈⟨ sletin'-pres-≈̇-right _ (∘-pres-≈̇-right _ (evalSub-pres-×-map-id σ a')) ⟩
    sletin' (evalTm t [ evalSub σ ]') (evalTm u [ evalSub σ ×'-map id' ]')
      ≈˘⟨ sletin'-nat₁ (evalTm t) (evalTm u) (evalSub σ) ⟩
    sletin' (evalTm t) (evalTm u) [ evalSub σ ]'
      ≡⟨⟩
    evalTm (sletin t u) [ evalSub σ ]'
      ∎
  evalTm-pres-∘ {a = a} {Δ} (jletin {a = a'} t u) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (jletin t u))
      ≡⟨⟩
    jletin' (evalTm (substTm σ t)) (evalTm (substTm (keepₛ σ) u))
      ≈⟨ jletin'-pres-≈̇ (evalTm-pres-∘ t σ) (evalTm-pres-∘ u (keepₛ σ)) ⟩
    jletin' (evalTm t [ evalSub σ ]') (evalTm u [ evalSub (keepₛ {a = a'} σ) ]')
      ≈⟨ jletin'-pres-≈̇-right _ (∘-pres-≈̇-right _ (evalSub-pres-×-map-id σ a')) ⟩
    jletin' (evalTm t [ evalSub σ ]') (evalTm u [ evalSub σ ×'-map id' ]')
      ≈˘⟨ jletin'-nat₁ (evalTm t) (evalTm u) (evalSub σ) ⟩
    jletin' (evalTm t) (evalTm u) [ evalSub σ ]'
      ≡⟨⟩
    evalTm (jletin t u) [ evalSub σ ]'
      ∎

abstract
  evalTm-sound : (s : t ≈ t') → evalTm t ≈̇ evalTm t'
  evalTm-sound (exp-unit _)              = []'-eta
  evalTm-sound (red-prod1 _ u)           = ×'-beta-left (evalTm u)
  evalTm-sound (red-prod2 t _)           = ×'-beta-right (evalTm t)
  evalTm-sound (exp-prod _)              = ×'-eta
  evalTm-sound (cong-fst t≈t')           = fst'-pres-≈̇ (evalTm-sound t≈t')
  evalTm-sound (cong-snd t≈t')           = snd'-pres-≈̇ (evalTm-sound t≈t')
  evalTm-sound (cong-pair t≈t' u≈u')     = ⟨,⟩'-pres-≈̇ (evalTm-sound t≈t') (evalTm-sound u≈u')
  evalTm-sound (red-fun {Γ} {a} {b} t u) = let open EqReasoning (Tm'-setoid Γ b) in begin
    evalTm (app (lam t) u)
      ≈⟨ ⇒'-beta (evalTm t) (evalTm u) ⟩
    evalTm t [ ⟨ id'[ evalCtx Γ ] , evalTm u ⟩' ]'
      ≈˘⟨ ∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-left (evalSub-pres-id Γ) (evalTm u)) ⟩
    evalTm t [ ⟨ evalSub idₛ[ Γ ] , evalTm u ⟩' ]'
      ≈˘⟨ evalTm-pres-∘ t (idₛ `, u) ⟩
    evalTm (substTm (idₛ[ Γ ] `, u) t)
      ∎
  evalTm-sound (exp-fun {Γ} {a} {b} t) = let open EqReasoning (Tm'-setoid Γ (a ⇒ b)) in begin
    evalTm t
      ≈⟨ ⇒'-eta (evalTm t) ⟩
    lam' (app' (evalTm t [ π₁'[ evalTy a ] ]') π₂'[ evalCtx Γ ])
      ≈˘⟨ lam'-pres-≈̇ (app'-pres-≈̇-left (∘-pres-≈̇-right (evalTm t) (evalWk-pres-π₁ Γ a)) π₂'[ evalCtx Γ ]) ⟩
    lam' (app' (evalTm t [ evalWk (freshWk {Γ} {a}) ]') π₂'[ evalCtx Γ ])
      ≈˘⟨ lam'-pres-≈̇ (app'-pres-≈̇-left (evalTm-pres-∘' freshWk t) π₂'[ evalCtx Γ ]) ⟩
    evalTm (lam (app (wkTm freshWk t) (var zero)))
      ∎
  evalTm-sound (exp-dia {Γ} {a} t) = let open EqReasoning (Tm'-setoid Γ (◇ a)) in begin
    evalTm t
      ≈⟨ exp-dia' (evalTm t) ⟩
    sletin' (evalTm t) π₂'
      ≡⟨⟩
    sletin' (evalTm t) (evalVar {Γ `, a} zero) ∎
  evalTm-sound (red-dia1 {Γ} {a} {b} {c} t u u') = let open EqReasoning (Tm'-setoid Γ (◇ c)) in begin
    sletin' (sletin' (evalTm t) (evalTm u)) (evalTm u')
      ≈⟨ red-dia1' (evalTm t) (evalTm u) (evalTm u') ⟩
    sletin' (evalTm t) (evalTm u' [ ⟨ π₁' , evalTm u ⟩' ]')
      ≈˘⟨ sletin'-pres-≈̇-right (evalTm t) (∘-pres-≈̇-right (evalTm u') (⟨,⟩'-pres-≈̇-left (∘-unit-left _ π₁') (evalTm u))) ⟩
    sletin' (evalTm t) (evalTm u' [ ⟨ id'[ evalCtx Γ ] ∘ π₁' , evalTm u ⟩' ]')
      ≈˘⟨ sletin'-pres-≈̇-right (evalTm t) (∘-pres-≈̇-right (evalTm u') (⟨,⟩'-pres-≈̇-left (∘-pres-≈̇-left (evalSub-pres-id Γ) π₁') (evalTm u))) ⟩
    sletin' (evalTm t) (evalTm u' [ ⟨ evalSub idₛ[ Γ ] ∘ π₁'[  evalTy a ] , evalTm u ⟩' ]')
      ≈˘⟨ sletin'-pres-≈̇-right (evalTm t) (∘-pres-≈̇-right (evalTm u') (⟨,⟩'-pres-≈̇-left (evalSub-pres-∘-π₁ idₛ[ Γ ] a) (evalTm u))) ⟩
    sletin' (evalTm t) (evalTm u' [ evalSub (dropₛ idₛ `, u) ]')
      ≈˘⟨ sletin'-pres-≈̇-right (evalTm t) (evalTm-pres-∘ u' (dropₛ idₛ `, u)) ⟩
    sletin' (evalTm t) (evalTm (substTm (dropₛ idₛ `, u) u'))
      ∎
  evalTm-sound (red-dia2 {Γ} {a} {b} {c} t u u') = let open EqReasoning (Tm'-setoid Γ (◇ c)) in begin
    jletin' (sletin' (evalTm t) (evalTm u)) (evalTm u')
      ≈⟨ red-dia2' (evalTm t) (evalTm u) (evalTm u') ⟩
    jletin' (evalTm t) (evalTm u' [ ⟨ π₁' , evalTm u ⟩' ]')
      ≈˘⟨ jletin'-pres-≈̇-right (evalTm t) (∘-pres-≈̇-right (evalTm u') (⟨,⟩'-pres-≈̇-left (∘-unit-left _ π₁') (evalTm u))) ⟩
    jletin' (evalTm t) (evalTm u' [ ⟨ id'[ evalCtx Γ ] ∘ π₁' , evalTm u ⟩' ]')
      ≈˘⟨ jletin'-pres-≈̇-right (evalTm t) (∘-pres-≈̇-right (evalTm u') (⟨,⟩'-pres-≈̇-left (∘-pres-≈̇-left (evalSub-pres-id Γ) π₁') (evalTm u))) ⟩
    jletin' (evalTm t) (evalTm u' [ ⟨ evalSub idₛ[ Γ ] ∘ π₁'[  evalTy a ] , evalTm u ⟩' ]')
      ≈˘⟨ jletin'-pres-≈̇-right (evalTm t) (∘-pres-≈̇-right (evalTm u') (⟨,⟩'-pres-≈̇-left (evalSub-pres-∘-π₁ idₛ[ Γ ] a) (evalTm u))) ⟩
    jletin' (evalTm t) (evalTm u' [ evalSub (dropₛ idₛ `, u) ]')
      ≈˘⟨ jletin'-pres-≈̇-right (evalTm t) (evalTm-pres-∘ u' (dropₛ idₛ `, u)) ⟩
    jletin' (evalTm t) (evalTm (substTm (dropₛ idₛ `, u) u'))
      ∎
  evalTm-sound (ass-dia {Γ} {a} {b} {c} t u u') = let open EqReasoning (Tm'-setoid Γ (◇ c)) in begin
    jletin' (jletin' (evalTm t) (evalTm u)) (evalTm u')
      ≈⟨ ass-dia' (evalTm t) (evalTm u) (evalTm u') ⟩
    jletin' (evalTm t) (jletin' (evalTm u) (evalTm u' ∘ (π₁' ×'-map id')))
      ≈˘⟨ jletin'-pres-≈̇-right _ (jletin'-pres-≈̇-right _ (∘-pres-≈̇-right (evalTm u')
            (⟨,⟩'-pres-≈̇-left (∘-pres-≈̇-left (evalWk-pres-π₁ Γ a) _) _))) ⟩
    jletin' (evalTm t) (jletin' (evalTm u) (evalTm u' ∘ (evalWk freshWk[ Γ , a ] ×'-map id')))
      ≈˘⟨ jletin'-pres-≈̇-right _ (jletin'-pres-≈̇-right _ (∘-pres-≈̇-right (evalTm u')
            (evalWk-pres-×-map-id {a = b} {w = freshWk[ Γ , a ] }))) ⟩
    jletin' (evalTm t) (jletin' (evalTm u) (evalTm u' [ evalWk (keep[ b ] freshWk[ Γ , a ]) ]'))
      ≈˘⟨ jletin'-pres-≈̇-right _ (jletin'-pres-≈̇-right _ (evalTm-pres-∘' (keep freshWk[ Γ , a ]) u')) ⟩
    jletin' (evalTm t) (jletin' (evalTm u) (evalTm (wkTm (keep freshWk[ Γ , a ]) u')))
      ∎
  evalTm-sound (com-dia {Γ} {a} {b} {c} t u u') = let open EqReasoning (Tm'-setoid Γ (◇ c)) in begin
    sletin' (jletin' (evalTm t) (evalTm u)) (evalTm u')
      ≈⟨ com-dia' (evalTm t) (evalTm u) (evalTm u') ⟩
    jletin' (evalTm t) (sletin' (evalTm u) (evalTm u' ∘ (π₁' ×'-map id')))
      ≈˘⟨ jletin'-pres-≈̇-right _ (sletin'-pres-≈̇-right _ (∘-pres-≈̇-right (evalTm u')
            (⟨,⟩'-pres-≈̇-left (∘-pres-≈̇-left (evalWk-pres-π₁ Γ a) _) _))) ⟩
    jletin' (evalTm t) (sletin' (evalTm u) (evalTm u' ∘ (evalWk freshWk[ Γ , a ] ×'-map id')))
      ≈˘⟨ jletin'-pres-≈̇-right _ (sletin'-pres-≈̇-right _ (∘-pres-≈̇-right (evalTm u')
            (evalWk-pres-×-map-id {a = b} {w = freshWk[ Γ , a ] }))) ⟩
    jletin' (evalTm t) (sletin' (evalTm u) (evalTm u' [ evalWk (keep[ b ] freshWk[ Γ , a ]) ]'))
      ≈˘⟨ jletin'-pres-≈̇-right _ (sletin'-pres-≈̇-right _ (evalTm-pres-∘' (keep freshWk[ Γ , a ]) u')) ⟩
    jletin' (evalTm t) (sletin' (evalTm u) (evalTm (wkTm (keep freshWk[ Γ , a ]) u')))
      ∎
  evalTm-sound (cong-lam s)            = lam'-pres-≈̇ (evalTm-sound s)
  evalTm-sound (cong-app t≈t' u≈u')    = app'-pres-≈̇ (evalTm-sound t≈t') (evalTm-sound u≈u') 
  evalTm-sound (cong-sletin t≈t' u≈u') = sletin'-pres-≈̇ (evalTm-sound t≈t') (evalTm-sound u≈u')
  evalTm-sound (cong-jletin t≈t' u≈u') = jletin'-pres-≈̇ (evalTm-sound t≈t') (evalTm-sound u≈u')
  evalTm-sound ≈-refl                  = ≈̇-refl
  evalTm-sound (≈-trans r s)           = ≈̇-trans (evalTm-sound r) (evalTm-sound s)
  evalTm-sound (≈-sym s)               = ≈̇-sym (evalTm-sound s)
