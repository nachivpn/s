{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Category.Evaluation.Functor.Properties
  (Ctx' : Set₁)

  (_→̇_ : (P Q : Ctx') → Set) (let infixr 19 _→̇_; _→̇_ = _→̇_)

  (_≈̇_     : {P Q : Ctx'} → (φ ψ : P →̇ Q) → Set) (let infix 18 _≈̇_; _≈̇_ = _≈̇_)
  (≈̇-refl  : ∀ {P Q : Ctx'} {φ : P →̇ Q} → φ ≈̇ φ)
  (≈̇-sym   : ∀ {P Q : Ctx'} {φ ψ : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → ψ ≈̇ φ)
  (≈̇-trans : ∀ {P Q : Ctx'} {φ ψ ω : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → (ψ≈̇ω : ψ ≈̇ ω) → φ ≈̇ ω)

  (_∘_      : {P Q R : Ctx'} → (ψ : Q →̇ R) → (φ : P →̇ Q) → (P →̇ R)) (let infixr 19 _∘_; _∘_ = _∘_)
  (∘-pres-≈̇ : ∀ {P Q R : Ctx'} {ψ ψ' : Q →̇ R} {φ φ' : P →̇ Q} (ψ≈̇ψ' : ψ ≈̇ ψ') (φ≈̇φ' : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ' ∘ φ')
  (∘-assoc  : {P Q R S : Ctx'} → (ω : R →̇ S) → (ψ : Q →̇ R) → (φ : P →̇ Q) → (ω ∘ ψ) ∘ φ ≈̇ ω ∘ ψ ∘ φ)
  (let _[_]' = _∘_)

  (id'[_]         : (P : Ctx') → P →̇ P)
  (id'-unit-left  : ∀ {P : Ctx'} (Q : Ctx') (φ : P →̇ Q) → id'[ Q ] ∘ φ ≈̇ φ)
  (id'-unit-right : ∀ (P : Ctx') {Q : Ctx'} (φ : P →̇ Q) → φ ∘ id'[ P ] ≈̇ φ)

  ([]'     : Ctx')
  (unit'   : {P : Ctx'} → P →̇ []')
  ([]'-eta : ∀ {P : Ctx'} {φ : P →̇ []'} → φ ≈̇ unit')

  (_×'_          : (P Q : Ctx') → Ctx')
  (⟨_,_⟩'        : {R P Q : Ctx'} → (φ : R →̇ P) → (ψ : R →̇ Q) → R →̇ P ×' Q)
  (⟨,⟩'-pres-≈̇   : ∀ {R P Q : Ctx'} {φ φ' : R →̇ P} {ψ ψ' : R →̇ Q} (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ' , ψ' ⟩')
  (π₁'[_]        : {P : Ctx'} → (Q : Ctx') → P ×' Q →̇ P)
  (π₂'[_]        : (P : Ctx') → {Q : Ctx'} → P ×' Q →̇ Q)
  (let fst'[_]_ = λ {R} {P} Q φ → _∘_ {R} {P ×' Q} {P} π₁'[ Q ] φ)
  (let snd'[_]_ = λ {R} P {Q} φ → _∘_ {R} {P ×' Q} {Q} π₂'[ P ] φ)
  (×'-beta-left  : ∀ {R P Q : Ctx'} {φ : R →̇ P} (ψ : R →̇ Q) → π₁'[ Q ] ∘ ⟨ φ , ψ ⟩' ≈̇ φ)
  (×'-beta-right : ∀ {R P Q : Ctx'} (φ : R →̇ P) {ψ : R →̇ Q} → π₂'[ P ] ∘ ⟨ φ , ψ ⟩' ≈̇ ψ)
  (×'-eta        : ∀ {R P Q : Ctx'} {φ : R →̇ P ×' Q} → φ ≈̇ ⟨ fst'[ Q ] φ , snd'[ P ] φ ⟩')
  (⟨,⟩'-nat      : ∀ {R' R P Q : Ctx'} (φ : R →̇ P) (ψ : R →̇ Q) (ω : R' →̇ R) → ⟨ φ , ψ ⟩' ∘ ω ≈̇ ⟨ φ ∘ ω , ψ ∘ ω ⟩')
  (let _×'-map_ = λ {P} {P'} {Q} {Q'} φ ψ → ⟨_,_⟩' {P ×' Q} {P'} {Q'} (φ ∘ π₁'[ Q ]) (ψ ∘ π₂'[ P ]))

  (let Ty' = Ctx')

  (_⇒'_        : (P Q : Ty') → Ty')
  (lam'        : {R P Q : Ty'} → (φ : R ×' P →̇ Q) → R →̇ P ⇒' Q)
  (lam'-pres-≈̇ : ∀ {R P Q : Ty'} {φ φ' : R ×' P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → lam' φ ≈̇ lam' φ')
  (app'        : {R P Q : Ty'} → (φ : R →̇ P ⇒' Q) → (ψ : R →̇ P) → R →̇ Q)
  (app'-pres-≈̇ : ∀ {R P Q : Ty'} {φ φ' : R →̇ P ⇒' Q} {ψ ψ' : R →̇ P} (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → app' φ ψ ≈̇ app' φ' ψ')
  (⇒'-beta     : ∀ {R P Q : Ty'} (φ : R ×' P →̇ Q) (ψ : R →̇ P) → app' (lam' φ) ψ ≈̇ φ [ ⟨ id'[ R ] , ψ ⟩' ]')
  (⇒'-eta      : ∀ {R P Q : Ty'} (φ : R →̇ P ⇒' Q) → φ ≈̇ lam' (app' (φ [ π₁'[ P ] ]') π₂'[ R ]))
  (lam'-nat    : ∀ {R' R P Q : Ty'} (φ : R ×' P →̇ Q) (ψ : R' →̇ R) → lam' φ ∘ ψ ≈̇ lam' (φ ∘ ψ ×'-map id'[ P ]))
  (app'-nat    : ∀ {R' R P Q : Ty'} (φ : R →̇ P ⇒' Q) (ψ : R →̇ P) (ω : R' →̇ R) → app' φ ψ ∘ ω ≈̇ app' (φ ∘ ω) (ψ ∘ ω))

  (◯'_          : (P : Ty') → Ty')
  (letin' : {P Q R : Ty'} → (φ : P →̇ ◯' Q) → (ψ : (P ×' Q) →̇ R) → P →̇ ◯' R)
  (letin'-pres-≈̇ : {P Q R : Ty'} {φ φ' : P →̇ ◯' Q} {ψ ψ' : (P ×' Q) →̇ R} → (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → letin' φ ψ ≈̇ letin' φ' ψ')
  (letin'-nat    : ∀ {P P' Q R : Ty'} (φ : P →̇ ◯' Q) → (ψ : (P ×' Q) →̇ R) (ω : P' →̇ P) → letin' φ ψ ∘ ω ≈̇ letin' (φ ∘ ω) (ψ ∘ (ω ×'-map id'[ Q ])))
  (◯'-beta : ∀ {P Q R R' : Ty'} (t : P →̇ ◯' Q) (u : (P ×' Q) →̇ R) (u' : (P ×' R →̇ R'))
    → letin' (letin' t u) u' ≈̇ letin' t (u' ∘ ⟨ π₁'[ Q ] , u ⟩' ))
  (◯'-eta : ∀ {P : Ctx'} {Q : Ty'} (φ : P →̇ ◯' Q) → φ ≈̇ letin' φ π₂'[ P ])

  (N : Ty')
  where

open import Level using (0ℓ)

open import Relation.Binary using (IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Functor.Term
open import Functor.Term.Reduction

open import Semantics.Category.Evaluation.Functor.Base
    Ctx' _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ id'[_]
    []' unit' _×'_ ⟨_,_⟩' π₁'[_] π₂'[_]
    _⇒'_ lam' app'
    ◯'_ letin'
  renaming (module Eval to FunctorBaseEval)

open FunctorBaseEval N

∘-pres-≈̇-left : ∀ {P Q R : Ctx'} {ψ ψ' : Q →̇ R} (ψ≈̇ψ' : ψ ≈̇ ψ') (φ : P →̇ Q) → ψ ∘ φ ≈̇ ψ' ∘ φ
∘-pres-≈̇-left ψ≈̇ψ' φ = ∘-pres-≈̇ ψ≈̇ψ' (≈̇-refl {φ = φ})

∘-pres-≈̇-right : ∀ {P Q R : Ctx'} (ψ : Q →̇ R) {φ φ' : P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ ∘ φ'
∘-pres-≈̇-right ψ φ≈̇φ' = ∘-pres-≈̇ (≈̇-refl {φ = ψ}) φ≈̇φ'

abstract
  ⟨,⟩'-pres-≈̇-left : ∀ {R P Q : Ctx'} {φ φ' : R →̇ P} (φ≈̇φ' : φ ≈̇ φ') (ψ : R →̇ Q) → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ' , ψ ⟩'
  ⟨,⟩'-pres-≈̇-left ψ≈̇ψ' φ = ⟨,⟩'-pres-≈̇ ψ≈̇ψ' (≈̇-refl {φ = φ})

  ⟨,⟩'-pres-≈̇-right : ∀ {R P Q : Ctx'} (φ : R →̇ P) {ψ ψ' : R →̇ Q} (ψ≈̇ψ' : ψ ≈̇ ψ') → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ , ψ' ⟩'
  ⟨,⟩'-pres-≈̇-right ψ φ≈̇φ' = ⟨,⟩'-pres-≈̇ (≈̇-refl {φ = ψ}) φ≈̇φ'

abstract
  ×'-map-pres-≈̇ : {P Q P' Q' : Ctx'} {φ φ' : P →̇ P'} (φ≈̇φ' : φ ≈̇ φ') {ψ ψ' : Q →̇ Q'} (ψ≈̇ψ' : ψ ≈̇ ψ') → φ ×'-map ψ ≈̇ φ' ×'-map ψ'
  ×'-map-pres-≈̇ {φ = φ} {φ'} φ≈̇φ' {ψ} {ψ'} ψ≈̇ψ' = let open EqReasoning (→̇-setoid _ _) in begin
    φ ×'-map ψ                ≡⟨⟩
    ⟨ φ  ∘ π₁' , ψ  ∘ π₂' ⟩'  ≈⟨ ⟨,⟩'-pres-≈̇ (∘-pres-≈̇-left φ≈̇φ' π₁') (∘-pres-≈̇-left ψ≈̇ψ' π₂') ⟩
    ⟨ φ' ∘ π₁' , ψ' ∘ π₂' ⟩'  ∎

  ×'-map-pres-≈̇-left : {P Q P' : Ctx'} {φ φ' : P →̇ P'} (φ≈̇φ' : φ ≈̇ φ') (ψ : Q →̇ Q) → φ ×'-map ψ ≈̇ φ' ×'-map ψ
  ×'-map-pres-≈̇-left = λ φ≈̇φ' ψ → ×'-map-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

  ×'-map-pres-≈̇-right : {P Q Q' : Ctx'} (φ : P →̇ P) {ψ ψ' : Q →̇ Q'} (ψ≈̇ψ' : ψ ≈̇ ψ') → φ ×'-map ψ ≈̇ φ ×'-map ψ'
  ×'-map-pres-≈̇-right = λ φ ψ≈̇ψ' → ×'-map-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

  ×'-map-pres-id' : {P Q : Ctx'} → id'[ P ] ×'-map id'[ Q ] ≈̇ id'[ P ×' Q ]
  ×'-map-pres-id' {P} {Q} = let open EqReasoning (→̇-setoid _ _) in begin
    id' ×'-map id'              ≡⟨⟩
    ⟨ id' ∘ π₁' , id' ∘ π₂' ⟩'  ≈⟨ ⟨,⟩'-pres-≈̇ (id'-unit-left P π₁') (id'-unit-left Q π₂') ⟩
    ⟨ π₁'       , π₂'       ⟩'  ≈˘⟨ ⟨,⟩'-pres-≈̇ (id'-unit-right (P ×' Q) π₁') (id'-unit-right (P ×' Q) π₂') ⟩
    ⟨ π₁' ∘ id' , π₂' ∘ id' ⟩'  ≈˘⟨ ×'-eta ⟩
    id'                         ∎

abstract
  app'-pres-≈̇-left : ∀ {R : Ctx'} {P Q : Ty'} {φ φ' : R →̇ P ⇒' Q} (φ≈̇φ' : φ ≈̇ φ') (ψ : R →̇ P) → app' φ ψ ≈̇ app' φ' ψ
  app'-pres-≈̇-left φ≈̇φ' ψ = app'-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

  app'-pres-≈̇-right : ∀ {R : Ctx'} {P Q : Ty'} (φ : R →̇ P ⇒' Q) {ψ ψ' : R →̇ P} (ψ≈̇ψ' : ψ ≈̇ ψ') → app' φ ψ ≈̇ app' φ ψ'
  app'-pres-≈̇-right φ ψ≈̇ψ' = app'-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

abstract
  letin'-pres-≈̇-left : ∀ {P Q R : Ty'} {φ φ' : P →̇ ◯' Q} (φ≈̇φ' : φ ≈̇ φ') (ψ : (P ×' Q) →̇ R) → letin' φ ψ ≈̇ letin' φ' ψ
  letin'-pres-≈̇-left φ≈̇φ' ψ = letin'-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

  letin'-pres-≈̇-right : ∀ {P Q R : Ty'} (φ : P →̇ ◯' Q) {ψ ψ' : (P ×' Q) →̇ R} (ψ≈̇ψ' : ψ ≈̇ ψ')→ letin' φ ψ ≈̇ letin' φ ψ'
  letin'-pres-≈̇-right φ ψ≈̇ψ' = letin'-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

abstract
  evalWk-pres-id : ∀ (Γ : Ctx) → evalWk idWk[ Γ ] ≈̇ id'
  evalWk-pres-id []          = ≈̇-sym []'-eta
  evalWk-pres-id Γ@(Γ' `, a) = let open EqReasoning (Sub'-setoid Γ Γ) in begin
    evalWk (keep[ a ] idWk[ Γ' ])             ≈⟨ ×'-map-pres-≈̇-left (evalWk-pres-id Γ') id'[ evalTy a ] ⟩
    id'[ evalCtx Γ' ] ×'-map id'[ evalTy a ]  ≈⟨ ×'-map-pres-id' ⟩
    id'[ evalCtx Γ ]                          ∎

  evalWk-pres-∘-π₁ : evalWk (drop[ a ] w) ≈̇ evalWk w ∘ π₁'[ evalTy a ]
  evalWk-pres-∘-π₁ = ≈̇-refl

  evalWk-pres-×-map-id : evalWk (keep[ a ] w) ≈̇ evalWk w ×'-map id'[ evalTy a ]
  evalWk-pres-×-map-id = ≈̇-refl

  evalWk-pres-π₁ : ∀ (Γ : Ctx) (a : Ty) → evalWk (freshWk {Γ} {a}) ≈̇ π₁'[ evalTy a ]
  evalWk-pres-π₁ Γ a = let open EqReasoning (Sub'-setoid (Γ `, a) Γ) in begin
    evalWk (freshWk {Γ} {a})              ≈⟨ ∘-pres-≈̇-left (evalWk-pres-id Γ) π₁'[ evalTy a ] ⟩
    id'[ evalCtx Γ ] ∘ π₁'[ evalTy a ]  ≈⟨ id'-unit-left (evalCtx Γ) π₁'[ evalTy a ] ⟩
    π₁'[ evalTy a ]                     ∎

module _ {a : Ty} where
  abstract
    evalVar-pres-∘ : ∀ (w : Γ ⊆ Δ) (n : Var Γ a) → evalVar (wkVar w n) ≈̇ evalVar n ∘ evalWk w
    evalVar-pres-∘ (drop {Δ = Δ} {b} w) v = let open EqReasoning (Tm'-setoid (Δ `, b) a) in begin
      evalVar (wkVar (drop[ b ] w) v)                     ≈⟨ ∘-pres-≈̇-left (evalVar-pres-∘ w v) π₁'[ evalTy b ] ⟩
      (evalVar v ∘ evalWk w) ∘ π₁'[ evalTy b ]            ≈⟨ ∘-assoc (evalVar v) (evalWk w) π₁'[ evalTy b ] ⟩
      evalVar v ∘ evalWk (drop[ b ] w)                    ∎
    evalVar-pres-∘ (keep {Δ = Δ} {a} w) (zero {Γ}) = let open EqReasoning (Tm'-setoid (Δ `, a) a) in begin
      evalVar (wkVar (keep[ a ] w) (zero {Γ}))            ≈˘⟨ id'-unit-left (evalTy a) π₂'[ evalCtx Δ ] ⟩
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
  evalTm-pres-∘' {Δ = Δ} {a} w (letin {a = a'} t u) = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (letin t u))
      ≈⟨ letin'-pres-≈̇ (evalTm-pres-∘' w t) (evalTm-pres-∘' (keep w) u) ⟩
    letin' (evalTm t ∘ evalWk w) (evalTm u ∘ evalWk (keep[ a' ] w))
      ≈˘⟨ letin'-nat (evalTm t) (evalTm u) (evalWk w) ⟩
    evalTm (letin t u) [ evalWk w ]'
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
    evalSub (keepₛ {Δ} {Γ} {a} σ)    ≈⟨ ⟨,⟩'-pres-≈̇ (evalSub-pres-∘-π₁ σ a) (≈̇-sym (id'-unit-left (evalTy a) π₂'[ evalCtx Δ ])) ⟩
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
    evalSub idₛ[ Γ ]  ≈⟨ evalSub-pres-wk idWk[ Γ ] ⟩
    evalWk idWk[ Γ ]  ≈⟨ evalWk-pres-id Γ ⟩
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
  evalTm-pres-∘ (var v) σ = evalTm-pres-∘'' v σ
  evalTm-pres-∘ {a = a} {Δ} (lam {a = a'} t) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (lam t))
      ≈⟨ lam'-pres-≈̇ (evalTm-pres-∘ t (wkSub (freshWk {Δ} {a'}) σ `, var zero)) ⟩
    lam' (evalTm t [ evalSub (wkSub (freshWk {Δ} {a'}) σ `, var zero) ]')
      ≈⟨ lam'-pres-≈̇ (∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-left (evalSub-pres-∘' σ (freshWk {Δ} {a'})) π₂'[ evalCtx Δ ])) ⟩
    lam' (evalTm t [ ⟨ evalSub σ ∘ evalWk (freshWk {Δ} {a'}) , π₂'[ evalCtx Δ ] ⟩' ]' )
      ≈⟨ lam'-pres-≈̇ (∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-left (∘-pres-≈̇-right (evalSub σ) (evalWk-pres-π₁ Δ a')) π₂'[ evalCtx Δ ])) ⟩
    lam' (evalTm t [ ⟨ evalSub σ ∘ π₁'[ evalTy a' ] , π₂'[ evalCtx Δ ] ⟩' ]')
      ≈˘⟨ lam'-pres-≈̇ (∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-right (evalSub σ ∘ π₁'[ evalTy a' ]) (id'-unit-left (evalTy a') π₂'[ evalCtx Δ ]))) ⟩
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
  evalTm-pres-∘ {a = a} {Δ} (letin {a = a'} t u) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (letin t u))
      ≈⟨ letin'-pres-≈̇ (evalTm-pres-∘ t σ) (evalTm-pres-∘ u (keepₛ σ)) ⟩
    letin' (evalTm t [ evalSub σ ]') (evalTm u [ evalSub (wkSub (freshWk {Δ} {a'}) σ `, var zero) ]')
      ≈⟨ letin'-pres-≈̇-right _ (∘-pres-≈̇-right (evalTm u) (⟨,⟩'-pres-≈̇-left (evalSub-pres-∘' σ (freshWk {Δ} {a'})) π₂'[ evalCtx Δ ])) ⟩
    letin' (evalTm t [ evalSub σ ]') (evalTm u [ ⟨ evalSub σ ∘ evalWk (freshWk {Δ} {a'}) , π₂'[ evalCtx Δ ] ⟩' ]')
      ≈⟨ letin'-pres-≈̇-right _ ((∘-pres-≈̇-right (evalTm u) (⟨,⟩'-pres-≈̇-left (∘-pres-≈̇-right (evalSub σ) (evalWk-pres-π₁ Δ a')) π₂'[ evalCtx Δ ]))) ⟩
    letin' (evalTm t [ evalSub σ ]') (evalTm u [ ⟨ evalSub σ ∘ π₁'[ evalTy a' ] , π₂'[ evalCtx Δ ] ⟩' ]')
      ≈˘⟨ letin'-pres-≈̇-right _ (∘-pres-≈̇-right (evalTm u) ((⟨,⟩'-pres-≈̇-right (evalSub σ ∘ π₁'[ evalTy a' ]) (id'-unit-left (evalTy a') π₂'[ evalCtx Δ ])))) ⟩
    letin' (evalTm t [ evalSub σ ]') (evalTm u [ (evalSub σ) ×'-map id'[ evalTy a' ]  ]')
      ≈˘⟨ letin'-nat (evalTm t) (evalTm u) (evalSub σ) ⟩
    (evalTm (letin t u) [ evalSub σ ]')
      ∎

abstract
  evalTm-sound : (s : t ⟶ t') → evalTm t ≈̇ evalTm t'
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
  evalTm-sound (red-circ {Γ} {a} {b} {c} t u u') = let open EqReasoning (Tm'-setoid Γ (◯ c)) in begin
    evalTm (letin (letin t u) u')
      ≈⟨ ◯'-beta (evalTm t) (evalTm u) (evalTm u') ⟩
    letin' (evalTm t) (evalTm u' [ ⟨ π₁'[ evalTy a ] , evalTm u ⟩' ]')
      ≈˘⟨ letin'-pres-≈̇-right (evalTm t) (∘-pres-≈̇-right (evalTm u') (⟨,⟩'-pres-≈̇-left (id'-unit-left (evalCtx Γ) π₁'[ evalTy a ]) (evalTm u))) ⟩
    letin' (evalTm t) (evalTm u' [ ⟨ id' ∘ π₁'[ evalTy a ] , evalTm u ⟩' ]' )
      ≈˘⟨ letin'-pres-≈̇-right (evalTm t) (∘-pres-≈̇-right (evalTm u') (⟨,⟩'-pres-≈̇-left (∘-pres-≈̇ (evalSub-pres-id Γ) (≈̇-trans (∘-pres-≈̇-left (evalWk-pres-id Γ) π₁') (id'-unit-left (evalCtx Γ) π₁'))) (evalTm u))) ⟩
    letin' (evalTm t) (evalTm u' [ ⟨ evalSub idₛ[ Γ ] ∘ evalWk (freshWk {Γ = Γ} {a = a}) , evalTm u ⟩' ]' )
      ≈˘⟨ letin'-pres-≈̇-right (evalTm t) (∘-pres-≈̇-right (evalTm u') (⟨,⟩'-pres-≈̇-left (evalSub-pres-∘' idₛ[ Γ ] freshWk) (evalTm u))) ⟩
    letin' (evalTm t) (evalTm u' [ evalSub (wkSub freshWk (idₛ[ Γ ]) `, u) ]' )
      ≈˘⟨ letin'-pres-≈̇-right (evalTm t) (evalTm-pres-∘ u' (wkSub freshWk idₛ `, u)) ⟩
    letin' (evalTm t) (evalTm (substTm (wkSub freshWk (idₛ[ Γ ]) `, u) u'))
       ≡⟨⟩
    (evalTm (letin t (substTm (wkSub freshWk idₛ `, u) u'))) ∎
  evalTm-sound (exp-circ {Γ} {a} t) = let open EqReasoning (Tm'-setoid Γ (◯ a)) in begin
    evalTm t
      ≈⟨ ◯'-eta (evalTm t) ⟩
    letin' (evalTm t) π₂'[ evalCtx Γ ]
      ≡⟨ refl ⟩
    evalTm (letin t (var zero))
      ∎
  evalTm-sound (cong-lam s)            = lam'-pres-≈̇        (evalTm-sound s)
  evalTm-sound (cong-app1 {u = u} s)   = app'-pres-≈̇-left   (evalTm-sound s) (evalTm u)
  evalTm-sound (cong-app2 {t = t} s)   = app'-pres-≈̇-right  (evalTm t) (evalTm-sound s)
  evalTm-sound (cong-letin1 {u = u} s) = letin'-pres-≈̇-left   (evalTm-sound s) (evalTm u)
  evalTm-sound (cong-letin2 {t = t} s) = letin'-pres-≈̇-right  (evalTm t) (evalTm-sound s)
