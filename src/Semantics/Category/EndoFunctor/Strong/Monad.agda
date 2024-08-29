{-# OPTIONS  --safe --without-K #-}

module Semantics.Category.EndoFunctor.Strong.Monad where

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Pointed
open import Semantics.Category.EndoFunctor.Multiplicative
open import Semantics.Category.EndoFunctor.Monad
open import Semantics.Category.EndoFunctor.Strong.Base
open import Semantics.Category.EndoFunctor.Strong.Pointed
open import Semantics.Category.EndoFunctor.Strong.Multiplicative

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

record IsStrongMonad {C : Category} {isCartesian : IsCartesian C} (F : EndoFunctor C)
  {isStrong : IsStrong isCartesian F} {isPointed : IsPointed F} {isMultiplicative : IsMultiplicative F}
  (isStrongPointed : IsStrongPointed F isStrong isPointed)
  (isStrongMultiplicative : IsStrongMultiplicative F isStrong isMultiplicative)
  (isMonad : IsMonad isPointed isMultiplicative) : Set₂ where
  
  open Category C
  open IsCartesian isCartesian
  open EndoFunctor F
  open IsStrong isStrong renaming (letin' to sletin') hiding (exp-dia' ; red-dia')
  open IsStrongPointed isStrongPointed public
  open IsStrongMultiplicative isStrongMultiplicative public
  open IsMonad isMonad public

  abstract
    red-dia' : {P Q R : Obj} (φ : P →̇ Q) (ψ : (P ×' Q) →̇ ℱ' R) → letin' (return' φ) ψ ≈̇ (ψ ∘ ⟨ id'[ P ] , φ ⟩')
    red-dia' {P} {Q} {R} φ ψ = let open EqReasoning (→̇-setoid P (ℱ' R)) in begin
      join ∘ sletin' (return' φ) ψ
        -- defn.
        ≡⟨⟩
      join[ R ] ∘ (map ψ ∘ strength[ P , Q ]) ∘ ⟨ id'[ P ] , point[ Q ] ∘ φ ⟩'
        -- assoc
        ≈⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩        
      join[ R ] ∘ map ψ ∘ strength[ P , Q ] ∘ ⟨ id'[ P ] , point[ Q ] ∘ φ ⟩'
        -- cartesian crunching prep.
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (⟨,⟩'-pres-≈̇-left (∘-unit-left P _) _))) ⟩
      (join[ R ] ∘ map ψ ∘ strength[ P , Q ] ∘ ⟨ id'[ P ] ∘ id'[ P ] , point[ Q ] ∘ φ ⟩')
        -- cartesian crunching
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (×'-map-∘-⟨,⟩' _ _ _ _))) ⟩
      join[ R ] ∘ map ψ ∘ strength[ P , Q ] ∘ (id'[ P ] ×'-map point[ Q ] ) ∘ ⟨ id'[ P ] , φ ⟩'
        -- strong-pointedness
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (≈̇-trans (≈̇-sym (∘-assoc _ _ _)) (∘-pres-≈̇-left strength-point _)))  ⟩        
      join[ R ] ∘ map ψ ∘ point[ P ×' Q ] ∘ ⟨ id'[ P ] , φ ⟩'
        -- assoc
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩
      join[ R ] ∘ (map ψ ∘ point[ P ×' Q ]) ∘ ⟨ id'[ P ] , φ ⟩'
        -- return is natural
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (point-natural _) _) ⟩
      join[ R ] ∘ (point[ ℱ' R ] ∘ ψ) ∘ ⟨ id'[ P ] , φ ⟩'
        -- assoc
        ≈˘⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (≈̇-sym (∘-assoc _ _ _))) ⟩
      (join[ R ] ∘ point[ ℱ' R ]) ∘ ψ ∘ ⟨ id'[ P ] , φ ⟩'
        -- right unit of monad
        ≈⟨ ∘-pres-≈̇-left join-unit-left _ ⟩
      id'[ ℱ' R ] ∘ ψ ∘ ⟨ id'[ P ] , φ ⟩'
        -- unit of ∘ 
        ≈⟨ ∘-unit-left (ℱ' R) _ ⟩
      ψ ∘ ⟨ id'[ P ] , φ ⟩' ∎

    exp-dia' : {P Q : Obj} (φ : P →̇ ℱ' Q) → φ ≈̇ letin' φ (return' π₂')
    exp-dia' {P} {Q} φ = ≈̇-sym let open EqReasoning (→̇-setoid P (ℱ' Q)) in begin
      letin' φ (return' π₂')
        -- defn.
        ≡⟨⟩
      join ∘ (map (point ∘ π₂') ∘ strength) ∘ ⟨ id' , φ ⟩'
        -- functoriality
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (∘-pres-≈̇-left (map-pres-∘ _ _) _) _) ⟩
      join ∘ ((map point ∘ map π₂') ∘ strength) ∘ ⟨ id' , φ ⟩'
        -- assoc
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (∘-assoc _ _ _) _) ⟩
      join ∘ (map point ∘ (map π₂' ∘ strength)) ∘ ⟨ id' , φ ⟩'
        -- strength coherence
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (∘-pres-≈̇-right _ strength-π₂) _) ⟩
      join ∘ (map point ∘ π₂') ∘ ⟨ id' , φ ⟩'
        -- assoc
        ≈⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩
      join ∘ map point ∘ (π₂' ∘ ⟨ id' , φ ⟩')
        -- cartesian crunching
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (×'-beta-right _)) ⟩
      join ∘ map point ∘ φ
        -- assoc
        ≈˘⟨ ∘-assoc _ _ _ ⟩
      (join ∘ map point) ∘ φ
        -- left unit of monad
        ≈⟨ ∘-pres-≈̇-left join-unit-right _ ⟩
      id' ∘ φ
        -- unit of ∘
        ≈⟨ ∘-unit-left _ _ ⟩
      φ ∎
