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
  open IsStrong isStrong renaming (letin' to sletin')
  open IsPointed isPointed
  open IsMultiplicative isMultiplicative
  open IsStrongPointed isStrongPointed
  open IsStrongMultiplicative isStrongMultiplicative
  open IsMonad isMonad

  abstract
    ℱ'-red : {P Q R : Obj} (φ : P →̇ Q) (ψ : (P ×' Q) →̇ ℱ' R) → letin' (ℱ'-return[ Q ] ∘ φ) ψ ≈̇ (ψ ∘ ⟨ id'[ P ] , φ ⟩')
    ℱ'-red {P} {Q} {R} φ ψ = let open EqReasoning (→̇-setoid P (ℱ' R)) in begin
      ℱ'-join ∘ sletin' (ℱ'-return[ Q ] ∘ φ) ψ
        -- defn.
        ≡⟨⟩
      ℱ'-mult[ R ] ∘ (ℱ'-map ψ ∘ ℱ'-strength[ P , Q ]) ∘ ⟨ id'[ P ] , ℱ'-return[ Q ] ∘ φ ⟩'
        -- assoc
        ≈⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩        
      ℱ'-mult[ R ] ∘ ℱ'-map ψ ∘ ℱ'-strength[ P , Q ] ∘ ⟨ id'[ P ] , ℱ'-return[ Q ] ∘ φ ⟩'
        -- cartesian crunching prep.
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (⟨,⟩'-pres-≈̇-left (id'-unit-left P _) _))) ⟩
      (ℱ'-mult[ R ] ∘ ℱ'-map ψ ∘ ℱ'-strength[ P , Q ] ∘ ⟨ id'[ P ] ∘ id'[ P ] , ℱ'-return[ Q ] ∘ φ ⟩')
        -- cartesian crunching
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (×'-map-∘-⟨,⟩' _ _ _ _))) ⟩
      ℱ'-mult[ R ] ∘ ℱ'-map ψ ∘ ℱ'-strength[ P , Q ] ∘ (id'[ P ] ×'-map ℱ'-return[ Q ] ) ∘ ⟨ id'[ P ] , φ ⟩'
        -- strong-pointedness
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (≈̇-trans (≈̇-sym (∘-assoc _ _ _)) (∘-pres-≈̇-left ℱ'-strength-point _)))  ⟩        
      ℱ'-mult[ R ] ∘ ℱ'-map ψ ∘ ℱ'-return[ P ×' Q ] ∘ ⟨ id'[ P ] , φ ⟩'
        -- assoc
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩
      ℱ'-mult[ R ] ∘ (ℱ'-map ψ ∘ ℱ'-return[ P ×' Q ]) ∘ ⟨ id'[ P ] , φ ⟩'
        -- return is natural
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (ℱ'-point-natural _) _) ⟩
      ℱ'-mult[ R ] ∘ (ℱ'-return[ ℱ' R ] ∘ ψ) ∘ ⟨ id'[ P ] , φ ⟩'
        -- assoc
        ≈˘⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (≈̇-sym (∘-assoc _ _ _))) ⟩
      (ℱ'-mult[ R ] ∘ ℱ'-return[ ℱ' R ]) ∘ ψ ∘ ⟨ id'[ P ] , φ ⟩'
        -- right unit of monad
        ≈⟨ ∘-pres-≈̇-left ℱ'-return-unit-right _ ⟩
      id'[ ℱ' R ] ∘ ψ ∘ ⟨ id'[ P ] , φ ⟩'
        -- unit of ∘ 
        ≈⟨ id'-unit-left (ℱ' R) _ ⟩
      ψ ∘ ⟨ id'[ P ] , φ ⟩' ∎

    ℱ'-exp : {P Q : Obj} (φ : P →̇ ℱ' Q) → letin' φ (ℱ'-return[ Q ] ∘ π₂') ≈̇ φ
    ℱ'-exp {P} {Q} φ = let open EqReasoning (→̇-setoid P (ℱ' Q)) in begin
      letin' φ (ℱ'-return ∘ π₂')
        -- defn.
        ≡⟨⟩
      ℱ'-join ∘ (ℱ'-map (ℱ'-return ∘ π₂') ∘ ℱ'-strength) ∘ ⟨ id' , φ ⟩'
        -- functoriality
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (∘-pres-≈̇-left (ℱ'-map-pres-∘ _ _) _) _) ⟩
      ℱ'-join ∘ ((ℱ'-map ℱ'-return ∘ ℱ'-map π₂') ∘ ℱ'-strength) ∘ ⟨ id' , φ ⟩'
        -- assoc
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (∘-assoc _ _ _) _) ⟩
      ℱ'-join ∘ (ℱ'-map ℱ'-return ∘ (ℱ'-map π₂' ∘ ℱ'-strength)) ∘ ⟨ id' , φ ⟩'
        -- strength coherence
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (∘-pres-≈̇-right _ ℱ'-strength-π₂) _) ⟩
      ℱ'-join ∘ (ℱ'-map ℱ'-return ∘ π₂') ∘ ⟨ id' , φ ⟩'
        -- assoc
        ≈⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩
      ℱ'-join ∘ ℱ'-map ℱ'-return ∘ (π₂' ∘ ⟨ id' , φ ⟩')
        -- cartesian crunching
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (×'-beta-right _)) ⟩
      ℱ'-join ∘ ℱ'-map ℱ'-return ∘ φ
        -- assoc
        ≈˘⟨ ∘-assoc _ _ _ ⟩
      (ℱ'-join ∘ ℱ'-map ℱ'-return) ∘ φ
        -- left unit of monad
        ≈⟨ ∘-pres-≈̇-left ℱ'-return-unit-left _ ⟩
      id' ∘ φ
        -- unit of ∘
        ≈⟨ id'-unit-left _ _ ⟩
      φ ∎
