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
  open IsStrong isStrong renaming (letin' to sletin' ; letin'-nat₂ to sletin'-nat₂)
  open IsMultiplicative isMultiplicative

  field
    ℱ'-strength-mult :{P Q : Obj} → ℱ'-mult[ P ×' Q ] ∘ ℱ'-map (ℱ'-strength[ P , Q ]) ∘ ℱ'-strength[ P , ℱ' Q ]
      ≈̇ ℱ'-strength[ P , Q ] ∘ (id'[ P ] ×'-map ℱ'-mult[ Q ])

  letin' : {P Q R : Obj} (φ : P →̇ ℱ' Q) → (ψ : (P ×' Q) →̇ ℱ' R) → P →̇ ℱ' R
  letin' {_} {_} {R} φ ψ = ℱ'-mult[ R ] ∘ sletin' φ ψ

  abstract
    ℱ'-comm : {P Q R S : Obj} (φ : P →̇ ℱ' Q) (ψ : (P ×' Q) →̇ ℱ' R) (ϕ : (P ×' R) →̇ ℱ' S)
      → sletin' (letin' φ ψ) ϕ ≈̇ letin' φ (sletin' ψ (ϕ ∘ (π₁' ×'-map id')))
    ℱ'-comm {P} {Q} {R} {S} φ ψ ϕ = let
      f : P →̇ ℱ' (P ×' Q)
      f = ℱ'-strength[ P , Q ] ∘ ⟨ id' , φ ⟩'
      open EqReasoning (→̇-setoid P (ℱ' ℱ' S)) in begin
      sletin' (letin' φ ψ) ϕ
        -- defn.
        ≡⟨⟩
      (ℱ'-map ϕ ∘ ℱ'-strength) ∘ ⟨ id' , ℱ'-mult ∘ sletin' φ ψ ⟩'
        -- cartesian crunching
        ≈˘⟨ ∘-pres-≈̇-right _ (≈̇-trans (×'-map-∘-⟨,⟩' _ _ _ _) (⟨,⟩'-pres-≈̇-left (id'-unit-left _ _) _)) ⟩
      (ℱ'-map ϕ ∘ ℱ'-strength) ∘ id' ×'-map ℱ'-mult ∘ ⟨ id' , sletin' φ ψ ⟩'
        -- assoc
        ≈⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (≈̇-sym (∘-assoc _ _ _ ))) ⟩
      ℱ'-map ϕ ∘ (ℱ'-strength[ P , R ] ∘ id' ×'-map ℱ'-mult) ∘ ⟨ id' , sletin' φ ψ ⟩'
        -- strong multiplicative
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left ℱ'-strength-mult _) ⟩
      ℱ'-map ϕ ∘ (ℱ'-mult[ P ×' R ]  ∘ ℱ'-map ℱ'-strength[ P , R ] ∘ ℱ'-strength[ P , ℱ' R ]) ∘ ⟨ id' , sletin' φ ψ ⟩'
        -- assoc.
        ≈⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩
      ℱ'-map ϕ ∘ ℱ'-mult  ∘ (ℱ'-map ℱ'-strength[ P , R ] ∘ ℱ'-strength) ∘ ⟨ id' , sletin' φ ψ ⟩'
        -- defn.
        ≡⟨⟩
      ℱ'-map ϕ ∘ ℱ'-mult  ∘ sletin' (sletin' φ ψ) ℱ'-strength
        -- strength
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (ℱ'-beta _ _ _)) ⟩
      ℱ'-map ϕ ∘ ℱ'-mult ∘ sletin' φ (ℱ'-strength ∘ ⟨ π₁' , ψ ⟩')
        -- defn.
        ≡⟨⟩
      ℱ'-map ϕ ∘ ℱ'-mult ∘ ((ℱ'-map (ℱ'-strength ∘ ⟨ π₁' , ψ ⟩') ∘ ℱ'-strength) ∘ ⟨ id' , φ ⟩')
        -- assoc.
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (∘-assoc _ _ _)) ⟩
      ℱ'-map ϕ ∘ ℱ'-mult  ∘ ℱ'-map (ℱ'-strength ∘ ⟨ π₁' , ψ ⟩') ∘ (ℱ'-strength) ∘ ⟨ id' , φ ⟩'
        -- defn.
        ≡⟨⟩
      ℱ'-map ϕ ∘ ℱ'-mult  ∘ ℱ'-map (ℱ'-strength ∘ ⟨ π₁' , ψ ⟩') ∘ f
        -- assoc.
          ≈˘⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩
      ℱ'-map ϕ ∘ (ℱ'-mult ∘ ℱ'-map (ℱ'-strength ∘ ⟨ π₁' , ψ ⟩')) ∘ f
        -- cartesian crunching
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (∘-pres-≈̇-right _ (ℱ'-map-pres-≈̇ (∘-pres-≈̇-right _
             (≈̇-trans (×'-map-∘-⟨,⟩' _ _ _ _) (⟨,⟩'-pres-≈̇ (id'-unit-right _ _) (id'-unit-left _ _)))))) _) ⟩
      ℱ'-map ϕ ∘ (ℱ'-mult ∘ ℱ'-map (ℱ'-strength ∘ ((π₁' ×'-map id') ∘ ⟨ id' , ψ ⟩'))) ∘ f
        -- functoriality
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (∘-pres-≈̇-right _ (≈̇-trans
             (ℱ'-map-pres-∘ _ _)
             (≈̇-trans (∘-pres-≈̇-right _ (ℱ'-map-pres-∘ _ _)) (≈̇-sym (∘-assoc _ _ _))))) _) ⟩
      ℱ'-map ϕ ∘ (ℱ'-mult ∘ (ℱ'-map (ℱ'-strength) ∘ ℱ'-map (π₁' ×'-map id')) ∘ (ℱ'-map ⟨ id' , ψ ⟩')) ∘ f
        -- strength
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (∘-pres-≈̇-right _ (∘-pres-≈̇-left (≈̇-trans
             (≈̇-sym (ℱ'-map-pres-∘ _ _))
             (≈̇-trans (ℱ'-map-pres-≈̇ (ℱ'-strength-natural₁ _)) (ℱ'-map-pres-∘ _ _))) _)) _) ⟩
      ℱ'-map ϕ ∘ (ℱ'-mult ∘ (ℱ'-map (ℱ'-map (π₁' ×'-map id')) ∘ (ℱ'-map ℱ'-strength)) ∘ (ℱ'-map ⟨ id' , ψ ⟩')) ∘ f
        -- assoc.
        ≈⟨ ∘-pres-≈̇-right _ (≈̇-trans
             (∘-assoc _ _ _) (≈̇-trans (∘-pres-≈̇-right _ (≈̇-trans (∘-assoc _ _ _) (∘-assoc _ _ _)))
             (≈̇-sym (∘-assoc _ _ _)))) ⟩
      ℱ'-map ϕ ∘ (ℱ'-mult[ P ×' R ] ∘ ℱ'-map (ℱ'-map (π₁' ×'-map id'))) ∘ (ℱ'-map ℱ'-strength[ P ×' Q , R ]) ∘ ℱ'-map ⟨ id' , ψ ⟩' ∘ f
        -- multiplicative
        ≈⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (ℱ'-mult-natural _) _) ⟩
      ℱ'-map ϕ ∘ (ℱ'-map (π₁' ×'-map id') ∘ ℱ'-mult[ (P ×' Q) ×' R ]) ∘ (ℱ'-map ℱ'-strength[ P ×' Q , R ]) ∘ ℱ'-map ⟨ id' , ψ ⟩' ∘ f
        --  assoc.
        ≈˘⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (∘-pres-≈̇-right _ (∘-assoc _ _ _))) ⟩
      (ℱ'-map ϕ ∘ ℱ'-map (π₁' ×'-map id') ∘ ℱ'-mult) ∘ (ℱ'-map ℱ'-strength ∘ ℱ'-map ⟨ id' , ψ ⟩') ∘ f
        -- functoriality
        ≈˘⟨ ∘-pres-≈̇
            (≈̇-trans (∘-pres-≈̇-left (ℱ'-map-pres-∘ _ _) _ ) (∘-assoc _ _ _))
            (∘-pres-≈̇-left (ℱ'-map-pres-∘ _ _) _) ⟩
      (ℱ'-map (ϕ ∘ π₁' ×'-map id') ∘ ℱ'-mult) ∘ ℱ'-map (ℱ'-strength ∘ ⟨ id' , ψ ⟩') ∘ f
        -- multiplicative
        ≈˘⟨ ∘-pres-≈̇-left (ℱ'-mult-natural _) _ ⟩
      (ℱ'-mult ∘ ℱ'-map (ℱ'-map (ϕ ∘ π₁' ×'-map id'))) ∘ ℱ'-map (ℱ'-strength ∘ ⟨ id' , ψ ⟩') ∘ f
        -- assoc.
        ≈⟨ ≈̇-trans (∘-assoc _ _ _) (∘-pres-≈̇-right _ (≈̇-sym (∘-assoc _ _ _))) ⟩
      ℱ'-mult ∘ (ℱ'-map (ℱ'-map (ϕ ∘ π₁' ×'-map id')) ∘ ℱ'-map (ℱ'-strength ∘ ⟨ id' , ψ ⟩')) ∘ f
        -- functoriality
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-pres-≈̇-left (≈̇-trans (ℱ'-map-pres-≈̇ (∘-assoc _ _ _)) (ℱ'-map-pres-∘ _ _)) _) ⟩
      ℱ'-mult ∘ ℱ'-map ((ℱ'-map (ϕ ∘ π₁' ×'-map id') ∘ ℱ'-strength) ∘ ⟨ id' , ψ ⟩') ∘ f
        ≡⟨⟩
      ℱ'-mult ∘ ℱ'-map ((ℱ'-map (ϕ ∘ π₁' ×'-map id') ∘ ℱ'-strength) ∘ ⟨ id' , ψ ⟩') ∘ (ℱ'-strength ∘ ⟨ id' , φ ⟩')
        -- assoc.
        ≈˘⟨ ∘-pres-≈̇-right _ (∘-assoc _ _ _) ⟩
      ℱ'-mult ∘ ((ℱ'-map ((ℱ'-map (ϕ ∘ π₁' ×'-map id') ∘ ℱ'-strength) ∘ ⟨ id' , ψ ⟩')) ∘ ℱ'-strength) ∘ ⟨ id' , φ ⟩'
        -- defn.
        ≡⟨⟩
      letin' φ (sletin' ψ (ϕ ∘ (π₁' ×'-map id'))) ∎

    ℱ'-ass : {P Q R S : Obj} (φ : P →̇ ℱ' Q) (ψ : (P ×' Q) →̇ ℱ' R) (ϕ : (P ×' R) →̇ ℱ' S)
        → letin' (letin' φ ψ) ϕ ≈̇ letin' φ (letin' ψ (ϕ ∘ (π₁' ×'-map id'[ R ])))
    ℱ'-ass {P} {Q} {R} {S} φ ψ ϕ = let open EqReasoning (→̇-setoid P (ℱ' S)) in begin
      letin' (letin' φ ψ) ϕ
        -- defn. (of top-most letin')
        ≡⟨⟩
      ℱ'-mult ∘ sletin' (letin' φ ψ) ϕ
        -- sletin' commutes with letin' in a way
        ≈⟨ ∘-pres-≈̇-right _ (ℱ'-comm _ _ _) ⟩
      ℱ'-mult ∘ letin' φ (sletin' ψ (ϕ ∘ (π₁' ×'-map id')))
        -- defn.
        ≡⟨⟩
      ℱ'-mult ∘ ℱ'-mult[ ℱ' S ] ∘ sletin' φ (sletin' ψ (ϕ ∘ (π₁' ×'-map id')))
        -- assoc.
        ≈˘⟨ ∘-assoc _ _ _ ⟩
      (ℱ'-mult[ S ] ∘ ℱ'-mult[ ℱ' S ]) ∘ sletin' φ (sletin' ψ (ϕ ∘ (π₁' ×'-map id')))
        -- multiplicative (is assoc.)
        ≈˘⟨ ∘-pres-≈̇-left ℱ'-mult-assoc _ ⟩
      (ℱ'-mult[ S ] ∘ ℱ'-map ℱ'-mult[ S ]) ∘ sletin' φ (sletin' ψ (ϕ ∘ (π₁' ×'-map id')))
        -- assoc.
        ≈⟨ ∘-assoc _ _ _ ⟩
      ℱ'-mult[ S ] ∘ ℱ'-map ℱ'-mult[ S ] ∘ sletin' φ (sletin' ψ (ϕ ∘ (π₁' ×'-map id')))
        -- strength
        ≈⟨ ∘-pres-≈̇-right _ (sletin'-nat₂ _ _ _) ⟩
      ℱ'-mult ∘ sletin' φ (ℱ'-mult ∘ sletin' ψ (ϕ ∘ (π₁' ×'-map id')))
        -- defn.
        ≡⟨⟩
      letin' φ (letin' ψ (ϕ ∘ (π₁' ×'-map id'[ R ]))) ∎
