{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_)

module Semantics.Kripke.IFrame where

-- Intuitionistic Frame
record IFrame (W : Set) (_⊆_ : W → W → Set) : Set where
  field
    ⊆-trans            : ∀ {Γ Γ' Γ'' : W} → (w : Γ ⊆ Γ') → (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ''
    ⊆-trans-assoc      : ∀ {Γ Γ' Γ'' Γ''' : W} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (w'' : Γ'' ⊆ Γ''') → ⊆-trans (⊆-trans w w') w'' ≡ ⊆-trans w (⊆-trans w' w'')
    ⊆-refl             : ∀ {Γ : W} → Γ ⊆ Γ
    ⊆-refl-unit-right  : ∀ {Γ Γ' : W} (w : Γ ⊆ Γ') → ⊆-trans ⊆-refl w ≡ w
    ⊆-refl-unit-left   : ∀ {Γ Γ' : W} (w : Γ ⊆ Γ') → ⊆-trans w ⊆-refl ≡ w
