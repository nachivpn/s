{-# OPTIONS --safe --without-K #-}

module MLC.Norm.Properties where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
  
open import MLC.Term
open import MLC.Term.NormalForm

open import MLC.Norm.Base

open import Data.Sum
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

-- "Relation constructor"
data RelC : Set₁ where
  nil : RelC
  id  : RelC
  _⊕_ : RelC → RelC → RelC 
  neu : RelC → RelC

⟦_⟧ : RelC → (Ctx → Ctx → Set) → (Ctx → Ctx → Set)
⟦ nil   ⟧ R = λ Γ Δ → Γ ≡ Δ
⟦ id    ⟧ R = R
⟦ F ⊕ G ⟧ R = λ Γ Δ → (⟦ F ⟧ R) Γ Δ ⊎ (⟦ G ⟧ R) Γ Δ
⟦ neu F ⟧ R = λ Γ Δ → ∃ (λ (a : Ty) → Ne Γ (◇ a) × (⟦ F ⟧ R) (Γ `, a) Δ )

data μ_ (F : RelC) : Ctx → Ctx → Set where 
  lfp : {Γ Δ : Ctx} → (⟦ F ⟧ (μ F)) Γ Δ → (μ F) Γ Δ
 
_⊲'_ : Ctx → Ctx → Set
_⊲'_ = μ (nil ⊕ neu id)

-- ⊲' and ⊲ are isomorphic
to : Γ ⊲ Δ → Γ ⊲' Δ
to nil = lfp (inj₁ ≡-refl)
to (cons x m) = lfp (inj₂ (-, x , to m))

from : Γ ⊲' Δ → Γ ⊲ Δ
from (lfp (inj₁ ≡-refl)) = nil
from (lfp (inj₂ (_ , n , m'))) = cons n (from m')

to-from-is-id : (m : Γ ⊲ Δ) → from (to m) ≡ m
to-from-is-id nil = ≡-refl
to-from-is-id (cons x m) = cong₂ cons ≡-refl (to-from-is-id m)

from-to-is-id : (m' : Γ ⊲' Δ) → to (from m') ≡ m'
from-to-is-id (lfp (inj₁ ≡-refl)) = ≡-refl
from-to-is-id (lfp (inj₂ (_ , n , m'))) = cong lfp (cong inj₂ (cong (λ z → (-, n , z)) (from-to-is-id m')))
