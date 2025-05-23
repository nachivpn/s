{-# OPTIONS --safe --without-K #-}
module PUtil where

open import Data.Product            using (Σ ; _,_ ; proj₁ ; proj₂ ; ∃ ; _×_)
open import Data.Product.Properties using (Σ-≡,≡↔≡; ×-≡,≡↔≡)

open import Function using (Inverse)

open import Relation.Binary.PropositionalEquality using (_≡_ ; sym ; trans ; subst)
open import PEUtil

module _ {a} {b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B} where
  open import Function
  open import Data.Product.Properties
  open Inverse (Σ-≡,≡↔≡ {p₁ = p₁} {p₂ = p₂}) public
    using    ()
    renaming (to to Σ-≡,≡→≡)

×-≡,≡→≡ : {A B : Set} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : A × B} → a₁ ≡ a₂ × b₁ ≡ b₂ → p₁ ≡ p₂
×-≡,≡→≡ = ×-≡,≡↔≡ .Inverse.to

Σ×-≡,≡,≡→≡ : {A : Set} {B B' : A → Set} {p₁@(a₁ , b₁ , b₁') p₂@(a₂ , b₂ , b₂') : ∃ λ (a : A) → B a × B' a} → (∃ λ (p : a₁ ≡ a₂) → subst B p b₁ ≡ b₂ × subst B' p b₁' ≡ b₂') → p₁ ≡ p₂
Σ×-≡,≡,≡→≡ {A} {_B} {_B'} {p₁} {p₂} (p , q , q') = Σ-≡,≡→≡ (p , ×-≡,≡→≡ (˘trans (subst-application′ proj₁ p) q , ˘trans (subst-application′ proj₂ p) q'))

Σ×-≡,≡,≡→≡˘ : {A : Set} {B B' : A → Set} {p₁@(a₁ , b₁ , b₁') p₂@(a₂ , b₂ , b₂') : ∃ λ (a : A) → B a × B' a} → (∃ λ (p : a₁ ≡ a₂) → subst B p b₁ ≡ b₂ × subst B' p b₁' ≡ b₂') → p₂ ≡ p₁
Σ×-≡,≡,≡→≡˘ p = sym (Σ×-≡,≡,≡→≡ p)
