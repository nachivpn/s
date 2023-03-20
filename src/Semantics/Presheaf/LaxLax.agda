{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.EndoFunctor

module Semantics.Presheaf.LaxLax
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (⊆-trans           : ∀ {Γ Γ' Γ'' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  (⊆-trans-assoc     : ∀ {Γ Γ' Γ'' Γ''' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (w'' : Γ'' ⊆ Γ''') → ⊆-trans (⊆-trans w w') w'' ≡ ⊆-trans w (⊆-trans w' w''))
  (⊆-refl            : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-refl-unit-left  : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans w ⊆-refl ≡ w)
  (⊆-refl-unit-right : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans ⊆-refl w ≡ w)
  (_R_               : (Γ Δ : C) → Set)
  where

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base C _⊆_ ⊆-refl ⊆-trans

open import Semantics.Presheaf.CartesianClosure C _⊆_ ⊆-trans ⊆-trans-assoc ⊆-refl ⊆-refl-unit-left ⊆-refl-unit-right

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    Θ Θ' Θ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'    : Psh
    𝒬 𝒬'     : Psh
    ℛ ℛ' ℛ'' : Psh
    s s'       : 𝒫 →̇ 𝒬
    t t'       : 𝒫 →̇ 𝒬
    u u'       : 𝒫 →̇ 𝒬

module _ where

  record ◇'-Fam (𝒫 : Psh) (Γ : C) : Set where
    constructor elem
    field
      triple : Σ λ Δ → (Γ R Δ) × 𝒫 ₀ Δ

  open ◇'-Fam

  record _◇'-≋_ {𝒫 : Psh} {Γ : C} (x y : ◇'-Fam 𝒫 Γ) : Set where
    constructor proof
    field
      pw : let (Δ , r , p) = x .triple ; (Δ' , r' , p') = y. triple
        in ∃ λ Δ≡Δ' → subst (_ R_) Δ≡Δ' r ≡ r' ∧ subst (𝒫 ₀_) Δ≡Δ' p ≋[ 𝒫 ] p'

  abstract
    ◇'-≋-refl : {x : ◇'-Fam 𝒫 Γ} → x ◇'-≋ x
    ◇'-≋-refl {𝒫} = proof (refl , refl , ≋[ 𝒫 ]-refl)

    ◇'-≋-sym : {x y : ◇'-Fam 𝒫 Γ} → x ◇'-≋ y → y ◇'-≋ x
    ◇'-≋-sym {𝒫} (proof (refl , refl , p)) = proof (refl , refl , ≋[ 𝒫 ]-sym p)

    ◇'-≋-trans : {x y z : ◇'-Fam 𝒫 Γ} → x ◇'-≋ y → y ◇'-≋ z → x ◇'-≋ z
    ◇'-≋-trans {𝒫} (proof (refl , refl , p)) (proof (refl , refl , q)) = proof (refl , refl , ≋[ 𝒫 ]-trans p q)

    ≡-to-◇'-≋ : {x y : ◇'-Fam 𝒫 Γ} → x ≡ y → x ◇'-≋ y
    ≡-to-◇'-≋ refl = ◇'-≋-refl

    ◇'-≋-equiv : IsEquivalence (_◇'-≋_ {𝒫} {Γ})
    ◇'-≋-equiv = record
      { refl  = ◇'-≋-refl
      ; sym   = ◇'-≋-sym
      ; trans = ◇'-≋-trans
      }

  ◇'-≋[]-syn : (𝒫 : Psh) → (x y : ◇'-Fam 𝒫 Γ) → Set
  ◇'-≋[]-syn {Γ = Γ} 𝒫 = _◇'-≋_ {𝒫} {Γ}

  ◇'-map : (t : 𝒫 →̇ 𝒬) → ({Γ : C} → ◇'-Fam 𝒫 Γ → ◇'-Fam 𝒬 Γ)
  ◇'-map t (elem (Δ , r , p)) = elem (Δ , r , t .apply p)

  syntax ◇'-≋[]-syn 𝒫 x y = x ◇'-≋[ 𝒫 ] y

  abstract

    ◇'-map-pres-≋ : (t : 𝒫 →̇ 𝒬) → {p p' : ◇'-Fam 𝒫 Γ} → p ◇'-≋[ 𝒫 ] p' → (◇'-map t p) ◇'-≋[ 𝒬 ] (◇'-map t p')
    ◇'-map-pres-≋ t (proof (refl , refl , p≋p')) = proof (refl , refl , t .apply-≋ p≋p')

    ◇'-map-pres-≈̇ : {t t' : 𝒫 →̇ 𝒬} → t ≈̇ t' → ∀ (p : ◇'-Fam 𝒫 Γ) → ◇'-map t p ◇'-≋[ 𝒬 ] ◇'-map t' p
    ◇'-map-pres-≈̇ {𝒫} t≈̇t' (elem (Δ , r , p)) = proof (refl , (refl , apply-sq t≈̇t' ≋[ 𝒫 ]-refl))

record ◯'-Fam (𝒫 : Psh) (Γ : C) : Set where
  constructor elem
  field
      fun : {Γ' : C} → (w : Γ ⊆ Γ') → ◇'-Fam 𝒫 Γ'

open ◯'-Fam using () renaming (fun to apply-◯) public

record _◯'-≋_ {𝒫 : Psh} {Γ : C} (f f' : ◯'-Fam 𝒫 Γ) : Set where
    constructor proof
    field
      pw : {Γ' : C} → (w : Γ ⊆ Γ') → (f .apply-◯ {Γ'} w) ◇'-≋[ 𝒫 ] (f' .apply-◯ w)

open _◯'-≋_ using (pw) public

◯'_ : (𝒫 : Psh) → Psh -- type \bigcirc or \ci5
◯' 𝒫 = record
  { Fam           = ◯'-Fam 𝒫
  ; _≋_           = _◯'-≋_
  ; ≋-equiv       = ≋-equiv
  ; wk            = wk
  ; wk-pres-≋     = wk-pres-≋
  ; wk-pres-refl  = wk-pres-refl
  ; wk-pres-trans = wk-pres-trans
  }
  where
    abstract
      ≋-equiv : (Γ : C) → IsEquivalence (_◯'-≋_ {𝒫} {Γ})
      ≋-equiv = λ Γ → record
        { refl  = proof λ _w → ◇'-≋-refl
        ; sym   = λ f≋f' → proof λ w → ◇'-≋-sym (f≋f' .pw w)
        ; trans = λ f≋f' f'≋f'' → proof λ w → ◇'-≋-trans (f≋f' .pw w) (f'≋f'' .pw w)
        }

    wk : Γ ⊆ Δ → ◯'-Fam 𝒫 Γ → ◯'-Fam 𝒫 Δ
    wk {Δ = Δ} w f = elem (λ w' → f. apply-◯ (⊆-trans w w'))

    abstract
      wk-pres-≋ : (w : Γ ⊆ Γ') {f f' : ◯'-Fam 𝒫 Γ} (f≋f' : f ◯'-≋ f') → wk w f ◯'-≋ wk w f'
      wk-pres-≋ w f≋f' = proof λ w' → f≋f' .pw (⊆-trans w w')

      wk-pres-refl : (f : ◯'-Fam 𝒫 Γ) → wk ⊆-refl f ◯'-≋ f
      wk-pres-refl f = proof (λ w → ≡-to-◇'-≋ (cong (f .apply-◯) (⊆-refl-unit-right w)))

      wk-pres-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (f : ◯'-Fam 𝒫 Γ) → wk (⊆-trans w w') f ◯'-≋ wk w' (wk w f)
      wk-pres-trans w w' f = proof (λ w'' → ≡-to-◇'-≋ (cong (f .apply-◯) (⊆-trans-assoc w w' w'')))

◯'-map_ : (t : 𝒫 →̇ 𝒬) → (◯' 𝒫 →̇ ◯' 𝒬)
◯'-map_ {𝒫} {𝒬} = λ t → record
    { fun     = λ p → elem λ w → ◇'-map t (p .apply-◯ w)
    ; pres-≋  = λ p≋p' → proof λ w → ◇'-map-pres-≋ t (p≋p' .pw w)
    ; natural = λ _w _p → ≋[ ◯' 𝒬 ]-refl
    }

abstract
  ◯'-map-pres-≈̇ : t ≈̇ t' → ◯'-map t ≈̇ ◯'-map t'
  ◯'-map-pres-≈̇ t≈̇t' = record { proof = λ p → proof λ w → ◇'-map-pres-≈̇ t≈̇t' (p .apply-◯ w) }

  ◯'-map-pres-id : ◯'-map id'[ 𝒫 ] ≈̇ id'
  ◯'-map-pres-id = record { proof = λ _p → proof λ _w → ◇'-≋-refl }

  ◯'-map-pres-∘ : (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ◯'-map (t' ∘ t) ≈̇ ◯'-map t' ∘ ◯'-map t
  ◯'-map-pres-∘ _t' _t = record { proof = λ _p → proof λ w → ◇'-≋-refl }

◯'-is-PshFunctor : EndoFunctor PshCat
◯'-is-PshFunctor = record
               { ◯'_ = ◯'_
               ; ◯'-map_ = ◯'-map_
               ; ◯'-map-pres-≈̇ = ◯'-map-pres-≈̇
               ; ◯'-map-pres-id = ◯'-map-pres-id
               ; ◯'-map-pres-∘ = ◯'-map-pres-∘
               }