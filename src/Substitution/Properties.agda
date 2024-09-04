{-# OPTIONS --safe --without-K #-}

import Context as Context

module Substitution.Properties
  (Ty          : Set)
  (let open Context Ty using (Ctx ; _⊆_ ; Var))
  (Tm          : (Γ : Ctx) → (a : Ty) → Set)
  (var         : {Γ : Ctx} → {a : Ty} → (v : Var Γ a) → Tm Γ a)
  (wkTm        : {Γ' Γ : Ctx} → {a : Ty} → (w : Γ ⊆ Γ') → (t : Tm Γ a) → Tm Γ' a)
  where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence)

open Context Ty hiding (Ctx ; _⊆_ ; Var)
open import Substitution.Base Ty Tm var wkTm

private
  variable
    a b c d : Ty

-- naturality of trimSub
trimSub-nat : (s : Sub Γ Δ) (w : Δ' ⊆ Δ) (w' : Γ ⊆ Γ')
  → wkSub w' (trimSub w s) ≡ trimSub w (wkSub w' s)
trimSub-nat []         base      w' = refl
trimSub-nat (s `, t)   (drop w)  w' = trimSub-nat s w w'
trimSub-nat (s `, t)   (keep w)  w' = cong (_`, wkTm w' t) (trimSub-nat s w w')

-- trimSub (which is composition, really) has a left unit
trimSub-unit-left : (s : Sub Δ Γ) → trimSub ⊆-refl s ≡ s
trimSub-unit-left []       = refl
trimSub-unit-left (s `, x) = cong (_`, _) (trimSub-unit-left s)

-- trimSub (which is composition, really) has a right unit
trimSub-unit-right : (w : Γ ⊆ Δ) → trimSub w idₛ ≡ embWk w
trimSub-unit-right base      = refl
trimSub-unit-right (drop w)  = trans
  (sym (trimSub-nat idₛ w freshWk))
  (cong (wkSub freshWk) (trimSub-unit-right w))
trimSub-unit-right (keep w)  = cong (_`, var zero) (trans
  (sym (trimSub-nat idₛ w freshWk))
  (cong (wkSub freshWk) (trimSub-unit-right w)))

-- naturality of substVar
substVar-nat : (x : Var Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substVar (wkSub w s) x ≡ wkTm w (substVar s x)
substVar-nat zero     (s `, t) w = refl
substVar-nat (succ x) (s `, t) w = substVar-nat x s w

-- 
assoc-substVar-wkVar : (x : Var Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → substVar (trimSub w s) x ≡ substVar s (wkVar w x)
assoc-substVar-wkVar zero     (s `, x)  (drop w)
  = assoc-substVar-wkVar zero s w
assoc-substVar-wkVar zero     (s `, x)  (keep w)
  = refl
assoc-substVar-wkVar (succ x) (s `, x₁) (drop w)
  = assoc-substVar-wkVar (succ x) s w
assoc-substVar-wkVar (succ x) (s `, x₁) (keep w)
  = assoc-substVar-wkVar x s w

assoc-substVar-trimSub = assoc-substVar-wkVar

module Conversion
  (_≈_        : {Γ : Ctx} {a : Ty} (t t' : Tm Γ a) → Set)
  (≈-is-equiv : {Γ : Ctx} {a : Ty} → IsEquivalence (_≈_ {Γ} {a}))
  where

  open IsEquivalence renaming
    ( refl to ≈-refl
    ; sym to ≈-sym
    ; trans to ≈-trans
    )

  data _≈ₛ_ : Sub Γ Δ → Sub Γ Δ → Set where
    []   : [] ≈ₛ [] {Γ}
    _`,_ : {s s' : Sub Γ Δ} {t t' : Tm Γ a} → s ≈ₛ s' → t ≈ t' → (s `, t) ≈ₛ (s' `, t')

  ≈ₛ-refl : Reflexive {A = Sub Γ Δ} _≈ₛ_
  ≈ₛ-refl {x = []}     = []
  ≈ₛ-refl {x = δ `, t} = ≈ₛ-refl `, ≈-is-equiv .≈-refl

  ≈ₛ-sym : Symmetric {A = Sub Γ Δ} _≈ₛ_
  ≈ₛ-sym []             = []
  ≈ₛ-sym (φ≋φ' `, t≈t') = (≈ₛ-sym φ≋φ') `, (≈-is-equiv .≈-sym t≈t') -- (≈ₛ-sym φ≋φ') `, ? -- ≈-sym t≈t'

  ≈ₛ-trans : Transitive {A = Sub Γ Δ} _≈ₛ_
  ≈ₛ-trans []            ψ≋ω              = ψ≋ω
  ≈ₛ-trans (φ≋ψ `, t≈t') (ψ≋ω `, t'≈t'')  = (≈ₛ-trans φ≋ψ ψ≋ω) `, ≈-is-equiv. ≈-trans t≈t' t'≈t''

  ≈ₛ-equiv : IsEquivalence {A = Sub Γ Δ} _≈ₛ_
  ≈ₛ-equiv = record
    { refl  = ≈ₛ-refl
    ; sym   = ≈ₛ-sym
    ; trans = ≈ₛ-trans
    }
