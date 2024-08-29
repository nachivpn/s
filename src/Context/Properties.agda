{-# OPTIONS --safe --without-K #-}
module Context.Properties (Ty : Set) where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
  
open import Context.Base Ty

open import Semantics.Kripke.Frame

private
  variable
    a b c d : Ty

⊆-trans-unit-left : (w : Γ' ⊆ Γ) → ⊆-refl ∙ w ≡ w
⊆-trans-unit-left base      = refl
⊆-trans-unit-left (drop w)  = cong drop (⊆-trans-unit-left w)
⊆-trans-unit-left (keep w)  = cong keep (⊆-trans-unit-left w)

-- weakening composition obeys the right identity law
⊆-trans-unit-right : (w : Γ' ⊆ Γ) → w ∙ ⊆-refl ≡ w
⊆-trans-unit-right base      = refl
⊆-trans-unit-right (drop w)  = cong drop (⊆-trans-unit-right w)
⊆-trans-unit-right (keep w)  = cong keep (⊆-trans-unit-right w)

-- weakening composition is associative
∙-assoc : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (w3 : Γ4 ⊆ Γ3) (w2 : Γ3 ⊆ Γ2) → (w1 : Γ2 ⊆ Γ1)
  → (w3 ∙ w2) ∙ w1 ≡ w3 ∙ (w2 ∙ w1)
∙-assoc w3         w2         base       = refl
∙-assoc w3         w2         (drop w1)  = cong drop (∙-assoc w3 w2 w1)
∙-assoc w3         (drop w2)  (keep w1)  = cong drop (∙-assoc w3 w2 w1)
∙-assoc (drop w3)  (keep w2)  (keep w1)  = cong drop (∙-assoc w3 w2 w1)
∙-assoc (keep w3)  (keep w2)  (keep w1)  = cong keep (∙-assoc w3 w2 w1)

𝒲 : IFrame Ctx _⊆_
𝒲 = record
      { ⊆-trans           = _∙_
      ; ⊆-trans-assoc     = ∙-assoc
      ; ⊆-refl            = ⊆-refl
      ; ⊆-trans-unit-left = ⊆-trans-unit-left
      ; ⊆-trans-unit-right  = ⊆-trans-unit-right
      }

wkVar-pres-⊆-refl : (x : Var Γ a) → wkVar ⊆-refl x ≡ x
wkVar-pres-⊆-refl v0       = refl
wkVar-pres-⊆-refl (succ x) = cong succ (wkVar-pres-⊆-refl x)

wkVar-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (x : Var Γ a)
  → wkVar (w ∙ w') x ≡ wkVar w' (wkVar w x)
wkVar-pres-⊆-trans (drop w) (drop w') zero     = cong succ (wkVar-pres-⊆-trans (drop w) w' zero)
wkVar-pres-⊆-trans (drop w) (keep w') zero     = cong succ (wkVar-pres-⊆-trans w w' zero)
wkVar-pres-⊆-trans (keep w) (drop w') zero     = cong succ (wkVar-pres-⊆-trans (keep w) w' zero)
wkVar-pres-⊆-trans (keep w) (keep w') zero     = refl
wkVar-pres-⊆-trans (drop w) (drop w') (succ x) = cong succ (wkVar-pres-⊆-trans (drop w) w' (succ x))
wkVar-pres-⊆-trans (drop w) (keep w') (succ x) = cong succ (wkVar-pres-⊆-trans w w' (succ x))
wkVar-pres-⊆-trans (keep w) (drop w') (succ x) = cong succ (wkVar-pres-⊆-trans (keep w) w' (succ x))
wkVar-pres-⊆-trans (keep w) (keep w') (succ x) = cong succ (wkVar-pres-⊆-trans w w' x)

freshWk-natural : (w : Γ ⊆ Γ') → w ∙ freshWk[ Γ' , a ] ≡ freshWk[ Γ , a ] ∙ keep w
freshWk-natural w = cong drop (≡-trans (⊆-trans-unit-right w) (≡-sym (⊆-trans-unit-left w)))

-- weakening a variable index increments
wkIncr : (x : Var Γ a) → wkVar freshWk[ Γ , b ] x ≡ succ x
wkIncr zero     = refl
wkIncr (succ x) = cong succ (cong succ (wkVar-pres-⊆-refl x))

