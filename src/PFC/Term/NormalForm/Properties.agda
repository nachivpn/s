{-# OPTIONS --safe --without-K #-}
module PFC.Term.NormalForm.Properties where

open import PFC.Term.Base
open import PFC.Term.NormalForm.Base

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; subst₂ ; cong ; cong₂ ; module ≡-Reasoning)

------------------------
-- Naturality conditions
------------------------

-- Normal forms and neutrals obey "naturality" of embeddding, i.e.,
-- weakening can be commuted with embedding.

-- the mutual brothers normal forms and neutrals who,
-- as always, must be handled (mutually) together
embNe-nat : (w : Γ ⊆ Γ') (n : Ne Γ a)
  → wkTm w (embNe-fun n) ≡ embNe-fun (wkNe w n)
embNf-nat : (w : Γ ⊆ Γ') (n : Nf Γ a)
  → wkTm w (embNf-fun n) ≡ embNf-fun (wkNf w n)

embNf-nat w (up  n)     = embNe-nat w n
embNf-nat w (lam n)     = cong lam (embNf-nat (keep w) n)
embNf-nat w (return n)  = cong return (embNf-nat w n)
embNf-nat w (letin n m) = cong₂ letin (embNe-nat w n) (embNf-nat (keep w) m)

embNe-nat w (var   v)   = refl
embNe-nat w (app   n m) = cong₂ app   (embNe-nat w n) (embNf-nat w m)

wkNe-pres-⊆-refl : (n : Ne Γ a) → wkNe ⊆-refl n ≡ n
wkNf-pres-⊆-refl : (n : Nf Γ a) → wkNf ⊆-refl n ≡ n

wkNe-pres-⊆-refl (var   v)   = cong var (wkVar-pres-⊆-refl v)
wkNe-pres-⊆-refl (app   n m) = cong₂ app (wkNe-pres-⊆-refl n) (wkNf-pres-⊆-refl m)

wkNf-pres-⊆-refl (up  n)     = cong up  (wkNe-pres-⊆-refl n)
wkNf-pres-⊆-refl (lam n)     = cong lam (wkNf-pres-⊆-refl n)
wkNf-pres-⊆-refl (return n)  = cong return (wkNf-pres-⊆-refl n)
wkNf-pres-⊆-refl (letin n m) = cong₂ letin (wkNe-pres-⊆-refl n) (wkNf-pres-⊆-refl m)

wkNe-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe (w ∙ w') n ≡ wkNe w' (wkNe w n)
wkNf-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Nf Γ a)
  → wkNf (w ∙ w') n ≡ wkNf w' (wkNf w n)

wkNe-pres-⊆-trans w w' (var v)   = cong var (wkVar-pres-⊆-trans w w' v)
wkNe-pres-⊆-trans w w' (app n m) = cong₂ app (wkNe-pres-⊆-trans  w w' n) (wkNf-pres-⊆-trans w w' m)

wkNf-pres-⊆-trans w w' (up  n)     = cong up  (wkNe-pres-⊆-trans w         w'         n)
wkNf-pres-⊆-trans w w' (lam n)     = cong lam (wkNf-pres-⊆-trans (keep  w) (keep  w') n)
wkNf-pres-⊆-trans w w' (return n)  = cong return (wkNf-pres-⊆-trans w w' n)
wkNf-pres-⊆-trans w w' (letin n m) = cong₂ letin (wkNe-pres-⊆-trans w w' n) (wkNf-pres-⊆-trans (keep w) (keep w') m)
