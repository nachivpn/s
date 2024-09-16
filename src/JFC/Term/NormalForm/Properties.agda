{-# OPTIONS --safe --without-K #-}
module JFC.Term.NormalForm.Properties where

open import JFC.Term.Base
open import JFC.Term.NormalForm.Base

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
embNf-nat w unit        = refl
embNf-nat w (pair n m)  = cong₂ pair (embNf-nat w n) (embNf-nat w m)
embNf-nat w (lam n)     = cong lam (embNf-nat (keep w) n)
embNf-nat w (sletin n m) = cong₂ sletin (embNe-nat w n) (embNf-nat (keep w) m)
embNf-nat w (jletin n m) = cong₂ jletin (embNe-nat w n) (embNf-nat (keep w) m)

embNe-nat w (var   v)   = refl
embNe-nat w (fst n)     = cong fst (embNe-nat w n)
embNe-nat w (snd n)     = cong snd (embNe-nat w n)
embNe-nat w (app   n m) = cong₂ app   (embNe-nat w n) (embNf-nat w m)

wkNe-pres-⊆-refl : (n : Ne Γ a) → wkNe ⊆-refl n ≡ n
wkNf-pres-⊆-refl : (n : Nf Γ a) → wkNf ⊆-refl n ≡ n

wkNe-pres-⊆-refl (var   v)   = cong var (wkVar-pres-⊆-refl v)
wkNe-pres-⊆-refl (fst n)     = cong fst (wkNe-pres-⊆-refl n)
wkNe-pres-⊆-refl (snd n)     = cong snd (wkNe-pres-⊆-refl n)
wkNe-pres-⊆-refl (app   n m) = cong₂ app (wkNe-pres-⊆-refl n) (wkNf-pres-⊆-refl m)

wkNf-pres-⊆-refl (up  n)      = cong up  (wkNe-pres-⊆-refl n)
wkNf-pres-⊆-refl unit         = refl
wkNf-pres-⊆-refl (pair n m)   = cong₂ pair (wkNf-pres-⊆-refl n) (wkNf-pres-⊆-refl m)
wkNf-pres-⊆-refl (lam n)      = cong lam (wkNf-pres-⊆-refl n)
wkNf-pres-⊆-refl (sletin n m) = cong₂ sletin (wkNe-pres-⊆-refl n) (wkNf-pres-⊆-refl m)
wkNf-pres-⊆-refl (jletin n m) = cong₂ jletin (wkNe-pres-⊆-refl n) (wkNf-pres-⊆-refl m)

wkNe-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe (w ∙ w') n ≡ wkNe w' (wkNe w n)
wkNf-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Nf Γ a)
  → wkNf (w ∙ w') n ≡ wkNf w' (wkNf w n)

wkNe-pres-⊆-trans w w' (var v)   = cong var (wkVar-pres-⊆-trans w w' v)
wkNe-pres-⊆-trans w w' (fst n)   = cong fst (wkNe-pres-⊆-trans w w' n)
wkNe-pres-⊆-trans w w' (snd n)   = cong snd (wkNe-pres-⊆-trans w w' n)
wkNe-pres-⊆-trans w w' (app n m) = cong₂ app (wkNe-pres-⊆-trans  w w' n) (wkNf-pres-⊆-trans w w' m)

wkNf-pres-⊆-trans w w' (up  n)      = cong up  (wkNe-pres-⊆-trans w         w'         n)
wkNf-pres-⊆-trans w w' unit         = refl
wkNf-pres-⊆-trans w w' (pair n m)   = cong₂ pair (wkNf-pres-⊆-trans w w' n) (wkNf-pres-⊆-trans w w' m)
wkNf-pres-⊆-trans w w' (lam n)      = cong lam (wkNf-pres-⊆-trans (keep  w) (keep  w') n)
wkNf-pres-⊆-trans w w' (sletin n m) = cong₂ sletin (wkNe-pres-⊆-trans w w' n) (wkNf-pres-⊆-trans (keep w) (keep w') m)
wkNf-pres-⊆-trans w w' (jletin n m) = cong₂ jletin (wkNe-pres-⊆-trans w w' n) (wkNf-pres-⊆-trans (keep w) (keep w') m)
