{-# OPTIONS --safe --without-K #-}
module Functor.Term.NormalForm.Properties where

open import Functor.Term.Base
open import Functor.Term.NormalForm

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; subst₂ ; cong ; cong₂ ; module ≡-Reasoning)

------------------------
-- Naturality conditions
------------------------

-- Normal forms and neutrals obey "naturality" of embeddding, i.e.,
-- weakening can be commuted with embedding.

-- the mutual brothers normal forms and neutrals who,
-- as always, must be handled (mutually) together
nat-embNe : (w : Γ ⊆ Γ') (n : Ne Γ a)
  → wkTm w (embNe n) ≡ embNe (wkNe w n)
nat-embNf : (w : Γ ⊆ Γ') (n : Nf Γ a)
  → wkTm w (embNf n) ≡ embNf (wkNf w n)

nat-embNf w (up  n)     = nat-embNe w n
nat-embNf w (lam n)     = cong lam (nat-embNf (keep w) n)
nat-embNf w (letin n m) = cong₂ letin (nat-embNe w n) (nat-embNf (keep w) m)

nat-embNe w (var   v)   = refl
nat-embNe w (app   n m) = cong₂ app   (nat-embNe w n) (nat-embNf w m)

wkNe-pres-⊆-refl : (n : Ne Γ a) → wkNe ⊆-refl n ≡ n
wkNf-pres-⊆-refl : (n : Nf Γ a) → wkNf ⊆-refl n ≡ n

wkNe-pres-⊆-refl (var   v)   = cong var (wkVar-pres-⊆-refl v)
wkNe-pres-⊆-refl (app   n m) = cong₂ app (wkNe-pres-⊆-refl n) (wkNf-pres-⊆-refl m)

wkNf-pres-⊆-refl (up  n)     = cong up  (wkNe-pres-⊆-refl n)
wkNf-pres-⊆-refl (lam n)     = cong lam (wkNf-pres-⊆-refl n)
wkNf-pres-⊆-refl (letin n m) = cong₂ letin (wkNe-pres-⊆-refl n) (wkNf-pres-⊆-refl m)

wkNe-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe w' (wkNe w n) ≡ wkNe (w ∙ w') n
wkNf-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Nf Γ a)
  → wkNf w' (wkNf w n) ≡ wkNf (w ∙ w') n

wkNe-pres-⊆-trans w w' (var v)   = cong var (wkVar-pres-⊆-trans w w' v)
wkNe-pres-⊆-trans w w' (app n m) = cong₂ app (wkNe-pres-⊆-trans  w w' n) (wkNf-pres-⊆-trans w w' m)

wkNf-pres-⊆-trans w w' (up  n)     = cong up  (wkNe-pres-⊆-trans w         w'         n)
wkNf-pres-⊆-trans w w' (lam n)     = cong lam (wkNf-pres-⊆-trans (keep  w) (keep  w') n)
wkNf-pres-⊆-trans w w' (letin n m) = cong₂ letin (wkNe-pres-⊆-trans w w' n) (wkNf-pres-⊆-trans (keep w) (keep w') m)
