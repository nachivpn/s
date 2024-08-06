{-# OPTIONS --safe --without-K #-}
module MLC.Term.NormalForm.Base where

open import MLC.Term.Base

---------------
-- Normal forms
---------------

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var : Var Γ a → Ne Γ a
  app : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b

data Nf where
  up     : Ne Γ ι → Nf Γ ι
  lam    : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  return : Nf Γ a → Nf Γ (◇ a)
  letin  : Ne Γ (◇ a) → Nf (Γ `, a) (◇ b) → Nf Γ (◇ b)

embNe-fun : Ne Γ a → Tm Γ a
embNf-fun : Nf Γ a → Tm Γ a

embNe-fun (var  x)   = var x
embNe-fun (app  m n) = app (embNe-fun m) (embNf-fun n)

embNf-fun (up  x)     = embNe-fun x
embNf-fun (lam n)     = lam (embNf-fun n)
embNf-fun (return n)  = return (embNf-fun n)
embNf-fun (letin m n) = letin (embNe-fun m) (embNf-fun n)

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a

wkNe w (var x)     = var (wkVar w x)
wkNe w (app n m)   = app (wkNe w n) (wkNf w m)

wkNf w (up n)      = up (wkNe w n)
wkNf w (lam n)     = lam (wkNf (keep w) n)
wkNf w (return n)  = return (wkNf w n)
wkNf w (letin x n) = letin (wkNe w x) (wkNf (keep w) n)
