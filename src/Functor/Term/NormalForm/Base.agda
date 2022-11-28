{-# OPTIONS --safe --without-K #-}
module Functor.Term.NormalForm.Base where

open import Functor.Term.Base

---------------
-- Normal forms
---------------

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var : Var Γ a → Ne Γ a
  app : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b

data Nf where
  up    : Ne Γ ι → Nf Γ ι
  lam   : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  letin : Ne Γ (◯ a) → Nf (Γ `, a) b → Nf Γ (◯ b)

embNe : Ne Γ a → Tm Γ a
embNf : Nf Γ a → Tm Γ a

embNe (var  x)   = var x
embNe (app  m n) = app (embNe m) (embNf n)

embNf (up  x)     = embNe x
embNf (lam n)     = lam (embNf n)
embNf (letin m n) = letin (embNe m) (embNf n)
