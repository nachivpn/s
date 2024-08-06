{-# OPTIONS --safe --without-K #-}
module SFC.Term.Base where

open import Type public
import Context Ty as Context
import Substitution    as Substitution

open Context public

data Tm : Ctx → Ty → Set where

  var  : (v : Var Γ a)
       ---------------
       → Tm Γ a

  lam  : (t : Tm (Γ `, a) b)
         -------------------
       → Tm Γ (a ⇒ b)

  app  : (t : Tm Γ (a ⇒ b))
       → (u : Tm Γ a)
         ------------------
       → Tm Γ b

  letin : (t : Tm Γ (◇ a))
        → (u : Tm (Γ `, a) b)
          ------------------
        → Tm Γ (◇ b)

variable
  t t' t'' t''' : Tm Γ a
  u u' u'' u''' : Tm Γ a

wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x)     = var (wkVar w x)
wkTm w (lam t)     = lam (wkTm (keep w) t)
wkTm w (app t u)   = app (wkTm w t) (wkTm w u)
wkTm w (letin t u) = letin (wkTm w t) (wkTm (keep w) u)

open Substitution Ty Tm var wkTm public
  renaming (module Composition to SubstitutionComposition)

substTm : Sub Δ Γ → Tm Γ a → Tm Δ a
substTm s (var x)     = substVar s x
substTm s (lam t)     = lam (substTm (keepₛ s) t)
substTm s (app t u)   = app (substTm s t) (substTm s u)
substTm s (letin t u) = letin (substTm s t) (substTm (keepₛ s) u)

open SubstitutionComposition substTm public
