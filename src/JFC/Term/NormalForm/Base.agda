{-# OPTIONS --safe --without-K #-}
module JFC.Term.NormalForm.Base where

open import JFC.Term.Base

---------------
-- Normal forms
---------------

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var : Var Γ a → Ne Γ a
  fst : Ne Γ (a × b) → Ne Γ a
  snd : Ne Γ (a × b) → Ne Γ b
  app : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b

data Nf where
  up     : Ne Γ ι → Nf Γ ι
  unit   : Nf Γ 𝟙
  pair   : Nf Γ a → Nf Γ b → Nf Γ (a × b)
  lam    : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  sletin : Ne Γ (◇ a) → Nf (Γ `, a) b → Nf Γ (◇ b)
  jletin : Ne Γ (◇ a) → Nf (Γ `, a) (◇ b) → Nf Γ (◇ b)

embNe-fun : Ne Γ a → Tm Γ a
embNf-fun : Nf Γ a → Tm Γ a

embNe-fun (var  x)   = var x
embNe-fun (fst n)    = fst (embNe-fun n)
embNe-fun (snd n)    = snd (embNe-fun n)
embNe-fun (app  m n) = app (embNe-fun m) (embNf-fun n)

embNf-fun (up  x)      = embNe-fun x
embNf-fun unit         = unit
embNf-fun (pair m n)   = pair (embNf-fun m) (embNf-fun n)
embNf-fun (lam n)      = lam (embNf-fun n)
embNf-fun (sletin m n) = sletin (embNe-fun m) (embNf-fun n)
embNf-fun (jletin m n) = jletin (embNe-fun m) (embNf-fun n)

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a

wkNe w (var x)     = var (wkVar w x)
wkNe w (fst n)     = fst (wkNe w n)
wkNe w (snd n)     = snd (wkNe w n)
wkNe w (app n m)   = app (wkNe w n) (wkNf w m)

wkNf w (up n)       = up (wkNe w n)
wkNf w unit         = unit
wkNf w (pair n m)   = pair (wkNf w n) (wkNf w m)
wkNf w (lam n)      = lam (wkNf (keep w) n)
wkNf w (sletin x n) = sletin (wkNe w x) (wkNf (keep w) n)
wkNf w (jletin x n) = jletin (wkNe w x) (wkNf (keep w) n)
