{-# OPTIONS --safe --without-K #-}

import Context.Base as Context

-- Substitutions (parameterized by terms `Tm` and modal accessibility relation `Acc`)
-------------------------------------------------------------------------------------

module Substitution
  (Ty          : Set)
  (let open Context Ty using (Ctx ; _⊆_ ; Var))
  (Tm          : (Γ : Ctx) → (a : Ty) → Set)
  (var         : {Γ : Ctx} → {a : Ty} → (v : Var Γ a) → Tm Γ a)
  (wkTm        : {Γ' Γ : Ctx} → {a : Ty} → (w : Γ ⊆ Γ') → (t : Tm Γ a) → Tm Γ' a)
  where


open import Substitution.Base Ty Tm var wkTm public
open import Substitution.Properties Ty Tm var wkTm public
