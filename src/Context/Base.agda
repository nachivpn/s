{-# OPTIONS --safe --without-K #-}
module Context.Base (Ty : Set) where

private
  variable
    a b c d : Ty

infix  5 _⊆_
infixl 5 _,,_

-----------
-- Contexts
-----------

data Ctx : Set where
  []   : Ctx
  _`,_ : (Γ : Ctx) → (a : Ty) → Ctx

[_] : Ty → Ctx
[_] a = [] `, a

variable
  Γ Γ' Γ'' ΓL ΓL' ΓL'' ΓLL ΓLR ΓR ΓR' ΓR'' : Ctx
  Δ Δ' Δ'' ΔL ΔL' ΔL'' ΔLL ΔLR ΔR ΔR' ΔR'' ΔRL ΔRR : Ctx
  Θ Θ' Θ'' ΘL ΘL' ΘL'' ΘLL ΘLR ΘR ΘR' ΘR'' ΘRL ΘRR : Ctx
  Ξ Ξ' Ξ'' ΞL ΞL' ΞL'' ΞLL ΞLR ΞR ΞR' ΞR'' ΞRL ΞRR : Ctx

-- append contexts (++)
_,,_ : Ctx → Ctx → Ctx
Γ ,, []       = Γ
Γ ,, (Δ `, x) = (Γ ,, Δ) `, x

-------------
-- Weakenings
-------------

-- weakening relation
data _⊆_  : Ctx → Ctx → Set where
  base   : [] ⊆ []
  drop   : (w : Γ ⊆ Δ) → Γ ⊆ Δ `, a
  keep   : (w : Γ ⊆ Δ) → Γ `, a ⊆ Δ `, a

pattern drop[_] a w = drop {a = a} w
pattern keep[_] a w = keep {a = a} w

variable
  w w' w'' : Γ ⊆ Γ'

⊆-refl[_] : (Γ : Ctx) → Γ ⊆ Γ
⊆-refl[_] []        = base
⊆-refl[_] (Γ `, _a) = keep  ⊆-refl[ Γ ]

⊆-refl : Γ ⊆ Γ
⊆-refl {Γ} = ⊆-refl[ Γ ]

freshWk[_,_] : (Γ : Ctx) → (a : Ty) → Γ ⊆ (Γ `, a)
freshWk[ Γ , a ] = drop ⊆-refl

freshWk : Γ ⊆ (Γ `, a)
freshWk = freshWk[ _ , _ ]

_∙_ : Θ ⊆ Δ → Δ ⊆ Γ → Θ ⊆ Γ
w       ∙ base     = w
w       ∙ drop  w' = drop  (w ∙ w')
drop  w ∙ keep  w' = drop  (w ∙ w')
keep  w ∙ keep  w' = keep  (w ∙ w')

⊆-trans = _∙_

------------
-- Variables
------------

data Var : Ctx → Ty → Set where
  zero : Var (Γ `, a) a
  succ : (v : Var Γ a) → Var (Γ `, b) a

pattern v0 = zero
pattern v1 = succ v0
pattern v2 = succ v1

wkVar : Γ ⊆ Γ' → Var Γ a → Var Γ' a
wkVar (drop e) v        = succ (wkVar e v)
wkVar (keep e) zero     = zero
wkVar (keep e) (succ v) = succ (wkVar e v)
