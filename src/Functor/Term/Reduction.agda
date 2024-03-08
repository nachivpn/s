{-# OPTIONS --safe --without-K #-}
module Functor.Term.Reduction where

open import Relation.Binary using (Preorder)

import      Relation.Binary.Construct.Closure.ReflexiveTransitive            as ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using (preorder)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

open ReflexiveTransitive public using (ε ; _◅_)

import RUtil

open import Functor.Term.Base

-------------------
-- Reduction rules
-------------------

data _⟶_ : Tm Γ a → Tm Γ a → Set where

  red-fun : (t : Tm (Γ `, a) b) (u : Tm Γ a)
    → app (lam t) u ⟶ substTm (idₛ `, u) t

  exp-fun : (t : Tm Γ (a ⇒ b))
    → t ⟶ lam (app (wkTm freshWk t) (var zero))

  red-circ : (t : Tm Γ (◇ a)) (u : Tm (Γ `, a) b) (u' : Tm (Γ `, b) c)
    → letin (letin t u) u' ⟶ letin t (substTm (wkSub freshWk idₛ `, u) u')

  exp-circ : (t : Tm Γ (◇ a))
    → t ⟶ letin t (var zero)

  cong-lam : {t t' : Tm (Γ `, a) b}
    → t ⟶ t'
    → lam t ⟶ lam t'

  cong-app1 : {t t' : Tm Γ (a ⇒ b)} {u : Tm Γ a}
    → t ⟶ t'
    → app t u ⟶ app t' u

  cong-app2 : {t : Tm Γ (a ⇒ b)} {u u' : Tm Γ a}
    → u ⟶ u'
    → app t u ⟶ app t u'

  cong-letin1 : {t t' : Tm Γ (◇ a)} {u : Tm (Γ `, a) b}
    → t ⟶ t'
    → letin t u ⟶ letin t' u

  cong-letin2 : {t : Tm Γ (◇ a)} {u u' : Tm (Γ `, a) b}
    → u ⟶ u'
    → letin t u ⟶ letin t u'

module _ {Γ : Ctx} {a : Ty} where
  open RUtil (_⟶_ {Γ} {a}) public

-- zero or more steps of reduction
Tm-preorder : (Γ : Ctx) → (a : Ty) → Preorder _ _ _
Tm-preorder Γ a = preorder (_⟶_ {Γ} {a})

module _ {Γ : Ctx} {a : Ty} where
  open Preorder (Tm-preorder Γ a) public
    using    ()
    renaming (_∼_ to _⟶*_ ; refl to ⟶*-refl ; reflexive to none ; trans to multi)

single : (t⟶t' : t ⟶ t') → t ⟶* t'
single t⟶t' = t⟶t' ◅ ε

single-≡ : (t⟶t' : t ⟶ t') → (t'≡t'' : t' ≡ t'') → t ⟶* t''
single-≡ t⟶t' refl = single t⟶t'

≡-single : (t≡t' : t ≡ t') → (t'⟶t'' : t' ⟶ t'') → t ⟶* t''
≡-single refl t'⟶t'' = single t'⟶t''

≡-single-≡ : (t≡t' : t ≡ t') → (t'⟶t'' : t' ⟶ t'') → (t''≡t''' : t'' ≡ t''') → t ⟶* t'''
≡-single-≡ refl t'⟶t'' refl = single t'⟶t''

multi-≡ : (t⟶*t' : t ⟶* t') → (t'≡t'' : t' ≡ t'') → t ⟶* t''
multi-≡ t⟶*t' refl = t⟶*t'

≡-multi : (t≡t' : t ≡ t') → (t'⟶*t'' : t' ⟶* t'') → t ⟶* t''
≡-multi refl t'⟶*t'' = t'⟶*t''

≡-multi-≡ : (t≡t' : t ≡ t') → (t'⟶*t'' : t' ⟶* t'') → (t''≡t''' : t'' ≡ t''') → t ⟶* t'''
≡-multi-≡ refl t'⟶*t'' refl = t'⟶*t''

⟶-multi : (t⟶t' : t ⟶ t') → (t'⟶*t'' : t' ⟶* t'') → t ⟶* t''
⟶-multi t⟶t' t'⟶*t'' = multi (single t⟶t') t'⟶*t''

multi-⟶ : (t⟶*t' : t ⟶* t') → (t'⟶t'' : t' ⟶ t'') → t ⟶* t''
multi-⟶ t⟶*t' t'⟶t'' = multi t⟶*t' (single t'⟶t'')

module _ {t : Tm Γ a → Tm Δ b} (cong-t : ∀ {u u' : Tm Γ a} → (u⟶u' : u ⟶ u') → t u ⟶* t u') where
  cong-⟶*-to-cong-⟶* : ∀ (u⟶*u' : u ⟶* u') → t u ⟶* t u'
  cong-⟶*-to-cong-⟶* ε                 = ε
  cong-⟶*-to-cong-⟶* (u⟶u'' ◅ u''⟶*u') = multi (cong-t u⟶u'') (cong-⟶*-to-cong-⟶* u''⟶*u')

cong-⟶-to-cong-⟶* : {t : Tm Γ a → Tm Δ b} (cong-t : ∀ {u u' : Tm Γ a} → (u⟶u' : u ⟶ u') → t u ⟶ t u') (u⟶*u' : u ⟶* u') → t u ⟶* t u'
cong-⟶-to-cong-⟶* cong-t = cong-⟶*-to-cong-⟶* (λ u⟶u' → single (cong-t u⟶u'))

cong-app : {t t' : Tm Γ (a ⇒ b)} {u u' : Tm Γ  a}
  → t ⟶ t' → u ⟶ u'
  → app t u ⟶* app t' u'
cong-app t⟶t' u⟶u' = cong-app1 t⟶t' ◅ cong-app2 u⟶u' ◅ ε

cong-letin : {t t' : Tm Γ (◇ a)} {u u' : Tm (Γ `, a) b}
  → t ⟶ t' → u ⟶ u'
  → letin t u ⟶* letin t' u'
cong-letin t⟶t' u⟶u' = cong-letin1 t⟶t' ◅ cong-letin2 u⟶u' ◅ ε

cong-lam* : {t t' : Tm (Γ `, a) b}
  → t ⟶* t'
  → lam t ⟶* lam t'
cong-lam* = cong-⟶-to-cong-⟶* cong-lam

cong-app*≡ : {t t' : Tm Γ (a ⇒ b)} {u u' : Tm Γ  a}
  → t ⟶* t'
  → u ≡ u'
  → app t u ⟶* app t' u'
cong-app*≡ t⟶*t' refl = cong-⟶-to-cong-⟶* cong-app1 t⟶*t'

cong-app1* : {t t' : Tm Γ (a ⇒ b)} {u : Tm Γ  a}
  → t ⟶* t'
  → app t u ⟶* app t' u
cong-app1* t⟶*t' = cong-app*≡ t⟶*t' refl

cong-app≡* : {t t' : Tm Γ (a ⇒ b)} {u u' : Tm Γ  a}
  → t ≡ t'
  → u ⟶* u'
  → app t u ⟶* app t' u'
cong-app≡* refl u⟶*u' = cong-⟶-to-cong-⟶* cong-app2 u⟶*u'

cong-app2* : {t : Tm Γ (a ⇒ b)} {u u' : Tm Γ  a}
  → u ⟶* u'
  → app t u ⟶* app t u'
cong-app2* u⟶*u' = cong-app≡* refl u⟶*u'

cong-app*  : {t t' : Tm Γ (a ⇒ b)} {u u' : Tm Γ  a}
  → t ⟶* t' → u ⟶* u'
  → app t u ⟶* app t' u'
cong-app* t⟶*t' u⟶*u' = multi (cong-app1* t⟶*t') (cong-app2* u⟶*u')

cong-letin*≡ :  {t t' : Tm Γ (◇ a)} {u u' : Tm (Γ `, a) b}
  → t ⟶* t'
  → u ≡ u'
  → letin t u ⟶* letin t' u'
cong-letin*≡ t⟶*t' refl = cong-⟶-to-cong-⟶* cong-letin1 t⟶*t'

cong-letin1* :  {t t' : Tm Γ (◇ a)} {u  : Tm (Γ `, a) b}
  → t ⟶* t'
  → letin t u ⟶* letin t' u
cong-letin1* t⟶*t' = cong-letin*≡ t⟶*t' refl

cong-letin≡* :  {t t' : Tm Γ (◇ a)} {u u' : Tm (Γ `, a) b}
  → t ≡ t'
  → u ⟶* u'
  → letin t u ⟶* letin t' u'
cong-letin≡* refl u⟶*u' = cong-⟶-to-cong-⟶* cong-letin2 u⟶*u'

cong-letin2* :  {t : Tm Γ (◇ a)} {u u' : Tm (Γ `, a) b}
  → u ⟶* u'
  → letin t u ⟶* letin t u'
cong-letin2* u⟶*u' = cong-letin≡* refl u⟶*u'

cong-letin*  :  {t t' : Tm Γ (◇ a)} {u u' : Tm (Γ `, a) b}
  → t ⟶* t' → u ⟶* u'
  → letin t u ⟶* letin t' u'
cong-letin* t⟶*t' u⟶*u' = multi (cong-letin1* t⟶*t') (cong-letin2* u⟶*u')
