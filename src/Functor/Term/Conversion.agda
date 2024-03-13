{-# OPTIONS --safe --without-K #-}
module Functor.Term.Conversion where

open import Functor.Term.Base

open import Relation.Binary
  using (Setoid ; IsEquivalence)
open import Relation.Binary.Construct.Closure.Equivalence
  using (setoid)
import Relation.Binary.Construct.Closure.Equivalence.Properties
  as EquivalenceProperties
  
open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)

data _≈_ : Tm Γ a → Tm Γ a → Set where

  red-fun : (t : Tm (Γ `, a) b) (u : Tm Γ a)
    → app (lam t) u ≈ substTm (idₛ `, u) t

  exp-fun : (t : Tm Γ (a ⇒ b))
    → t ≈ lam (app (wkTm freshWk t) (var zero))

  red-dia : (t : Tm Γ (◇ a)) (u : Tm (Γ `, a) b) (u' : Tm (Γ `, b) c)
    → letin (letin t u) u' ≈ letin t (substTm (wkSub freshWk idₛ `, u) u')

  exp-dia : (t : Tm Γ (◇ a))
    → t ≈ letin t (var zero)

  cong-lam : {t t' : Tm (Γ `, a) b}
    → t ≈ t'
    → lam t ≈ lam t'

  cong-app1 : {t t' : Tm Γ (a ⇒ b)} {u : Tm Γ a}
    → t ≈ t'
    → app t u ≈ app t' u

  cong-app2 : {t : Tm Γ (a ⇒ b)} {u u' : Tm Γ a}
    → u ≈ u'
    → app t u ≈ app t u'

  cong-letin1 : {t t' : Tm Γ (◇ a)} {u : Tm (Γ `, a) b}
    → t ≈ t'
    → letin t u ≈ letin t' u

  cong-letin2 : {t : Tm Γ (◇ a)} {u u' : Tm (Γ `, a) b}
    → u ≈ u'
    → letin t u ≈ letin t u'

  ≈-refl : {t : Tm Γ a}
    → t ≈ t

  ≈-sym : {t u : Tm Γ a}
    → t ≈ u → u ≈ t

  ≈-trans : {t u u' : Tm Γ a}
    → t ≈ u → u ≈ u' → t ≈ u'

≈-is-equiv : IsEquivalence (_≈_ {Γ} {a})
≈-is-equiv = record
    { refl  = ≈-refl
    ; sym   = ≈-sym
    ; trans = ≈-trans
    }

Tm-setoid : (Γ : Ctx) → (a : Ty) → Setoid _ _
Tm-setoid Γ a = record
  { Carrier       = Tm Γ a
  ; _≈_           = _≈_
  ; isEquivalence = ≈-is-equiv
  }

≡-to-≈ : ∀ {t u : Tm Γ a} → t ≡ u → t ≈ u
≡-to-≈ ≡-refl = ≈-refl

cong-app≈≡ : ∀ (t≈t' : t ≈ t') (u≡u' : u ≡ u') → app t u ≈ app t' u
cong-app≈≡ t≈t' ≡-refl = cong-app1 t≈t'

cong-app1≈ : ∀ (t≈t' : t ≈ t') → app t u ≈ app t' u
cong-app1≈ t≈t' = cong-app≈≡ t≈t' ≡-refl

cong-app≡≈ : ∀ (t≡t' : t ≡ t') (u≈u' : u ≈ u') → app t u ≈ app t' u'
cong-app≡≈ ≡-refl u≈u' = cong-app2 u≈u'

cong-app2≈ : ∀ (u≈u' : u ≈ u') → app t u ≈ app t u'
cong-app2≈ u≈u' = cong-app≡≈ ≡-refl u≈u'

cong-app≈ : ∀ (t≈t' : t ≈ t') (u≈u' : u ≈ u') → app t u ≈ app t' u'
cong-app≈ t≈t' u≈u' = ≈-trans (cong-app1≈ t≈t') (cong-app2≈ u≈u')

cong-letin : {t t' : Tm Γ (◇ a)} {u : Tm (Γ `, a) b}
    → t ≈ t' → u ≈ u' → letin t u ≈ letin t' u'
cong-letin t≈t' u≈u' = ≈-trans (cong-letin1 t≈t') (cong-letin2 u≈u')
