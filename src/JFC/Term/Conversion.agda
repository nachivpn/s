{-# OPTIONS --safe --without-K #-}
module JFC.Term.Conversion where

open import JFC.Term.Base
open import JFC.Term.Properties

open import Relation.Binary
  using (Setoid ; IsEquivalence)
open import Relation.Binary.Construct.Closure.Equivalence
  using (setoid)
import Relation.Binary.Construct.Closure.Equivalence.Properties
  as EquivalenceProperties

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)

import Relation.Binary.Reasoning.Setoid as EqReasoning

data _≈_ : Tm Γ a → Tm Γ a → Set where

  red-fun : (t : Tm (Γ `, a) b) (u : Tm Γ a)
    → app (lam t) u ≈ substTm (idₛ `, u) t

  exp-fun : (t : Tm Γ (a ⇒ b))
    → t ≈ lam (app (wkTm freshWk t) (var zero))
    
  red-dia : (t : Tm Γ (◇ a)) (u : Tm (Γ `, a) b) (u' : Tm (Γ `, b) c)
    → sletin (sletin t u) u' ≈ sletin t (substTm (wkSub freshWk idₛ `, u) u')

  exp-dia : (t : Tm Γ (◇ a))
    → t ≈ sletin t (var zero)

  -- TODO: add necessary equations for ◇ type
  
  cong-lam : {t t' : Tm (Γ `, a) b}
    → t ≈ t'
    → lam t ≈ lam t'

  cong-app1 : {t t' : Tm Γ (a ⇒ b)} {u : Tm Γ a}
    → t ≈ t'
    → app t u ≈ app t' u

  cong-app2 : {t : Tm Γ (a ⇒ b)} {u u' : Tm Γ a}
    → u ≈ u'
    → app t u ≈ app t u'
    
  cong-sletin1 : {t t' : Tm Γ (◇ a)} {u : Tm (Γ `, a) b}
    → t ≈ t'
    → sletin t u ≈ sletin t' u

  cong-sletin2 : {t : Tm Γ (◇ a)} {u u' : Tm (Γ `, a) b}
    → u ≈ u'
    → sletin t u ≈ sletin t u'

  cong-jletin1 : {t t' : Tm Γ (◇ a)} {u : Tm (Γ `, a) (◇ b)}
    → t ≈ t'
    → jletin t u ≈ jletin t' u

  cong-jletin2 : {t : Tm Γ (◇ a)} {u u' : Tm (Γ `, a) (◇ b)}
    → u ≈ u'
    → jletin t u ≈ jletin t u'

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

cong-app : ∀ (t≈t' : t ≈ t') (u≈u' : u ≈ u') → app t u ≈ app t' u'
cong-app t≈t' u≈u' = ≈-trans (cong-app1 t≈t') (cong-app2 u≈u')

cong-sletin : {t t' : Tm Γ (◇ a)} {u : Tm (Γ `, a) b}
    → t ≈ t' → u ≈ u' → sletin t u ≈ sletin t' u'
cong-sletin t≈t' u≈u' = ≈-trans (cong-sletin1 t≈t') (cong-sletin2 u≈u')

cong-jletin : {t t' : Tm Γ (◇ a)} {u : Tm (Γ `, a) (◇ b)}
    → t ≈ t' → u ≈ u' → jletin t u ≈ jletin t' u'
cong-jletin t≈t' u≈u' = ≈-trans (cong-jletin1 t≈t') (cong-jletin2 u≈u')

--
-- Derived equations
--

open AdhocLemmas

wkTm-pres-≈ : (w : Γ ⊆ Γ') {t t' : Tm Γ a} → t ≈ t' → wkTm w t ≈ wkTm w t'
wkTm-pres-≈ w (red-fun t u)         = ≈-trans (red-fun _ _) (≡-to-≈ (red-fun-crunch-lemma w u t))
wkTm-pres-≈ w (exp-fun _)           = ≈-trans (exp-fun _) (≡-to-≈ (cong lam (cong₂ app keepFreshLemma ≡-refl)))
wkTm-pres-≈ w (red-dia t u u')      = ≈-trans (red-dia _ _ _) (cong-sletin2 (≡-to-≈ (red-dia-crunch-lemma w t u u')))
wkTm-pres-≈ w (exp-dia _)           = exp-dia (wkTm w _)
wkTm-pres-≈ w (cong-lam t≈t')       = cong-lam (wkTm-pres-≈ (_⊆_.keep w) t≈t')
wkTm-pres-≈ w (cong-app1 t≈t')      = cong-app1 (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-app2 t≈t')      = cong-app2 (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-sletin1 t≈t')   = cong-sletin1 (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-sletin2 t≈t')   = cong-sletin2 (wkTm-pres-≈ (_⊆_.keep w) t≈t')
wkTm-pres-≈ w (cong-jletin1 t≈t')   = cong-jletin1 (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-jletin2 t≈t')   = cong-jletin2 (wkTm-pres-≈ (_⊆_.keep w) t≈t')
wkTm-pres-≈ w ≈-refl                = ≈-refl
wkTm-pres-≈ w (≈-sym t≈t')          = ≈-sym (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (≈-trans t≈t' t'≈t'') = ≈-trans (wkTm-pres-≈ w t≈t') (wkTm-pres-≈ w t'≈t'')

--
-- Substitution conversion and its properties
--

open SubstitutionConversion _≈_ ≈-is-equiv public

dropₛ-pres-≈ₛ : s ≈ₛ s' → dropₛ {a = a} s ≈ₛ dropₛ s'
dropₛ-pres-≈ₛ []             = []
dropₛ-pres-≈ₛ (s≈s' `, t≈t') = dropₛ-pres-≈ₛ s≈s' `, wkTm-pres-≈ freshWk t≈t'

keepₛ-pres-≈ₛ : s ≈ₛ s' → keepₛ {a = a} s ≈ₛ keepₛ s'
keepₛ-pres-≈ₛ []             = ≈ₛ-refl
keepₛ-pres-≈ₛ (s≈s' `, t≈t') = dropₛ-pres-≈ₛ (s≈s' `, t≈t') `, ≈-refl

subsVar-pres-≈ₛ : {s s' : Sub Δ Γ} (x : Var Γ a) → s ≈ₛ s' → substVar s x ≈ substVar s' x
subsVar-pres-≈ₛ zero     (_ `, t≈t') = t≈t'
subsVar-pres-≈ₛ (succ x) (s≈s' `, _) = subsVar-pres-≈ₛ x s≈s'

subsTm-pres-≈-left : {s s' : Sub Δ Γ} (t : Tm Γ a) → s ≈ₛ s' → substTm s t ≈ substTm s' t
subsTm-pres-≈-left (var v)      s≈s'
  = subsVar-pres-≈ₛ v s≈s'
subsTm-pres-≈-left (lam t)      s≈s'
  = cong-lam (subsTm-pres-≈-left t (keepₛ-pres-≈ₛ s≈s'))
subsTm-pres-≈-left (app t u)    s≈s'
  = cong-app (subsTm-pres-≈-left t s≈s') (subsTm-pres-≈-left u s≈s')
subsTm-pres-≈-left (sletin t u) s≈s'
  = cong-sletin (subsTm-pres-≈-left t s≈s') (subsTm-pres-≈-left u (keepₛ-pres-≈ₛ s≈s'))
subsTm-pres-≈-left (jletin t u) s≈s'
  = cong-jletin (subsTm-pres-≈-left t s≈s') (subsTm-pres-≈-left u (keepₛ-pres-≈ₛ s≈s'))

subsTm-pres-≈-right : (s : Sub Δ Γ) {t t' : Tm Γ a} → t ≈ t' → substTm s t ≈ substTm s t'
subsTm-pres-≈-right s (red-fun t u)
  = ≈-trans (red-fun _ _) (≡-to-≈ (red-fun-crunch-subst-lemma s t u))
subsTm-pres-≈-right s (exp-fun t)
  = ≈-trans (exp-fun _) (cong-lam (cong-app1 (≡-to-≈ (exp-fun-crunch-subst-lemma s t))))
subsTm-pres-≈-right s (red-dia t u u')
  = ≈-trans (red-dia _ _ _) (cong-sletin2 (≡-to-≈ (red-dia-crunch-subst-lemma s u u')))
subsTm-pres-≈-right s (exp-dia _)
  = exp-dia _
subsTm-pres-≈-right s (cong-lam t≈t')
  = cong-lam (subsTm-pres-≈-right (keepₛ s) t≈t')
subsTm-pres-≈-right s (cong-app1 t≈t')
  = cong-app1 (subsTm-pres-≈-right s t≈t')
subsTm-pres-≈-right s (cong-app2 t≈t')
  = cong-app2 (subsTm-pres-≈-right s t≈t')
subsTm-pres-≈-right s (cong-sletin1 t≈t')
  = cong-sletin1  (subsTm-pres-≈-right s t≈t')
subsTm-pres-≈-right s (cong-sletin2 t≈t')
  = cong-sletin2  (subsTm-pres-≈-right (keepₛ s) t≈t')
subsTm-pres-≈-right s (cong-jletin1 t≈t')
  = cong-jletin1  (subsTm-pres-≈-right s t≈t')
subsTm-pres-≈-right s (cong-jletin2 t≈t')
  = cong-jletin2  (subsTm-pres-≈-right (keepₛ s) t≈t')
subsTm-pres-≈-right s ≈-refl
  = ≈-refl
subsTm-pres-≈-right s (≈-sym t≈t')
  = ≈-sym (subsTm-pres-≈-right s t≈t')
subsTm-pres-≈-right s (≈-trans t≈t' t≈t'')
  = ≈-trans (subsTm-pres-≈-right s t≈t') (subsTm-pres-≈-right s t≈t'')

subsTm-pres-≈ : {s s' : Sub Δ Γ} {t t' : Tm Γ a} → s ≈ₛ s' → t ≈ t' → substTm s t ≈ substTm s' t'
subsTm-pres-≈ {s' = s'} {t} s≈s' t≈t'
  = ≈-trans (subsTm-pres-≈-left t s≈s') (subsTm-pres-≈-right s' t≈t')

--
-- Derived lemmas for proving the fundamental theorem
--

red-fun-tr-lemma : (w : Γ ⊆ Γ') (s : Sub Γ Δ) (t : Tm (Δ `, a) b) (u : Tm Γ' a)
  → app (wkTm w (substTm s (lam t))) u ≈ substTm (wkSub w s `, u) t
red-fun-tr-lemma w s t u = let open EqReasoning (Tm-setoid _ _) in begin
    -- normalize
  app (lam (wkTm (keep w) (substTm (keepₛ s) t))) u
    ≈⟨ red-fun _ u  ⟩
  substTm (idₛ `, u) (wkTm (keep w) (substTm (keepₛ s) t))
    ≡˘⟨ cong (substTm (idₛ `, u)) (substTm-nat t (keepₛ s) (keep w)) ⟩
  substTm (idₛ `, u) (substTm (wkSub (keep w) (keepₛ s)) t)
    ≡˘⟨ substTm-pres-∙ₛ _ _ t ⟩
  substTm (wkSub (keep w) (keepₛ s) ∙ₛ (idₛ `, u)) t
    ≡˘⟨ cong (λ s' → substTm ((s' ∙ₛ _) `, u) t) (wkSub-pres-⊆-trans _ _ _) ⟩
  substTm ((wkSub (freshWk ∙ keep w) s ∙ₛ (idₛ `, u)) `, u) t
    ≡⟨ cong (λ s' → substTm (s' `, u) t) (cong (_∙ₛ _) (cong₂ wkSub (cong drop (⊆-trans-unit-left w)) ≡-refl)) ⟩
  substTm ((wkSub (drop w) s ∙ₛ (idₛ `, u)) `, u) t
    ≡˘⟨ cong (λ s' → substTm (s' `, u) t) (assoc-wkSub-∙ₛ _ _ _) ⟩
    -- normalize
  substTm ((s ∙ₛ trimSub w idₛ) `, u) t
    ≡⟨ cong (λ s' → substTm ((s ∙ₛ s') `, u) t) (trimSub-unit-right w) ⟩
  substTm ((s ∙ₛ embWk w) `, u) t
    ≡˘⟨ cong (λ s' → substTm (s' `, u) t) (cong (s ∙ₛ_) (wkSub-unit-right w)) ⟩
  substTm ((s ∙ₛ wkSub w idₛ) `, u) t
    ≡˘⟨ cong (λ s' → substTm (s' `, u) t) (assoc-∙ₛ-wkSub _ _ _) ⟩
  substTm (wkSub w (s ∙ₛ idₛ) `, u) t
    ≡⟨ cong (λ s' → substTm (s' `, u) t) (cong (wkSub w) (∙ₛ-unit-right s)) ⟩
  substTm (wkSub w s `, u) t ∎   
