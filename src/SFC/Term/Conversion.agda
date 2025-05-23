{-# OPTIONS --safe --without-K #-}
module SFC.Term.Conversion where

open import SFC.Term.Base
open import SFC.Term.Properties

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

--
-- Derived equations
--

--
-- Derived lemmas for proving the fundamental theorem
--

open AdhocLemmas

wkTm-pres-≈ : (w : Γ ⊆ Γ') {t t' : Tm Γ a} → t ≈ t' → wkTm w t ≈ wkTm w t'
wkTm-pres-≈ w (red-fun t u)         = ≈-trans (red-fun _ _) (≡-to-≈ (red-fun-crunch-lemma w u t))
wkTm-pres-≈ w (exp-fun _)           = ≈-trans (exp-fun _) (≡-to-≈ (cong lam (cong₂ app keepFreshLemma ≡-refl)))
wkTm-pres-≈ w (red-dia t u u')      = ≈-trans (red-dia _ _ _) (cong-letin2 (≡-to-≈ (red-dia-crunch-lemma w t u u')))
wkTm-pres-≈ w (exp-dia _)           = exp-dia (wkTm w _)
wkTm-pres-≈ w (cong-lam t≈t')       = cong-lam (wkTm-pres-≈ (_⊆_.keep w) t≈t')
wkTm-pres-≈ w (cong-app1 t≈t')      = cong-app1 (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-app2 t≈t')      = cong-app2 (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-letin1 t≈t')    = cong-letin1 (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-letin2 t≈t')    = cong-letin2 (wkTm-pres-≈ (_⊆_.keep w) t≈t')
wkTm-pres-≈ w ≈-refl                = ≈-refl
wkTm-pres-≈ w (≈-sym t≈t')          = ≈-sym (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (≈-trans t≈t' t'≈t'') = ≈-trans (wkTm-pres-≈ w t≈t') (wkTm-pres-≈ w t'≈t'')

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

red-dia-tr-lemma : (s : Sub Γ Δ) (n : Tm Γ (◇ a)) (t' : Tm (Γ `, a) b) (u : Tm (Δ `, b) c)
  → letin (letin n t') (substTm (dropₛ s `, var zero) u) ≈ letin n (substTm (dropₛ s `, t') u)
red-dia-tr-lemma s n t' u = let open EqReasoning (Tm-setoid _ _) in begin
  letin (letin n t') (substTm (dropₛ s `, var zero) u)
    ≈⟨ red-dia n t' _ ⟩
  letin n (substTm (dropₛ idₛ `, t') (substTm (dropₛ s `, var zero) u))
    ≡˘⟨ cong (letin n) (substTm-pres-∙ₛ _ _ u) ⟩
    -- normalize
  letin n (substTm ((dropₛ s ∙ₛ (dropₛ idₛ  `, t')) `, t') u)
    ≡˘⟨ cong (letin n) (cong (λ s' → substTm (s' `, t') u) (assoc-wkSub-∙ₛ s (dropₛ idₛ  `, t') freshWk)) ⟩
  letin n (substTm ((s ∙ₛ trimSub freshWk (dropₛ idₛ  `, t')) `, t') u)
    -- normalize
    ≡⟨ cong (letin n) (cong (λ s' → substTm ((s ∙ₛ s') `, t') u) (trimSub-unit-left (dropₛ idₛ))) ⟩
  letin n (substTm ((s ∙ₛ dropₛ idₛ) `, t') u)
    -- normalize
    ≡˘⟨ cong (letin n) (cong (λ s' → substTm (s' `, t') u) (assoc-∙ₛ-wkSub s idₛ freshWk)) ⟩
  letin n (substTm (dropₛ (s ∙ₛ idₛ) `, t') u)
    ≡⟨ cong (letin n) (cong (λ s' → substTm (dropₛ s' `, t') u) (∙ₛ-unit-right s)) ⟩
  letin n (substTm (dropₛ s `, t') u) ∎
