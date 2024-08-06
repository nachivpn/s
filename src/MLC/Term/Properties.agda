{-# OPTIONS --safe --without-K #-}
module MLC.Term.Properties where

open import MLC.Term.Base

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

wkTm-pres-⊆-refl : (t : Tm Γ a) → wkTm ⊆-refl t ≡ t
wkTm-pres-⊆-refl (var   v)   = cong  var (wkVar-pres-⊆-refl v)
wkTm-pres-⊆-refl (lam   t)   = cong  lam (wkTm-pres-⊆-refl  t)
wkTm-pres-⊆-refl (app   t u) = cong₂ app (wkTm-pres-⊆-refl  t) (wkTm-pres-⊆-refl u)
wkTm-pres-⊆-refl (return t)  = cong return (wkTm-pres-⊆-refl t)
wkTm-pres-⊆-refl (letin t u) = cong₂ letin (wkTm-pres-⊆-refl t) (wkTm-pres-⊆-refl u)

wkTm-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (t : Tm Γ a)
  → wkTm (w ∙ w') t ≡ wkTm w' (wkTm w t)
wkTm-pres-⊆-trans w w' (var   v)   = cong  var (wkVar-pres-⊆-trans w w' v)
wkTm-pres-⊆-trans w w' (lam   t)   = cong  lam (wkTm-pres-⊆-trans (keep w) (keep  w') t)
wkTm-pres-⊆-trans w w' (app   t u) = cong₂ app (wkTm-pres-⊆-trans w w' t) (wkTm-pres-⊆-trans w w' u)
wkTm-pres-⊆-trans w w' (return t)  = cong return (wkTm-pres-⊆-trans w w' t) 
wkTm-pres-⊆-trans w w' (letin t u) = cong₂ letin (wkTm-pres-⊆-trans w w' t) (wkTm-pres-⊆-trans (keep w) (keep w') u)

wkSub-pres-⊆-refl : (s : Sub Γ Δ) → wkSub ⊆-refl s ≡ s
wkSub-pres-⊆-refl []       = refl
wkSub-pres-⊆-refl (s `, t) = cong₂ _`,_ (wkSub-pres-⊆-refl s) (wkTm-pres-⊆-refl t)

wkSub-unit-left = wkSub-pres-⊆-refl

wkSub-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (s : Sub Γ ΓR)
  → wkSub (w ∙ w') s ≡ wkSub w' (wkSub w s)
wkSub-pres-⊆-trans w w' []         = refl
wkSub-pres-⊆-trans w w' (s `, t)   = cong₂ _`,_ (wkSub-pres-⊆-trans w w' s) (wkTm-pres-⊆-trans w w' t)

private
  wkSubFreshLemma : {s : Sub Δ Γ} {w : Δ ⊆ Δ'}
    → wkSub freshWk[ Δ' , a ] (wkSub w s) ≡ wkSub (keep w) (dropₛ s)
  wkSubFreshLemma {s = s} {w} = trans
    (trans
      (sym (wkSub-pres-⊆-trans _ _ _))
      (cong₂ wkSub (cong drop (trans (⊆-refl-unit-right _) (sym (⊆-refl-unit-left _)))) refl))
    (wkSub-pres-⊆-trans _ _ _)

substTm-nat : (t : Tm Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substTm (wkSub w s) t ≡ wkTm w (substTm s t)
substTm-nat (var x)           s          w
  = substVar-nat x s w
substTm-nat (lam {Γ} {a} t)   s          w
  = cong lam
      (trans
        (cong (λ s → substTm (s `, var zero) t) wkSubFreshLemma)
        (substTm-nat t (keepₛ s) (keep w)))
substTm-nat (app t u)         s          w
  = cong₂ app (substTm-nat t s w) (substTm-nat u s w)
substTm-nat (return t)        s          w
  = cong return (substTm-nat t s w) 
substTm-nat (letin t u)       s          w
  = cong₂ letin (substTm-nat t s w)
      (trans
        (cong (λ s → substTm (s `, var zero) u) wkSubFreshLemma)
        (substTm-nat u (keepₛ s) (keep w)))

assoc-substTm-wkTm : (t : Tm Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
    → substTm (trimSub w s) t ≡ substTm s (wkTm w t)
assoc-substTm-wkTm (var x)           s          w
  = assoc-substVar-wkVar x s w
assoc-substTm-wkTm (lam t)           s          w
  = cong lam (trans
    (cong (λ p → substTm (p `, var zero) t) (trimSub-nat s w freshWk))
    (assoc-substTm-wkTm t (keepₛ s) (keep w)))
assoc-substTm-wkTm (app t u)         s          w
  = cong₂ app (assoc-substTm-wkTm t s w) (assoc-substTm-wkTm u s w)
assoc-substTm-wkTm (return t)        s          w
  = cong return (assoc-substTm-wkTm t s w) 
assoc-substTm-wkTm (letin t u)       s          w
  = cong₂ letin
      (assoc-substTm-wkTm t s w)
      (trans
        (cong (λ p → substTm (p `, var zero) u) (trimSub-nat s w freshWk))
        (assoc-substTm-wkTm u (keepₛ s) (keep w)))

assoc-substTm-trimSub = assoc-substTm-wkTm

private
  -- just a helper to reduce redundancy, nothing too interesting
  auxLemma : (w : Γ ⊆ Δ) → wkSub (drop[ a ] (w ∙ ⊆-refl)) idₛ ≡ dropₛ (embWk w)

wkSub-unit-right : (w : Γ ⊆ Δ) → wkSub w idₛ ≡ embWk w
auxLemma w = (trans
    (wkSub-pres-⊆-trans w freshWk idₛ)
    (cong (wkSub freshWk) (wkSub-unit-right w)))

wkSub-unit-right base      = refl
wkSub-unit-right (drop w)  = trans
  (cong (λ w' → wkSub (drop w') idₛ) (sym (⊆-refl-unit-right w)))
  (auxLemma w)
wkSub-unit-right (keep w)  = cong (_`, var zero) (trans
  (sym (wkSub-pres-⊆-trans freshWk (keep w) idₛ))
  (trans
    (cong₂ wkSub (cong drop (trans (⊆-refl-unit-left _) (sym (⊆-refl-unit-right _)))) refl)
    (auxLemma w)))

substVar-pres-idₛ : (x : Var Γ a) → substVar idₛ x ≡ var x
substVar-pres-idₛ zero     = refl
substVar-pres-idₛ (succ x) = trans (substVar-nat x idₛ freshWk) (trans
  (cong (wkTm freshWk) (substVar-pres-idₛ x))
  (cong var (wkIncr x)))

substTm-pres-idₛ : (t : Tm Γ a) → substTm idₛ t ≡ t
substTm-pres-idₛ (var x)     = substVar-pres-idₛ x
substTm-pres-idₛ (lam t)     = cong lam (substTm-pres-idₛ t)
substTm-pres-idₛ (app t u)   = cong₂ app (substTm-pres-idₛ t) (substTm-pres-idₛ u)
substTm-pres-idₛ (return t)  = cong return (substTm-pres-idₛ t) 
substTm-pres-idₛ (letin t u) = cong₂ letin (substTm-pres-idₛ t) (substTm-pres-idₛ u)

-- TBD: rename
assoc-∙ₛ-wkSub  : {Δ'' : Ctx} (s : Sub Δ Γ) (s' : Sub Δ' Δ) (w : Δ' ⊆ Δ'')
         → wkSub w (s ∙ₛ s') ≡ s ∙ₛ (wkSub w s')
assoc-∙ₛ-wkSub []           s'             w
  = refl
assoc-∙ₛ-wkSub (s `, x)     s'             w
  = cong₂ _`,_  (assoc-∙ₛ-wkSub s s' w) (sym (substTm-nat x s' w))

-- TBD: rename
assoc-wkSub-∙ₛ  : {Δ₁ : Ctx} (s : Sub Δ Γ) (s' : Sub Δ₁ Δ') (w : Δ ⊆ Δ')
         → s ∙ₛ (trimSub w s') ≡ (wkSub w s) ∙ₛ s'
assoc-wkSub-∙ₛ []               s'          w
  = refl
assoc-wkSub-∙ₛ (s `, x)         s'          w
  = cong₂ _`,_ (assoc-wkSub-∙ₛ s s' w) (assoc-substTm-wkTm x s' w)
  
substVarPres∙ₛ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (x : Var Γ a)
  → substVar (s ∙ₛ s') x ≡ substTm s' (substVar s x)
substVarPres∙ₛ (s `, x) s' zero      = refl
substVarPres∙ₛ (s `, x) s' (succ x₁) = substVarPres∙ₛ s s' x₁

private
  dropKeepLemma : (s' : Sub Δ' Δ) (s : Sub Γ Δ')
           →  dropₛ (s' ∙ₛ s) ≡ dropₛ {a = a} s' ∙ₛ keepₛ s
  dropKeepLemma s' s = trans (assoc-∙ₛ-wkSub s' s freshWk)
    (trans
      ((cong (s' ∙ₛ_) (sym (trimSub-unit-left (dropₛ s)))))
      (assoc-wkSub-∙ₛ s' (keepₛ s) freshWk))
      
substTm-pres-∙ₛ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (t : Tm Γ a)
  → substTm (s ∙ₛ s') t ≡ substTm s' (substTm s t)
substTm-pres-∙ₛ s s'             (var x)
  = substVarPres∙ₛ s s' x
substTm-pres-∙ₛ s s'             (lam t)
  = cong lam
    (trans (cong ((λ s → substTm (s `, var zero) t)) ((dropKeepLemma s s')))
    (substTm-pres-∙ₛ _ _ t))
substTm-pres-∙ₛ s s'             (app t u)
  = cong₂ app (substTm-pres-∙ₛ s s' t) (substTm-pres-∙ₛ s s' u)
substTm-pres-∙ₛ s s'             (return t)
  = cong return (substTm-pres-∙ₛ s s' t) 
substTm-pres-∙ₛ s s'             (letin t u)
  = cong₂ letin
      (substTm-pres-∙ₛ s s' t)
      (trans
        (cong ((λ s → substTm (s `, var zero) u)) ((dropKeepLemma s s')))
        (substTm-pres-∙ₛ _ _ u))

∙ₛ-unit-right : (s : Sub Γ Γ') → s ∙ₛ idₛ ≡ s
∙ₛ-unit-right []           = refl
∙ₛ-unit-right (s `, t)     = cong₂ _`,_ (∙ₛ-unit-right s) (substTm-pres-idₛ t)

module AdhocLemmas where

  --
  keepFreshLemma : {w : Γ ⊆ Γ'} {t : Tm Γ a}
    → wkTm freshWk[ Γ' , b ] (wkTm w t) ≡ wkTm (keep w) (wkTm freshWk t)
  keepFreshLemma = trans
    (trans
      (sym (wkTm-pres-⊆-trans _ _ _))
      (cong₂ wkTm (cong drop (trans (⊆-refl-unit-right _) (sym (⊆-refl-unit-left _)))) refl))
    (wkTm-pres-⊆-trans _ _ _) 

  --
  red-fun-crunch-lemma : (w  : Γ ⊆ Δ) (u : Tm Γ a) (t : Tm (Γ `, a) b)
    → substTm (idₛ `, wkTm w u) (wkTm (keep w) t) ≡ wkTm w (substTm (idₛ `, u) t)
  red-fun-crunch-lemma w u t = trans
    (sym (assoc-substTm-wkTm t _ (keep w)))
    (sym (trans
      (sym (substTm-nat t _ _))
      (cong
        (λ p → substTm (p `, wkTm w u) t)
        (sym (trans (trimSub-unit-right w) (sym (wkSub-unit-right w)))))))

  --
  ass-dia-crunch-lemma : (w : Γ ⊆ Γ') (u' : Tm (Γ `, b) (◇ c))
    → wkTm (keep freshWk[ Γ' , a ]) (wkTm (keep w) u') ≡ wkTm (keep (keep w)) (wkTm (keep freshWk[ Γ , a ]) u')
  ass-dia-crunch-lemma w u' = trans
    (sym (wkTm-pres-⊆-trans _ _ _))
    (trans
      (cong₂ wkTm (cong (λ z → keep (drop z)) (⊆-refl-unit-right _)) refl)
      (sym (trans
        (sym (wkTm-pres-⊆-trans _ _ _))
        (cong₂ wkTm (cong (λ z → keep (drop z)) (⊆-refl-unit-left _)) refl))))
