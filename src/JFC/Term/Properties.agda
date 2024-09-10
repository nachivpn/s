{-# OPTIONS --safe --without-K #-}
module JFC.Term.Properties where

open import JFC.Term.Base

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

wkTm-pres-⊆-refl : (t : Tm Γ a) → wkTm ⊆-refl t ≡ t
wkTm-pres-⊆-refl (var   v)    = cong  var (wkVar-pres-⊆-refl v)
wkTm-pres-⊆-refl unit         = refl
wkTm-pres-⊆-refl (fst t)      = cong fst (wkTm-pres-⊆-refl t)
wkTm-pres-⊆-refl (snd t)      = cong snd (wkTm-pres-⊆-refl t)
wkTm-pres-⊆-refl (pair t u)   = cong₂ pair (wkTm-pres-⊆-refl t) (wkTm-pres-⊆-refl u)
wkTm-pres-⊆-refl (lam   t)    = cong  lam (wkTm-pres-⊆-refl  t)
wkTm-pres-⊆-refl (app   t u)  = cong₂ app (wkTm-pres-⊆-refl  t) (wkTm-pres-⊆-refl u)
wkTm-pres-⊆-refl (sletin t u) = cong₂ sletin (wkTm-pres-⊆-refl t) (wkTm-pres-⊆-refl u)
wkTm-pres-⊆-refl (jletin t u) = cong₂ jletin (wkTm-pres-⊆-refl t) (wkTm-pres-⊆-refl u)

wkTm-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (t : Tm Γ a)
  → wkTm (w ∙ w') t ≡ wkTm w' (wkTm w t)
wkTm-pres-⊆-trans w w' (var   v)    = cong  var (wkVar-pres-⊆-trans w w' v)
wkTm-pres-⊆-trans w w' unit         = refl
wkTm-pres-⊆-trans w w' (fst t)      = cong fst (wkTm-pres-⊆-trans w w' t)
wkTm-pres-⊆-trans w w' (snd t)      = cong snd (wkTm-pres-⊆-trans w w' t)
wkTm-pres-⊆-trans w w' (pair t u)   = cong₂ pair (wkTm-pres-⊆-trans w w' t) (wkTm-pres-⊆-trans w w' u)
wkTm-pres-⊆-trans w w' (lam   t)    = cong  lam (wkTm-pres-⊆-trans (keep w) (keep  w') t)
wkTm-pres-⊆-trans w w' (app   t u)  = cong₂ app (wkTm-pres-⊆-trans w w' t) (wkTm-pres-⊆-trans w w' u)
wkTm-pres-⊆-trans w w' (sletin t u) = cong₂ sletin (wkTm-pres-⊆-trans w w' t) (wkTm-pres-⊆-trans (keep w) (keep w') u)
wkTm-pres-⊆-trans w w' (jletin t u) = cong₂ jletin (wkTm-pres-⊆-trans w w' t) (wkTm-pres-⊆-trans (keep w) (keep w') u)


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
      (cong₂ wkSub (cong drop (trans (⊆-trans-unit-right _) (sym (⊆-trans-unit-left _)))) refl))
    (wkSub-pres-⊆-trans _ _ _)

substTm-nat : (t : Tm Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substTm (wkSub w s) t ≡ wkTm w (substTm s t)
substTm-nat (var x)           s          w
  = substVar-nat x s w
substTm-nat unit              s          w = refl
substTm-nat (fst t)           s          w
  = cong fst (substTm-nat t s w)
substTm-nat (snd t)           s          w
  = cong snd (substTm-nat t s w)
substTm-nat (pair t u)        s          w
  = cong₂ pair (substTm-nat t s w) (substTm-nat u s w)
substTm-nat (lam {Γ} {a} t)   s          w
  = cong lam
      (trans
        (cong (λ s → substTm (s `, var zero) t) wkSubFreshLemma)
        (substTm-nat t (keepₛ s) (keep w)))
substTm-nat (app t u)         s          w
  = cong₂ app (substTm-nat t s w) (substTm-nat u s w)
substTm-nat (sletin t u)      s         w
  = cong₂ sletin (substTm-nat t s w)
      (trans
        (cong (λ s → substTm (s `, var zero) u) wkSubFreshLemma)
        (substTm-nat u (keepₛ s) (keep w)))
substTm-nat (jletin t u)      s         w
  = cong₂ jletin (substTm-nat t s w)
      (trans
        (cong (λ s → substTm (s `, var zero) u) wkSubFreshLemma)
        (substTm-nat u (keepₛ s) (keep w)))

assoc-substTm-wkTm : (t : Tm Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
    → substTm (trimSub w s) t ≡ substTm s (wkTm w t)
assoc-substTm-wkTm (var x)           s          w
  = assoc-substVar-wkVar x s w
assoc-substTm-wkTm unit s w
  = refl
assoc-substTm-wkTm (fst t)           s          w
  = cong fst (assoc-substTm-wkTm t s w)
assoc-substTm-wkTm (snd t)           s          w
  = cong snd (assoc-substTm-wkTm t s w)
assoc-substTm-wkTm (pair t u)        s          w
  = cong₂ pair (assoc-substTm-wkTm t s w) (assoc-substTm-wkTm u s w)
assoc-substTm-wkTm (lam t)           s          w
  = cong lam (trans
    (cong (λ p → substTm (p `, var zero) t) (trimSub-nat s w freshWk))
    (assoc-substTm-wkTm t (keepₛ s) (keep w)))
assoc-substTm-wkTm (app t u)         s          w
  = cong₂ app (assoc-substTm-wkTm t s w) (assoc-substTm-wkTm u s w)
assoc-substTm-wkTm (sletin t u)       s          w
  = cong₂ sletin
      (assoc-substTm-wkTm t s w)
      (trans
        (cong (λ p → substTm (p `, var zero) u) (trimSub-nat s w freshWk))
        (assoc-substTm-wkTm u (keepₛ s) (keep w)))
assoc-substTm-wkTm (jletin t u)       s          w
  = cong₂ jletin
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
  (cong (λ w' → wkSub (drop w') idₛ) (sym (⊆-trans-unit-right w)))
  (auxLemma w)
wkSub-unit-right (keep w)  = cong (_`, var zero) (trans
  (sym (wkSub-pres-⊆-trans freshWk (keep w) idₛ))
  (trans
    (cong₂ wkSub (cong drop (trans (⊆-trans-unit-left _) (sym (⊆-trans-unit-right _)))) refl)
    (auxLemma w)))

substVar-pres-idₛ : (x : Var Γ a) → substVar idₛ x ≡ var x
substVar-pres-idₛ zero     = refl
substVar-pres-idₛ (succ x) = trans (substVar-nat x idₛ freshWk) (trans
  (cong (wkTm freshWk) (substVar-pres-idₛ x))
  (cong var (wkIncr x)))

substTm-pres-idₛ : (t : Tm Γ a) → substTm idₛ t ≡ t
substTm-pres-idₛ (var x)      = substVar-pres-idₛ x
substTm-pres-idₛ unit         = refl
substTm-pres-idₛ (fst t)      = cong fst (substTm-pres-idₛ t)
substTm-pres-idₛ (snd t)      = cong snd (substTm-pres-idₛ t)
substTm-pres-idₛ (pair t u)   = cong₂ pair (substTm-pres-idₛ t) (substTm-pres-idₛ u)
substTm-pres-idₛ (lam t)      = cong lam (substTm-pres-idₛ t)
substTm-pres-idₛ (app t u)    = cong₂ app (substTm-pres-idₛ t) (substTm-pres-idₛ u)
substTm-pres-idₛ (sletin t u) = cong₂ sletin (substTm-pres-idₛ t) (substTm-pres-idₛ u)
substTm-pres-idₛ (jletin t u) = cong₂ jletin (substTm-pres-idₛ t) (substTm-pres-idₛ u)

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
substTm-pres-∙ₛ s s'             unit
  = refl
substTm-pres-∙ₛ s s'             (fst t)
  = cong fst (substTm-pres-∙ₛ s s' t)
substTm-pres-∙ₛ s s'             (snd t)
  = cong snd (substTm-pres-∙ₛ s s' t)
substTm-pres-∙ₛ s s'             (pair t u)
  = cong₂ pair (substTm-pres-∙ₛ s s' t) (substTm-pres-∙ₛ s s' u)
substTm-pres-∙ₛ s s'             (lam t)
  = cong lam
    (trans (cong ((λ s → substTm (s `, var zero) t)) ((dropKeepLemma s s')))
    (substTm-pres-∙ₛ _ _ t))
substTm-pres-∙ₛ s s'             (app t u)
  = cong₂ app (substTm-pres-∙ₛ s s' t) (substTm-pres-∙ₛ s s' u)
substTm-pres-∙ₛ s s'             (sletin t u)
  = cong₂ sletin
      (substTm-pres-∙ₛ s s' t)
      (trans
        (cong ((λ s → substTm (s `, var zero) u)) ((dropKeepLemma s s')))
        (substTm-pres-∙ₛ _ _ u))
substTm-pres-∙ₛ s s'             (jletin t u)
  = cong₂ jletin
      (substTm-pres-∙ₛ s s' t)
      (trans
        (cong ((λ s → substTm (s `, var zero) u)) ((dropKeepLemma s s')))
        (substTm-pres-∙ₛ _ _ u))

∙ₛ-unit-right : (s : Sub Γ Γ') → s ∙ₛ idₛ ≡ s
∙ₛ-unit-right []           = refl
∙ₛ-unit-right (s `, t)     = cong₂ _`,_ (∙ₛ-unit-right s) (substTm-pres-idₛ t)

∙ₛ-unit-left : (s : Sub Γ Γ') → idₛ ∙ₛ s ≡ s
∙ₛ-unit-left []       = refl
∙ₛ-unit-left (s `, t) = cong (_`, t) (trans
  (trans
    (cong (_∙ₛ (s `, t)) (sym (auxLemma ⊆-refl)))
    (trans
      (sym (trans (assoc-wkSub-∙ₛ  idₛ (s `, t) freshWk)
      (cong (λ w → (wkSub w idₛ ∙ₛ (s `, t))) (cong drop (sym (⊆-trans-unit-left _))) )))
    (cong (idₛ ∙ₛ_) (trimSub-unit-left s))))
  (∙ₛ-unit-left s))

dropₛ-trims : (s : Sub Γ Δ) (s' : Sub Γ' Γ) (t : Tm Γ' a) → dropₛ s ∙ₛ (s' `, t) ≡ s ∙ₛ s'
dropₛ-trims s s' t = trans
  (sym (assoc-wkSub-∙ₛ _ _ _))
  (cong (s ∙ₛ_) (trimSub-unit-left _))

dropₛ-nat : (s : Sub Γ Δ) (s' : Sub Γ' Γ) → dropₛ {a = a} (s ∙ₛ s') ≡ s ∙ₛ dropₛ s'
dropₛ-nat s s' = assoc-∙ₛ-wkSub s s' freshWk
      
module AdhocLemmas where

  --
  keepFreshLemma : {w : Γ ⊆ Γ'} {t : Tm Γ a}
    → wkTm freshWk[ Γ' , b ] (wkTm w t) ≡ wkTm (keep w) (wkTm freshWk t)
  keepFreshLemma = trans
    (trans
      (sym (wkTm-pres-⊆-trans _ _ _))
      (cong₂ wkTm (cong drop (trans (⊆-trans-unit-right _) (sym (⊆-trans-unit-left _)))) refl))
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
  aux-dia-crunch-lemma : (w : Γ ⊆ Γ') (u' : Tm (Γ `, b) c)
    → wkTm (keep freshWk[ Γ' , a ]) (wkTm (keep w) u') ≡ wkTm (keep (keep w)) (wkTm (keep freshWk[ Γ , a ]) u')
  aux-dia-crunch-lemma w u' = trans
    (sym (wkTm-pres-⊆-trans _ _ _))
    (trans
      (cong₂ wkTm (cong (λ z → keep (drop z)) (⊆-trans-unit-right _)) refl)
      (sym (trans
        (sym (wkTm-pres-⊆-trans _ _ _))
        (cong₂ wkTm (cong (λ z → keep (drop z)) (⊆-trans-unit-left _)) refl))))

  --
  letin-collecAcc-crunch-lemma : (w : (Γ `, c) ⊆ Δ) (t : Tm Δ a) (u : Tm (Γ `, a) b)
    → substTm (embWk w `, t) (wkTm (keep freshWk) u) ≡ substTm (embWk (freshWk ∙ w) `, t) u
  letin-collecAcc-crunch-lemma w t u = let open ≡-Reasoning in begin
      substTm (embWk w `, t) (wkTm (keep freshWk) u)
        ≡˘⟨ assoc-substTm-wkTm u (embWk w `, t) (keep freshWk) ⟩
      substTm (trimSub (keep freshWk) (embWk w `, t)) u
        ≡˘⟨ cong (λ z → substTm (trimSub (keep freshWk) (z `, t)) u) (wkSub-unit-right w) ⟩
      substTm (trimSub (keep freshWk) (wkSub w idₛ `, t)) u
        ≡⟨⟩
      substTm (trimSub ⊆-refl (wkSub w (wkSub freshWk idₛ) `, t)) u
        ≡⟨ cong (λ z → substTm (z `, t) u) (trimSub-unit-left _) ⟩
      substTm ((wkSub w (wkSub freshWk idₛ) `, t)) u
        ≡˘⟨ cong (λ z → substTm (z `, t) u) (wkSub-pres-⊆-trans freshWk w idₛ)  ⟩
      substTm (wkSub (freshWk ∙ w) idₛ `, t) u
        ≡⟨ cong (λ z → substTm (z `, t) u) (wkSub-unit-right (freshWk ∙ w)) ⟩
      substTm (embWk (freshWk ∙ w) `, t) u ∎

  --
  red-ass-dia-crunch-lemma : (w : Γ ⊆ Θ) (s : Sub Γ Δ) (t : Tm Θ a)
    → wkSub freshWk s ∙ₛ (embWk w `, t) ≡ wkSub w s
  red-ass-dia-crunch-lemma w s t = let open ≡-Reasoning in begin
    wkSub freshWk s ∙ₛ (embWk w `, t)
      ≡˘⟨ assoc-wkSub-∙ₛ s (embWk w `, t) freshWk ⟩
    s ∙ₛ trimSub freshWk (embWk w `, t)
      ≡⟨⟩
    s ∙ₛ trimSub ⊆-refl (embWk w)
      ≡⟨ cong (s ∙ₛ_) (trimSub-unit-left (embWk w)) ⟩
    s ∙ₛ embWk w
      ≡˘⟨ cong (s ∙ₛ_) (wkSub-unit-right w) ⟩
    s ∙ₛ wkSub w idₛ
      ≡˘⟨ assoc-∙ₛ-wkSub s idₛ w ⟩
    wkSub w (s ∙ₛ idₛ)
      ≡⟨ cong (wkSub w) (∙ₛ-unit-right s) ⟩
    wkSub w s ∎

  --
  red-dia-crunch-lemma : (w : Γ ⊆ Γ') (u : Tm (Γ `, a) b) (u' : Tm (Γ `, b) c)
    → substTm (dropₛ idₛ `, wkTm (keep w) u) (wkTm (keep w) u') ≡ wkTm (keep w) (substTm (dropₛ idₛ `, u) u')
  red-dia-crunch-lemma w u u' = let open ≡-Reasoning in begin
    substTm (wkSub freshWk idₛ `, wkTm (keep w) u) (wkTm (keep w) u')
      ≡⟨ sym (assoc-substTm-wkTm u' _ _) ⟩
    substTm (trimSub (keep w) (wkSub freshWk idₛ `, wkTm (keep w) u)) u'
      ≡⟨⟩
    substTm (trimSub w (wkSub freshWk idₛ) `, wkTm (keep w) u) u'
      ≡⟨ cong₂ substTm (cong (_`, wkTm (keep w) u) (sym (trimSub-nat idₛ w freshWk))) (refl {x = u'}) ⟩
    substTm (wkSub freshWk (trimSub w idₛ) `, wkTm (keep w) u) u'
      ≡⟨ cong₂ substTm (cong (_`, wkTm (keep w) u) (cong (wkSub _) (trimSub-unit-right w))) (refl {x = u'}) ⟩
    substTm (wkSub freshWk (embWk w) `, wkTm (keep w) u) u'
      ≡⟨ cong₂ substTm (cong (_`, wkTm (keep w) u) (cong (wkSub _) (sym (wkSub-unit-right w)))) (refl {x = u'}) ⟩      
    substTm (wkSub freshWk (wkSub w idₛ) `, wkTm (keep w) u) u'
     ≡⟨ cong₂ substTm (cong (_`, wkTm (keep w) u) (sym (wkSub-pres-⊆-trans w freshWk idₛ))) (refl {x = u'}) ⟩
    substTm (wkSub (w ∙ freshWk) idₛ `, wkTm (keep w) u) u'  
     ≡⟨ cong₂ substTm (cong (_`, wkTm (keep w) u) (cong₂ wkSub (cong drop (trans (⊆-trans-unit-right w) (sym (⊆-trans-unit-left w)) )) refl)) (refl {x = u'}) ⟩     
    substTm (wkSub (drop (⊆-refl ∙ w)) idₛ `, wkTm (keep w) u) u'
     ≡⟨⟩
    substTm (wkSub (freshWk ∙ keep w) idₛ `, wkTm (keep w) u) u'
     ≡⟨ cong₂ substTm (cong₂ _`,_ (wkSub-pres-⊆-trans freshWk (keep w) idₛ) refl) (refl {x = u'}) ⟩
    substTm (wkSub (keep w) (wkSub freshWk idₛ) `, wkTm (keep w) u) u'
      ≡⟨⟩
    substTm (wkSub (keep w) (wkSub freshWk idₛ `, u)) u'
      ≡⟨ substTm-nat u' _ _ ⟩
    wkTm (keep w) (substTm (wkSub freshWk idₛ `, u) u') ∎

  dropₛ-keepₛ-lemma = dropKeepLemma

  red-fun-crunch-subst-lemma : (s : Sub Δ Γ) (t : Tm (Γ `, a) b) (u : Tm Γ a)
    → substTm (idₛ `, substTm s u) (substTm (keepₛ s) t) ≡ substTm s (substTm (idₛ `, u) t)
  red-fun-crunch-subst-lemma s t u = let open ≡-Reasoning in begin
    substTm _ (substTm _ t)
      ≡˘⟨ substTm-pres-∙ₛ _ _ t ⟩
    substTm ((dropₛ s ∙ₛ (idₛ `, substTm s u)) `, substTm s u) t
      ≡⟨ cong (λ z → substTm (z `, substTm s u) t) (dropₛ-trims _ _ _) ⟩
    substTm ((s ∙ₛ idₛ) `, substTm s u) t
      ≡⟨ cong (λ z → substTm (z `, substTm s u) t) (∙ₛ-unit-right s) ⟩
    substTm (s `, substTm s u) t
      ≡˘⟨ cong (λ z → substTm (z `, substTm s u) t) (∙ₛ-unit-left s)  ⟩
    substTm ((idₛ ∙ₛ s) `, substTm s u) t
      ≡⟨ substTm-pres-∙ₛ (idₛ `, u) s t ⟩
    substTm s (substTm (idₛ `, u) t) ∎  

  exp-fun-crunch-subst-lemma : (s : Sub Δ Γ) (t : Tm Γ (a ⇒ b))
    → wkTm freshWk[ Δ , a ] (substTm s t)
    ≡ substTm (keepₛ s) (wkTm freshWk t)
  exp-fun-crunch-subst-lemma s t = sym (trans
      (trans
        (sym (assoc-substTm-wkTm t (keepₛ s) freshWk))
        (cong (λ z → substTm z t) (trimSub-unit-left (wkSub freshWk s))))
      (substTm-nat t s freshWk))
  
  red-dia-crunch-subst-lemma : ∀ (s : Sub Δ Γ) (u : Tm (Γ `, a) b) (u' : Tm (Γ `, b) c)
    → substTm (dropₛ {a = a} idₛ `, substTm (keepₛ s) u) (substTm (keepₛ s) u')
    ≡ substTm (keepₛ s) (substTm (dropₛ idₛ `, u) u')

  red-dia-crunch-subst-lemma s u u' = trans
    (sym (substTm-pres-∙ₛ (keepₛ s) _ u'))
    (trans
      (cong (λ z → substTm (z `, substTm (keepₛ s) u) u')
         (trans
           (dropₛ-trims _ _ _)
           (trans
             (sym (trans
               (cong dropₛ (trans (∙ₛ-unit-left s) (sym (∙ₛ-unit-right s))))
               (dropₛ-nat s idₛ)))
             (dropₛ-keepₛ-lemma idₛ s))))
       (substTm-pres-∙ₛ _ (keepₛ s) u'))

  aux-dia-crunch-subst-lemma : (s : Sub Δ Γ) (u : Tm (Γ `, a) (◇ b)) (u' : Tm (Γ `, b) c)
    → wkTm (keep freshWk) (substTm (keepₛ s) u') ≡ substTm (keepₛ (keepₛ {a = d} s)) (wkTm (keep freshWk) u')
  aux-dia-crunch-subst-lemma s u u' = let open ≡-Reasoning in begin
    wkTm (keep freshWk) (substTm (keepₛ s) u')
      ≡˘⟨ substTm-nat u' _ _ ⟩
    substTm (wkSub (keep freshWk) (keepₛ s)) u'
      ≡˘⟨ cong (λ z → substTm (z `, _) u') (wkSub-pres-⊆-trans _ _ s) ⟩
    substTm (wkSub (freshWk ∙ keep freshWk) s `, var zero) u'
      ≡⟨ cong (λ z → substTm (z `, _) u') (wkSub-pres-⊆-trans _ _ s) ⟩
    substTm (wkSub freshWk (dropₛ s) `, var zero) u'
      ≡˘⟨ cong (λ z → substTm (z `, _) u') (trimSub-unit-left _) ⟩
    substTm (trimSub (keep freshWk) (keepₛ (keepₛ s))) u'
      ≡⟨ assoc-substTm-wkTm u' _ _ ⟩
    substTm (keepₛ (keepₛ s)) (wkTm (keep freshWk) u')
      ∎
