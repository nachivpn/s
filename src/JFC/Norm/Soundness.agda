{-# OPTIONS --safe --without-K #-}
module JFC.Norm.Soundness where

open import Data.Unit using (⊤ ; tt)
open import Data.Product as DP using (Σ ; _,_ ; -,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import JFC.Term
open import JFC.Term.NormalForm
open import JFC.Term.Conversion

open import JFC.Norm.Base

Tm'- : Ty → Psh
Tm'- a = record
          { Fam           = λ Γ → Tm Γ a
          ; _≋_           = _≈_
          ; ≋-equiv       = λ _ → ≈-is-equiv
          ; wk            = wkTm
          ; wk-pres-≋     = wkTm-pres-≈
          ; wk-pres-refl  = λ x → ≡-to-≈ (wkTm-pres-⊆-refl x)
          ; wk-pres-trans = λ w w' x → ≡-to-≈ (wkTm-pres-⊆-trans w w' x)
          }

embNe : Ne'- a →̇ Tm'- a
embNe = record
  { fun     = embNe-fun
  ; pres-≋  = λ p≋p' → ≡-to-≈ (cong embNe-fun p≋p')
  ; natural = λ w n → ≡-to-≈ (embNe-nat w n)
  }

embNf : Nf'- a →̇ Tm'- a
embNf = record
  { fun     = embNf-fun
  ; pres-≋  = λ p≋p' → ≡-to-≈ (cong embNf-fun p≋p')
  ; natural = λ w n → ≡-to-≈ (embNf-nat w n)
  }

reifyTm : (a : Ty) → Ty'- a →̇ Tm'- a
reifyTm a = embNf ∘ reify a

quotTm : Sub'- Γ →̇ Ty'- a → Tm Γ a
quotTm {Γ} {a} f = reifyTm a .apply (f .apply (idEnv Γ))

registerTm : {a : Ty} → Ne'- (◇ a) →̇ ◇' (Tm'- a)
registerTm = (◇'-map embNe) ∘ register

module Core
  (collectTm     : {a : Ty} → ◇' (Tm'- a) →̇ Tm'- (◇ a))
  (collect-comm  : {a : Ty} → collectTm ∘ ◇'-map embNf ≈̇ embNf ∘ collectNf {a})
  (register-exp  : {a : Ty} → embNe ≈̇ collectTm {a} ∘ registerTm)
  where

  ℒ : (a : Ty) → (t : Tm Γ a) → (x : Ty' Γ a) → Set
  ℒ {_} ι       t n =
    t ≈ reifyTm ι .apply n
  ℒ {_} 𝟙       t n =
    ⊤
  ℒ {_} (a × b) t p =
    ℒ a (fst t) (π₁' .apply p) DP.× ℒ b (snd t) (π₂' .apply p)
  ℒ {Γ} (a ⇒ b) t f =
    ∀ {Γ' : Ctx} {u : Tm Γ' a} {x : Ty' Γ' a}
    → (w : Γ ⊆ Γ') → (uℒx : ℒ a u x) → ℒ b (app (wkTm w t) u) (f .apply w x)
  ℒ {_} (◇ a)   t (elem (Δ , r , x)) =
    Σ (Tm Δ a) λ u → t ≈ collectTm .apply (elem (Δ , r , u)) DP.× ℒ a u x

  ℒₛ : {Γ : Ctx} (Δ : Ctx) → Sub Γ Δ → Sub' Γ Δ → Set
  ℒₛ []       []       tt              = ⊤
  ℒₛ (Δ `, a) (s `, t) (elem (δ , x)) = ℒₛ Δ s δ DP.× ℒ a t x

  ℒ-prepend : (a : Ty) {t u : Tm Γ a} {x : Ty' Γ a}
    → t ≈ u → ℒ a u x → ℒ a t x
  ℒ-prepend ι       t≈u uLn
    = ≈-trans t≈u uLn
  ℒ-prepend 𝟙       t≈u _uLx
    = tt
  ℒ-prepend (a × b) t≈u uLp
    = ℒ-prepend a (cong-fst t≈u) (proj₁ uLp) , ℒ-prepend b (cong-snd t≈u) (proj₂ uLp)
  ℒ-prepend (a ⇒ b) t≈u uLf
    = λ w uLy → ℒ-prepend b (cong-app1 (wk[ Tm'- (a ⇒ b) ]-pres-≋ w t≈u)) (uLf w uLy)
  ℒ-prepend (◇ a)   t≈u (u' , u≈_ , u'Lx)
    = u' , ≈-trans t≈u u≈_ , u'Lx

  ℒ-build   : (a : Ty) → {t : Tm Γ a} {x : Ty' Γ a} → ℒ a t x → t ≈ reifyTm a .apply x
  ℒ-reflect : (a : Ty) (n : Ne Γ a) → ℒ a (embNe .apply n) (reflect a .apply n)

  ℒ-build ι        tLx
    = tLx
  ℒ-build 𝟙        tLx
    = exp-unit _
  ℒ-build (a × b)  tLp
    = ≈-trans (exp-prod _) (cong-pair (ℒ-build a (proj₁ tLp)) (ℒ-build b (proj₂ tLp)))
  ℒ-build (a ⇒ b)  tLx
    = ≈-trans (exp-fun _) (cong-lam (ℒ-build b (tLx freshWk (ℒ-reflect a (var zero)))))
  ℒ-build (◇ a)    {x = elem (Δ , r , x)} tr@(u , t≈_ , uLx)
    = ≈-trans t≈_ (≈-trans (collectTm .apply-≋ (proof (≡-refl , ≡-refl , ℒ-build a uLx))) (collect-comm .apply-≋ _))

  ℒ-reflect ι       n = ≈-refl
  ℒ-reflect 𝟙       n = tt
  ℒ-reflect (a × b) n = ℒ-reflect a (fst n) , ℒ-reflect b (snd n)
  ℒ-reflect (a ⇒ b) n = λ w uLx → ℒ-prepend b (cong-app (embNe .natural w _) (ℒ-build a uLx)) (ℒ-reflect b (app (wkNe w n) (reify a .apply _)))
  ℒ-reflect (◇ a)   n = var zero , register-exp .apply-≋ n , ℒ-reflect a (var zero)

  ℒ-cast : {t u : Tm Γ a} {x : Ty' Γ a}
       → (t≡u : t ≡ u)
       → (uℒx : ℒ a u x)
       → ℒ a t x
  ℒ-cast ≡-refl uLx = uLx

  wkTm-pres-ℒ : {t : Tm Γ a} {x : Ty' Γ a}
    → (w : Γ ⊆ Γ')
    → (tLx : ℒ a t x)
    → ℒ a (wkTm w t) (wkTy' a w x)
  wkTm-pres-ℒ {a = ι}     {x = x} w tLn
    = ≈-trans (wkTm-pres-≈ w tLn) (embNf .natural w (reify _ .apply x))
  wkTm-pres-ℒ {a = 𝟙}     {x = x} w tLx
    = tt
  wkTm-pres-ℒ {a = a × b} {t = t} w tLp
    = wkTm-pres-ℒ w (proj₁ tLp) , wkTm-pres-ℒ w (proj₂ tLp)
  wkTm-pres-ℒ {a = a ⇒ b} {t = t} w tLf
    = λ w' y → ℒ-cast (cong₂ app (≡-sym (wkTm-pres-⊆-trans w w' t)) ≡-refl) (tLf (w ∙ w') y)
  wkTm-pres-ℒ {a = ◇ a}  {x = elem (Δ , r , x)}         w (u , tr , uLx)
    = wkTm (factor⊆ w r) u
      , ≈-trans (wkTm-pres-≈ w tr) (collectTm .natural w (elem (Δ , r , u)))
      , wkTm-pres-ℒ (factor⊆ w r) uLx

  --
  wkSub-pres-ℒₛ : {s : Sub Γ Δ} {δ : Sub' Γ Δ}
    → (w : Γ ⊆ Γ')
    → (sLδ : ℒₛ Δ s δ)
    → ℒₛ Δ (wkSub w s) (wkSub' Δ w δ)
  wkSub-pres-ℒₛ {s = []}       w p
    = tt
  wkSub-pres-ℒₛ {s = _s `, t}  w (sLδ , tLx)
    = wkSub-pres-ℒₛ w sLδ , wkTm-pres-ℒ w tLx

  --
  idℒₛ : ∀ Δ → ℒₛ Δ idₛ (idEnv Δ)
  idℒₛ []       = tt
  idℒₛ (Δ `, a) = wkSub-pres-ℒₛ freshWk (idℒₛ Δ) , ℒ-reflect a (var zero)

  --
  Fund : Tm Δ a → Set
  Fund {Δ} {a} t = ∀ {Γ} {s : Sub Γ Δ} {δ : Sub' Γ Δ}
    → (sLδ : ℒₛ Δ s δ) → ℒ a (substTm s t) (eval t .apply δ)

  --
  module Sound (fund : {Δ : Ctx} {a : Ty} → (t : Tm Δ a) → Fund t) where

    --
    quotTm-retracts-eval : (t : Tm Γ a) → t ≈ quotTm (eval t)
    quotTm-retracts-eval t = ℒ-build _ (ℒ-prepend _ (≡-to-≈ (≡-sym (substTm-pres-idₛ t))) (fund t (idℒₛ _)))

    -- normalization is sound
    norm-sound : {t u : Tm Γ a} → norm t ≡ norm u → t ≈ u
    norm-sound {Γ} {a} {t} {u} nt≡nu = ≈-trans
      (quotTm-retracts-eval t)
      (≈-trans
        (≡-to-≈ (cong (embNf .apply) nt≡nu))
        (≈-sym (quotTm-retracts-eval u)))

collectAcc : Γ ⊲ Δ → Tm Δ a → Tm Γ (◇ a)
collectAcc (single n) t0 = sletin (embNe-fun n) t0
collectAcc (cons n m) t0 = jletin (embNe-fun n) (collectAcc m t0)

collect-fun : (◇' Tm'- a) ₀ Γ → Tm'- (◇ a) ₀ Γ
collect-fun (elem (Δ , m , t0)) = collectAcc m t0

collectAcc-pres-≈ : (m : Γ ⊲ Δ) {t t' : Tm Δ a} → t ≈ t' → collectAcc m t ≈ collectAcc m t'
collectAcc-pres-≈ (single n) t≈t' = cong-sletin2 t≈t'
collectAcc-pres-≈ (cons x m) t≈t' = cong-jletin2 (collectAcc-pres-≈ m t≈t')

collect-pres-≋ : Pres-≋ (◇' Tm'- a) (Tm'- (◇ a)) collect-fun
collect-pres-≋ {p = elem (Δ , m , t)} {p' = elem (.Δ , .m , t')} (proof (≡-refl , ≡-refl , tr))
  = collectAcc-pres-≈ m tr

collectAcc-nat : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) (t : Tm Δ a)
  → wkTm w (collectAcc m t) ≈ collectAcc (factor⊲ w m) (wkTm (factor⊆ w m) t)
collectAcc-nat w (single n) t0 = cong-sletin1 (embNe .natural w n)
collectAcc-nat w (cons n m) t0 = cong-jletin (embNe .natural w n) (collectAcc-nat (keep w) m t0)

collect-nat : Natural (◇' Tm'- a) (Tm'- (◇ a)) collect-fun
collect-nat w (elem (Δ , m , t0)) = collectAcc-nat w m t0

collectTm : {a : Ty} → ◇' (Tm'- a) →̇ Tm'- (◇ a)
collectTm = record
  { fun     = collect-fun
  ; pres-≋  = collect-pres-≋
  ; natural = collect-nat
  }

collectAcc-comm : (m : Γ ⊲ Δ) (n0 : Nf Δ a)
  → collectAcc m (embNf-fun n0) ≈ embNf-fun (collectNfAcc m n0)
collectAcc-comm (single n) t0 = ≈-refl
collectAcc-comm (cons n m) t0 = cong-jletin2 (collectAcc-comm m t0)

collect-comm : collectTm ∘ ◇'-map embNf ≈̇ embNf ∘ collectNf {a}
collect-comm = record { proof = λ { (elem (Δ , m , n0)) → collectAcc-comm m n0 } }

register-exp : embNe ≈̇ collectTm {a} ∘ registerTm
register-exp = record { proof = λ n → exp-dia (embNe .apply n) }

open Core collectTm collect-comm register-exp

private
  fund-var : (v : Var Δ a) {s : Sub Γ Δ} {δ : Sub' Γ Δ}
    → (sLδ : ℒₛ Δ s δ)
    → ℒ a (substVar s v) (eval (var v) .apply δ)
  fund-var v0       {s = _ `, _}  (_ , sLδ) = sLδ
  fund-var (succ v) {s = _ `, _} (sLδ  , _tLx) = fund-var v sLδ

join : Tm Γ (◇ (◇ a)) → Tm Γ (◇ a)
join t = jletin t (var v0)

collectAcc-joins-⊲ : (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ') (t : Tm Δ' a)
  → join (collectAcc m (collectAcc m' t)) ≈ collectAcc (⊲-trans m m') t
collectAcc-joins-⊲ (single n) m' t
  = red-dia2 _ _ _
collectAcc-joins-⊲ (cons x m) m' t
  = ≈-trans (ass-dia _ _ _) (cong-jletin2 (collectAcc-joins-⊲ m m' t))

-- collecting "letin"
cletin : (m : Γ ⊲ Δ) (t : Tm Δ a) (u : Tm (Γ `, a) b) → Tm Γ (◇ b)
cletin m t u = collectAcc m (substTm (embWk (⊲-to-⊆ m) `, t) u)

open AdhocLemmas using (collectAcc-crunch-lemma ; comp-dia-crunch-lemma)

sletin-tr-lemma : (m : Γ ⊲ Δ) (t : Tm Δ a) (u : Tm (Γ `, a) b)
  → sletin (collectAcc m t) u ≈ cletin m t u
sletin-tr-lemma (single x) t u = red-dia1 _ _ _
sletin-tr-lemma (cons x m) t u = ≈-trans (com-dia _ _ _)
  (cong-jletin2 (≈-trans
    (sletin-tr-lemma m t (wkTm (keep freshWk) u))
    (collectAcc-pres-≈ m (≡-to-≈ (collectAcc-crunch-lemma (⊲-to-⊆ m) t u)))))

jletin-tr-lemma : (m : Γ ⊲ Δ) (t : Tm Δ a) (u : Tm (Γ `, a) (◇ b))
  → jletin (collectAcc m t) u ≈ join (cletin m t u)
jletin-tr-lemma (single x) t u = ≈-trans (red-dia2 _ _ _) (≈-sym (red-dia2 _ _ _))
jletin-tr-lemma (cons x m) t u = ≈-trans (ass-dia _ _ _)
  (≈-trans
    (cong-jletin2
      (≈-trans (jletin-tr-lemma m t (wkTm (keep freshWk) u))
      (cong-jletin1 (collectAcc-pres-≈ m (≡-to-≈ (collectAcc-crunch-lemma (⊲-to-⊆ m) t u))))))
    (≈-sym (ass-dia _ _ _)))

fund : (t : Tm Δ a) → Fund t
fund (var v) {_Γ} {_s} {_δ}   sLδ
  = fund-var v sLδ
fund unit         sLδ
  = tt
fund (fst t)      sLδ
  = proj₁ (fund t sLδ)
fund (snd t)      sLδ
  = proj₂ (fund t sLδ)
fund (pair t u)   sLδ
  = ℒ-prepend _ (red-prod1 _ _) (fund t sLδ)
  , ℒ-prepend _ (red-prod2 _ _) (fund u sLδ)
fund (lam t) {_Γ} {s} {_δ}    sLδ {_Γ'} {u}
  = λ w uLx → ℒ-prepend _
      (red-fun-tr-lemma w s t u)
      (fund t (wkSub-pres-ℒₛ w sLδ , uLx))
fund (app t u) {_Γ} {_s} {_δ} sLδ
  = ℒ-cast
      (cong₂ app (≡-sym (wkTm-pres-⊆-refl _)) ≡-refl)
      (fund t sLδ ⊆-refl (fund u sLδ))
fund (sletin {Δ} {a} {b} t u) {Γ} {s} {δ} sLδ
  with eval t .apply δ | fund t sLδ
... | elem (Θ , mt , x) | (t' , tr-t , t'Lx)
  = substTm (wkSub (⊲-to-⊆ mt) s `, t') u
  , tr-aux
  , fund u (wkSub-pres-ℒₛ (⊲-to-⊆ mt) sLδ , t'Lx)
  where
  tr-aux : substTm s (sletin t u) ≈ collectAcc mt (substTm (wkSub (⊲-to-⊆ mt) s `, t') u)
  tr-aux = let open EqReasoning (Tm-setoid _ _) in begin
    sletin (substTm s t) (substTm (keepₛ s) u)
      ≈⟨ cong-sletin1 tr-t ⟩
    sletin (collectAcc mt t') _
      ≈⟨ sletin-tr-lemma mt t' (substTm (keepₛ s) u) ⟩
    cletin mt t' (substTm (keepₛ s) u)
      -- normalize, and:
      ≡˘⟨ cong (collectAcc mt) (substTm-pres-∙ₛ _ _ u) ⟩
    collectAcc mt (substTm (keepₛ s ∙ₛ (embWk (⊲-to-⊆ mt) `, t')) u)
      ≡⟨ cong (λ z → (collectAcc mt (substTm (z `, t') u))) (comp-dia-crunch-lemma _ _ _) ⟩
    collectAcc mt (substTm (wkSub (⊲-to-⊆ mt) s `, t') u)
      ∎
fund (jletin {Δ} {a} {b} t u) {Γ} {s} {δ} sLδ
  with eval t .apply δ | fund t sLδ
... | elem (Θt , mt , x) | (t' , tr-t , t'Lx)
  with eval u .apply (elem (wk[ Sub'- Δ ] (⊲-to-⊆ mt) δ , x)) | fund u (wkSub-pres-ℒₛ (⊲-to-⊆ mt) sLδ , t'Lx)
... | elem (Θu , mu , y) | (u' , tr-u , u'Ly)
  = u'
  , tr-aux
  , u'Ly
  where
  tr-aux : substTm s (jletin t u) ≈ collectAcc (⊲-trans mt mu) u'
  tr-aux = let open EqReasoning (Tm-setoid _ _) in begin
    jletin (substTm s t) _
      ≈⟨ cong-jletin1 tr-t ⟩
    jletin (collectAcc mt t') (substTm (keepₛ s) u)
      ≈⟨ jletin-tr-lemma _ _ _ ⟩
    join (cletin mt t' (substTm (keepₛ s) u))
      ≡˘⟨ cong (λ z → join (collectAcc mt z)) (substTm-pres-∙ₛ _ _ u) ⟩
    join (collectAcc mt (substTm (_ `, t') u))
      ≡⟨ cong (λ z → join (collectAcc mt (substTm (z `, t') u))) (comp-dia-crunch-lemma _ _ _) ⟩
    join (collectAcc mt (substTm (wkSub (⊲-to-⊆ mt) s `, t') u))
      ≈⟨ cong-jletin1 (collectAcc-pres-≈ mt tr-u) ⟩
    join (collectAcc mt (collectAcc mu u'))
      ≈⟨ collectAcc-joins-⊲ mt mu u' ⟩
    collectAcc (⊲-trans mt mu) u'
      ∎

open Sound fund
