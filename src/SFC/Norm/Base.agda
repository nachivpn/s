{-# OPTIONS --safe --without-K #-}

module SFC.Norm.Base where

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product.Properties using ()

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import SFC.Term
open import SFC.Term.Conversion
open import SFC.Term.NormalForm
open import SFC.Term.NormalForm.Properties

open import Semantics.Kripke.Frame

data _⊲_ : Ctx → Ctx → Set where
  single : Ne Γ (◇ a) → Γ ⊲ (Γ `, a)

factor : Γ ⊆ Γ' → Γ ⊲ Δ → ∃ (λ Δ' → (Γ' ⊲ Δ') ∧ Δ ⊆ Δ')
factor w (single n) = _ , (single (wkNe w n) , keep w)

factorR : {w w' v : Ctx} → (i : w ⊆ w') (r : w ⊲ v) → w' ⊲ _
factorR  w r = factor w r .snd .fst

factor⊆ : {w w' v : Ctx} → (i : w ⊆ w') (r : w ⊲ v) → v ⊆ _
factor⊆ w r = factor w r .snd .snd

factor-pres-⊆-refl : (m : Γ ⊲ Δ) → factor ⊆-refl m ≡ (Δ , m , ⊆-refl)
factor-pres-⊆-refl (single m) rewrite wkNe-pres-⊆-refl m = refl

factor-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (m : Γ ⊲ Δ)
  → factor (w ∙ w') m ≡ (-, (factorR w' (factorR w m) , ((factor⊆ w m) ∙ (factor⊆ w' (factorR w m)))))
factor-pres-⊆-trans w w' (single m) rewrite wkNe-pres-⊆-trans w w' m = refl

⊲-to-⊆ : Γ ⊲ Δ → Γ ⊆ Δ
⊲-to-⊆ (single {a = a} n) = freshWk[ _ , a ]

MF : MFrame 𝒲  _⊲_
MF = record
      { factor              = factor
      ; factor-pres-⊆-refl  = factor-pres-⊆-refl
      ; factor-pres-⊆-trans = factor-pres-⊆-trans
      }

factor-pres-R-to-⊆ : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → w ∙ (⊲-to-⊆ (factorR w m)) ≡ (⊲-to-⊆ m) ∙ (factor⊆ w m)
factor-pres-R-to-⊆ w (single m) = freshWk-natural w

IMF : InclusiveMFrame MF
IMF = record { R-to-⊆ = ⊲-to-⊆ ; factor-pres-R-to-⊆ = factor-pres-R-to-⊆ }

open import Semantics.Presheaf.Base 𝒲 public
open import Semantics.Presheaf.CartesianClosure 𝒲 public
open import Semantics.Presheaf.Possibility.Base MF public
open import Semantics.Presheaf.Possibility.Strong.Base MF IMF public

Ne'- : Ty → Psh
Ne'- a = record
          { Fam           = λ Γ → Ne Γ a
          ; _≋_           = _≡_
          ; ≋-equiv       = λ _ → ≡-equiv
          ; wk            = wkNe
          ; wk-pres-≋     = λ w → cong (wkNe w)
          ; wk-pres-refl  = wkNe-pres-⊆-refl
          ; wk-pres-trans = wkNe-pres-⊆-trans
          }

Nf'- : Ty → Psh
Nf'- a = record
          { Fam           = λ Γ → Nf Γ a
          ; _≋_           = _≡_
          ; ≋-equiv       = λ _ → ≡-equiv
          ; wk            = wkNf
          ; wk-pres-≋     = λ w → cong (wkNf w)
          ; wk-pres-refl  = wkNf-pres-⊆-refl
          ; wk-pres-trans = wkNf-pres-⊆-trans 
          }

open import Semantics.Category.Evaluation.SFC.Base PshCat PshCat-is-CC PshCat-is-CCC ◇'-is-PshFunctor ◇'-is-strong
open import Semantics.Category.Evaluation.SFC.Properties PshCat PshCat-is-CC PshCat-is-CCC ◇'-is-PshFunctor ◇'-is-strong (Ne'- ι)

open Eval (Ne'- ι) hiding (Sub' ; Tm')

-- interpretation of types
Ty'- : (a : Ty) → Psh
Ty'- = evalTy

Ty' : Ctx → Ty → Set
Ty' Γ a = Ty'- a ₀ Γ

-- interpretation of contexts
Sub'- : (Γ : Ctx) → Psh
Sub'- = evalCtx

Sub' : Ctx → Ctx → Set
Sub' Γ Δ = Sub'- Δ ₀ Γ

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Ty'- a)
eval = evalTm

register-fun : Ne Γ (◇ a) → ◇' (Ne'- a) ₀ Γ
register-fun n = elem (_ , single n , var zero)

register-natural : Natural (Ne'- (◇ a)) (◇' (Ne'- a)) register-fun 
register-natural w p = proof (refl , (refl , refl))

register : Ne'- (◇ a) →̇ ◇' (Ne'- a)
register = record
  { fun     = register-fun
  ; pres-≋  = λ p≋p' → proof (refl , cong single p≋p' , refl) 
  ; natural = register-natural
  }

collectNf-fun : (◇' Nf'- a) ₀ Γ → Nf'- (◇ a) ₀ Γ
collectNf-fun (elem (Δ , (single n) , m))= letin n m

collectNf-pres-≋ : Pres-≋ (◇' (Nf'- a)) (Nf'- (◇ a)) collectNf-fun 
collectNf-pres-≋ (proof (refl , refl , refl)) = refl

collectNf-natural : Natural (◇' (Nf'- a)) (Nf'- (◇ a)) collectNf-fun
collectNf-natural w (elem (Δ , (single n) , m)) = refl

collectNf : ◇' (Nf'- a) →̇ Nf'- (◇ a)
collectNf = record
  { fun     = collectNf-fun
  ; pres-≋  = collectNf-pres-≋
  ; natural = collectNf-natural
  }

module _ where

  reflect-fun     : (a : Ty) → Ne  Γ a → Ty' Γ a
  reflect-pres-≋  : (a : Ty) → Pres-≋ (Ne'- a) (Ty'- a) (reflect-fun a)
  reflect-natural : (a : Ty) → Natural (Ne'- a) (Ty'- a) (reflect-fun a)

  reify-fun     : (a : Ty) → Ty' Γ a → Nf Γ a
  reify-pres-≋  : (a : Ty) → Pres-≋ (Ty'- a) (Nf'- a) (reify-fun a)
  reify-natural : (a : Ty) → Natural (Ty'- a) (Nf'- a) (reify-fun a)

  reflect-fun ι       n = n
  reflect-fun (a ⇒ b) n = record
    { fun     = λ w    p    → reflect-fun b (app (wkNe w n) (reify-fun a p))
    ; pres-≋  = λ w    p≋p' → reflect-pres-≋ b (cong (app (wkNe w n)) (reify-pres-≋ a p≋p'))
    ; natural = λ w w' p    → let open EqReasoning ≋[ evalTy b ]-setoid in begin
      wk[ evalTy b ] w' (reflect-fun b (app (wkNe w n) (reify-fun a p)))            ≈⟨ reflect-natural b w' _ ⟩
      reflect-fun b (wkNe w' (app (wkNe w n) (reify-fun a p)))                      ≡⟨⟩
      reflect-fun b (app (wkNe w' (wkNe w n)) (wkNf w' (reify-fun a p)))            ≡⟨ cong (λ m → reflect-fun b (app _ m)) (reify-natural a w' p) ⟩
      reflect-fun b (app (wkNe w' (wkNe w n)) (reify-fun a (wk[ evalTy a ] w' p)))  ≡⟨ cong (λ n → reflect-fun b (app n _)) (≡-sym (wkNe-pres-⊆-trans w w' n)) ⟩
      reflect-fun b (app (wkNe (w ∙ w') n) (reify-fun a (wk[ evalTy a ] w' p)))     ∎
    }
  reflect-fun (◇ a)   n = ◇'-map-fun (reflect-fun a) (register-fun n)
  
  reify-fun ι         n  = up  n
  reify-fun (a ⇒ b)   f  = lam (reify-fun b (f .apply freshWk (reflect-fun a (var zero))))
  reify-fun (◇ a)     x  = collectNf-fun (◇'-map-fun (reify-fun a) x)
  
  reflect-pres-≋  = λ a n≡n' → ≋[ evalTy a ]-reflexive (cong (reflect-fun a) n≡n')

  reflect-natural ι       w n = ≋[ evalTy ι ]-refl
  reflect-natural (a ⇒ b) w n = record
    { pw = λ w' p → let open EqReasoning ≋[ evalTy b ]-setoid in begin
       wk[ evalTy (a ⇒ b) ] w (reflect-fun (a ⇒ b) n) .apply w' p
          ≡⟨⟩
       reflect-fun b (app (wkNe (w ∙ w') n) (reify-fun a p))
         ≡˘⟨ cong (λ n → reflect-fun b (app n (reify-fun a p))) (≡-sym (wkNe-pres-⊆-trans w w' n)) ⟩
       reflect-fun b (app (wkNe w' (wkNe w n)) (reify-fun a p))
         ≡⟨⟩
       reflect-fun (a ⇒ b) (wkNe w n) .apply w' p ∎
    }
  reflect-natural (◇ a) w n = ◇'-map-natural (reflect-natural a) w (register-fun n) 
  
  reify-pres-≋ ι       x≋x' = cong up  x≋x'
  reify-pres-≋ (a ⇒ b) x≋x' = cong lam (reify-pres-≋ b (x≋x' .pw freshWk[ _ , a ] _))
  reify-pres-≋ (◇ a)   x≋x' = collectNf-pres-≋ (◇'-map-fun-pres-≋ (reify-pres-≋ a) x≋x')

  reify-natural ι       w x = refl
  reify-natural (a ⇒ b) w x = let open ≡-Reasoning in begin
    wkNf w (reify-fun (a ⇒ b) x)
      ≡⟨⟩
    lam (wkNf (keep[ a ] w) (reify-fun b (x .apply freshWk[ _ , a ] _)))
      ≡⟨ cong lam (reify-natural b (keep[ a ] w) _) ⟩
    lam (reify-fun b (wk[ evalTy b ] (keep[ a ] w) (x .apply freshWk[ _ , a ] _)))
      ≡⟨ cong lam (reify-pres-≋ b (x .natural freshWk (keep[ a ] w) _)) ⟩
    lam (reify-fun b (x .apply (freshWk[ _ , a ] ∙ keep[ a ] w) (wk[ evalTy a ] (keep[ a ] w) _)))
      ≡⟨ cong lam (reify-pres-≋ b (x .apply-≋ _ (reflect-natural a (keep[ a ] w) _)))  ⟩
    lam (reify-fun b (x .apply (freshWk[ _ , a ] ∙ keep[ a ] w) (reflect-fun a (wkNe (keep[ a ] w) _)))) ≡⟨  cong₂ (λ w n → lam (reify-fun b (x .apply w (reflect-fun a n)))) (cong drop (≡-trans (⊆-trans-unit-left _) (≡-sym (⊆-trans-unit-right _)))) refl ⟩
    lam (reify-fun b (x .apply (w ∙ freshWk[ _ , a ]) _))
      ≡⟨⟩
    reify-fun (a ⇒ b) (wk[ evalTy (a ⇒ b) ] w x) ∎
  reify-natural (◇ a)   w x = let open ≡-Reasoning in begin
    wk[ Nf'- (◇ a) ] w (reify-fun (◇ a) x)
      ≡⟨⟩
    wk[ Nf'- (◇ a) ] w (collectNf-fun (◇'-map-fun (reify-fun a) x))
      ≡⟨ collectNf-natural w (◇'-map-fun (reify-fun a) x) ⟩
    collectNf-fun (wk[ ◇' Nf'- a ] w (◇'-map-fun (reify-fun a) x))
      ≡⟨ collectNf-pres-≋ (◇'-map-natural (reify-natural a) w x) ⟩
    collectNf-fun (◇'-map-fun (reify-fun a) (wk[ Ty'- (◇ a) ] w x))
      ≡⟨⟩
    reify-fun (◇ a) (wk[ Ty'- (◇ a) ] w x) ∎ 

reflect : (a : Ty) → Ne'- a →̇ Ty'- a
reflect a = record
  { fun     = reflect-fun a
  ; pres-≋  = reflect-pres-≋ a
  ; natural = reflect-natural a
  }

reify : (a : Ty) → Ty'- a →̇ Nf'- a
reify a = record
  { fun     = reify-fun a
  ; pres-≋  = reify-pres-≋ a
  ; natural = reify-natural a
  }

-- monotonicity lemma
wkTy' : (a : Ty) → (w : Γ ⊆ Γ') → (x : Ty' Γ a) → Ty' Γ' a
wkTy' a = wk[ evalTy a ]

-- monotonicity lemma
wkSub' : (Δ : Ctx) → (w : Γ ⊆ Γ') → (ρ : Sub' Γ Δ) → Sub' Γ' Δ
wkSub' Δ = wk[ evalCtx Δ ]

-- identity environment
idEnv : (Γ : Ctx) → Sub' Γ Γ
idEnv []       = _
idEnv (Γ `, a) = elem (wkSub' Γ freshWk (idEnv Γ) , reflect a .apply (var zero))

-- retraction of interpretation
quot : Sub'- Γ →̇ Ty'- a → Nf Γ a
quot {Γ} {a} f = reify a .apply (f .apply (idEnv Γ))

-- normalization function
norm : Tm Γ a → Nf Γ a
norm t = quot (eval t)

-- normalization is complete
norm-complete : (t≈u : t ≈ u) → norm t ≡ norm u
norm-complete {Γ} {a} t≈u = reify-pres-≋ a (apply-sq (evalTm-sound t≈u) ≋[ evalCtx Γ ]-refl)
