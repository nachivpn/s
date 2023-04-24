{-# OPTIONS --without-K #-}

module Functor.Norm where

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product.Properties using ()

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import Functor.Term
open import Functor.Term.Reduction hiding (single)
open import Functor.Term.NormalForm
open import Functor.Term.NormalForm.Properties

open import Semantics.Kripke.Frame

data _⊲_ : Ctx → Ctx → Set where
  single : Ne Γ (◯ a) → Γ ⊲ (Γ `, a)

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

MF : MFrame Ctx _⊆_  _⊲_
MF = record
      { IF                  = 𝒲
      ; factor              = factor
      ; factor-pres-⊆-refl  = factor-pres-⊆-refl
      ; factor-pres-⊆-trans = factor-pres-⊆-trans
      }

factor-pres-R-to-⊆ : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → w ∙ (⊲-to-⊆ (factorR w m)) ≡ (⊲-to-⊆ m) ∙ (factor⊆ w m)
factor-pres-R-to-⊆ w (single m) = freshWk-natural w

IMF : InclusiveMFrame MF
IMF = record { R-to-⊆ = ⊲-to-⊆ ; factor-pres-R-to-⊆ = factor-pres-R-to-⊆ }

open import Semantics.Presheaf.Base 𝒲
open import Semantics.Presheaf.CartesianClosure 𝒲
open import Semantics.Presheaf.Possibility MF
open import Semantics.Presheaf.Strong MF IMF


Ne'- : Ty → Psh
Ne'- a = record
          { Fam           = λ Γ → Ne Γ a
          ; _≋_           = _≡_
          ; ≋-equiv       = λ _ → ≡-equiv
          ; wk            = wkNe
          ; wk-pres-≋     = λ w → cong (wkNe w)
          ; wk-pres-refl  = wkNe-pres-⊆-refl
          ; wk-pres-trans = λ w w' n → ≡-sym (wkNe-pres-⊆-trans w w' n)
          }

Nf'- : Ty → Psh
Nf'- a = record
          { Fam           = λ Γ → Nf Γ a
          ; _≋_           = _≡_
          ; ≋-equiv       = λ _ → ≡-equiv
          ; wk            = wkNf
          ; wk-pres-≋     = λ w → cong (wkNf w)
          ; wk-pres-refl  = wkNf-pres-⊆-refl
          ; wk-pres-trans = λ w w' n → ≡-sym (wkNf-pres-⊆-trans w w' n)
          }

open import Semantics.Category.Evaluation.Functor.Base PshCat PshCat-is-CC PshCat-is-CCC ◇'-is-PshFunctor ◇'-is-strong
open import Semantics.Category.Evaluation.Functor.Properties PshCat PshCat-is-CC PshCat-is-CCC ◇'-is-PshFunctor ◇'-is-strong (Ne'- ι)

open Eval (Ne'- ι) hiding (Sub' ; Tm')

-- interpretation of types
Tm'- : (a : Ty) → Psh
Tm'- = evalTy

Tm' : Ctx → Ty → Set
Tm' Γ a = Tm'- a ₀ Γ

-- interpretation of contexts
Sub'- : (Γ : Ctx) → Psh
Sub'- = evalCtx

Sub' : Ctx → Ctx → Set
Sub' Γ Δ = Sub'- Δ ₀ Γ

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Tm'- a)
eval = evalTm

register : Ne'- (◯ a) →̇ ◇' (Ne'- a)
register = record
  { fun     = λ p    → elem (_ , (single p , var zero))
  ; pres-≋  = λ p≋p' → proof (refl , cong single p≋p' , refl)
  ; natural = λ w p  → proof (refl , (refl , refl))
  }

collect : ◇' (Nf'- a) →̇ Nf'- (◯ a)
collect = record
  { fun     = collect-fun
  ; pres-≋  = collect-fun-pres-≋
  ; natural = collect-natural
  }
  where
  collect-fun : (◇' Nf'- a) ₀ Γ → Nf'- (◯ a) ₀ Γ
  collect-fun (elem (Δ , (single n) , m))= letin n m

  collect-fun-pres-≋ : {p p' : (◇' Nf'- a) ₀ Γ} (p≋p' : ≋[]-syntax (◇' Nf'- a) p p')
    → (collect-fun p) ≡ (collect-fun p')
  collect-fun-pres-≋ (proof (refl , refl , refl)) = refl

  collect-natural : (w : Γ ⊆ Δ) (p : (◇' Nf'- a) ₀ Γ)
    → wk[ Nf'- (◯ a) ] w (collect-fun p) ≡ collect-fun (wk[ ◇' Nf'- a ] w p)
  collect-natural w (elem (Δ , (single n) , m)) = refl

module _ where
  reflect         : (a : Ty) → Ne'- a →̇ Tm'- a
  reflect-fun     : (a : Ty) → (n : Ne  Γ a) → Tm' Γ a
  reflect-pres-≋  : (a : Ty) {n n' : Ne Γ a} (n≡n' : n ≡ n') → reflect-fun a n ≋[ evalTy a ] reflect-fun a n'
  reflect-natural : (a : Ty) (w : Γ ⊆ Γ') (n : Ne Γ a) → wk[ evalTy a ] w (reflect-fun a n) ≋[ evalTy a ] reflect-fun a (wkNe w n)

  reify         : (a : Ty) → Tm'- a →̇ Nf'- a
  reify-fun     : (a : Ty) → (x : Tm' Γ a) → Nf Γ a
  reify-pres-≋  : (a : Ty) {x x' : Tm' Γ a} (x≋x' : x ≋[ evalTy a ] x') → reify-fun a x ≡ reify-fun a x'
  reify-natural : (a : Ty) (w : Γ ⊆ Γ') (x : Tm' Γ a) → wkNf w (reify-fun a x) ≡ reify-fun a (wk[ evalTy a ] w x)

  reflect-fun ι       n = n
  reflect-fun (a ⇒ b) n = record
    { fun     = λ w    p    → reflect-fun b (app (wkNe w n) (reify-fun a p))
    ; pres-≋  = λ w    p≋p' → reflect-pres-≋ b (cong (app (wkNe w n)) (reify-pres-≋ a p≋p'))
    ; natural = λ w w' p    → let open EqReasoning ≋[ evalTy b ]-setoid in begin
      wk[ evalTy b ] w' (reflect-fun b (app (wkNe w n) (reify-fun a p)))            ≈⟨ reflect-natural b w' _ ⟩
      reflect-fun b (wkNe w' (app (wkNe w n) (reify-fun a p)))                      ≡⟨⟩
      reflect-fun b (app (wkNe w' (wkNe w n)) (wkNf w' (reify-fun a p)))            ≡⟨ cong (λ m → reflect-fun b (app _ m)) (reify-natural a w' p) ⟩
      reflect-fun b (app (wkNe w' (wkNe w n)) (reify-fun a (wk[ evalTy a ] w' p)))  ≡⟨ cong (λ n → reflect-fun b (app n _)) (wkNe-pres-⊆-trans w w' n) ⟩
      reflect-fun b (app (wkNe (w ∙ w') n) (reify-fun a (wk[ evalTy a ] w' p)))     ∎
    }
  reflect-fun {Γ = Γ} (◯ a)   n = (◇'-map (reflect a) ∘ register) .apply n
  
  reify-fun ι         n  = up  n
  reify-fun (a ⇒ b)   f  = lam (reify-fun b (f .apply freshWk (reflect-fun a (var zero))))
  reify-fun (◯ a)     x  = (collect ∘ ◇'-map (reify a)) .apply x
  
  reflect-pres-≋  = λ a n≡n' → ≋[ evalTy a ]-reflexive (cong (reflect-fun a) n≡n')

  reflect-natural ι       w n = ≋[ evalTy ι ]-refl
  reflect-natural (a ⇒ b) w n = record
    { pw = λ w' p → let open EqReasoning ≋[ evalTy b ]-setoid in begin
       wk[ evalTy (a ⇒ b) ] w (reflect-fun (a ⇒ b) n) .apply w' p
          ≡⟨⟩
       reflect-fun b (app (wkNe (w ∙ w') n) (reify-fun a p))
         ≡˘⟨ cong (λ n → reflect-fun b (app n (reify-fun a p))) (wkNe-pres-⊆-trans w w' n) ⟩
       reflect-fun b (app (wkNe w' (wkNe w n)) (reify-fun a p))
         ≡⟨⟩
       reflect-fun (a ⇒ b) (wkNe w n) .apply w' p ∎
    }
  reflect-natural (◯ a) w n = (◇'-map (reflect a) ∘ register) .natural w n
  
  reify-pres-≋ ι       x≋x' = cong up  x≋x'
  reify-pres-≋ (a ⇒ b) x≋x' = cong lam (reify-pres-≋ b (x≋x' .pw freshWk[ _ , a ] _))
  reify-pres-≋ (◯ a)   x≋x' = (collect ∘ ◇'-map (reify a)) ._→̇_.pres-≋ x≋x'

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
    lam (reify-fun b (x .apply (freshWk[ _ , a ] ∙ keep[ a ] w) (reflect-fun a (wkNe (keep[ a ] w) _))))
      ≡⟨  cong₂ (λ w n → lam (reify-fun b (x .apply w (reflect-fun a n)))) (cong drop (≡-trans (⊆-refl-unit-left _) (≡-sym (⊆-refl-unit-right _)))) refl ⟩
    lam (reify-fun b (x .apply (w ∙ freshWk[ _ , a ]) _))
      ≡⟨⟩
    reify-fun (a ⇒ b) (wk[ evalTy (a ⇒ b) ] w x) ∎
  reify-natural (◯ a)   w x = (collect ∘ ◇'-map (reify a)) .natural w x 

  --
  -- TODO: pull these record instances out of the grand mutual recursion
  --
  
  reflect a = record
    { fun     = reflect-fun a
    ; pres-≋  = reflect-pres-≋ a
    ; natural = reflect-natural a
    }

  reify a = record
    { fun     = reify-fun a
    ; pres-≋  = reify-pres-≋ a
    ; natural = reify-natural a
    }

-- monotonicity lemma
wkTm' : (a : Ty) → (w : Γ ⊆ Γ') → (x : Tm' Γ a) → Tm' Γ' a
wkTm' a = wk[ evalTy a ]

-- monotonicity lemma
wkSub' : (Δ : Ctx) → (w : Γ ⊆ Γ') → (ρ : Sub' Γ Δ) → Sub' Γ' Δ
wkSub' Δ = wk[ evalCtx Δ ]

-- identity environment
idEnv : (Γ : Ctx) → Sub' Γ Γ
idEnv []       = _
idEnv (Γ `, a) = elem (wkSub' Γ freshWk (idEnv Γ) , reflect a .apply (var zero))

-- retraction of interpretation
quot : Sub'- Γ →̇ Tm'- a → Nf Γ a
quot {Γ} {a} f = reify a .apply (f .apply (idEnv Γ))

-- normalization function
norm : Tm Γ a → Nf Γ a
norm t = quot (eval t)

-- normalization is complete
norm-complete : (t⟶*u : t ⟶* u) → norm t ≡ norm u
norm-complete {Γ} {a} t≈u = reify-pres-≋ a (apply-sq (evalTm-sound* t≈u) ≋[ evalCtx Γ ]-refl)
