{-# OPTIONS --safe --without-K #-}

module JFC.Norm.Base where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Unit
open import Data.Product using (∃; _,_; -,_ ; proj₁ ; proj₂)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import PUtil using (Σ×-≡,≡,≡→≡˘)
open import PEUtil using (subst-application′)

open import JFC.Term
open import JFC.Term.Conversion
open import JFC.Term.NormalForm.Base
open import JFC.Term.NormalForm.Properties

open import Semantics.Kripke.Frame

data _⊲_ : Ctx → Ctx → Set where
  single  : Ne Γ (◇ a) → Γ ⊲ (Γ `, a)
  cons    : Ne Γ (◇ a) → (Γ `, a) ⊲ Δ → Γ ⊲ Δ

factor : Γ ⊆ Γ' → Γ ⊲ Δ → ∃ (λ Δ' → (Γ' ⊲ Δ') ∧ Δ ⊆ Δ')
factor i (single n) = _ , single (wkNe i n) , keep i
factor i (cons n m) = let (Δ' , r' , w') = factor (keep i) m
  in Δ' , cons (wkNe i n) r' , w'

factorC : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → Ctx
factorC w m = factor w m .proj₁

factor⊲ : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → Γ' ⊲ _
factor⊲  w m = factor w m .proj₂ .proj₁

factor⊆ : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → Δ ⊆ _
factor⊆ w m = factor w m .proj₂ .proj₂

factor-is-a-triple : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → factor w m ≡ (factorC w m , factor⊲ w m , factor⊆  w m)
factor-is-a-triple w m = ≡-refl

factor-pres-⊆-refl : (m : Γ ⊲ Δ) → factor ⊆-refl m ≡ (-, m , ⊆-refl)
factor-pres-⊆-refl m = Σ×-≡,≡,≡→≡˘ (factorC-pres-⊆-refl m , factor⊲-pres-⊆-refl m , factor⊆-pres-⊆-refl m)
  where

  factorC-pres-⊆-refl : (m : Γ ⊲ Δ) → Δ ≡ factorC ⊆-refl m
  factorC-pres-⊆-refl (single n) = ≡-refl
  factorC-pres-⊆-refl (cons x m) = factorC-pres-⊆-refl m

  factor⊲-pres-⊆-refl : (m : Γ ⊲ Δ) → subst (Γ ⊲_) (factorC-pres-⊆-refl m) m ≡ factor⊲ ⊆-refl m
  factor⊲-pres-⊆-refl (single n) = cong single (≡-sym (wkNe-pres-⊆-refl n))
  factor⊲-pres-⊆-refl {Γ} (cons {a = a} n m) = ≡-trans
    (subst-application′ (cons n) (factorC-pres-⊆-refl m))
    (cong₂ cons (≡-sym (wkNe-pres-⊆-refl n)) (factor⊲-pres-⊆-refl m))

  factor⊆-pres-⊆-refl : (m : Γ ⊲ Δ) → subst (Δ ⊆_) (factorC-pres-⊆-refl m) ⊆-refl ≡ factor⊆ ⊆-refl m
  factor⊆-pres-⊆-refl (single n) = ≡-refl
  factor⊆-pres-⊆-refl (cons x m) = factor⊆-pres-⊆-refl m

factor-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (m : Γ ⊲ Δ)
  → factor (w ∙ w') m ≡ (-, (factor⊲ w' (factor⊲ w m) , (factor⊆ w m) ∙ (factor⊆ w' (factor⊲ w m))))
factor-pres-⊆-trans w w' m =  Σ×-≡,≡,≡→≡˘ (factorC-pres-⊆-trans w w' m , factor⊲-pres-⊆-trans w w' m , factor⊆-pres-⊆-trans w w' m)
  where
  factorC-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (m : Γ ⊲ Δ)
    → factorC w' (factor⊲ w m) ≡ factorC (w ∙ w') m
  factorC-pres-⊆-trans w w' (single n) = ≡-refl
  factorC-pres-⊆-trans w w' (cons x m) = factorC-pres-⊆-trans (keep w) (keep w') m

  factor⊲-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (m : Γ ⊲ Δ)
    → subst (Γ'' ⊲_) (factorC-pres-⊆-trans w w' m) (factor⊲ w' (factor⊲ w m)) ≡ factor⊲ (w ∙ w') m
  factor⊲-pres-⊆-trans w w' (single n) = cong single (≡-sym (wkNe-pres-⊆-trans w w' n))
  factor⊲-pres-⊆-trans w w' (cons n m) = ≡-trans
    (subst-application′ (cons _) (factorC-pres-⊆-trans (keep w) (keep w') m))
    (cong₂ cons (≡-sym (wkNe-pres-⊆-trans w w' n)) (factor⊲-pres-⊆-trans (keep w) (keep w') m))

  factor⊆-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (m : Γ ⊲ Δ)
    → subst (Δ ⊆_) (factorC-pres-⊆-trans w w' m) (factor⊆ w m ∙ (factor⊆ w' (factor⊲ w m))) ≡ factor⊆ (w ∙ w') m
  factor⊆-pres-⊆-trans w w' (single n) = ≡-refl
  factor⊆-pres-⊆-trans w w' (cons x m) = factor⊆-pres-⊆-trans (keep w) (keep w') m

⊲-to-⊆ : Γ ⊲ Δ → Γ ⊆ Δ
⊲-to-⊆ (single n) = freshWk
⊲-to-⊆ (cons x m) = freshWk ∙ (⊲-to-⊆ m)

MF : MFrame 𝒲  _⊲_
MF = record
      { factor              = factor
      ; factor-pres-⊆-refl  = factor-pres-⊆-refl
      ; factor-pres-⊆-trans = factor-pres-⊆-trans
      }

factor-pres-R-to-⊆ : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → w ∙ (⊲-to-⊆ (factor⊲ w m)) ≡ (⊲-to-⊆ m) ∙ (factor⊆ w m)
factor-pres-R-to-⊆ w (single n) = freshWk-natural w
factor-pres-R-to-⊆ w (cons x m) = let open ≡-Reasoning in begin
  w ∙ (freshWk ∙ ⊲-to-⊆ (factor⊲ (keep w) m))
    ≡˘⟨ ∙-assoc w freshWk (⊲-to-⊆ (factor⊲ (keep w) m)) ⟩
  (w ∙ freshWk) ∙ ⊲-to-⊆ (factor⊲ (keep w) m)
    ≡⟨ cong (_∙ ⊲-to-⊆ (factor⊲ (keep w) m)) (freshWk-natural w) ⟩
  (freshWk ∙ keep w) ∙ ⊲-to-⊆ (factor⊲ (keep w) m)
    ≡⟨ ∙-assoc freshWk (keep w) (⊲-to-⊆ (factor⊲ (keep w) m)) ⟩
  freshWk ∙ (keep w ∙ ⊲-to-⊆ (factor⊲ (keep w) m))
    ≡⟨ cong (freshWk ∙_) (factor-pres-R-to-⊆ (keep w) m) ⟩
  freshWk ∙ (⊲-to-⊆ m ∙ factor⊆ (keep w) m)
    ≡˘⟨ ∙-assoc freshWk (⊲-to-⊆ m) (factor⊆ (keep w) m) ⟩
  (freshWk ∙ ⊲-to-⊆ m) ∙ factor⊆ (keep w) m ∎

IMF : InclusiveMFrame MF
IMF = record { R-to-⊆ = ⊲-to-⊆ ; factor-pres-R-to-⊆ = factor-pres-R-to-⊆ }

⊲-trans : Γ ⊲ Γ' → Γ' ⊲ Γ'' → Γ ⊲ Γ''
⊲-trans (single n) m' = cons n m'
⊲-trans (cons x m) m' = cons x (⊲-trans m m')

factor-pres-⊲-trans : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ')
  → factor w (⊲-trans m m') ≡ (-, (⊲-trans (factor⊲ w m) (factor⊲ (factor⊆ w m) m') , factor⊆ (factor⊆ w m) m'))
factor-pres-⊲-trans w m m' = Σ×-≡,≡,≡→≡˘ (factorC-pres-⊲-trans w m m' , factor⊲-pres-⊲-trans w m m' , factor⊆-pres-⊲-trans w m m')
  where
    factorC-pres-⊲-trans : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ')
      → factorC (factor⊆ w m) m' ≡ factorC w (⊲-trans m m')
    factorC-pres-⊲-trans w (single n) m' = ≡-refl
    factorC-pres-⊲-trans w (cons x m) m' = factorC-pres-⊲-trans (keep w) m m'

    factor⊲-pres-⊲-trans : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ')
      → subst (Γ' ⊲_) (factorC-pres-⊲-trans w m m') (⊲-trans (factor⊲ w m) (factor⊲ (factor⊆ w m) m')) ≡ factor⊲ w (⊲-trans m m')
    factor⊲-pres-⊲-trans w (single n) m' = ≡-refl
    factor⊲-pres-⊲-trans w (cons n m) m' = ≡-trans
      (subst-application′ (cons _) (factorC-pres-⊲-trans (keep w) m m'))
      (cong (cons _) (factor⊲-pres-⊲-trans (keep w) m m'))

    factor⊆-pres-⊲-trans : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ')
      → subst (Δ' ⊆_) (factorC-pres-⊲-trans w m m') (factor⊆ (factor⊆ w m) m') ≡ factor⊆ w (⊲-trans m m')
    factor⊆-pres-⊲-trans w (single n) m' = ≡-refl
    factor⊆-pres-⊲-trans w (cons x m) m' = factor⊆-pres-⊲-trans (keep w) m m'

⊲-trans-assoc : (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ') (m'' : Δ' ⊲ Δ'') → ⊲-trans (⊲-trans m m') m'' ≡ ⊲-trans m (⊲-trans m' m'')
⊲-trans-assoc (single n) m' m'' = ≡-refl
⊲-trans-assoc (cons n m) m' m'' = cong (cons n) (⊲-trans-assoc m m' m'')

TMF : TransitiveMFrame MF
TMF = record
  { R-trans             = ⊲-trans
  ; factor-pres-R-trans = factor-pres-⊲-trans
  ; R-trans-assoc       = ⊲-trans-assoc
  }

⊲-to-⊆-pres-trans : (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ')
  → ⊲-to-⊆ (⊲-trans m m') ≡ ⊲-to-⊆ m ∙ ⊲-to-⊆ m'
⊲-to-⊆-pres-trans (single n) m' = ≡-refl
⊲-to-⊆-pres-trans (cons x m) m' = ≡-trans
  (cong (freshWk ∙_) (⊲-to-⊆-pres-trans m m'))
  (≡-sym (∙-assoc freshWk (⊲-to-⊆ m) (⊲-to-⊆ m')))

ITMF : InclusiveTransitiveMFrame MF IMF TMF
ITMF = record {R-to-⊆-pres-trans = ⊲-to-⊆-pres-trans }

open import Semantics.Presheaf.Base 𝒲 public
open import Semantics.Presheaf.CartesianClosure 𝒲 public
open import Semantics.Presheaf.Possibility.Base MF public
open import Semantics.Presheaf.Possibility.Multiplicative MF TMF public
open import Semantics.Presheaf.Possibility.Strong.Multiplicative MF ITMF public

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

open import JFC.Evaluation PshCat PshCat-is-CCC ◇'-is-PshFunctor ◇'-is-strong-multiplicative (Ne'- ι)

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
register-natural w p = proof (≡-refl , (≡-refl , ≡-refl))

register : Ne'- (◇ a) →̇ ◇' (Ne'- a)
register = record
  { fun     = register-fun
  ; pres-≋  = λ p≋p' → proof (≡-refl , cong single p≋p' , ≡-refl)
  ; natural = register-natural
  }

collectNfAcc : Γ ⊲ Δ → Nf Δ a → Nf Γ (◇ a)
collectNfAcc (single n) n0 = sletin n n0
collectNfAcc (cons n m) n0 = jletin n (collectNfAcc m n0)

collectNf-fun : (◇' Nf'- a) ₀ Γ → Nf'- (◇ a) ₀ Γ
collectNf-fun (elem (Δ , m , n)) = collectNfAcc m n

collectNf-pres-≋ : Pres-≋ (◇' (Nf'- a)) (Nf'- (◇ a)) collectNf-fun
collectNf-pres-≋ (proof (≡-refl , ≡-refl , ≡-refl)) = ≡-refl

collectNfAcc-nat : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) (n : Nf Δ a)
  → wkNf w (collectNfAcc m n) ≡ collectNfAcc (factor⊲ w m) (wkNf (factor⊆ w m) n)
collectNfAcc-nat w (single n) n0 = ≡-refl
collectNfAcc-nat w (cons n m) n0 = cong (jletin (wkNe w n)) (collectNfAcc-nat (keep w) m n0)

collectNf-natural : Natural (◇' (Nf'- a)) (Nf'- (◇ a)) collectNf-fun
collectNf-natural w (elem (Δ , m , n)) = collectNfAcc-nat w m n

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
  reflect-fun 𝟙       n = tt
  reflect-fun (a × b) n = elem (reflect-fun a (fst n) , reflect-fun b (snd n))
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

  reify-fun ι         n  = up n
  reify-fun 𝟙         _  = unit
  reify-fun (a × b)   p  = pair (reify-fun a (π₁' .apply p)) (reify-fun b (π₂' .apply p))
  reify-fun (a ⇒ b)   f  = lam (reify-fun b (f .apply freshWk (reflect-fun a (var zero))))
  reify-fun (◇ a)     x  = collectNf-fun (◇'-map-fun (reify-fun a) x)

  reflect-pres-≋  = λ a n≡n' → ≋[ evalTy a ]-reflexive (cong (reflect-fun a) n≡n')

  reflect-natural ι       w n = ≋[ evalTy ι ]-refl
  reflect-natural 𝟙       w n = ≡-refl
  reflect-natural (a × b) w n = proof (reflect-natural a w (fst n) , reflect-natural b w (snd n))
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
  reify-pres-≋ 𝟙       x≋x' = ≡-refl
  reify-pres-≋ (a × b) x≋x' = cong₂ pair (reify-pres-≋ a (π₁' .apply-≋ x≋x')) (reify-pres-≋ b (π₂' .apply-≋ x≋x'))
  reify-pres-≋ (a ⇒ b) x≋x' = cong lam (reify-pres-≋ b (x≋x' .pw freshWk[ _ , a ] _))
  reify-pres-≋ (◇ a)   x≋x' = collectNf-pres-≋ (◇'-map-fun-pres-≋ (reify-pres-≋ a) x≋x')

  reify-natural ι       w x = ≡-refl
  reify-natural 𝟙       w x = ≡-refl
  reify-natural (a × b) w x = cong₂ pair (reify-natural a w (π₁' .apply x)) (reify-natural b w (π₂' .apply x))
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
      ≡⟨  cong₂ (λ w n → lam (reify-fun b (x .apply w (reflect-fun a n)))) (cong drop (≡-trans (⊆-trans-unit-left _) (≡-sym (⊆-trans-unit-right _)))) ≡-refl ⟩
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
