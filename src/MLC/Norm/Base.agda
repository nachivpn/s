{-# OPTIONS --safe --without-K #-}

module MLC.Norm.Base where

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product.Properties using ()

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import PUtil using (Σ×-≡,≡,≡→≡˘)
open import PEUtil using (subst-application′)

open import MLC.Term
open import MLC.Term.Conversion
open import MLC.Term.NormalForm
open import MLC.Term.NormalForm.Properties

open import Semantics.Kripke.Frame

data _⊲_ : Ctx → Ctx → Set where
  nil  : Γ ⊲ Γ
  cons : Ne Γ (◇ a) → (Γ `, a) ⊲ Δ → Γ ⊲ Δ

factor : Γ ⊆ Γ' → Γ ⊲ Δ → ∃ (λ Δ' → (Γ' ⊲ Δ') ∧ Δ ⊆ Δ')
factor i nil        = _ , nil , i
factor i (cons n m) = let (Δ' , r' , w') = factor (keep i) m
  in Δ' , cons (wkNe i n) r' , w'

factorC : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → Ctx
factorC w m = factor w m .fst

factor⊲ : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → Γ' ⊲ _
factor⊲  w m = factor w m .snd .fst

factor⊆ : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → Δ ⊆ _
factor⊆ w m = factor w m .snd .snd

factor-is-a-triple : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → factor w m ≡ (factorC w m , factor⊲ w m , factor⊆  w m)
factor-is-a-triple w m = ≡-refl

factor-pres-⊆-refl : (m : Γ ⊲ Δ) → factor ⊆-refl m ≡ (-, m , ⊆-refl)
factor-pres-⊆-refl m = Σ×-≡,≡,≡→≡˘ (factorC-pres-⊆-refl m , factor⊲-pres-⊆-refl m , factor⊆-pres-⊆-refl m)
  where
  
  factorC-pres-⊆-refl : (m : Γ ⊲ Δ) → Δ ≡ factorC ⊆-refl m
  factorC-pres-⊆-refl nil        = ≡-refl
  factorC-pres-⊆-refl (cons x m) = factorC-pres-⊆-refl m

  factor⊲-pres-⊆-refl : (m : Γ ⊲ Δ) → subst (Γ ⊲_) (factorC-pres-⊆-refl m) m ≡ factor⊲ ⊆-refl m
  factor⊲-pres-⊆-refl nil = ≡-refl
  factor⊲-pres-⊆-refl {Γ} (cons {a = a} n m) = ≡-trans
    (subst-application′ (cons n) (factorC-pres-⊆-refl m))
    (cong₂ cons (≡-sym (wkNe-pres-⊆-refl n)) (factor⊲-pres-⊆-refl m))

  factor⊆-pres-⊆-refl : (m : Γ ⊲ Δ) → subst (Δ ⊆_) (factorC-pres-⊆-refl m) ⊆-refl ≡ factor⊆ ⊆-refl m
  factor⊆-pres-⊆-refl nil        = ≡-refl
  factor⊆-pres-⊆-refl (cons x m) = factor⊆-pres-⊆-refl m

factor-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (m : Γ ⊲ Δ)
  → factor (w ∙ w') m ≡ (-, (factor⊲ w' (factor⊲ w m) , (factor⊆ w m) ∙ (factor⊆ w' (factor⊲ w m))))
factor-pres-⊆-trans w w' m =  Σ×-≡,≡,≡→≡˘ (factorC-pres-⊆-trans w w' m , factor⊲-pres-⊆-trans w w' m , factor⊆-pres-⊆-trans w w' m)
  where
  factorC-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (m : Γ ⊲ Δ)
    → factorC w' (factor⊲ w m) ≡ factorC (w ∙ w') m
  factorC-pres-⊆-trans w w' nil        = ≡-refl
  factorC-pres-⊆-trans w w' (cons x m) = factorC-pres-⊆-trans (keep w) (keep w') m

  factor⊲-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (m : Γ ⊲ Δ)
    → subst (Γ'' ⊲_) (factorC-pres-⊆-trans w w' m) (factor⊲ w' (factor⊲ w m)) ≡ factor⊲ (w ∙ w') m
  factor⊲-pres-⊆-trans w w' nil        = ≡-refl
  factor⊲-pres-⊆-trans w w' (cons n m) = ≡-trans
    (subst-application′ (cons _) (factorC-pres-⊆-trans (keep w) (keep w') m))
    (cong₂ cons (≡-sym (wkNe-pres-⊆-trans w w' n)) (factor⊲-pres-⊆-trans (keep w) (keep w') m))

  factor⊆-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (m : Γ ⊲ Δ)
    → subst (Δ ⊆_) (factorC-pres-⊆-trans w w' m) (factor⊆ w m ∙ (factor⊆ w' (factor⊲ w m))) ≡ factor⊆ (w ∙ w') m 
  factor⊆-pres-⊆-trans w w' nil        = ≡-refl
  factor⊆-pres-⊆-trans w w' (cons x m) = factor⊆-pres-⊆-trans (keep w) (keep w') m
  
⊲-to-⊆ : Γ ⊲ Δ → Γ ⊆ Δ
⊲-to-⊆ nil        = ⊆-refl
⊲-to-⊆ (cons x m) = freshWk ∙ (⊲-to-⊆ m)

MF : MFrame 𝒲  _⊲_
MF = record
      { factor              = factor
      ; factor-pres-⊆-refl  = factor-pres-⊆-refl
      ; factor-pres-⊆-trans = factor-pres-⊆-trans
      }

factor-pres-R-to-⊆ : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) → w ∙ (⊲-to-⊆ (factor⊲ w m)) ≡ (⊲-to-⊆ m) ∙ (factor⊆ w m)
factor-pres-R-to-⊆ w nil        = ≡-trans (⊆-refl-unit-right w) (≡-sym (⊆-refl-unit-left w))
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

⊲-refl : Γ ⊲ Γ
⊲-refl = nil

RMF : ReflexiveMFrame MF
RMF = record { R-refl = ⊲-refl ; factor-pres-R-refl = λ i → ≡-refl }

⊲-trans : Γ ⊲ Γ' → Γ' ⊲ Γ'' → Γ ⊲ Γ''
⊲-trans nil        m' = m'
⊲-trans (cons x m) m' = cons x (⊲-trans m m')

factor-pres-⊲-trans : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ')
  → factor w (⊲-trans m m') ≡ (-, (⊲-trans (factor⊲ w m) (factor⊲ (factor⊆ w m) m') , factor⊆ (factor⊆ w m) m'))
factor-pres-⊲-trans w m m' = Σ×-≡,≡,≡→≡˘ (factorC-pres-⊲-trans w m m' , factor⊲-pres-⊲-trans w m m' , factor⊆-pres-⊲-trans w m m')
  where
    factorC-pres-⊲-trans : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ')
      → factorC (factor⊆ w m) m' ≡ factorC w (⊲-trans m m')
    factorC-pres-⊲-trans w nil        m' = ≡-refl
    factorC-pres-⊲-trans w (cons x m) m' = factorC-pres-⊲-trans (keep w) m m'

    factor⊲-pres-⊲-trans : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ')
      → subst (Γ' ⊲_) (factorC-pres-⊲-trans w m m') (⊲-trans (factor⊲ w m) (factor⊲ (factor⊆ w m) m')) ≡ factor⊲ w (⊲-trans m m')
    factor⊲-pres-⊲-trans w nil        m' = ≡-refl
    factor⊲-pres-⊲-trans w (cons n m) m' = ≡-trans
      (subst-application′ (cons _) (factorC-pres-⊲-trans (keep w) m m'))
      (cong (cons _) (factor⊲-pres-⊲-trans (keep w) m m'))

    factor⊆-pres-⊲-trans : (w : Γ ⊆ Γ') (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ')
      → subst (Δ' ⊆_) (factorC-pres-⊲-trans w m m') (factor⊆ (factor⊆ w m) m') ≡ factor⊆ w (⊲-trans m m')
    factor⊆-pres-⊲-trans w nil        m' = ≡-refl
    factor⊆-pres-⊲-trans w (cons x m) m' = factor⊆-pres-⊲-trans (keep w) m m'

⊲-trans-assoc : (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ') (m'' : Δ' ⊲ Δ'') → ⊲-trans (⊲-trans m m') m'' ≡ ⊲-trans m (⊲-trans m' m'')
⊲-trans-assoc nil        m' m'' = ≡-refl
⊲-trans-assoc (cons n m) m' m'' = cong (cons n) (⊲-trans-assoc m m' m'')

TMF : TransitiveMFrame MF
TMF = record
  { R-trans             = ⊲-trans
  ; factor-pres-R-trans = factor-pres-⊲-trans
  ; R-trans-assoc       = ⊲-trans-assoc
  }

IRMF : InclusiveReflexiveMFrame MF IMF RMF
IRMF = record { R-to-⊆-pres-refl = ≡-refl }

⊲-to-⊆-pres-trans : (m : Γ ⊲ Δ) (m' : Δ ⊲ Δ')
  → ⊲-to-⊆ (⊲-trans m m') ≡ ⊲-to-⊆ m ∙ ⊲-to-⊆ m'
⊲-to-⊆-pres-trans nil        m' = ≡-sym (⊆-refl-unit-left (⊲-to-⊆ m'))
⊲-to-⊆-pres-trans (cons x m) m' = ≡-trans
  (cong (freshWk ∙_) (⊲-to-⊆-pres-trans m m'))
  (≡-sym (∙-assoc freshWk (⊲-to-⊆ m) (⊲-to-⊆ m')))

ITMF : InclusiveTransitiveMFrame MF IMF TMF
ITMF = record {R-to-⊆-pres-trans = ⊲-to-⊆-pres-trans }

open import Semantics.Presheaf.Base 𝒲 public
open import Semantics.Presheaf.CartesianClosure 𝒲 public
open import Semantics.Presheaf.Possibility MF public
open import Semantics.Presheaf.Strong.Monad MF IMF RMF TMF IRMF ITMF public

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


