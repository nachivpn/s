{-# OPTIONS --safe --without-K #-}

module MLC.Norm.Properties where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

open import MLC.Term
open import MLC.Term.NormalForm

open import MLC.Norm.Base renaming (_⊲_ to _⊲ML_) using ()
open _⊲ML_

open import Data.Sum
open import Data.Product using (Σ ; ∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Unit

-- Relation
Rel = Ctx → Ctx → Set

-- "Relation generator"
data RelG : Set₁ where
  nil  : RelG
  id   : RelG
  ext  : Ty → RelG → RelG
  _×'_ : Rel → RelG → RelG
  _⊎'_ : RelG → RelG → RelG
  ∃'_  : ((a : Ty) → RelG) → RelG

-- constant relation
rel : Rel → RelG
rel Q = Q ×' nil

-- constant set
con : Set → RelG
con X = rel (λ _ _ → X)

-- neutral binding
neu : RelG → RelG
neu RG = ∃' λ a → (λ Γ _ → Ne Γ (◇ a)) ×' ext a RG

-- semantics of relation generators
⟦_⟧ : RelG → Rel → Rel
⟦ nil      ⟧ _ = λ Γ Δ → Γ ≡ Δ
⟦ id       ⟧ R = λ Γ Δ → R Γ Δ
⟦ ext a F  ⟧ R = λ Γ Δ → (⟦ F ⟧ R) (Γ `, a) Δ
⟦ F ⊎' G   ⟧ R = λ Γ Δ → (⟦ F ⟧ R) Γ Δ ⊎ (⟦ G ⟧ R) Γ Δ
⟦ Q ×' G   ⟧ R = λ Γ Δ → Q Γ Δ × (⟦ G ⟧ R) Γ Δ
⟦ ∃' Fₐ    ⟧ R = λ Γ Δ → ∃ λ a → ⟦ Fₐ a ⟧ R Γ Δ

-- least fixed point
data μ_ (F : RelG) : Rel where
  lfp : {Γ Δ : Ctx} → (⟦ F ⟧ (μ F)) Γ Δ → (μ F) Γ Δ

-- relation generator for MLC
⊲MLG : RelG
⊲MLG = nil ⊎' neu id

-- relation for MLC
_⊲ML'_ : Rel
_⊲ML'_ = μ ⊲MLG

-- ⊲ML' (generated) and ⊲ (implemented directly) are isomorphic
module _ where

  to : Γ ⊲ML Δ → Γ ⊲ML' Δ
  to nil = lfp (inj₁ ≡-refl)
  to (cons x m) = lfp (inj₂ (-, x , to m))

  from : Γ ⊲ML' Δ → Γ ⊲ML Δ
  from (lfp (inj₁ ≡-refl)) = nil
  from (lfp (inj₂ (_ , n , m'))) = cons n (from m')

  to-from-is-id : (m : Γ ⊲ML Δ) → from (to m) ≡ m
  to-from-is-id nil = ≡-refl
  to-from-is-id (cons x m) = cong₂ cons ≡-refl (to-from-is-id m)

  from-to-is-id : (m' : Γ ⊲ML' Δ) → to (from m') ≡ m'
  from-to-is-id (lfp (inj₁ ≡-refl)) = ≡-refl
  from-to-is-id (lfp (inj₂ (_ , n , m'))) = cong lfp (cong inj₂ (cong (λ z → (-, n , z)) (from-to-is-id m')))

--
-- Observe an unrestricted ×' as follows
--
--  _×'_ : RelG → RelG → RelG
--  ⟦ F ×' G ⟧ R = λ Γ Δ → (⟦ F ⟧ R) Γ Δ × (⟦ G ⟧ R) Γ Δ
--
-- introduces branching
--
-- e.g. neu (id ×' id)
--

⊲SFG : RelG
⊲SFG = neu nil

⊲PFG : RelG
⊲PFG = ⊲SFG ⊎' nil

⊲JFG : RelG
⊲JFG = ⊲SFG ⊎' neu id

-- observe we can write
--
-- split : RelG → RelG
-- split RG = ∃' λ a → ∃' (λ b → (λ Γ Δ → Ne Γ (a × b)) ×' ext a (ext b RG))

-- observe we can write (while pretending 𝒲 is some indexed set with monoidal structure)
--
-- write-let : RelG → RelG
-- write-let RG = (λ Γ _ → 𝒲 Γ) ×' neu RG
