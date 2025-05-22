--{-# OPTIONS --safe --without-K #-}

module MLC.Norm.Properties where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

open import Data.Unit
open import Data.Product using (Σ ; ∃; ∃₂; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum

open import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here ; there)

open import MLC.Term             -- Ctx, Ty, etc.
open import MLC.Term.NormalForm  -- Ne, Nf, etc.

open import MLC.Norm.Base renaming (_⊲_ to _⊲ML_) using ()
open _⊲ML_

-- binary relations (need not be monotonic in either Ctx)
Rel  = Ctx → Ctx → Set

-- should ideally be monotonic
ISet = Ctx → Set

-- Container defining the shape of relations
data Cont : Set₁ where
  id   : Cont
  rec  : Cont
  val  : ISet → Cont
  ext  : Ty → Cont → Cont   
  _×'_ : Cont → Cont → Cont
  _⊎'_ : Cont → Cont → Cont
  ∃'_  : ((a : Ty) → Cont) → Cont

-- can be used to add a constant payload to constructors
const : Set → Cont
const X = val λ _ → X

--------------------------
-- 'Linear' interpretation
--------------------------

-- semantics of containers
⟦_⟧ : Cont → Rel → Rel
⟦ id       ⟧ _ = λ Γ Δ → Γ ≡ Δ
⟦ rec      ⟧ R = λ Γ Δ → R Γ Δ
⟦ val X    ⟧ _ = λ Γ _ → X Γ
⟦ ext a F  ⟧ R = λ Γ Δ → (⟦ F ⟧ R) (Γ `, a) Δ
⟦ F ⊎' G   ⟧ R = λ Γ Δ → (⟦ F ⟧ R) Γ Δ ⊎ (⟦ G ⟧ R) Γ Δ
⟦ F ×' G   ⟧ R = λ Γ Δ → (⟦ F ⟧ R) Γ Δ × (⟦ G ⟧ R) Γ Δ
⟦ ∃' Fₐ    ⟧ R = λ Γ Δ → ∃ λ a → ⟦ Fₐ a ⟧ R Γ Δ

-- least fixed point
data μ_ (F : Cont) : Rel where
  lfp : {Γ Δ : Ctx} → (⟦ F ⟧ (μ F)) Γ Δ → (μ F) Γ Δ

--
-- Monad example
--

-- monadic binding
neu : Cont → Cont
neu C = ∃' λ a → val (λ Γ → Ne Γ (◇ a)) ×' ext a C

-- container for MLC
⊲MLC : Cont
⊲MLC = id ⊎' neu rec

-- relation for MLC
_⊲ML'_ : Rel
_⊲ML'_ = μ ⊲MLC

-- ⊲ML' (generated) and ⊲ (implemented directly) are isomorphic
module _ where

  toML : Γ ⊲ML Δ → Γ ⊲ML' Δ
  toML nil = lfp (inj₁ ≡-refl)
  toML (cons x m) = lfp (inj₂ (-, x , toML m))

  fromML : Γ ⊲ML' Δ → Γ ⊲ML Δ
  fromML (lfp (inj₁ ≡-refl)) = nil
  fromML (lfp (inj₂ (_ , n , m'))) = cons n (fromML m')

  toML-fromML-is-id : (m : Γ ⊲ML Δ) → fromML (toML m) ≡ m
  toML-fromML-is-id nil = ≡-refl
  toML-fromML-is-id (cons x m) = cong₂ cons ≡-refl (toML-fromML-is-id m)

  fromML-toML-is-id : (m' : Γ ⊲ML' Δ) → toML (fromML m') ≡ m'
  fromML-toML-is-id (lfp (inj₁ ≡-refl)) = ≡-refl
  fromML-toML-is-id (lfp (inj₂ (_ , n , m'))) = cong lfp (cong inj₂ (cong (λ z → (-, n , z)) (fromML-toML-is-id m')))

--
-- Non-monadic examples
--

-- strong (but not pointed or joinable)
⊲SFC : Cont
⊲SFC = neu id

-- strong pointed
⊲PFC : Cont
⊲PFC = id ⊎' neu id

-- strong joinable
⊲JFC : Cont
⊲JFC = neu id ⊎' neu rec
-- or alternativey `neu (id ⊎' rec)`

-----------------------------
-- 'Branching' interpretation
-----------------------------

-- family of worlds
Wₛ = List Ctx

variable
  Δs Δs' Δs1 Δs2 : Wₛ

-- covering relations
CovRel = Ctx → Wₛ → Set

-- semantics of containers as coverings
⟦_⟧ₛ : Cont → CovRel → CovRel
⟦ id       ⟧ₛ _ = λ Γ Δs → Γ ∈ Δs
⟦ rec      ⟧ₛ R = λ Γ Δs → R Γ Δs
⟦ val X    ⟧ₛ _ = λ Γ Δs → X Γ
⟦ ext a F  ⟧ₛ R = λ Γ Δs → (⟦ F ⟧ₛ R) (Γ `, a) Δs
⟦ F ⊎' G   ⟧ₛ R = λ Γ Δs → (⟦ F ⟧ₛ R) Γ Δs ⊎ (⟦ G ⟧ₛ R) Γ Δs
⟦ F ×' G   ⟧ₛ R = λ Γ Δs → (⟦ F ⟧ₛ R) Γ Δs × (⟦ G ⟧ₛ R) Γ Δs
⟦ ∃' Fₐ    ⟧ₛ R = λ Γ Δs → ∃ λ a → ⟦ Fₐ a ⟧ₛ R Γ Δs

-- least fixed point
data μₛ_ (F : Cont) : CovRel where
  lfp : {Γ : Ctx} {Δs : List Ctx}→ (⟦ F ⟧ₛ (μₛ F)) Γ Δs → (μₛ F) Γ Δs

--
-- Case tree example
--

postulate
  _+_ : Ty → Ty → Ty

-- case binding
case' : Cont
case' = ∃' (λ a → ∃' (λ b → val (λ Γ → Ne Γ (a + b)) ×' (ext a rec ×' ext b rec)))

⊲+C : Cont
⊲+C = id ⊎' case'

_⊲+'_ : CovRel
_⊲+'_ = μₛ ⊲+C

-- Q: Is this the correct defn.?
data _⊲+_ : Ctx → List Ctx → Set where
  nil  : Γ ∈ Δs → Γ ⊲+ Δs
  case : Ne Γ (a + b) → (Γ `, a) ⊲+ Δs → (Γ `, b) ⊲+ Δs → Γ ⊲+ Δs

-- Intuition: the 'cover' modality should be defined as
--
-- 𝒞 A ₀ w = ∃ λ vs → (w ⊲+ vs) × ∀ v → v ∈ vs → A ₀ v
--

-- Ideally, I would like ⊲+C to be given by the user
-- and the cover modality is defined as
--
-- 𝒞 A ₀ w = ∃ λ vs → (μₛ ⊲+C w vs) × ∀ v → v ∈ vs → A ₀ v
--
-- then, structure of an element of `Cont` (not CovRel)
-- will the determine the structure of the 𝒞 functor

-- observe:
⊲+-iden : Γ ⊲+ L.[ Γ ]
⊲+-iden = nil (here ≡-refl)

-- Q: what about ⊲+-trans? what should its type be?

-- ⊲+' (generated) and ⊲+ (implemented directly) are isomorphic
module _ where

  to+ : Γ ⊲+ Δs → Γ ⊲+' Δs
  to+ (nil p)        = lfp (inj₁ p)
  to+ (case n m1 m2) = lfp (inj₂ ((-, (-, n , to+ m1 , to+ m2))))

  from+ : Γ ⊲+' Δs → Γ ⊲+ Δs
  from+ (lfp (inj₁ p)) = nil p
  from+ (lfp (inj₂ (a , b , n , m1 , m2))) = case n (from+ m1) (from+ m2)


