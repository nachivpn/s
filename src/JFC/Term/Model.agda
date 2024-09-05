{-# OPTIONS --safe --without-K #-}

open import Semantics.Category.Base
--open import Semantics.Category.Cartesian
--open import Semantics.Category.CartesianClosed
open import Semantics.Category.EndoFunctor.Base
--open import Semantics.Category.EndoFunctor.Multiplicative
--open import Semantics.Category.EndoFunctor.Strong.Base
--open import Semantics.Category.EndoFunctor.Strong.Multiplicative

open import JFC.Term.Base
open import JFC.Term.Properties
open import JFC.Term.Conversion

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

module JFC.Term.Model where

open import Level using (0ℓ)
_⊢_ : Ty → Ty → Set
a ⊢ b = Tm [ a ] b

[_]ₛ : Tm [ a ] b → Sub [ a ] [ b ]
[ t ]ₛ = [] `, t

[-]ₛ-pres-≈ : t ≈ t' → [ t ]ₛ ≈ₛ [ t' ]ₛ
[-]ₛ-pres-≈ t≈t' = [] `, t≈t'

⊢-refl[_] : (a : Ty) → a ⊢ a
⊢-refl[ _ ] = var zero

⊢-trans : a ⊢ b → b ⊢ c → a ⊢ c
⊢-trans t u = substTm [ t ]ₛ u

infix 22 _⟨_⟩

_⟨_⟩ :  b ⊢ c → a ⊢ b → a ⊢ c
u ⟨ t ⟩ = ⊢-trans t u

⟨-⟩-pres-≈ : t ≈ t' → u ≈ u' → t ⟨ u ⟩ ≈ t' ⟨ u' ⟩
⟨-⟩-pres-≈  t≈t' u≈u' = subsTm-pres-≈ ([-]ₛ-pres-≈ u≈u') t≈t'

⟨-⟩-unit-right : (a : Ty) {b : Ty} (t : a ⊢ b) → t ⟨ ⊢-refl[ a ] ⟩ ≈ t
⟨-⟩-unit-right _ t = ≡-to-≈ (substTm-pres-idₛ t)

⟨-⟩-unit-left : {a : Ty} (b : Ty) (t : a ⊢ b) → ⊢-refl[ b ] ⟨ t ⟩ ≈ t
⟨-⟩-unit-left _ _ = ≈-refl

⟨-⟩-assoc : (t : c ⊢ d) (u : b ⊢ c) (u' : a ⊢ b) → (t ⟨ u ⟩) ⟨ u' ⟩ ≈ t ⟨ u ⟨ u' ⟩ ⟩
⟨-⟩-assoc t u u' = ≡-to-≈ ((≡-sym (substTm-pres-∙ₛ [ u ]ₛ [ u' ]ₛ t)))

Tm-Cat : Category₀
Tm-Cat = record
  { Obj          = Ty
  ; _→̇_          = _⊢_
  ; _≈̇_          = _≈_
  ; _∘_          = _⟨_⟩
  ; id'[_]       = ⊢-refl[_]
  ; ≈̇-refl       = ≈-refl
  ; ≈̇-sym        = ≈-sym
  ; ≈̇-trans      = ≈-trans
  ; ∘-pres-≈̇     = ⟨-⟩-pres-≈
  ; ∘-unit-left  = ⟨-⟩-unit-left
  ; ∘-unit-right = ⟨-⟩-unit-right
  ; ∘-assoc      = ⟨-⟩-assoc
  }

◇-map : a ⊢ b → (◇ a) ⊢ (◇ b)
◇-map t = sletin (var zero) (wkTm (keep freshWk) t)

◇-map-pres-≈ : t ≈ t' → ◇-map t ≈ ◇-map t'
◇-map-pres-≈ t≈t' = cong-sletin2 (wkTm-pres-≈ (keep freshWk) t≈t')

◇-map-pres-⊢refl : ◇-map ⊢-refl[ a ] ≈ ⊢-refl[ ◇ a ]
◇-map-pres-⊢refl = ≈-sym (exp-dia (var zero))

◇-map-pres-⟨-⟩ : (t : b ⊢ c) (u : a ⊢ b) → ◇-map (t ⟨ u ⟩) ≈ (◇-map t ⟨ ◇-map u ⟩ )
◇-map-pres-⟨-⟩ t u = let open EqReasoning (Tm-setoid _ _) in begin
  -- Agda's normalization is doing a lot in this proof;
  -- the details of which are noisy, and thus hidden.
  sletin (var zero) (wkTm _ (substTm [ u ]ₛ t))
    ≡˘⟨ cong (sletin _) (substTm-nat t _ _) ⟩
  sletin (var zero) (substTm (wkSub _ [ u ]ₛ ) t)
    ≡⟨ cong (sletin _) (substTm-pres-∙ₛ _ _ t) ⟩
  sletin (var zero) (substTm _{-u-} (substTm _ t))
    ≈˘⟨ red-dia _ _ _ ⟩
  sletin (sletin (var zero) _{-u-}) (substTm _ t)   
    ≡⟨ cong (sletin _) (assoc-substTm-trimSub t _ _) ⟩
  sletin (var zero) (wkTm _ t) ⟨ sletin (var zero) (wkTm _ u) ⟩
    ∎

◇-Functor : EndoFunctorₗ Tm-Cat
◇-Functor = record
  { ℱ'_         = ◇_
  ; map_        = ◇-map
  ; map-pres-≈̇  = ◇-map-pres-≈
  ; map-pres-id = ◇-map-pres-⊢refl
  ; map-pres-∘  = ◇-map-pres-⟨-⟩
  }






















































































