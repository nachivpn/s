{-# OPTIONS --safe --without-K #-}

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.CartesianClosed
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

[_]ₛ : Tm Γ a → Sub Γ [ a ]
[ t ]ₛ = [] `, t

[-]ₛ-pres-≈ : t ≈ t' → [ t ]ₛ ≈ₛ [ t' ]ₛ
[-]ₛ-pres-≈ t≈t' = [] `, t≈t'

⊢-refl[_] : (a : Ty) → a ⊢ a
⊢-refl[ a ] = var zero

⊢-trans : a ⊢ b → b ⊢ c → a ⊢ c
⊢-trans t u = substTm [ t ]ₛ u

id[_]  = ⊢-refl[_]

id : a ⊢ a
id = ⊢-refl[ _ ]


infix 21 _⟨_⟩

_⟨_⟩ :  b ⊢ c → a ⊢ b → a ⊢ c
u ⟨ t ⟩ = ⊢-trans t u

⟨-⟩-pres-≈ : t ≈ t' → u ≈ u' → t ⟨ u ⟩ ≈ t' ⟨ u' ⟩
⟨-⟩-pres-≈  t≈t' u≈u' = substTm-pres-≈ ([-]ₛ-pres-≈ u≈u') t≈t'

⟨-⟩-unit-right : (a : Ty) {b : Ty} (t : a ⊢ b) → t ⟨ id ⟩ ≈ t
⟨-⟩-unit-right _ t = ≡-to-≈ (substTm-pres-idₛ t)

⟨-⟩-unit-left : {a : Ty} (b : Ty) (t : a ⊢ b) → id ⟨ t ⟩ ≈ t
⟨-⟩-unit-left _ _ = ≈-refl

⟨-⟩-assoc : (t : c ⊢ d) (u : b ⊢ c) (u' : a ⊢ b) → (t ⟨ u ⟩) ⟨ u' ⟩ ≈ t ⟨ u ⟨ u' ⟩ ⟩
⟨-⟩-assoc t u u' = ≡-to-≈ ((≡-sym (substTm-pres-∙ₛ [ u ]ₛ [ u' ]ₛ t)))

Tm-Cat : Category₀
Tm-Cat = record
  { Obj          = Ty
  ; _→̇_          = _⊢_
  ; _≈̇_          = _≈_
  ; _∘_          = _⟨_⟩
  ; id'[_]       = λ _ → id
  ; ≈̇-refl       = ≈-refl
  ; ≈̇-sym        = ≈-sym
  ; ≈̇-trans      = ≈-trans
  ; ∘-pres-≈̇     = ⟨-⟩-pres-≈
  ; ∘-unit-left  = ⟨-⟩-unit-left
  ; ∘-unit-right = ⟨-⟩-unit-right
  ; ∘-assoc      = ⟨-⟩-assoc
  }

--
-- term model is a cartesian category
--

π₁ : (a × b) ⊢ a
π₁ = fst (var zero)

π₂ : (a × b) ⊢ b
π₂ = snd (var zero)

Tm-Cartesian : IsCartesianₗ Tm-Cat
Tm-Cartesian = record
  { []'           = 𝟙
  ; unit'         = unit
  ; []'-eta       = exp-unit _
  ; _×'_          = _×_
  ; ⟨_,_⟩'        = pair
  ; ⟨,⟩'-pres-≈̇   = cong-pair
  ; π₁'[_]        = λ _ → π₁
  ; π₂'[_]        = λ _ → π₂
  ; ×'-beta-left  = λ t → red-prod1 _ t
  ; ×'-beta-right = λ u → red-prod2 u _
  ; ×'-eta        = exp-prod _
  }

--
-- term model is cartesian closed
--

prₛ : Sub ([ a ] `, b) [ a × b ]
prₛ = [ pair (var (succ zero)) (var zero) ]ₛ

curry : (a × b) ⊢ c → a ⊢ (b ⇒ c)
curry t = lam (substTm prₛ t)

⇒-beta : (t : (a × b) ⊢ c) (u : a ⊢ b)
  → app (curry t) u ≈ t ⟨ pair id u ⟩
⇒-beta t u = ≈-trans (red-fun _ _) (≡-to-≈ (≡-sym (substTm-pres-∙ₛ _ _ t)))

wkFreshLemma : (t : a ⊢ b) → wkTm freshWk[ _ , c ] t ≈ substTm prₛ (t ⟨ π₁ ⟩)
wkFreshLemma t = let open EqReasoning (Tm-setoid _ _) in begin
  wkTm freshWk t
    ≡˘⟨ cong (wkTm freshWk) (substTm-pres-idₛ t) ⟩
  wkTm freshWk (substTm idₛ t)
    ≡⟨⟩
  wkTm freshWk (substTm [ var zero ]ₛ t)
    ≡˘⟨ substTm-nat t [ var zero ]ₛ freshWk ⟩
  substTm (wkSub freshWk [ var zero ]ₛ) t
    ≡⟨⟩
  substTm [ var (succ zero) ]ₛ t
    ≈˘⟨ substTm-pres-≈-left t ([-]ₛ-pres-≈ (red-prod1 _ _)) ⟩
  substTm ([ π₁ ]ₛ ∙ₛ prₛ) t
    ≡⟨ substTm-pres-∙ₛ _ _ t ⟩
  substTm prₛ (t ⟨ π₁ ⟩) ∎

⇒-eta : (t : a ⊢ (b ⇒ c)) → t ≈ curry (app (t ⟨ π₁ ⟩) π₂)
⇒-eta t = ≈-trans (exp-fun t) (cong-lam (cong-app (wkFreshLemma t) (≈-sym (red-prod2 _ _))))

open IsCartesian Tm-Cartesian using (_×'-map_)

curry-nat : (t : (b × c) ⊢ d) (u : a ⊢ b) → curry t ⟨ u ⟩ ≈ curry (t ⟨ u ×'-map id ⟩)
curry-nat t u = cong-lam lemma
  where
  lemma : substTm (keepₛ [ u ]ₛ) (substTm prₛ t) ≈ substTm prₛ (t ⟨ u ×'-map id ⟩)
  lemma = let open EqReasoning (Tm-setoid _ _) in begin
    substTm (keepₛ [ u ]ₛ) (substTm prₛ t)
      ≡˘⟨ substTm-pres-∙ₛ _ _ t ⟩
    substTm (prₛ ∙ₛ keepₛ [ u ]ₛ) t
      ≡⟨⟩
    substTm [ pair (wkTm freshWk u) (var zero) ]ₛ t
      ≈⟨ substTm-pres-≈-left t ([-]ₛ-pres-≈ (cong-pair
          (wkFreshLemma u)
          (≈-sym (red-prod2 _ _)))) ⟩
    substTm ([ pair (substTm prₛ (u ⟨ π₁ ⟩)) (snd (pair _ (var zero))) ]ₛ) t
      ≡⟨⟩
    substTm ([ u ×'-map id ]ₛ ∙ₛ prₛ) t
      ≡⟨  substTm-pres-∙ₛ _ _ t ⟩
    substTm prₛ (t ⟨ u ×'-map id ⟩) ∎

Tm-CartesianClosed : IsCartesianClosedₗ Tm-Cat Tm-Cartesian
Tm-CartesianClosed = record
  { _⇒'_        = _⇒_
  ; lam'        = curry
  ; lam'-pres-≈̇ = λ t≈t' → cong-lam (substTm-pres-≈-right _ t≈t')
  ; app'        = app
  ; app'-pres-≈̇ = cong-app
  ; ⇒'-beta     = ⇒-beta
  ; ⇒'-eta      = ⇒-eta
  ; lam'-nat    = curry-nat
  ; app'-nat    = λ _ _ _ → ≈-refl
  }

--
-- ◇ is a functor
--

◇-map : a ⊢ b → (◇ a) ⊢ (◇ b)
◇-map t = sletin (var zero) (wkTm (keep freshWk) t)

◇-map-pres-≈ : t ≈ t' → ◇-map t ≈ ◇-map t'
◇-map-pres-≈ t≈t' = cong-sletin2 (wkTm-pres-≈ (keep freshWk) t≈t')

◇-map-pres-⊢refl : ◇-map id[ a ] ≈ id[ ◇ a ]
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

--
-- categorical completeness machinery
--

-- will be replaced by evalCtx
⟦_⟧ : Ctx → Ty
⟦ [] ⟧     = 𝟙
⟦ Γ `, a ⟧ = ⟦ Γ ⟧ × a

-- "context term" (c.f. Lemma 3.1 in [Clouston 2018])
cₜ[_] : ∀ Γ → Tm Γ ⟦ Γ ⟧
cₜ[ [] ]     = unit
cₜ[ Γ `, a ] = pair (wkTm freshWk cₜ[ Γ ]) (var zero)

from-⊢ : ⟦ Γ ⟧ ⊢ a → Tm Γ a
from-⊢ = substTm [ cₜ[ _ ] ]ₛ

from-⊢-pres-≈ : {t' u' : ⟦ Γ ⟧ ⊢ a} → t' ≈ u' → from-⊢ t' ≈ from-⊢ u'
from-⊢-pres-≈ = substTm-pres-≈-right _
















































































