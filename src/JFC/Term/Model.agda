{-# OPTIONS --safe --without-K #-}

open import Semantics.Category.Base
open import Semantics.Category.Cartesian
open import Semantics.Category.CartesianClosed
open import Semantics.Category.EndoFunctor.Base
open import Semantics.Category.EndoFunctor.Multiplicative
open import Semantics.Category.EndoFunctor.Strong.Base
open import Semantics.Category.EndoFunctor.Strong.Multiplicative

open import JFC.Term.Base
open import JFC.Term.Properties
open import JFC.Term.Conversion

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

module JFC.Term.Model where

open import Level using (0ℓ)

infix 19 _⊢_

_⊢_ : Ty → Ty → Set
a ⊢ b = Tm [ a ] b

[_]ₛ : Tm Γ a → Sub Γ [ a ]
[ t ]ₛ = [] `, t

[-]ₛ-pres-≈ : t ≈ t' → [ t ]ₛ ≈ₛ [ t' ]ₛ
[-]ₛ-pres-≈ t≈t' = [] `, t≈t'

v0ₜ[_] : (a : Ty) → Tm (Γ `, a) a
v0ₜ[ _ ] = var v0

v0ₜ : Tm (Γ `, a) a
v0ₜ = v0ₜ[ _ ]

v1ₜ : Tm ((Γ `, a) `, b) a
v1ₜ = var v1

⊢-refl[_] = v0ₜ[_]

id[_]  = v0ₜ[_]

id : a ⊢ a
id = v0ₜ

⊢-trans : a ⊢ b → b ⊢ c → a ⊢ c
⊢-trans t u = substTm [ t ]ₛ u


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

𝒯 : Category₀
𝒯 = record
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
π₁ = fst v0ₜ

π₂ : (a × b) ⊢ b
π₂ = snd v0ₜ

𝒯-is-CC : IsCartesianₗ 𝒯
𝒯-is-CC = record
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
prₛ = [ pair v1ₜ v0ₜ ]ₛ

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
  wkTm freshWk (substTm [ v0ₜ ]ₛ t)
    ≡˘⟨ substTm-nat t [ v0ₜ ]ₛ freshWk ⟩
  substTm (wkSub freshWk [ v0ₜ ]ₛ) t
    ≡⟨⟩
  substTm [ v1ₜ ]ₛ t
    ≈˘⟨ substTm-pres-≈-left t ([-]ₛ-pres-≈ (red-prod1 _ _)) ⟩
  substTm ([ π₁ ]ₛ ∙ₛ prₛ) t
    ≡⟨ substTm-pres-∙ₛ _ _ t ⟩
  substTm prₛ (t ⟨ π₁ ⟩) ∎

⇒-eta : (t : a ⊢ (b ⇒ c)) → t ≈ curry (app (t ⟨ π₁ ⟩) π₂)
⇒-eta t = ≈-trans (exp-fun t) (cong-lam (cong-app (wkFreshLemma t) (≈-sym (red-prod2 _ _))))

open IsCartesian 𝒯-is-CC renaming
  (_×'-map_  to _×-map_
  ; ×'-assoc to ×-assoc)

curry-nat : (t : (b × c) ⊢ d) (u : a ⊢ b) → curry t ⟨ u ⟩ ≈ curry (t ⟨ u ×-map id ⟩)
curry-nat t u = cong-lam lemma
  where
  lemma : substTm (keepₛ [ u ]ₛ) (substTm prₛ t) ≈ substTm prₛ (t ⟨ u ×-map id ⟩)
  lemma = let open EqReasoning (Tm-setoid _ _) in begin
    substTm (keepₛ [ u ]ₛ) (substTm prₛ t)
      ≡˘⟨ substTm-pres-∙ₛ _ _ t ⟩
    substTm (prₛ ∙ₛ keepₛ [ u ]ₛ) t
      ≡⟨⟩
    substTm [ pair (wkTm freshWk u) v0ₜ ]ₛ t
      ≈⟨ substTm-pres-≈-left t ([-]ₛ-pres-≈ (cong-pair
          (wkFreshLemma u)
          (≈-sym (red-prod2 _ _)))) ⟩
    substTm ([ pair (substTm prₛ (u ⟨ π₁ ⟩)) (snd (pair _ v0ₜ)) ]ₛ) t
      ≡⟨⟩
    substTm ([ u ×-map id ]ₛ ∙ₛ prₛ) t
      ≡⟨  substTm-pres-∙ₛ _ _ t ⟩
    substTm prₛ (t ⟨ u ×-map id ⟩) ∎

𝒯-is-CCC : IsCartesianClosedₗ 𝒯 𝒯-is-CC
𝒯-is-CCC = record
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
◇-map t = sletin v0ₜ (wkTm (keep freshWk) t)

◇-map-pres-≈ : t ≈ t' → ◇-map t ≈ ◇-map t'
◇-map-pres-≈ t≈t' = cong-sletin2 (wkTm-pres-≈ (keep freshWk) t≈t')

◇-map-pres-⊢refl : ◇-map id[ a ] ≈ id[ ◇ a ]
◇-map-pres-⊢refl = ≈-sym (exp-dia v0ₜ)

◇-map-pres-⟨-⟩ : (t : b ⊢ c) (u : a ⊢ b) → ◇-map (t ⟨ u ⟩) ≈ (◇-map t ⟨ ◇-map u ⟩ )
◇-map-pres-⟨-⟩ t u = let open EqReasoning (Tm-setoid _ _) in begin
  -- Agda's normalization is doing a lot in this proof;
  -- the details of which are noisy, and thus hidden.
  sletin v0ₜ (wkTm _ (substTm [ u ]ₛ t))
    ≡˘⟨ cong (sletin _) (substTm-nat t _ _) ⟩
  sletin v0ₜ (substTm (wkSub _ [ u ]ₛ ) t)
    ≡⟨ cong (sletin _) (substTm-pres-∙ₛ _ _ t) ⟩
  sletin v0ₜ (substTm _{-u-} (substTm _ t))
    ≈˘⟨ red-dia1 _ _ _ ⟩
  sletin (sletin v0ₜ _{-u-}) (substTm _ t)
    ≡⟨ cong (sletin _) (assoc-substTm-trimSub t _ _) ⟩
  sletin v0ₜ (wkTm _ t) ⟨ sletin v0ₜ (wkTm _ u) ⟩
    ∎

◇ℱ : EndoFunctorₗ 𝒯
◇ℱ = record
  { ℱ'_         = ◇_
  ; map_        = ◇-map
  ; map-pres-≈̇  = ◇-map-pres-≈
  ; map-pres-id = ◇-map-pres-⊢refl
  ; map-pres-∘  = ◇-map-pres-⟨-⟩
  }

--
-- ◇ is a strong functor
--

◇-strength[_,_] : (a b : Ty) → (a × ◇ b) ⊢ ◇ (a × b)
◇-strength[ _ , _ ] = sletin (snd v0ₜ) (pair (fst v1ₜ) v0ₜ)

◇-strength : (a × ◇ b) ⊢ ◇ (a × b)
◇-strength = ◇-strength[ _ , _ ]

◇-strength-natural₁ : (t : a ⊢ b)
  → ◇-strength ⟨ t ×-map id[ ◇ c ] ⟩ ≈ ◇-map (t ×-map id[ c ]) ⟨ ◇-strength ⟩
◇-strength-natural₁ t = let open EqReasoning (Tm-setoid _ _) in begin
  sletin (snd (pair _ _)) (pair (fst (pair _ _)) _)
    ≈⟨ cong-sletin (red-prod2 _ _) (cong-pair1 (red-prod1 _ _)) ⟩
  sletin _ (pair (wkTm freshWk (t ⟨ π₁ ⟩)) _)
    ≈⟨ cong-sletin2 (cong-pair1 (wkFreshLemma (t ⟨ π₁ ⟩))) ⟩
  sletin _ (pair (substTm prₛ (t ⟨ π₁ ⟩ ⟨ π₁ ⟩)) _)
    ≡˘⟨ cong (λ z → sletin _ (pair z _))
          (≡-trans
            (substTm-pres-∙ₛ _ _ t)
            (substTm-pres-∙ₛ _ _ (t ⟨ π₁ ⟩))) ⟩
  sletin π₂ (pair (substTm [ fst (fst (pair _ _)) ]ₛ t) _)
    ≈⟨ cong-sletin2 (cong-pair1
         (substTm-pres-≈-left t
           ([-]ₛ-pres-≈ (cong-fst (red-prod1 _ _))))) ⟩
  sletin π₂ (pair (substTm [ fst _ ]ₛ t) v0ₜ)
    ≈˘⟨ cong-sletin2 (cong-pair1
          (substTm-pres-≈-left t ([-]ₛ-pres-≈ (red-prod1 _ _)))) ⟩
  sletin π₂ (pair (substTm [ fst (pair (fst _) _) ]ₛ t) _)
    ≈˘⟨ cong-sletin2 (cong-pair
          (≡-to-≈ (≡-sym (substTm-pres-∙ₛ _ _ t)))
          (red-prod2 _ _)) ⟩
  sletin π₂ (pair (substTm _ (substTm [ _ ]ₛ t)) _)
    ≈˘⟨ red-dia1 π₂ _ _ ⟩
  sletin (sletin _ _) (pair (substTm [ _ ]ₛ t) _)
    ≡⟨ cong (λ z → sletin _ (pair z _))
         (substTm-pres-∙ₛ _ _ t) ⟩
  sletin (sletin _ _) (pair (substTm [ _ ]ₛ (t ⟨ π₁ ⟩)) _)
    ≡⟨ cong (λ z → sletin _ (pair z _))
       (assoc-substTm-trimSub (t ⟨ π₁ ⟩) _ _) ⟩
  sletin (sletin _ _) (pair (substTm _ (wkTm _ (t ⟨ π₁ ⟩))) _)
    ∎

◇-strength-natural₂ : (t : b ⊢ c)
  → ◇-strength ⟨ id[ a ] ×-map (◇-map t) ⟩ ≈ ◇-map (id[ a ] ×-map t) ⟨ ◇-strength ⟩
◇-strength-natural₂ t = let open EqReasoning (Tm-setoid _ _) in begin
  sletin (snd (pair _ _)) (pair (fst (pair _ _)) _)
    ≈⟨ cong-sletin (red-prod2 _ _) (cong-pair1 (red-prod1 _ _)) ⟩
  sletin (sletin π₂ (substTm _ (wkTm _ t))) (pair _ _)
    ≡˘⟨ cong (λ z → sletin (sletin _ z ) (pair _ _)) (assoc-substTm-wkTm t _ _) ⟩
  sletin (sletin π₂ (substTm _ t)) (pair _ _)
    ≈⟨ red-dia1 _ _ _ ⟩
  sletin π₂ (pair _ (substTm [ v0ₜ ]ₛ t))
    ≈˘⟨ cong-sletin2 (cong-pair2 (substTm-pres-≈-left t ([-]ₛ-pres-≈ (red-prod2 _ _)))) ⟩
  sletin π₂ (pair _ (substTm [ (snd (pair _ _)) ]ₛ t))
    ≈˘⟨ cong-sletin2 (cong-pair (red-prod1 _ _) (≡-to-≈ (≡-sym (substTm-pres-∙ₛ _ _ t)))) ⟩
  sletin π₂ (pair (fst (pair _ _)) (substTm _ (substTm _ t)))
    ≈˘⟨ red-dia1 _ _ _ ⟩
  sletin (sletin _ _) (pair _ (substTm [ _ ]ₛ t))
    ≡⟨ cong (λ z → sletin _ (pair _ z)) (substTm-pres-∙ₛ _ _ t) ⟩
  sletin _ (pair _ (substTm _ (substTm _ t)))
    ≡⟨ cong (λ z → sletin _ (pair _ (substTm _ z))) (substTm-nat t _ _) ⟩
  sletin _ (pair _ (substTm _ (wkTm _ (substTm _ t))))
    ∎

◇-strength-unit : ◇-map π₂ ⟨ ◇-strength[ a , b ] ⟩ ≈ π₂
◇-strength-unit = let open EqReasoning (Tm-setoid _ _) in begin
  sletin (sletin π₂ (pair _ _)) (snd v0ₜ)
    ≈⟨ red-dia1 _ _ _ ⟩
  sletin π₂ (snd (pair _ _))
    ≈⟨ cong-sletin2 (red-prod2 _ _) ⟩
  sletin π₂ _
    ≈˘⟨ exp-dia _ ⟩
  π₂ ∎

◇-strength-assoc : (◇-map ×-assoc) ⟨ ◇-strength[ a × b , c ] ⟩
  ≈ (◇-strength ⟨ id ×-map (◇-strength) ⟩ ⟨ ×-assoc ⟩)
◇-strength-assoc = let open EqReasoning (Tm-setoid _ _) in begin
  sletin (sletin _ (pair _ _)) (pair _ _)
    ≈⟨ red-dia1 _ _ _ ⟩
  sletin π₂ (pair
      (fst (fst (pair _ _)))
      (pair (snd (fst (pair _ _))) (snd (pair _ _))))
    ≈⟨ cong-sletin2 (cong-pair
        (cong-fst (red-prod1 _ _))
        (cong-pair
          (cong-snd (red-prod1 _ _))
          (red-prod2 _ _))) ⟩
  sletin π₂ (pair _ (pair _ _))
    ≈˘⟨ red-dia1 _ _ _ ⟩
  sletin (sletin _ _) (pair _ _)
    ≈˘⟨ cong-sletin (cong-sletin
          (≈-trans (cong-snd (red-prod2 _ _)) (red-prod2 _ _))
          (cong-pair1 (≈-trans (cong-fst (red-prod2 _ _)) (red-prod1 _ _))))
          (cong-pair1 (red-prod1 _ _)) ⟩
  sletin
   (sletin (snd (snd (pair _ (pair _ _))))
   (pair (fst (snd (pair _ (pair _ _)))) _)) _
    ≈˘⟨ cong-sletin
          (red-prod2 _ _)
          (cong-pair1 (red-prod1 _ _)) ⟩
  sletin (snd (pair _ _)) (pair (fst (pair _ _ )) _)
    ∎

◇-is-strong : IsStrongₗ 𝒯-is-CC ◇ℱ
◇-is-strong = record
   { strength[_,_]     = λ _ _ → ◇-strength -- use implicit version for smaller goals
   ; strength-natural₁ = ◇-strength-natural₁
   ; strength-natural₂ = ◇-strength-natural₂
   ; strength-assoc    = ◇-strength-assoc
   ; strength-unit     = ◇-strength-unit
   }

--
-- ◇ is joinable
--

◇-join[_] : (a : Ty) → ◇ ◇ a ⊢ ◇ a
◇-join[ _ ] = jletin id v0ₜ

◇-join : ◇ ◇ a ⊢ ◇ a
◇-join = ◇-join[ _ ]

◇-join-natural : (t : a ⊢ b)
  → ◇-join[ b ] ⟨ ◇-map (◇-map t) ⟩ ≈ ◇-map t ⟨ ◇-join[ a ] ⟩
◇-join-natural {a} {b} t = let open EqReasoning (Tm-setoid _ _) in begin
  jletin (sletin id (sletin v0ₜ (wkTm _ (wkTm _ t)))) v0ₜ
    ≡˘⟨ cong (λ z → jletin (sletin _ (sletin _ z)) _) (wkTm-pres-⊆-trans _ _ t) ⟩
  jletin (sletin v0ₜ (sletin v0ₜ (wkTm _ t))) v0ₜ
    -- sletin elim
    ≈⟨ red-dia2 v0ₜ _ v0ₜ ⟩
  jletin id (sletin v0ₜ (wkTm _ t))
    ≈˘⟨ cong-jletin2 (cong-sletin2 (wkTm-pres-≈ _ (≡-to-≈ (substTm-pres-idₛ t)))) ⟩
  jletin id (sletin v0ₜ (wkTm _ (substTm idₛ t)))
    ≡˘⟨ cong (λ z → jletin v0ₜ (sletin v0ₜ z)) (substTm-nat t _ _) ⟩
  jletin id (sletin v0ₜ (substTm [ v0ₜ ]ₛ t))
    ≡⟨ cong (λ z → jletin v0ₜ (sletin v0ₜ z)) (substTm-nat t _ _) ⟩
  jletin id (sletin v0ₜ (wkTm (keep freshWk) (substTm [ v0ₜ ]ₛ t)))
    -- jletin-sletin commute
    ≈˘⟨ com-dia v0ₜ v0ₜ _ ⟩
  sletin (jletin id v0ₜ) (substTm [ v0ₜ ]ₛ t)
    ≡⟨ cong (λ z → sletin _ z) (assoc-substTm-wkTm t _ _)  ⟩
  sletin (jletin id v0ₜ) (substTm _ (wkTm _ t))
    ∎

◇-join-assoc : ◇-join[ a ] ⟨ ◇-map (◇-join[ a ]) ⟩ ≈ ◇-join[ a ] ⟨ ◇-join[ ◇  a ] ⟩
◇-join-assoc = let open EqReasoning (Tm-setoid _ _) in begin
  jletin (sletin v0ₜ (jletin v0ₜ v0ₜ)) v0ₜ
    -- sletin elim
    ≈⟨ red-dia2 _ _ _ ⟩
  jletin v0ₜ (jletin v0ₜ v0ₜ)
    ≈˘⟨ ass-dia _ _ _ ⟩
  jletin (jletin v0ₜ v0ₜ) v0ₜ
    ∎

◇-is-joinable : IsMultiplicativeₗ ◇ℱ
◇-is-joinable = record
  { mult[_]      = λ a → ◇-join
  ; mult-natural = ◇-join-natural
  ; mult-assoc   = ◇-join-assoc
  }

--
-- ◇ is strong joinable
--

◇-strength-mult : ◇-join[ a × b ] ⟨ ◇-map (◇-strength) ⟨  ◇-strength ⟩ ⟩ ≈ ◇-strength[ a , b ] ⟨ (id[ a ] ×-map ◇-join[ b ]) ⟩
◇-strength-mult = let open EqReasoning (Tm-setoid _ _) in begin
  jletin (sletin (sletin _ _) _) v0ₜ
    ≈⟨ red-dia2 _ _ _ ⟩
  jletin (sletin _ _) _
    ≈⟨ red-dia2 _ _ _ ⟩
  jletin _ (sletin (snd (pair _ _)) (pair (fst (pair _ _)) _))
    ≈⟨ cong-jletin2 (cong-sletin (red-prod2 _ _) (cong-pair1 (red-prod1 _ _))) ⟩
  jletin _ (sletin _ _)
    ≈˘⟨ com-dia _ _ _ ⟩
  sletin (jletin _ _) (pair _ v0ₜ)
    ≈˘⟨ cong-sletin (red-prod2 _ _) (cong-pair1 (red-prod1 _ _)) ⟩
  sletin (snd (pair _ _)) (pair (fst (pair _ _)) v0ₜ)
    ∎

◇-is-strong-joinable : IsStrongMultiplicativeₗ ◇ℱ ◇-is-strong ◇-is-joinable
◇-is-strong-joinable = record { strength-mult = ◇-strength-mult }

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
cₜ[ Γ `, a ] = pair (wkTm freshWk cₜ[ Γ ]) v0ₜ

from-⊢ : ⟦ Γ ⟧ ⊢ a → Tm Γ a
from-⊢ = substTm [ cₜ[ _ ] ]ₛ

from-⊢-pres-≈ : {t' u' : ⟦ Γ ⟧ ⊢ a} → t' ≈ u' → from-⊢ t' ≈ from-⊢ u'
from-⊢-pres-≈ = substTm-pres-≈-right _
