{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Semantics.Kripke.Frame using (MFrame ; ReflexiveMFrame)

module Semantics.Presheaf.Pointed
  {C      : Set}
  {_⊆_    : (Γ Δ : C) → Set}
  {_R_    : (Γ Δ : C) → Set}
  (MF     : MFrame C _⊆_ _R_)
  (RMF    : ReflexiveMFrame MF)
  (let open MFrame MF)
  (let open ReflexiveMFrame RMF)
  where

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base IF
open import Semantics.Presheaf.Possibility MF

private
  variable
    Γ Γ' Γ'' : C
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh

point'[_] : ∀ 𝒫 → 𝒫 →̇ ◇' 𝒫
point'[ 𝒫 ] = record
  { fun     = ◇'-point'-fun
  ; pres-≋  = ◇'-point'-fun-pres-≋
  ; natural = ◇'-point'-fun-natural
  }
  where
  
  ◇'-point'-fun : 𝒫 ₀ Γ → ◇'-Fam 𝒫 Γ
  ◇'-point'-fun x = elem (_ , (R-refl , x))

  abstract
    ◇'-point'-fun-pres-≋ : {x y : 𝒫 ₀ Γ} → x ≋[ 𝒫 ] y → ◇'-point'-fun x ◇'-≋ ◇'-point'-fun y
    ◇'-point'-fun-pres-≋ x≋y = proof (refl , refl , x≋y)

    ◇'-point'-fun-natural : (w : Γ ⊆ Γ') (p : 𝒫 ₀ Γ)
      → wk[ ◇' 𝒫 ] w (◇'-point'-fun p) ≋[ ◇' 𝒫 ] ◇'-point'-fun (wk[ 𝒫 ] w p) 
    ◇'-point'-fun-natural w _p rewrite (factor-pres-R-refl w) = proof (refl , refl , ≋[ 𝒫 ]-refl)

abstract
  -- point' is a natural transformation from the identity functor to ◇'
  point'-natural : (t : 𝒫 →̇ 𝒬) → point'[ 𝒬 ] ∘ t ≈̇ ◇'-map t ∘ point'[ 𝒫 ]
  point'-natural {𝒫} {𝒬} t = record { proof = λ _p → ≋[ ◇' 𝒬 ]-refl }

  -- obs: point' need not be well-pointed
  -- point'-well-pointed : (t : 𝒫 →̇ ◇' 𝒬) → ◇'-map point'[ 𝒫 ] ≈̇ point'[ ◇' 𝒫 ]

  -- obs: "The pointed endofunctor underlying a monad T is
  -- well-pointed if and only if T is idempotent."  [Proposition 3.1.,
  -- https://ncatlab.org/nlab/show/pointed+endofunctor]

point' = λ {𝒫} → point'[ 𝒫 ]
