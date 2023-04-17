open import Semantics.Kripke.Frame using (IFrame ; FMFrame)

module Semantics.Presheaf.Possibility
  (C    : Set)
  (_⊆_  : (Γ Δ : C) → Set)
  (_R_  : (Γ Δ : C) → Set)
  (IF   : IFrame C _⊆_)
  (let open IFrame IF)
  (FMF  : FMFrame _R_ IF)
  (let open FMFrame FMF)
  where

open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import Semantics.Presheaf.Base C _⊆_ IF
open import Semantics.Presheaf.LaxLax C _⊆_ _R_ IF

open import Semantics.Category.EndoFunctor

private
  variable
    w w' w'' v : C
    
◇'_ : (𝒫 : Psh) → Psh 
◇' 𝒫 = record
         { Fam           = ◇'-Fam 𝒫
         ; _≋_           = _◇'-≋_
         ; ≋-equiv       = λ _ → ◇'-≋-equiv
         ; wk            = wk-◇'
         ; wk-pres-≋     = wk-◇'-pres-≋
         ; wk-pres-refl  = wk-◇'-pres-refl
         ; wk-pres-trans = wk-◇'-pres-trans
         }
   where

   wk-◇' : w ⊆ w' → ◇'-Fam 𝒫 w → ◇'-Fam 𝒫 w'
   wk-◇' i (elem (v , r , p)) = elem (factorW i r , (factorR i r) , wk[ 𝒫 ] (factor⊆ i r) p) 

   wk-◇'-pres-≋ : (i : w ⊆ w') {x y : ◇'-Fam 𝒫 w} → x ◇'-≋ y → wk-◇' i x ◇'-≋ wk-◇' i y
   wk-◇'-pres-≋ i {x = elem (v , r , p)} (proof (≡-refl , ≡-refl , p≋p')) = proof (≡-refl , ≡-refl , (wk[ 𝒫 ]-pres-≋ (factor⊆ i r) p≋p'))
   
   wk-◇'-pres-refl : (x : ◇'-Fam 𝒫 w) → wk-◇' ⊆-refl x ◇'-≋ x
   wk-◇'-pres-refl (elem (v , r , p)) rewrite factor-pres-⊆-refl r = proof (≡-refl , (≡-refl , (wk[ 𝒫 ]-pres-refl p)))

   wk-◇'-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (x : ◇'-Fam 𝒫 w)
     → wk-◇' (⊆-trans i i') x ◇'-≋ wk-◇' i' (wk-◇' i x)
   wk-◇'-pres-trans i i' (elem (v , r , p)) rewrite factor-pres-⊆-trans i i' r = proof (≡-refl , (≡-refl , wk[ 𝒫 ]-pres-trans (factor⊆ i r) (factor⊆ i' (factorR i r)) p))

◇'-map_ : {𝒫 𝒬 : Psh} → (t : 𝒫 →̇ 𝒬) → (◇' 𝒫 →̇ ◇' 𝒬)
◇'-map_ {𝒫} {𝒬} t = record
  { fun     = ◇'-map-fun t
  ; pres-≋  = ◇'-map-fun-pres-≋ t
  ; natural = ◇'-map-natural }
  where
  ◇'-map-natural : (i : w ⊆ v) (p : (◇' 𝒫) ₀ w)
    → wk[ ◇' 𝒬 ] i (◇'-map-fun t p) ≋[ ◇' 𝒬 ] ◇'-map-fun t (wk[ ◇' 𝒫 ] i p)
  ◇'-map-natural w (elem (v , r , p)) = proof (≡-refl , (≡-refl , t .natural (factor⊆ w r) p))

abstract
  ◇'-map-pres-≈̇ : {𝒫 𝒬 : Psh} {t t' : 𝒫 →̇ 𝒬} → t ≈̇ t' → ◇'-map t ≈̇ ◇'-map t'
  ◇'-map-pres-≈̇ t≈̇t' = record { proof = λ p → ◇'-map-fun-pres-≈̇ t≈̇t' p }

  ◇'-map-pres-id : {𝒫 : Psh} → ◇'-map id'[ 𝒫 ] ≈̇ id'
  ◇'-map-pres-id = record { proof = λ p → ◇'-≋-refl }

  ◇'-map-pres-∘ : {𝒫 𝒬 ℛ : Psh} (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ◇'-map (t' ∘ t) ≈̇ ◇'-map t' ∘ ◇'-map t
  ◇'-map-pres-∘ _t' _t = record { proof = λ p → ◇'-≋-refl }

◇'-is-PshFunctor : EndoFunctor PshCat
◇'-is-PshFunctor = record
               { ◯'_ = ◇'_
               ; ◯'-map_ = ◇'-map_
               ; ◯'-map-pres-≈̇ = ◇'-map-pres-≈̇
               ; ◯'-map-pres-id = ◇'-map-pres-id
               ; ◯'-map-pres-∘ = ◇'-map-pres-∘
               }


-- Wraps ◯' with naturality
record ◯̇'-Fam (𝒫 : Psh) (w : C) : Set where
  constructor elem
  field
      fun     : ◯'-Fam 𝒫 w
      natural : (i : w ⊆ w') (i' : w' ⊆ w'')
        → wk[ ◇' 𝒫 ] i' (fun .apply-◯ i) ≋[ ◇' 𝒫 ] (wk[ ◯' 𝒫 ] i fun) .apply-◯ i'

open ◯̇'-Fam renaming (fun to unwrap) public

record _◯̇'-≋_ {𝒫 : Psh} {w : C} (f f' : ◯̇'-Fam 𝒫 w) : Set where
    constructor proof
    field
      pw : (f .unwrap) ≋[ ◯' 𝒫 ] (f' .unwrap)

open _◯̇'-≋_ using (pw) public

◯̇'_ : (𝒫 : Psh) → Psh
◯̇' 𝒫 = record
         { Fam           = ◯̇'-Fam 𝒫
         ; _≋_           = _◯̇'-≋_
         ; ≋-equiv       = λ _ → ◯̇'-≋-equiv
         ; wk            = wk
         ; wk-pres-≋     = wk-pres-≋
         ; wk-pres-refl  = wk-pres-refl
         ; wk-pres-trans = wk-pres-trans
         } 
    where

      ◯̇'-≋-equiv : IsEquivalence (_◯̇'-≋_ {𝒫} {w})
      ◯̇'-≋-equiv = record
        { refl  = proof ◯'-≋-refl
        ; sym   = λ f≋f' → proof (◯'-≋-sym (f≋f' .pw))
        ; trans = λ f≋f' f'≋f'' → proof (◯'-≋-trans (f≋f' .pw) (f'≋f'' .pw)) }

      wk : w ⊆ w' → ◯̇'-Fam 𝒫 w → ◯̇'-Fam 𝒫 w'
      wk {w' = w'} i f = record
        { fun     = wk[ ◯' 𝒫 ] i (f .unwrap)
        ; natural = λ i' i'' → let open EqReasoning ≋[ ◇' 𝒫 ]-setoid in begin
          wk[ ◇' 𝒫 ] i'' (wk[ ◯' 𝒫 ] i (f .unwrap) .apply-◯ i')
            ≈⟨ f .natural (⊆-trans i i') i'' ⟩
          (wk[ ◯' 𝒫 ] (⊆-trans i i') (f .unwrap)) .apply-◯ i''
            ≡⟨⟩
          f .unwrap .apply-◯ (⊆-trans (⊆-trans i i') i'')
            ≡⟨ cong (f .unwrap .apply-◯) (⊆-trans-assoc i i' i'') ⟩
          f .unwrap .apply-◯ (⊆-trans i (⊆-trans i' i''))
            ≡⟨⟩
          wk[ ◯' 𝒫 ] i' (wk[ ◯' 𝒫 ] i (f .unwrap)) .apply-◯ i'' ∎
        }
        
      wk-pres-≋ : (i : w ⊆ w') {f f' : ◯̇'-Fam 𝒫 w} (f≋f' : f ◯̇'-≋ f') → wk i f ◯̇'-≋ wk i f'
      wk-pres-≋ i f≋f' = proof (wk[ ◯' 𝒫 ]-pres-≋ i (f≋f' .pw))

      wk-pres-refl : (f : ◯̇'-Fam 𝒫 w) → wk ⊆-refl f ◯̇'-≋ f
      wk-pres-refl f = proof (wk[ ◯' 𝒫 ]-pres-refl (f .unwrap))

      wk-pres-trans : (i : w ⊆ w') (i' : w' ⊆ w'') (f : ◯̇'-Fam 𝒫 w) → wk (⊆-trans i i') f ◯̇'-≋ wk i' (wk i f)
      wk-pres-trans i i' f = proof (wk[ ◯' 𝒫 ]-pres-trans i i' (f .unwrap))

-- ◯̇' and ◇' are naturally isomorphic
module ◯̇'≅◇' {𝒫 : Psh} where

  -- forget the naturality condition wrapped by ◯̇'
  unwrap-nat : ◯̇' 𝒫 →̇ ◯' 𝒫
  unwrap-nat = record
    { fun     = unwrap
    ; pres-≋  = pw
    ; natural = λ w p → ◯'-≋-refl }
    
  ◯̇'≅◇'-forth : ◯̇' 𝒫 →̇ ◇' 𝒫
  ◯̇'≅◇'-forth = record
    { fun     = λ ◯p → ◯p .unwrap .apply-◯ ⊆-refl
    ; pres-≋  = λ ◯p≋◯p' → ◯p≋◯p' .pw .pw ⊆-refl
    ; natural = λ w p → let open EqReasoning ≋[ ◇' 𝒫 ]-setoid in
      begin
      wk[ ◇' 𝒫 ] w (p .unwrap .apply-◯ ⊆-refl)
        ≈⟨ p .natural ⊆-refl w ⟩
      p .unwrap .apply-◯ (⊆-trans ⊆-refl w)
        ≡⟨ cong (p .unwrap .apply-◯) (≡-trans (⊆-refl-unit-right _) (≡-sym (⊆-refl-unit-left _))) ⟩
      p .unwrap .apply-◯ (⊆-trans w ⊆-refl)
        ≡⟨⟩
      wk[ ◯̇' 𝒫 ] w p .unwrap .apply-◯ ⊆-refl ∎ }
  
  ◯̇'≅◇'-back : ◇' 𝒫 →̇ ◯̇' 𝒫
  ◯̇'≅◇'-back = record
    { fun     = λ ◇p → record
      { fun     = elem (λ w → wk[ ◇' 𝒫 ] w ◇p)
      ; natural = λ i i' → ≋[ ◇' 𝒫 ]-sym (wk[ ◇' 𝒫 ]-pres-trans i i' ◇p) }
    ; pres-≋  = λ ◇p≋◇p' → proof (proof (λ w → wk[ ◇' 𝒫 ]-pres-≋ w ◇p≋◇p')) 
    ; natural = λ w ◇p → proof (proof (λ w' → wk[ ◇' 𝒫 ]-pres-trans w w' ◇p)) }

  ◯'≅◇'-back-left-inverse : ◯̇'≅◇'-back ∘ ◯̇'≅◇'-forth ≈̇ id'[ ◯̇' 𝒫 ]
  ◯'≅◇'-back-left-inverse = record { proof = λ p → proof (proof λ w → let open EqReasoning ≋[ ◇' 𝒫 ]-setoid 
    in begin
      wk[ ◇' 𝒫 ] w (p .unwrap .apply-◯ ⊆-refl)
        ≈⟨ ◯̇'≅◇'-forth .natural w p ⟩
      p .unwrap .apply-◯ (⊆-trans w ⊆-refl)
        ≡⟨ cong (p .unwrap .apply-◯) (⊆-refl-unit-left w) ⟩
      p .unwrap .apply-◯ w ∎
    )}

  ◯'≅◇'-back-right-inverse : ◯̇'≅◇'-forth ∘ ◯̇'≅◇'-back ≈̇ id'[ ◇' 𝒫 ]
  ◯'≅◇'-back-right-inverse = record { proof = wk[ ◇' 𝒫 ]-pres-refl }

