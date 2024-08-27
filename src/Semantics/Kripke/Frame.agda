{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

module Semantics.Kripke.Frame where

-- Intuitionistic Frame
record IFrame (W : Set) (_⊆_ : W → W → Set) : Set where
  field
    ⊆-trans            : ∀ {w w' w'' : W} → (i : w ⊆ w') → (i' : w' ⊆ w'') → w ⊆ w''
    ⊆-trans-assoc      : ∀ {w w' w'' w''' : W} (i : w ⊆ w') (i' : w' ⊆ w'') (i'' : w'' ⊆ w''') → ⊆-trans (⊆-trans i i') i'' ≡ ⊆-trans i (⊆-trans i' i'')
    ⊆-refl             : ∀ {w : W} → w ⊆ w
    ⊆-refl-unit-right  : ∀ {w w' : W} (i : w ⊆ w') → ⊆-trans ⊆-refl i ≡ i
    ⊆-refl-unit-left   : ∀ {w w' : W} (i : w ⊆ w') → ⊆-trans i ⊆-refl ≡ i

record MFrame {W : Set} {_⊆_ : W → W → Set} (IF : IFrame W _⊆_) (_R_ : W → W → Set) : Set where

  open IFrame IF public

  --
  -- Factorisation conditions
  --
  
  field
      factor : {w w' v : W} → w ⊆ w' → w R v → ∃ λ v' → w' R v' × v ⊆ v'

  factorW : {w w' v : W} → (i : w ⊆ w') (r : w R v) → W       ; factorW  w r = factor w r .fst
  factorR : {w w' v : W} → (i : w ⊆ w') (r : w R v) → w' R _  ; factorR  w r = factor w r .snd .fst
  factor⊆ : {w w' v : W} → (i : w ⊆ w') (r : w R v) → v ⊆ _   ; factor⊆ w r = factor w r .snd .snd

  field
    factor-pres-⊆-refl  : {w v : W}
      → (m : w R v) → factor ⊆-refl m ≡ (v , m , ⊆-refl)
    factor-pres-⊆-trans : {w w' w'' v : W} → (i : w ⊆ w') (i' : w' ⊆ w'') (m : w R v)
      → factor (⊆-trans i i') m ≡ (-, (factorR i' (factorR i m) , (⊆-trans (factor⊆ i m) (factor⊆ i' (factorR i m)))))  

-- Inclusive, reflexive and transitive factorising frames
module _ {W : Set} {_⊆_ : W → W → Set} {_R_ : W → W → Set} {IF : IFrame W _⊆_} (MF : MFrame IF _R_) where

  open MFrame MF

  record InclusiveMFrame : Set where
    field
      R-to-⊆             : {w v : W} → w R v → w ⊆ v
      factor-pres-R-to-⊆ : {w w' v : W} → (i : w ⊆ w') → (m : w R v) → (⊆-trans i (R-to-⊆ (factorR i m))) ≡ ⊆-trans (R-to-⊆ m) (factor⊆ i m)

  record ReflexiveMFrame : Set where    
    field
      R-refl             : {w : W} → w R w
      factor-pres-R-refl : {w w' : W} (i : w ⊆ w') → factor i R-refl ≡ (w' , R-refl , i)

    R-refl[_] : (w : W) → w R w ; R-refl[ w ] = R-refl {w}
    
  record TransitiveMFrame : Set where
    field
      R-trans             : {w w' w'' : W} → w R w' → w' R w'' → w R w''
      factor-pres-R-trans : {w w' u v : W} (i : w ⊆ w') (m : w R v) (m' : v R u)
        → factor i (R-trans m m') ≡ ((-, ((R-trans (factorR i m) (factorR (factor⊆ i m) m')) , factor⊆ (factor⊆ i m) m')))
      R-trans-assoc : {v0 v1 v2 v3 : W} → (r : v0 R v1) (r' : v1 R v2) (r'' : v2 R v3) → R-trans (R-trans r r') r'' ≡ R-trans r (R-trans r' r'')

  record InclusiveReflexiveMFrame (IMF : InclusiveMFrame) (RMF : ReflexiveMFrame) : Set where
    open InclusiveMFrame IMF
    open ReflexiveMFrame RMF
    
    field
      R-to-⊆-pres-refl  : {w : W} → R-to-⊆ R-refl[ w ] ≡ ⊆-refl

  record InclusiveTransitiveMFrame (IMF : InclusiveMFrame) (TMF : TransitiveMFrame) : Set where
    open InclusiveMFrame IMF
    open TransitiveMFrame TMF
    
    field
      R-to-⊆-pres-trans : ∀ {w v u} → (r : w R v) →  (r' : v R u) → R-to-⊆ (R-trans r r') ≡ ⊆-trans (R-to-⊆ r) (R-to-⊆ r')

  record ReflexiveTransitiveMFrame (RMF : ReflexiveMFrame) (TMF : TransitiveMFrame) : Set where
    open ReflexiveMFrame RMF
    open TransitiveMFrame TMF
    
    field
      R-refl-unit-left  : {w v : W} (r : w R v) → R-trans r R-refl ≡ r
      R-refl-unit-right : {w v : W} (r : w R v) → R-trans R-refl r ≡ r
