{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

module Semantics.Kripke.IFrame where

-- Intuitionistic Frame
record IFrame (W : Set) (_⊆_ : W → W → Set) : Set where
  field
    ⊆-trans            : ∀ {w w' w'' : W} → (i : w ⊆ w') → (i' : w' ⊆ w'') → w ⊆ w''
    ⊆-trans-assoc      : ∀ {w w' w'' w''' : W} (i : w ⊆ w') (i' : w' ⊆ w'') (i'' : w'' ⊆ w''') → ⊆-trans (⊆-trans i i') i'' ≡ ⊆-trans i (⊆-trans i' i'')
    ⊆-refl             : ∀ {w : W} → w ⊆ w
    ⊆-refl-unit-right  : ∀ {w w' : W} (i : w ⊆ w') → ⊆-trans ⊆-refl i ≡ i
    ⊆-refl-unit-left   : ∀ {w w' : W} (i : w ⊆ w') → ⊆-trans i ⊆-refl ≡ i

-- Modal frame
record MFrame {W : Set} {_⊆_ : W → W → Set} (_R_ : W → W → Set) : Set where
  -- no extra structure needed

-- Factorising Modal frames
record FMFrame {W : Set} {_⊆_ : W → W → Set} (_R_ : W → W → Set) (IF : IFrame W _⊆_) : Set where
  open IFrame IF
  
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

-- Reflexive and transitive factorising frames
module _ {W : Set} {_⊆_ : W → W → Set} {_R_ : W → W → Set} {IF : IFrame W _⊆_} (FF : FMFrame _R_ IF) where

  record ReflexiveFMFrame (R-refl : {w : W} → w R w) : Set where
    open FMFrame FF
    
    field
      factor-pres-R-refl : {w w' : W} (i : w ⊆ w') → factor i R-refl ≡ (w' , R-refl , i)

  record TransitiveFMFrame (R-trans : {w w' w'' : W} → w R w' → w' R w'' → w R w'') : Set where
    open FMFrame FF
    
    field
      factor-pres-R-trans : {w w' u v : W} (i : w ⊆ w') (m : w R v) (m' : v R u)
        → factor i (R-trans m m') ≡ ((-, ((R-trans (factorR i m) (factorR (factor⊆ i m) m')) , factor⊆ (factor⊆ i m) m'))) 
