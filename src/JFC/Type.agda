{-# OPTIONS --safe --without-K #-}
module JFC.Type where

infixr 7 _⇒_ _×_

data Ty : Set where
  ι 𝟙     : Ty
  _×_ _⇒_ : (a : Ty) → (b : Ty) → Ty
  ◇_      : (a : Ty) → Ty

variable
  a b c d : Ty
