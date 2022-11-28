{-# OPTIONS --without-K #-}
module Everything where

import Type
import Context
import Substitution

import Functor.Term
import Functor.Term.Reduction
import Functor.Term.NormalForm

import Semantics.Category.Evaluation.Functor.Base
import Semantics.Category.Evaluation.Functor.Properties

import Semantics.Presheaf.Base
import Semantics.Presheaf.CartesianClosure
import Semantics.Presheaf.Strong

