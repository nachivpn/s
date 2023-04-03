{-# OPTIONS --safe --without-K #-}
module Everything where

import Type
import Context
import Substitution

import Functor.Term
import Functor.Term.Reduction
import Functor.Term.NormalForm

import Semantics.Category.Base
import Semantics.Category.Cartesian
import Semantics.Category.CartesianClosed
import Semantics.Category.EndoFunctor
import Semantics.Category.StrongFunctor

import Semantics.Category.Evaluation.Functor.Base
import Semantics.Category.Evaluation.Functor.Properties

import Semantics.Presheaf.Base
import Semantics.Presheaf.CartesianClosure
import Semantics.Presheaf.LaxLax
import Semantics.Presheaf.Strong
