{-# OPTIONS --safe --without-K #-}
module Everything where

import Type
import Context
import Substitution

-- Calculus for strong fucntors
import Functor.Term
import Functor.Term.Reduction
import Functor.Term.NormalForm

-- Definition of categorical structures which should be replaced by `agda-categories`
import Semantics.Category.Base
import Semantics.Category.Cartesian
import Semantics.Category.CartesianClosed
import Semantics.Category.EndoFunctor
import Semantics.Category.StrongFunctor

-- Categorical semantics for the calculi
import Semantics.Category.Evaluation.Functor.Base
import Semantics.Category.Evaluation.Functor.Properties

-- Intuitionistic Kripke frames
import Semantics.Kripke.IFrame

-- Presheaf category determined by possible-world frames
import Semantics.Presheaf.Base
import Semantics.Presheaf.CartesianClosure
import Semantics.Presheaf.LaxLax
import Semantics.Presheaf.Strong
import Semantics.Presheaf.Pointed
import Semantics.Presheaf.StrongPointed
import Semantics.Presheaf.Multiplicative.Magma
import Semantics.Presheaf.Multiplicative.Semigroup
import Semantics.Presheaf.Multiplicative
import Semantics.Presheaf.StrongMultiplicative
import Semantics.Presheaf.Monad
import Semantics.Presheaf.StrongMonad
