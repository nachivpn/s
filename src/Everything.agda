{-# OPTIONS --safe --without-K #-}
module Everything where

-- Basics for all calculi
import Type
import Context
import Substitution

-- Calculus for strong functors
import SFC.Term
import SFC.Term.Conversion
import SFC.Term.NormalForm

-- Calculus for monads
import MLC.Term
import MLC.Term.Conversion
import MLC.Term.NormalForm

-- Definition of categorical structures which could be replaced by `agda-categories`
import Semantics.Category.Base
import Semantics.Category.Cartesian
import Semantics.Category.CartesianClosed
import Semantics.Category.EndoFunctor.Base
import Semantics.Category.EndoFunctor.Pointed
import Semantics.Category.EndoFunctor.Multiplicative
import Semantics.Category.EndoFunctor.Monad
import Semantics.Category.EndoFunctor.Strong.Base
import Semantics.Category.EndoFunctor.Strong.Pointed
import Semantics.Category.EndoFunctor.Strong.Multiplicative
import Semantics.Category.EndoFunctor.Strong.Monad

-- Categorical semantics for the calculi
import Semantics.Category.Evaluation.SFC.Base
import Semantics.Category.Evaluation.SFC.Properties

-- Intuitionistic possible-world frames
import Semantics.Kripke.Frame

-- Presheaf category determined by possible-world frames
import Semantics.Presheaf.Base
import Semantics.Presheaf.CartesianClosure
import Semantics.Presheaf.Possibility
import Semantics.Presheaf.Lax
import Semantics.Presheaf.Pointed
import Semantics.Presheaf.Multiplicative.Magma
import Semantics.Presheaf.Multiplicative.Semigroup
import Semantics.Presheaf.Multiplicative
import Semantics.Presheaf.Monad
import Semantics.Presheaf.Strong
import Semantics.Presheaf.Strong.Pointed
import Semantics.Presheaf.Strong.Multiplicative
import Semantics.Presheaf.Strong.Monad

-- Normalization algorithms
import SFC.Norm
