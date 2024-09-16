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

-- Calculus for pointed functors
import PFC.Term
import PFC.Term.Conversion
import PFC.Term.NormalForm

-- Calculus for joinable functors
import JFC.Type {- temporarily -}
import JFC.Term
import JFC.Term.Conversion
import JFC.Term.NormalForm
import JFC.Term.Model

-- Calculus for monads
import MLC.Term
import MLC.Term.Conversion
import MLC.Term.NormalForm

-- Definition of categorical structures
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
import SFC.Evaluation
import PFC.Evaluation
import JFC.Evaluation
import MLC.Evaluation

-- Intuitionistic possible-world frames
import Semantics.Kripke.Frame

-- Presheaf category determined by possible-world frames
import Semantics.Presheaf.Base
import Semantics.Presheaf.CartesianClosure
import Semantics.Presheaf.Lax
import Semantics.Presheaf.Possibility.Base
import Semantics.Presheaf.Possibility.Pointed
import Semantics.Presheaf.Possibility.Multiplicative.Magma
import Semantics.Presheaf.Possibility.Multiplicative.Semigroup
import Semantics.Presheaf.Possibility.Multiplicative
import Semantics.Presheaf.Possibility.Monad
import Semantics.Presheaf.Possibility.Strong.Base
import Semantics.Presheaf.Possibility.Strong.Pointed
import Semantics.Presheaf.Possibility.Strong.Multiplicative
import Semantics.Presheaf.Possibility.Strong.Monad

-- Normalization algorithms
import SFC.Norm
import PFC.Norm
import JFC.Norm.Base
import MLC.Norm

