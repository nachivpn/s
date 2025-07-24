{-# OPTIONS --safe --without-K #-}
module Everything where

-- Basics for all calculi (Sections 2 and 3 in the paper)
import Type
import Context
import Substitution

-- Calculus for strong functors (λSL in the paper)
import SFC.Term
import SFC.Term.Conversion
import SFC.Term.NormalForm

-- Calculus for pointed functors (λRL in the paper)
import PFC.Term
import PFC.Term.Conversion
import PFC.Term.NormalForm

-- Calculus for joinable functors (λJL in the paper)
import JFC.Type {- temporarily -}
import JFC.Term
import JFC.Term.Conversion
import JFC.Term.NormalForm
import JFC.Term.Model {- Completeness half of Proposition 4 (again below) -}

-- Calculus for monads (λLL in the paper)
import MLC.Term
import MLC.Term.Conversion
import MLC.Term.NormalForm

-- Definition of categorical structures (Appendix of the paper)
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
-- Contains proofs of soundness half of Propositions 3-5
import SFC.Evaluation
import PFC.Evaluation
import JFC.Evaluation
import MLC.Evaluation

-- Intuitionistic possible-world frames
import Semantics.Kripke.Frame

-- Presheaf category determined by possible-world frames
-- Contains proofs of:
-- * Propositions 7-9
-- * Proposition 14
-- * Theorem 10 (implicitly, but used explicitly in *.Norm.Base)
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
-- Contains proofs of:
-- * Completeness half of Propositions 3-5 (implicitly)
-- * Theorem 11 (under *.Norm.Soundness)
import SFC.Norm
import PFC.Norm
import JFC.Norm
import MLC.Norm

