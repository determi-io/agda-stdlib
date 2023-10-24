------------------------------------------------------------------------
-- The Agda standard library
--
-- All library modules, along with short descriptions
------------------------------------------------------------------------

-- Note that core modules are not included.

{-# OPTIONS --safe --guardedness #-}

module EverythingSafe where

-- Definitions of algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
import Algebra

-- Algebraic objects with an apartness relation
import Algebra.Apartness

-- Bundles for local algebraic structures
import Algebra.Apartness.Bundles

-- Properties of Heyting Commutative Rings
import Algebra.Apartness.Properties.HeytingCommutativeRing

-- Algebraic structures with an apartness relation
import Algebra.Apartness.Structures

-- Definitions of algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
import Algebra.Bundles

-- Definitions of 'raw' bundles
import Algebra.Bundles.Raw

-- Lemmas relating algebraic definitions (such as associativity and
-- commutativity) that don't require the equality relation to be a setoid.
import Algebra.Consequences.Base

-- Relations between properties of functions, such as associativity and
-- commutativity (specialised to propositional equality)
import Algebra.Consequences.Propositional

-- Relations between properties of functions, such as associativity and
-- commutativity, when the underlying relation is a setoid
import Algebra.Consequences.Setoid

-- Definition of algebraic structures we get from freely adding an
-- identity element
import Algebra.Construct.Add.Identity

-- Instances of algebraic structures made by taking two other instances
-- A and B, and having elements of the new instance be pairs |A| × |B|.
-- In mathematics, this would usually be written A × B or A ⊕ B.
import Algebra.Construct.DirectProduct

-- Flipping the arguments of a binary operation preserves many of its
-- algebraic properties.
import Algebra.Construct.Flip.Op

-- Instances of algebraic structures where the carrier is ⊥.
-- In mathematics, this is usually called 0.
import Algebra.Construct.Initial

-- Definitions of the lexicographic product of two operators.
import Algebra.Construct.LexProduct

-- Definitions of the lexicographic product of two operators.
import Algebra.Construct.LexProduct.Base

-- Properties of the inner lexicographic product of two operators.
import Algebra.Construct.LexProduct.Inner

-- Choosing between elements based on the result of applying a function
import Algebra.Construct.LiftedChoice

-- Basic definition of an operator that computes the min/max value
-- with respect to a total preorder.
import Algebra.Construct.NaturalChoice.Base

-- The max operator derived from an arbitrary total preorder.
import Algebra.Construct.NaturalChoice.Max

-- Properties of a max operator derived from a spec over a total
-- preorder.
import Algebra.Construct.NaturalChoice.MaxOp

-- The min operator derived from an arbitrary total preorder.
import Algebra.Construct.NaturalChoice.Min

-- Properties of min and max operators specified over a total
-- preorder.
import Algebra.Construct.NaturalChoice.MinMaxOp

-- Properties of a min operator derived from a spec over a total
-- preorder.
import Algebra.Construct.NaturalChoice.MinOp

-- Substituting equalities for binary relations
import Algebra.Construct.Subst.Equality

-- Instances of algebraic structures where the carrier is ⊤.
-- In mathematics, this is usually called 0 (1 in the case of Group).
import Algebra.Construct.Terminal

-- Instances of algebraic structures where the carrier is ⊤.
-- In mathematics, this is usually called 0 (1 in the case of Group).
import Algebra.Construct.Zero

-- Properties of functions, such as associativity and commutativity
import Algebra.Definitions

-- Basic auxiliary definitions for magma-like structures
import Algebra.Definitions.RawMagma

-- Basic auxiliary definitions for monoid-like structures
import Algebra.Definitions.RawMonoid

-- Basic auxiliary definitions for semiring-like structures
import Algebra.Definitions.RawSemiring

-- Definitions of algebraic structures like semilattices and lattices
-- (packed in records together with sets, operations, etc.), defined via
-- meet/join operations and their properties
import Algebra.Lattice

-- Definitions of algebraic structures like semilattices and lattices
-- (packed in records together with sets, operations, etc.), defined via
-- meet/join operations and their properties
import Algebra.Lattice.Bundles

-- Definitions of 'raw' bundles
import Algebra.Lattice.Bundles.Raw

-- Instances of algebraic structures made by taking two other instances
-- A and B, and having elements of the new instance be pairs |A| × |B|.
-- In mathematics, this would usually be written A × B or A ⊕ B.
import Algebra.Lattice.Construct.DirectProduct

-- Choosing between elements based on the result of applying a function
import Algebra.Lattice.Construct.LiftedChoice

-- Properties of a max operator derived from a spec over a total
-- preorder.
import Algebra.Lattice.Construct.NaturalChoice.MaxOp

-- Properties of min and max operators specified over a total preorder.
import Algebra.Lattice.Construct.NaturalChoice.MinMaxOp

-- Properties of a min operator derived from a spec over a total
-- preorder.
import Algebra.Lattice.Construct.NaturalChoice.MinOp

-- Substituting equalities for binary relations
import Algebra.Lattice.Construct.Subst.Equality

-- Instances of algebraic lattice structures where the carrier is ⊤.
-- In mathematics, this is usually called 0.
import Algebra.Lattice.Construct.Zero

-- Morphisms between algebraic lattice structures
import Algebra.Lattice.Morphism

-- The composition of morphisms between algebraic lattice structures.
import Algebra.Lattice.Morphism.Construct.Composition

-- The identity morphism for algebraic lattice structures
import Algebra.Lattice.Morphism.Construct.Identity

-- Consequences of a monomorphism between lattice-like structures
import Algebra.Lattice.Morphism.LatticeMonomorphism

-- Morphisms between algebraic lattice structures
import Algebra.Lattice.Morphism.Structures

-- Some derivable properties of Boolean algebras
import Algebra.Lattice.Properties.BooleanAlgebra

-- Boolean algebra expressions
import Algebra.Lattice.Properties.BooleanAlgebra.Expression

-- Some derivable properties
import Algebra.Lattice.Properties.DistributiveLattice

-- Some derivable properties of lattices
import Algebra.Lattice.Properties.Lattice

-- Some derivable properties of semilattices
import Algebra.Lattice.Properties.Semilattice

-- Some lattice-like structures defined by properties of _∧_ and _∨_
-- (not packed up with sets, operations, etc.)
import Algebra.Lattice.Structures

-- Some biased records for lattice-like structures. Such records are
-- often easier to construct, but are suboptimal to use more widely and
-- should be converted to the standard record definitions immediately
-- using the provided conversion functions.
import Algebra.Lattice.Structures.Biased

-- Definitions of algebraic structure module
-- packed in records together with sets, operations, etc.
import Algebra.Module

-- Definitions of algebraic structures defined over some other
-- structure, like modules and vector spaces
import Algebra.Module.Bundles

-- Relations between properties of scaling and other operations
import Algebra.Module.Consequences

-- This module constructs the biproduct of two R-modules, and similar
-- for weaker module-like structures.
-- The intended universal property is that the biproduct is both a
-- product and a coproduct in the category of R-modules.
import Algebra.Module.Construct.DirectProduct

-- This module constructs the unit of the monoidal structure on
-- R-modules, and similar for weaker module-like structures.
-- The intended universal property is that the maps out of the tensor
-- unit into M are isomorphic to the elements of M.
import Algebra.Module.Construct.TensorUnit

-- This module constructs the zero R-module, and similar for weaker
-- module-like structures.
-- The intended universal property is that, given any R-module M, there
-- is a unique map into and a unique map out of the zero R-module
-- from/to M.
import Algebra.Module.Construct.Zero

-- This module collects the property definitions for left-scaling
-- (LeftDefs), right-scaling (RightDefs), and both (BiDefs).
import Algebra.Module.Definitions

-- Properties connecting left-scaling and right-scaling
import Algebra.Module.Definitions.Bi

-- Properties connecting left-scaling and right-scaling over the same scalars
import Algebra.Module.Definitions.Bi.Simultaneous

-- Properties of left-scaling
import Algebra.Module.Definitions.Left

-- Properties of right-scaling
import Algebra.Module.Definitions.Right

-- The composition of morphisms between module-like algebraic structures.
import Algebra.Module.Morphism.Construct.Composition

-- The identity morphism for module-like algebraic structures
import Algebra.Module.Morphism.Construct.Identity

-- Basic definitions for morphisms between module-like algebraic
-- structures
import Algebra.Module.Morphism.Definitions

-- Properties of linear maps.
import Algebra.Module.Morphism.ModuleHomomorphism

-- Morphisms between module-like algebraic structures
import Algebra.Module.Morphism.Structures

-- Properties of modules.
import Algebra.Module.Properties

-- Properties of semimodules.
import Algebra.Module.Properties.Semimodule

-- Some algebraic structures defined over some other structure
import Algebra.Module.Structures

-- This module provides alternative ways of providing instances of
-- structures in the Algebra.Module hierarchy.
import Algebra.Module.Structures.Biased

-- Morphisms between algebraic structures
import Algebra.Morphism

-- Some properties of Magma homomorphisms
import Algebra.Morphism.Consequences

-- The composition of morphisms between algebraic structures.
import Algebra.Morphism.Construct.Composition

-- The identity morphism for algebraic structures
import Algebra.Morphism.Construct.Identity

-- Basic definitions for morphisms between algebraic structures
import Algebra.Morphism.Definitions

-- Consequences of a monomorphism between group-like structures
import Algebra.Morphism.GroupMonomorphism

-- Consequences of a monomorphism between magma-like structures
import Algebra.Morphism.MagmaMonomorphism

-- Consequences of a monomorphism between monoid-like structures
import Algebra.Morphism.MonoidMonomorphism

-- Consequences of a monomorphism between ring-like structures
import Algebra.Morphism.RingMonomorphism

-- Morphisms between algebraic structures
import Algebra.Morphism.Structures

-- Some derivable properties
import Algebra.Properties.AbelianGroup

-- Some properties of operations in CancellativeCommutativeSemiring.
import Algebra.Properties.CancellativeCommutativeSemiring

-- Properties of divisibility over commutative magmas
import Algebra.Properties.CommutativeMagma.Divisibility

-- Some derivable properties
import Algebra.Properties.CommutativeMonoid

-- Multiplication over a monoid (i.e. repeated addition)
import Algebra.Properties.CommutativeMonoid.Mult

-- Multiplication over a monoid (i.e. repeated addition) optimised for
-- type checking.
import Algebra.Properties.CommutativeMonoid.Mult.TCOptimised

-- Finite summations over a commutative monoid
import Algebra.Properties.CommutativeMonoid.Sum

-- Some theory for commutative semigroup
import Algebra.Properties.CommutativeSemigroup

-- Properties of divisibility over commutative semigroups
import Algebra.Properties.CommutativeSemigroup.Divisibility

-- The Binomial Theorem for Commutative Semirings
import Algebra.Properties.CommutativeSemiring.Binomial

-- Exponentiation defined over a commutative semiring as repeated multiplication
import Algebra.Properties.CommutativeSemiring.Exp

-- Exponentiation over a semiring optimised for type-checking.
import Algebra.Properties.CommutativeSemiring.Exp.TCOptimised

-- Some derivable properties
import Algebra.Properties.Group

-- Some derivable properties
import Algebra.Properties.KleeneAlgebra

-- Some basic properties of Quasigroup
import Algebra.Properties.Loop

-- Divisibility over magmas
import Algebra.Properties.Magma.Divisibility

-- Some basic properties of Quasigroup
import Algebra.Properties.MiddleBolLoop

-- Properties of divisibility over monoids
import Algebra.Properties.Monoid.Divisibility

-- Multiplication over a monoid (i.e. repeated addition)
import Algebra.Properties.Monoid.Mult

-- Multiplication over a monoid (i.e. repeated addition) optimised for
-- type checking.
import Algebra.Properties.Monoid.Mult.TCOptimised

-- Finite summations over a monoid
import Algebra.Properties.Monoid.Sum

-- Some derivable properties
import Algebra.Properties.MoufangLoop

-- Some basic properties of Quasigroup
import Algebra.Properties.Quasigroup

-- Some basic properties of Rings
import Algebra.Properties.Ring

-- Some basic properties of RingWithoutOne
import Algebra.Properties.RingWithoutOne

-- Some theory for Semigroup
import Algebra.Properties.Semigroup

-- Properties of divisibility over semigroups
import Algebra.Properties.Semigroup.Divisibility

-- The Binomial Theorem for *-commuting elements in a Semiring
import Algebra.Properties.Semiring.Binomial

-- Properties of divisibility over semirings
import Algebra.Properties.Semiring.Divisibility

-- Exponentiation defined over a semiring as repeated multiplication
import Algebra.Properties.Semiring.Exp

-- Exponentiation over a semiring optimised for type-checking.
import Algebra.Properties.Semiring.Exp.TCOptimised

-- Exponentiation over a semiring optimised for tail-recursion.
import Algebra.Properties.Semiring.Exp.TailRecursiveOptimised

-- Multiplication by a natural number over a semiring
import Algebra.Properties.Semiring.Mult

-- Multiplication over a semiring optimised for type-checking.
import Algebra.Properties.Semiring.Mult.TCOptimised

-- Some theory for CancellativeCommutativeSemiring.
import Algebra.Properties.Semiring.Primality

-- Finite summations over a semiring
import Algebra.Properties.Semiring.Sum

-- Solver for equations in commutative monoids
import Algebra.Solver.CommutativeMonoid

-- An example of how Algebra.CommutativeMonoidSolver can be used
import Algebra.Solver.CommutativeMonoid.Example

-- Solver for equations in idempotent commutative monoids
import Algebra.Solver.IdempotentCommutativeMonoid

-- An example of how Algebra.IdempotentCommutativeMonoidSolver can be
-- used
import Algebra.Solver.IdempotentCommutativeMonoid.Example

-- A solver for equations over monoids
import Algebra.Solver.Monoid

-- Old solver for commutative ring or semiring equalities
import Algebra.Solver.Ring

-- Commutative semirings with some additional structure ("almost"
-- commutative rings), used by the ring solver
import Algebra.Solver.Ring.AlmostCommutativeRing

-- Some boring lemmas used by the ring solver
import Algebra.Solver.Ring.Lemmas

-- Instantiates the ring solver, using the natural numbers as the
-- coefficient "ring"
import Algebra.Solver.Ring.NaturalCoefficients

-- Instantiates the natural coefficients ring solver, using coefficient
-- equality induced by ℕ.
import Algebra.Solver.Ring.NaturalCoefficients.Default

-- Instantiates the ring solver with two copies of the same ring with
-- decidable equality
import Algebra.Solver.Ring.Simple

-- Some algebraic structures (not packed up with sets, operations, etc.)
import Algebra.Structures

-- Ways to give instances of certain structures where some fields can
-- be given in terms of others
import Algebra.Structures.Biased

-- Results concerning double negation elimination.
import Axiom.DoubleNegationElimination

-- Results concerning the excluded middle axiom.
import Axiom.ExcludedMiddle

-- Results concerning function extensionality for propositional equality
import Axiom.Extensionality.Heterogeneous

-- Results concerning function extensionality for propositional equality
import Axiom.Extensionality.Propositional

-- Results concerning uniqueness of identity proofs
import Axiom.UniquenessOfIdentityProofs

-- Results concerning uniqueness of identity proofs, with axiom K
import Axiom.UniquenessOfIdentityProofs.WithK

-- M-types (the dual of W-types)
import Codata.Guarded.M

-- Infinite streams defined as coinductive records
import Codata.Guarded.Stream

-- Properties of infinite streams defined as coinductive records
import Codata.Guarded.Stream.Properties

-- Coinductive pointwise lifting of relations to streams
import Codata.Guarded.Stream.Relation.Binary.Pointwise

-- Streams where all elements satisfy a given property
import Codata.Guarded.Stream.Relation.Unary.All

-- Streams where at least one element satisfies a given property
import Codata.Guarded.Stream.Relation.Unary.Any

-- "Finite" sets indexed on coinductive "natural" numbers
import Codata.Musical.Cofin

-- Coinductive "natural" numbers
import Codata.Musical.Conat

-- Coinductive "natural" numbers: base type and operations
import Codata.Musical.Conat.Base

-- M-types (the dual of W-types)
import Codata.Musical.M

-- Indexed M-types (the dual of indexed W-types aka Petersson-Synek
-- trees).
import Codata.Musical.M.Indexed

-- Basic types related to coinduction
import Codata.Musical.Notation

-- Booleans
import Data.Bool

-- The type for booleans and some operations
import Data.Bool.Base

-- Instances for booleans
import Data.Bool.Instances

-- A bunch of properties
import Data.Bool.Properties

-- Showing booleans
import Data.Bool.Show

-- Automatic solvers for equations over booleans
import Data.Bool.Solver

-- Characters
import Data.Char

-- Basic definitions for Characters
import Data.Char.Base

-- Instances for characters
import Data.Char.Instances

-- Properties of operations on characters
import Data.Char.Properties

-- Containers, based on the work of Abbott and others
import Data.Container

-- Container combinators
import Data.Container.Combinator

-- Correctness proofs for container combinators
import Data.Container.Combinator.Properties

-- Fixpoints for containers - using guardedness
import Data.Container.Fixpoints.Guarded

-- The free monad construction on containers
import Data.Container.FreeMonad

-- Indexed containers aka interaction structures aka polynomial
-- functors. The notation and presentation here is closest to that of
-- Hancock and Hyvernat in "Programming interfaces and basic topology"
-- (2006/9).
import Data.Container.Indexed

-- Indexed container combinators
import Data.Container.Indexed.Combinator

-- Greatest fixpoint for indexed containers - using guardedness
import Data.Container.Indexed.Fixpoints.Guarded

-- The free monad construction on indexed containers
import Data.Container.Indexed.FreeMonad

-- Some code related to indexed containers that uses heterogeneous
-- equality
import Data.Container.Indexed.WithK

-- Membership for containers
import Data.Container.Membership

-- Container Morphisms
import Data.Container.Morphism

-- Propertiers of any for containers
import Data.Container.Morphism.Properties

-- Properties of operations on containers
import Data.Container.Properties

-- Several kinds of "relatedness" for containers such as equivalences,
-- surjections and bijections
import Data.Container.Related

-- Equality over container extensions parametrised by some setoid
import Data.Container.Relation.Binary.Equality.Setoid

-- Pointwise equality for containers
import Data.Container.Relation.Binary.Pointwise

-- Properties of pointwise equality for containers
import Data.Container.Relation.Binary.Pointwise.Properties

-- All (□) for containers
import Data.Container.Relation.Unary.All

-- Any (◇) for containers
import Data.Container.Relation.Unary.Any

-- Propertiers of any for containers
import Data.Container.Relation.Unary.Any.Properties

-- A way to specify that a function's argument takes a default value
-- if the argument is not passed explicitly.
import Data.Default

-- Lists with fast append
import Data.DifferenceList

-- Natural numbers with fast addition (for use together with
-- DifferenceVec)
import Data.DifferenceNat

-- Vectors with fast append
import Data.DifferenceVec

-- Digits and digit expansions
import Data.Digit

-- Properties of digits and digit expansions
import Data.Digit.Properties

-- Empty type, judgementally proof irrelevant
import Data.Empty

-- An irrelevant version of ⊥-elim
import Data.Empty.Irrelevant

-- Level polymorphic Empty type
import Data.Empty.Polymorphic

-- Finite sets
import Data.Fin

-- Finite sets
import Data.Fin.Base

-- Induction over Fin
import Data.Fin.Induction

-- Instances for finite sets
import Data.Fin.Instances

-- Fin Literals
import Data.Fin.Literals

-- Patterns for Fin
import Data.Fin.Patterns

-- Bijections on finite sets (i.e. permutations).
import Data.Fin.Permutation

-- Component functions of permutations found in `Data.Fin.Permutation`
import Data.Fin.Permutation.Components

-- Decomposition of permutations into a list of transpositions.
import Data.Fin.Permutation.Transposition.List

-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
import Data.Fin.Properties

-- Reflection utilities for Fin
import Data.Fin.Reflection

-- The 'top' view of Fin.
import Data.Fin.Relation.Unary.Top

-- Showing finite numbers
import Data.Fin.Show

-- Subsets of finite sets
import Data.Fin.Subset

-- Induction over Subset
import Data.Fin.Subset.Induction

-- Some properties about subsets
import Data.Fin.Subset.Properties

-- Substitutions
import Data.Fin.Substitution

-- Substitution lemmas
import Data.Fin.Substitution.Lemmas

-- Application of substitutions to lists, along with various lemmas
import Data.Fin.Substitution.List

-- Floating point numbers
import Data.Float

-- Floats: basic types and operations
import Data.Float.Base

-- Instances for floating point numbers
import Data.Float.Instances

-- Properties of operations on floats
import Data.Float.Properties

-- Directed acyclic multigraphs
import Data.Graph.Acyclic

-- Integers
import Data.Integer

-- Integers, basic types and operations
import Data.Integer.Base

-- Coprimality
import Data.Integer.Coprimality

-- Integer division
import Data.Integer.DivMod

-- Unsigned divisibility
import Data.Integer.Divisibility

-- Alternative definition of divisibility without using modulus.
import Data.Integer.Divisibility.Signed

-- Greatest Common Divisor for integers
import Data.Integer.GCD

-- Instances for integers
import Data.Integer.Instances

-- Least Common Multiple for integers
import Data.Integer.LCM

-- Integer Literals
import Data.Integer.Literals

-- Some properties about integers
import Data.Integer.Properties

-- Showing integers
import Data.Integer.Show

-- Automatic solvers for equations over integers
import Data.Integer.Solver

-- Automatic solvers for equations over integers
import Data.Integer.Tactic.RingSolver

-- Wrapper for the proof irrelevance modality
import Data.Irrelevant

-- Lists
import Data.List

-- Lists, basic types and operations
import Data.List.Base

-- A data structure which keeps track of an upper bound on the number
-- of elements /not/ in a given list
import Data.List.Countdown

-- An effectful view of List
import Data.List.Effectful

-- An effectful view of List
import Data.List.Effectful.Transformer

-- Finding the maximum/minimum values in a list
import Data.List.Extrema

-- Finding the maximum/minimum values in a list, specialised for Nat
import Data.List.Extrema.Nat

-- Fresh lists, a proof relevant variant of Catarina Coquand's contexts
-- in "A Formalised Proof of the Soundness and Completeness of a Simply
-- Typed Lambda-Calculus with Explicit Substitutions"
import Data.List.Fresh

-- Membership predicate for fresh lists
import Data.List.Fresh.Membership.Setoid

-- Properties of the membership predicate for fresh lists
import Data.List.Fresh.Membership.Setoid.Properties

-- A non-empty fresh list
import Data.List.Fresh.NonEmpty

-- Properties of fresh lists and functions acting on them
import Data.List.Fresh.Properties

-- All predicate transformer for fresh lists
import Data.List.Fresh.Relation.Unary.All

-- Properties of All predicate transformer for fresh lists
import Data.List.Fresh.Relation.Unary.All.Properties

-- Any predicate transformer for fresh lists
import Data.List.Fresh.Relation.Unary.Any

-- Properties of Any predicate transformer for fresh lists
import Data.List.Fresh.Relation.Unary.Any.Properties

-- Typeclass instances for List
import Data.List.Instances

-- An alternative definition of mutually-defined lists and non-empty
-- lists, using the Kleene star and plus.
import Data.List.Kleene

-- A different interface to the Kleene lists, designed to mimic
-- Data.List.
import Data.List.Kleene.AsList

-- Lists, based on the Kleene star and plus, basic types and operations.
import Data.List.Kleene.Base

-- List Literals
import Data.List.Literals

-- Decidable propositional membership over lists
import Data.List.Membership.DecPropositional

-- Decidable setoid membership over lists
import Data.List.Membership.DecSetoid

-- Data.List.Any.Membership instantiated with propositional equality,
-- along with some additional definitions.
import Data.List.Membership.Propositional

-- Properties related to propositional list membership
import Data.List.Membership.Propositional.Properties

-- Properties related to propositional list membership, that rely on
-- the K rule
import Data.List.Membership.Propositional.Properties.WithK

-- List membership and some related definitions
import Data.List.Membership.Setoid

-- Properties related to setoid list membership
import Data.List.Membership.Setoid.Properties

-- Nondependent N-ary functions manipulating lists
import Data.List.Nary.NonDependent

-- Non-empty lists
import Data.List.NonEmpty

-- Non-empty lists: base type and operations
import Data.List.NonEmpty.Base

-- An effectful view of List⁺
import Data.List.NonEmpty.Effectful

-- An effectful view of List
import Data.List.NonEmpty.Effectful.Transformer

-- Typeclass instances for List⁺
import Data.List.NonEmpty.Instances

-- Properties of non-empty lists
import Data.List.NonEmpty.Properties

-- Non-empty lists where all elements satisfy a given property
import Data.List.NonEmpty.Relation.Unary.All

-- List-related properties
import Data.List.Properties

-- Reflection utilities for List
import Data.List.Reflection

-- Bag and set equality
import Data.List.Relation.Binary.BagAndSetEquality

-- Pairs of lists that share no common elements (propositional equality)
import Data.List.Relation.Binary.Disjoint.Propositional

-- Pairs of lists that share no common elements (setoid equality)
import Data.List.Relation.Binary.Disjoint.Setoid

-- Properties of disjoint lists (setoid equality)
import Data.List.Relation.Binary.Disjoint.Setoid.Properties

-- Decidable pointwise equality over lists using propositional equality
import Data.List.Relation.Binary.Equality.DecPropositional

-- Pointwise decidable equality over lists parameterised by a setoid
import Data.List.Relation.Binary.Equality.DecSetoid

-- Pointwise equality over lists using propositional equality
import Data.List.Relation.Binary.Equality.Propositional

-- Pointwise equality over lists parameterised by a setoid
import Data.List.Relation.Binary.Equality.Setoid

-- An inductive definition of the heterogeneous infix relation
import Data.List.Relation.Binary.Infix.Heterogeneous

-- Properties of the heterogeneous infix relation
import Data.List.Relation.Binary.Infix.Heterogeneous.Properties

-- Properties of the homogeneous infix relation
import Data.List.Relation.Binary.Infix.Homogeneous.Properties

-- Lexicographic ordering of lists
import Data.List.Relation.Binary.Lex

-- Lexicographic ordering of lists
import Data.List.Relation.Binary.Lex.NonStrict

-- Lexicographic ordering of lists
import Data.List.Relation.Binary.Lex.Strict

-- A definition for the permutation relation using setoid equality
import Data.List.Relation.Binary.Permutation.Homogeneous

-- An inductive definition for the permutation relation
import Data.List.Relation.Binary.Permutation.Propositional

-- Properties of permutation
import Data.List.Relation.Binary.Permutation.Propositional.Properties

-- A definition for the permutation relation using setoid equality
import Data.List.Relation.Binary.Permutation.Setoid

-- Properties of permutations using setoid equality
import Data.List.Relation.Binary.Permutation.Setoid.Properties

-- Pointwise lifting of relations to lists
import Data.List.Relation.Binary.Pointwise

-- Pointwise lifting of relations to lists
import Data.List.Relation.Binary.Pointwise.Base

-- Properties of pointwise lifting of relations to lists
import Data.List.Relation.Binary.Pointwise.Properties

-- An inductive definition of the heterogeneous prefix relation
import Data.List.Relation.Binary.Prefix.Heterogeneous

-- Properties of the heterogeneous prefix relation
import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties

-- Properties of the homogeneous prefix relation
import Data.List.Relation.Binary.Prefix.Homogeneous.Properties

-- An inductive definition of the sublist relation for types which have
-- a decidable equality. This is commonly known as Order Preserving
-- Embeddings (OPE).
import Data.List.Relation.Binary.Sublist.DecPropositional

-- A solver for proving that one list is a sublist of the other for
-- types which enjoy decidable equalities.
import Data.List.Relation.Binary.Sublist.DecPropositional.Solver

-- An inductive definition of the sublist relation with respect to a
-- setoid which is decidable. This is a generalisation of what is
-- commonly known as Order Preserving Embeddings (OPE).
import Data.List.Relation.Binary.Sublist.DecSetoid

-- A solver for proving that one list is a sublist of the other.
import Data.List.Relation.Binary.Sublist.DecSetoid.Solver

-- An inductive definition of the heterogeneous sublist relation
-- This is a generalisation of what is commonly known as Order
-- Preserving Embeddings (OPE).
import Data.List.Relation.Binary.Sublist.Heterogeneous

-- Properties of the heterogeneous sublist relation
import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties

-- A solver for proving that one list is a sublist of the other.
import Data.List.Relation.Binary.Sublist.Heterogeneous.Solver

-- An inductive definition of the sublist relation. This is commonly
-- known as Order Preserving Embeddings (OPE).
import Data.List.Relation.Binary.Sublist.Propositional

-- Sublist-related properties
import Data.List.Relation.Binary.Sublist.Propositional.Disjoint

-- A larger example for sublists (propositional case):
-- Simply-typed lambda terms with globally unique variables
-- (both bound and free ones).
import Data.List.Relation.Binary.Sublist.Propositional.Example.UniqueBoundVariables

-- Sublist-related properties
import Data.List.Relation.Binary.Sublist.Propositional.Properties

-- An inductive definition of the sublist relation with respect to a
-- setoid. This is a generalisation of what is commonly known as Order
-- Preserving Embeddings (OPE).
import Data.List.Relation.Binary.Sublist.Setoid

-- Properties of the setoid sublist relation
import Data.List.Relation.Binary.Sublist.Setoid.Properties

-- The sublist relation over propositional equality.
import Data.List.Relation.Binary.Subset.Propositional

-- Properties of the sublist relation over setoid equality.
import Data.List.Relation.Binary.Subset.Propositional.Properties

-- The extensional sublist relation over setoid equality.
import Data.List.Relation.Binary.Subset.Setoid

-- Properties of the extensional sublist relation over setoid equality.
import Data.List.Relation.Binary.Subset.Setoid.Properties

-- An inductive definition of the heterogeneous suffix relation
import Data.List.Relation.Binary.Suffix.Heterogeneous

-- Properties of the heterogeneous suffix relation
import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties

-- Properties of the homogeneous suffix relation
import Data.List.Relation.Binary.Suffix.Homogeneous.Properties

-- Generalised view of appending two lists into one.
import Data.List.Relation.Ternary.Appending

-- Properties of the generalised view of appending two lists
import Data.List.Relation.Ternary.Appending.Properties

-- Appending of lists using propositional equality
import Data.List.Relation.Ternary.Appending.Propositional

-- Properties of list appending
import Data.List.Relation.Ternary.Appending.Propositional.Properties

-- Appending of lists using setoid equality
import Data.List.Relation.Ternary.Appending.Setoid

-- Properties of list appending
import Data.List.Relation.Ternary.Appending.Setoid.Properties

-- Generalised notion of interleaving two lists into one in an
-- order-preserving manner
import Data.List.Relation.Ternary.Interleaving

-- Properties of general interleavings
import Data.List.Relation.Ternary.Interleaving.Properties

-- Interleavings of lists using propositional equality
import Data.List.Relation.Ternary.Interleaving.Propositional

-- Properties of interleaving using propositional equality
import Data.List.Relation.Ternary.Interleaving.Propositional.Properties

-- Interleavings of lists using setoid equality
import Data.List.Relation.Ternary.Interleaving.Setoid

-- Properties of interleaving using setoid equality
import Data.List.Relation.Ternary.Interleaving.Setoid.Properties

-- Lists where all elements satisfy a given property
import Data.List.Relation.Unary.All

-- Properties related to All
import Data.List.Relation.Unary.All.Properties

-- Lists where every pair of elements are related (symmetrically)
import Data.List.Relation.Unary.AllPairs

-- Properties related to AllPairs
import Data.List.Relation.Unary.AllPairs.Properties

-- Lists where at least one element satisfies a given property
import Data.List.Relation.Unary.Any

-- Properties related to Any
import Data.List.Relation.Unary.Any.Properties

-- Lists which contain every element of a given type
import Data.List.Relation.Unary.Enumerates.Setoid

-- Properties of lists which contain every element of a given type
import Data.List.Relation.Unary.Enumerates.Setoid.Properties

-- First generalizes the idea that an element is the first in a list to
-- satisfy a predicate.
import Data.List.Relation.Unary.First

-- Properties of First
import Data.List.Relation.Unary.First.Properties

-- Property that elements are grouped
import Data.List.Relation.Unary.Grouped

-- Property related to Grouped
import Data.List.Relation.Unary.Grouped.Properties

-- Lists where every consecutative pair of elements is related.
import Data.List.Relation.Unary.Linked

-- Properties related to Linked
import Data.List.Relation.Unary.Linked.Properties

-- Sorted lists
import Data.List.Relation.Unary.Sorted.TotalOrder

-- Sorted lists
import Data.List.Relation.Unary.Sorted.TotalOrder.Properties

-- 'Sufficient' lists: a structurally inductive view of lists xs
-- as given by xs ≡ non-empty prefix + sufficient suffix
import Data.List.Relation.Unary.Sufficient

-- Lists made up entirely of unique elements (setoid equality)
import Data.List.Relation.Unary.Unique.DecPropositional

-- Properties of lists made up entirely of decidably unique elements
import Data.List.Relation.Unary.Unique.DecPropositional.Properties

-- Lists made up entirely of unique elements (setoid equality)
import Data.List.Relation.Unary.Unique.DecSetoid

-- Properties of lists made up entirely of decidably unique elements
import Data.List.Relation.Unary.Unique.DecSetoid.Properties

-- Lists made up entirely of unique elements (propositional equality)
import Data.List.Relation.Unary.Unique.Propositional

-- Properties of unique lists (setoid equality)
import Data.List.Relation.Unary.Unique.Propositional.Properties

-- Lists made up entirely of unique elements (setoid equality)
import Data.List.Relation.Unary.Unique.Setoid

-- Properties of unique lists (setoid equality)
import Data.List.Relation.Unary.Unique.Setoid.Properties

-- Reverse view
import Data.List.Reverse

-- Functions and definitions for sorting lists
import Data.List.Sort

-- The core definition of a sorting algorithm
import Data.List.Sort.Base

-- An implementation of merge sort along with proofs of correctness.
import Data.List.Sort.MergeSort

-- List Zippers, basic types and operations
import Data.List.Zipper

-- List Zipper-related properties
import Data.List.Zipper.Properties

-- The Maybe type
import Data.Maybe

-- The Maybe type and some operations
import Data.Maybe.Base

-- An effectful view of Maybe
import Data.Maybe.Effectful

-- An effectful view of Maybe
import Data.Maybe.Effectful.Transformer

-- Typeclass instances for Maybe
import Data.Maybe.Instances

-- Maybe-related properties
import Data.Maybe.Properties

-- Lifting a relation such that `nothing` is also related to `just`
import Data.Maybe.Relation.Binary.Connected

-- Pointwise lifting of relations to maybes
import Data.Maybe.Relation.Binary.Pointwise

-- Maybes where all the elements satisfy a given property
import Data.Maybe.Relation.Unary.All

-- Properties related to All
import Data.Maybe.Relation.Unary.All.Properties

-- Maybes where one of the elements satisfies a given property
import Data.Maybe.Relation.Unary.Any

-- Natural numbers
import Data.Nat

-- Natural numbers, basic types and operations
import Data.Nat.Base

-- Natural numbers represented in binary natively in Agda.
import Data.Nat.Binary

-- Natural numbers represented in binary.
import Data.Nat.Binary.Base

-- Induction over _<_ for ℕᵇ.
import Data.Nat.Binary.Induction

-- Instances for binary natural numbers
import Data.Nat.Binary.Instances

-- Basic properties of ℕᵇ
import Data.Nat.Binary.Properties

-- Subtraction on Bin and some of its properties.
import Data.Nat.Binary.Subtraction

-- Combinatorial operations
import Data.Nat.Combinatorics

-- Combinatorics operations
import Data.Nat.Combinatorics.Base

-- The specification for combinatorics operations
import Data.Nat.Combinatorics.Specification

-- Coprimality
import Data.Nat.Coprimality

-- Natural number division
import Data.Nat.DivMod

-- More efficient mod and divMod operations (require the K axiom)
import Data.Nat.DivMod.WithK

-- Divisibility
import Data.Nat.Divisibility

-- Greatest common divisor
import Data.Nat.GCD

-- Boring lemmas used in Data.Nat.GCD and Data.Nat.Coprimality
import Data.Nat.GCD.Lemmas

-- A generalisation of the arithmetic operations
import Data.Nat.GeneralisedArithmetic

-- Various forms of induction for natural numbers
import Data.Nat.Induction

-- Definition of and lemmas related to "true infinitely often"
import Data.Nat.InfinitelyOften

-- Instances for natural numbers
import Data.Nat.Instances

-- Least common multiple
import Data.Nat.LCM

-- Natural Literals
import Data.Nat.Literals

-- Logarithm base 2 and respective properties
import Data.Nat.Logarithm

-- Primality
import Data.Nat.Primality

-- A bunch of properties about natural number operations
import Data.Nat.Properties

-- Linear congruential pseudo random generators for natural numbers
-- /!\ NB: LCGs must not be used for cryptographic applications
import Data.Nat.PseudoRandom.LCG

-- Reflection utilities for ℕ
import Data.Nat.Reflection

-- Showing natural numbers
import Data.Nat.Show

-- Properties of showing natural numbers
import Data.Nat.Show.Properties

-- Automatic solvers for equations over naturals
import Data.Nat.Solver

-- Automatic solvers for equations over naturals
import Data.Nat.Tactic.RingSolver

-- Natural number types and operations requiring the axiom K.
import Data.Nat.WithK

-- Parity
import Data.Parity

-- Parity
import Data.Parity.Base

-- Instances for parities
import Data.Parity.Instances

-- Some properties about parities
import Data.Parity.Properties

-- Products
import Data.Product

-- Algebraic properties of products
import Data.Product.Algebra

-- Products
import Data.Product.Base

-- Universe-sensitive functor and monad instances for the Product type.
import Data.Product.Effectful.Examples

-- Left-biased universe-sensitive functor and monad instances for the
-- Product type.
import Data.Product.Effectful.Left

-- Base definitions for the left-biased universe-sensitive functor and
-- monad instances for the Product type.
import Data.Product.Effectful.Left.Base

-- Right-biased universe-sensitive functor and monad instances for the
-- Product type.
import Data.Product.Effectful.Right

-- Base definitions for the right-biased universe-sensitive functor
-- and monad instances for the Product type.
import Data.Product.Effectful.Right.Base

-- Dependent product combinators for propositional equality
-- preserving functions
import Data.Product.Function.Dependent.Propositional

-- Dependent product combinators for propositional equality
-- preserving functions
import Data.Product.Function.Dependent.Propositional.WithK

-- Dependent product combinators for setoid equality preserving
-- functions.
import Data.Product.Function.Dependent.Setoid

-- Non-dependent product combinators for propositional equality
-- preserving functions
import Data.Product.Function.NonDependent.Propositional

-- Non-dependent product combinators for setoid equality preserving
-- functions
import Data.Product.Function.NonDependent.Setoid

-- Typeclass instances for products
import Data.Product.Instances

-- Nondependent heterogeneous N-ary products
import Data.Product.Nary.NonDependent

-- Properties of products
import Data.Product.Properties

-- Properties, related to products, that rely on the K rule
import Data.Product.Properties.WithK

-- Lexicographic products of binary relations
import Data.Product.Relation.Binary.Lex.NonStrict

-- Lexicographic products of binary relations
import Data.Product.Relation.Binary.Lex.Strict

-- Pointwise lifting of binary relations to sigma types
import Data.Product.Relation.Binary.Pointwise.Dependent

-- Properties that are related to pointwise lifting of binary
-- relations to sigma types and make use of heterogeneous equality
import Data.Product.Relation.Binary.Pointwise.Dependent.WithK

-- Pointwise products of binary relations
import Data.Product.Relation.Binary.Pointwise.NonDependent

-- Lifting of two predicates
import Data.Product.Relation.Unary.All

-- Rational numbers
import Data.Rational

-- Rational numbers
import Data.Rational.Base

-- Instances for rational numbers
import Data.Rational.Instances

-- Rational Literals
import Data.Rational.Literals

-- Properties of Rational numbers
import Data.Rational.Properties

-- Showing rational numbers
import Data.Rational.Show

-- Automatic solvers for equations over rationals
import Data.Rational.Solver

-- Rational numbers in non-reduced form.
import Data.Rational.Unnormalised

-- Rational numbers in non-reduced form.
import Data.Rational.Unnormalised.Base

-- Properties of unnormalized Rational numbers
import Data.Rational.Unnormalised.Properties

-- Showing unnormalised rational numbers
import Data.Rational.Unnormalised.Show

-- Automatic solvers for equations over rationals
import Data.Rational.Unnormalised.Solver

-- Record types with manifest fields and "with", based on Randy
-- Pollack's "Dependently Typed Records in Type Theory"
import Data.Record

-- Refinement type: a value together with a proof irrelevant witness.
import Data.Refinement

-- Predicate lifting for refinement types
import Data.Refinement.Relation.Unary.All

-- Signs
import Data.Sign

-- Signs
import Data.Sign.Base

-- Instances for signs
import Data.Sign.Instances

-- Some properties about signs
import Data.Sign.Properties

-- Bounded vectors (inefficient implementation)
import Data.Star.BoundedVec

-- Decorated star-lists
import Data.Star.Decoration

-- Environments (heterogeneous collections)
import Data.Star.Environment

-- Finite sets defined using the reflexive-transitive closure, Star
import Data.Star.Fin

-- Lists defined in terms of the reflexive-transitive closure, Star
import Data.Star.List

-- Natural numbers defined using the reflexive-transitive closure, Star
import Data.Star.Nat

-- Pointers into star-lists
import Data.Star.Pointer

-- Vectors defined in terms of the reflexive-transitive closure, Star
import Data.Star.Vec

-- Strings
import Data.String

-- Strings: builtin type and basic operations
import Data.String.Base

-- Instances for strings
import Data.String.Instances

-- String Literals
import Data.String.Literals

-- Properties of operations on strings
import Data.String.Properties

-- Sums (disjoint unions)
import Data.Sum

-- Algebraic properties of sums (disjoint unions)
import Data.Sum.Algebra

-- Sums (disjoint unions)
import Data.Sum.Base

-- Usage examples of the effectful view of the Sum type
import Data.Sum.Effectful.Examples

-- An effectful view of the Sum type (Left-biased)
import Data.Sum.Effectful.Left

-- An effectful view of the Sum type (Left-biased)
import Data.Sum.Effectful.Left.Transformer

-- An effectful view of the Sum type (Right-biased)
import Data.Sum.Effectful.Right

-- An effectful view of the Sum type (Right-biased)
import Data.Sum.Effectful.Right.Transformer

-- Sum combinators for propositional equality preserving functions
import Data.Sum.Function.Propositional

-- Sum combinators for setoid equality preserving functions
import Data.Sum.Function.Setoid

-- Typeclass instances for sums
import Data.Sum.Instances

-- Properties of sums (disjoint unions)
import Data.Sum.Properties

-- Sums of binary relations
import Data.Sum.Relation.Binary.LeftOrder

-- Pointwise sum
import Data.Sum.Relation.Binary.Pointwise

-- Heterogeneous `All` predicate for disjoint sums
import Data.Sum.Relation.Unary.All

-- An either-or-both data type
import Data.These

-- An either-or-both data type, basic type and operations
import Data.These.Base

-- Left-biased universe-sensitive functor and monad instances for These.
import Data.These.Effectful.Left

-- Base definitions for the left-biased universe-sensitive functor and
-- monad instances for These.
import Data.These.Effectful.Left.Base

-- Right-biased universe-sensitive functor and monad instances for These.
import Data.These.Effectful.Right

-- Base definitions for the right-biased universe-sensitive functor and
-- monad instances for These.
import Data.These.Effectful.Right.Base

-- Typeclass instances for These
import Data.These.Instances

-- Properties of These
import Data.These.Properties

-- AVL trees
import Data.Tree.AVL

-- Types and functions which are used to keep track of height
-- invariants in AVL Trees
import Data.Tree.AVL.Height

-- AVL trees where the stored values may depend on their key
import Data.Tree.AVL.Indexed

-- AVL trees whose elements satisfy a given property
import Data.Tree.AVL.Indexed.Relation.Unary.All

-- AVL trees where at least one element satisfies a given property
import Data.Tree.AVL.Indexed.Relation.Unary.Any

-- Properties related to Any
import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties

-- Some code related to indexed AVL trees that relies on the K rule
import Data.Tree.AVL.Indexed.WithK

-- Finite maps with indexed keys and values, based on AVL trees
import Data.Tree.AVL.IndexedMap

-- Keys for AVL trees -- the original key type extended with a new
-- minimum and maximum.
import Data.Tree.AVL.Key

-- Maps from keys to values, based on AVL trees
-- This modules provides a simpler map interface, without a dependency
-- between the key and value types.
import Data.Tree.AVL.Map

-- Membership relation for AVL Maps identifying values up to
-- propositional equality.
import Data.Tree.AVL.Map.Membership.Propositional

-- Properties of the membership relation for AVL Maps identifying values
-- up to propositional equality.
import Data.Tree.AVL.Map.Membership.Propositional.Properties

-- AVL trees where at least one element satisfies a given property
import Data.Tree.AVL.Map.Relation.Unary.Any

-- Non-empty AVL trees
import Data.Tree.AVL.NonEmpty

-- Non-empty AVL trees, where equality for keys is propositional equality
import Data.Tree.AVL.NonEmpty.Propositional

-- AVL trees where at least one element satisfies a given property
import Data.Tree.AVL.Relation.Unary.Any

-- Finite sets, based on AVL trees
import Data.Tree.AVL.Sets

-- Membership relation for AVL sets
import Data.Tree.AVL.Sets.Membership

-- Properties of membership for AVL sets
import Data.Tree.AVL.Sets.Membership.Properties

-- Values for AVL trees
-- Values must respect the underlying equivalence on keys
import Data.Tree.AVL.Value

-- Binary Trees
import Data.Tree.Binary

-- Properties of binary trees
import Data.Tree.Binary.Properties

-- Pointwise lifting of a predicate to a binary tree
import Data.Tree.Binary.Relation.Unary.All

-- Properties of the pointwise lifting of a predicate to a binary tree
import Data.Tree.Binary.Relation.Unary.All.Properties

-- Zippers for Binary Trees
import Data.Tree.Binary.Zipper

-- Tree Zipper-related properties
import Data.Tree.Binary.Zipper.Properties

-- The unit type
import Data.Unit

-- The unit type and the total relation on unit
import Data.Unit.Base

-- Instances for the unit type
import Data.Unit.Instances

-- Some unit types
import Data.Unit.NonEta

-- The universe polymorphic unit type and the total relation on unit
import Data.Unit.Polymorphic

-- A universe polymorphic unit type, as a Lift of the Level 0 one.
import Data.Unit.Polymorphic.Base

-- Instances for the polymorphic unit type
import Data.Unit.Polymorphic.Instances

-- Properties of the polymorphic unit type
-- Defines Decidable Equality and Decidable Ordering as well
import Data.Unit.Polymorphic.Properties

-- Properties of the unit type
import Data.Unit.Properties

-- Universes
import Data.Universe

-- Indexed universes
import Data.Universe.Indexed

-- Vectors
import Data.Vec

-- Vectors, basic types and operations
import Data.Vec.Base

-- Bounded vectors
import Data.Vec.Bounded

-- Bounded vectors, basic types and operations
import Data.Vec.Bounded.Base

-- An effectful view of Vec
import Data.Vec.Effectful

-- An effectful view of Vec
import Data.Vec.Effectful.Transformer

-- Vectors defined as functions from a finite set to a type.
import Data.Vec.Functional

-- Some Vector-related properties
import Data.Vec.Functional.Properties

-- Pointwise lifting of relations over Vector
import Data.Vec.Functional.Relation.Binary.Equality.Setoid

-- Pointwise lifting of relations over Vector
import Data.Vec.Functional.Relation.Binary.Pointwise

-- Properties related to Pointwise
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties

-- Universal lifting of predicates over Vectors
import Data.Vec.Functional.Relation.Unary.All

-- Properties related to All
import Data.Vec.Functional.Relation.Unary.All.Properties

-- Existential lifting of predicates over Vectors
import Data.Vec.Functional.Relation.Unary.Any

-- Typeclass instances for Vec
import Data.Vec.Instances

-- Decidable propositional membership over vectors
import Data.Vec.Membership.DecPropositional

-- Decidable setoid membership over vectors.
import Data.Vec.Membership.DecSetoid

-- Data.Vec.Any.Membership instantiated with propositional equality,
-- along with some additional definitions.
import Data.Vec.Membership.Propositional

-- Properties of membership of vectors based on propositional equality.
import Data.Vec.Membership.Propositional.Properties

-- Membership of vectors, along with some additional definitions.
import Data.Vec.Membership.Setoid

-- Code for converting Vec A n → B to and from n-ary functions
import Data.Vec.N-ary

-- Some Vec-related properties
import Data.Vec.Properties

-- Some Vec-related properties that depend on the K rule or make use
-- of heterogeneous equality
import Data.Vec.Properties.WithK

-- Vectors defined by recursion
import Data.Vec.Recursive

-- An effectful view of vectors defined by recursion
import Data.Vec.Recursive.Effectful

-- Properties of n-ary products
import Data.Vec.Recursive.Properties

-- Reflection utilities for Vector
import Data.Vec.Reflection

-- An equational reasoning library for propositional equality over
-- vectors of different indices using cast.
import Data.Vec.Relation.Binary.Equality.Cast

-- Decidable vector equality over propositional equality
import Data.Vec.Relation.Binary.Equality.DecPropositional

-- Decidable semi-heterogeneous vector equality over setoids
import Data.Vec.Relation.Binary.Equality.DecSetoid

-- Vector equality over propositional equality
import Data.Vec.Relation.Binary.Equality.Propositional

-- Code related to vector equality over propositional equality that
-- makes use of heterogeneous equality
import Data.Vec.Relation.Binary.Equality.Propositional.WithK

-- Semi-heterogeneous vector equality over setoids
import Data.Vec.Relation.Binary.Equality.Setoid

-- Lexicographic ordering of same-length vector
import Data.Vec.Relation.Binary.Lex.NonStrict

-- Lexicographic ordering of lists of same-length vectors
import Data.Vec.Relation.Binary.Lex.Strict

-- Extensional pointwise lifting of relations to vectors
import Data.Vec.Relation.Binary.Pointwise.Extensional

-- Inductive pointwise lifting of relations to vectors
import Data.Vec.Relation.Binary.Pointwise.Inductive

-- Vectors where all elements satisfy a given property
import Data.Vec.Relation.Unary.All

-- Properties related to All
import Data.Vec.Relation.Unary.All.Properties

-- Vectors where every pair of elements are related (symmetrically)
import Data.Vec.Relation.Unary.AllPairs

-- Properties related to AllPairs
import Data.Vec.Relation.Unary.AllPairs.Properties

-- Vectors where at least one element satisfies a given property
import Data.Vec.Relation.Unary.Any

-- Properties of vector's Any
import Data.Vec.Relation.Unary.Any.Properties

-- Vectors where every consecutative pair of elements is related.
import Data.Vec.Relation.Unary.Linked

-- Properties related to Linked
import Data.Vec.Relation.Unary.Linked.Properties

-- Vectors made up entirely of unique elements (propositional equality)
import Data.Vec.Relation.Unary.Unique.Propositional

-- Properties of unique vectors (setoid equality)
import Data.Vec.Relation.Unary.Unique.Propositional.Properties

-- Vectors made up entirely of unique elements (setoid equality)
import Data.Vec.Relation.Unary.Unique.Setoid

-- Properties of unique vectors (setoid equality)
import Data.Vec.Relation.Unary.Unique.Setoid.Properties

-- W-types
import Data.W

-- Indexed W-types aka Petersson-Synek trees
import Data.W.Indexed

-- Some code related to the W type that relies on the K rule
import Data.W.WithK

-- Machine words
import Data.Word

-- Machine words: basic type and conversion functions
import Data.Word.Base

-- Instances for words
import Data.Word.Instances

-- Properties of operations on machine words
import Data.Word.Properties

-- Turn a relation into a record definition so as to remember the things
-- being related.
-- This module has a readme file: README.Data.Wrap
import Data.Wrap

-- Applicative functors
import Effect.Applicative

-- Indexed applicative functors
import Effect.Applicative.Indexed

-- Applicative functors on indexed sets (predicates)
import Effect.Applicative.Predicate

-- Type constructors giving rise to a semigroup at every type
-- e.g. (List, _++_)
import Effect.Choice

-- Comonads
import Effect.Comonad

-- Empty values (e.g. [] for List, nothing for Maybe)
import Effect.Empty

-- Functors
import Effect.Functor

-- Functors on indexed sets (predicates)
import Effect.Functor.Predicate

-- Monads
import Effect.Monad

-- A delimited continuation monad
import Effect.Monad.Continuation

-- The error monad transformer
import Effect.Monad.Error.Transformer

-- An effectful view of the identity function
import Effect.Monad.Identity

-- Typeclass instances for Identity
import Effect.Monad.Identity.Instances

-- Indexed monads
import Effect.Monad.Indexed

-- The partiality monad
import Effect.Monad.Partiality

-- An All predicate for the partiality monad
import Effect.Monad.Partiality.All

-- Typeclass instances for _⊥
import Effect.Monad.Partiality.Instances

-- Monads on indexed sets (predicates)
import Effect.Monad.Predicate

-- The reader monad
import Effect.Monad.Reader

-- The indexed reader monad
import Effect.Monad.Reader.Indexed

-- Instances for the reader monad
import Effect.Monad.Reader.Instances

-- The reader monad transformer
import Effect.Monad.Reader.Transformer

-- Basic type and definition of the reader monad transformer
import Effect.Monad.Reader.Transformer.Base

-- The state monad
import Effect.Monad.State

-- The indexed state monad
import Effect.Monad.State.Indexed

-- Instances for the state monad
import Effect.Monad.State.Instances

-- The state monad transformer
import Effect.Monad.State.Transformer

-- Basic definition and functions on the state monad transformer
import Effect.Monad.State.Transformer.Base

-- The writer monad
import Effect.Monad.Writer

-- The indexed writer monad
import Effect.Monad.Writer.Indexed

-- Instances for the writer monad
import Effect.Monad.Writer.Instances

-- The writer monad transformer
import Effect.Monad.Writer.Transformer

-- Basic type and definition of the writer monad transformer
import Effect.Monad.Writer.Transformer.Base

-- Functions
import Function

-- Simple combinators working solely on and with functions
import Function.Base

-- Bundles for types of functions
import Function.Bundles

-- Relationships between properties of functions. See
-- `Function.Consequences.Propositional` for specialisations to
-- propositional equality.
import Function.Consequences

-- Relationships between properties of functions where the equality
-- over both the domain and codomain is assumed to be _≡_
import Function.Consequences.Propositional

-- Composition of functional properties
import Function.Construct.Composition

-- The constant function
import Function.Construct.Constant

-- The identity function
import Function.Construct.Identity

-- Some functional properties are symmetric
import Function.Construct.Symmetry

-- Definitions for types of functions.
import Function.Definitions

-- Bundles for types of functions
import Function.Dependent.Bundles

-- Endomorphisms on a Set
import Function.Endomorphism.Propositional

-- Endomorphisms on a Setoid
import Function.Endomorphism.Setoid

-- An effectful view of the identity function
import Function.Identity.Effectful

-- Operations on Relations for Indexed sets
import Function.Indexed.Bundles

-- Function setoids and related constructions
import Function.Indexed.Relation.Binary.Equality

-- Metrics with arbitrary domains and codomains
import Function.Metric

-- Bundles for metrics
import Function.Metric.Bundles

-- Definitions of properties over distance functions
import Function.Metric.Definitions

-- Metrics with ℕ as the codomain of the metric function
import Function.Metric.Nat

-- Bundles for metrics over ℕ
import Function.Metric.Nat.Bundles

-- Core definitions for metrics over ℕ
import Function.Metric.Nat.Definitions

-- Core definitions for metrics over ℕ
import Function.Metric.Nat.Structures

-- Metrics with ℚ as the codomain of the metric function
import Function.Metric.Rational

-- Bundles for metrics over ℚ
import Function.Metric.Rational.Bundles

-- Core definitions for metrics over ℚ
import Function.Metric.Rational.Definitions

-- Core definitions for metrics over ℚ
import Function.Metric.Rational.Structures

-- Some metric structures (not packed up with sets, operations, etc.)
import Function.Metric.Structures

-- Heterogeneous N-ary Functions
import Function.Nary.NonDependent

-- Heterogeneous N-ary Functions: basic types and operations
import Function.Nary.NonDependent.Base

-- Basic properties of the function type
import Function.Properties

-- Some basic properties of bijections.
import Function.Properties.Bijection

-- Some basic properties of equivalences. This file is designed to be
-- imported qualified.
import Function.Properties.Equivalence

-- Properties for injections
import Function.Properties.Injection

-- Properties of inverses.
import Function.Properties.Inverse

-- Half adjoint equivalences
import Function.Properties.Inverse.HalfAdjointEquivalence

-- Properties of right inverses
import Function.Properties.RightInverse

-- Properties of surjections
import Function.Properties.Surjection

-- A module used for creating function pipelines, see
-- README.Function.Reasoning for examples
import Function.Reasoning

-- Relatedness for the function hierarchy
import Function.Related.Propositional

-- Basic lemmas showing that various types are related (isomorphic or
-- equivalent or…)
import Function.Related.TypeIsomorphisms

-- Automatic solver for equations over product and sum types
import Function.Related.TypeIsomorphisms.Solver

-- Strict combinators (i.e. that use call-by-value)
import Function.Strict

-- Structures for types of functions
import Function.Structures

-- An abstraction of various forms of recursion/induction
import Induction

-- Lexicographic induction
import Induction.Lexicographic

-- Well-founded induction
import Induction.WellFounded

-- Universe levels
import Level

-- Conversion from naturals to universe levels
import Level.Literals

-- Support for reflection
import Reflection

-- The reflected abstract syntax tree
import Reflection.AST

-- Abstractions used in the reflection machinery
import Reflection.AST.Abstraction

-- Alpha equality over terms
import Reflection.AST.AlphaEquality

-- Arguments used in the reflection machinery
import Reflection.AST.Argument

-- Argument information used in the reflection machinery
import Reflection.AST.Argument.Information

-- Modalities used in the reflection machinery
import Reflection.AST.Argument.Modality

-- Argument quantities used in the reflection machinery
import Reflection.AST.Argument.Quantity

-- Argument relevance used in the reflection machinery
import Reflection.AST.Argument.Relevance

-- Argument visibility used in the reflection machinery
import Reflection.AST.Argument.Visibility

-- Weakening, strengthening and free variable check for reflected terms.
import Reflection.AST.DeBruijn

-- Definitions used in the reflection machinery
import Reflection.AST.Definition

-- Instances for reflected syntax
import Reflection.AST.Instances

-- Literals used in the reflection machinery
import Reflection.AST.Literal

-- Metavariables used in the reflection machinery
import Reflection.AST.Meta

-- Names used in the reflection machinery
import Reflection.AST.Name

-- Patterns used in the reflection machinery
import Reflection.AST.Pattern

-- Converting reflection machinery to strings
import Reflection.AST.Show

-- Terms used in the reflection machinery
import Reflection.AST.Term

-- de Bruijn-aware generic traversal of reflected terms.
import Reflection.AST.Traversal

-- A universe for the types involved in the reflected syntax.
import Reflection.AST.Universe

-- Annotated reflected syntax.
import Reflection.AnnotatedAST

-- Computing free variable annotations on reflected syntax.
import Reflection.AnnotatedAST.Free

-- Support for system calls as part of reflection
import Reflection.External

-- The TC (Type Checking) monad
import Reflection.TCM

-- Typeclass instances for TC
import Reflection.TCM.Effectful

-- Printf-style versions of typeError and debugPrint
import Reflection.TCM.Format

-- Typeclass instances for TC
import Reflection.TCM.Instances

-- Monad syntax for the TC monad
import Reflection.TCM.Syntax

-- Properties of homogeneous binary relations
import Relation.Binary

-- Bundles for homogeneous binary relations
import Relation.Binary.Bundles

-- Some properties imply others
import Relation.Binary.Consequences

-- A pointwise lifting of a relation to incorporate new extrema.
import Relation.Binary.Construct.Add.Extrema.Equality

-- The lifting of a non-strict order to incorporate new extrema
import Relation.Binary.Construct.Add.Extrema.NonStrict

-- The lifting of a strict order to incorporate new extrema
import Relation.Binary.Construct.Add.Extrema.Strict

-- A pointwise lifting of a relation to incorporate a new infimum.
import Relation.Binary.Construct.Add.Infimum.Equality

-- The lifting of a non-strict order to incorporate a new infimum
import Relation.Binary.Construct.Add.Infimum.NonStrict

-- The lifting of a non-strict order to incorporate a new infimum
import Relation.Binary.Construct.Add.Infimum.Strict

-- A pointwise lifting of a relation to incorporate an additional point.
import Relation.Binary.Construct.Add.Point.Equality

-- A pointwise lifting of a relation to incorporate a new supremum.
import Relation.Binary.Construct.Add.Supremum.Equality

-- The lifting of a non-strict order to incorporate a new supremum
import Relation.Binary.Construct.Add.Supremum.NonStrict

-- The lifting of a strict order to incorporate a new supremum
import Relation.Binary.Construct.Add.Supremum.Strict

-- The universal binary relation
import Relation.Binary.Construct.Always

-- The reflexive, symmetric and transitive closure of a binary
-- relation (aka the equivalence closure).
import Relation.Binary.Construct.Closure.Equivalence

-- Some properties of equivalence closures.
import Relation.Binary.Construct.Closure.Equivalence.Properties

-- Reflexive closures
import Relation.Binary.Construct.Closure.Reflexive

-- Some properties of reflexive closures
import Relation.Binary.Construct.Closure.Reflexive.Properties

-- Some properties of reflexive closures which rely on the K rule
import Relation.Binary.Construct.Closure.Reflexive.Properties.WithK

-- The reflexive transitive closures of McBride, Norell and Jansson
import Relation.Binary.Construct.Closure.ReflexiveTransitive

-- Some properties of reflexive transitive closures.
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties

-- Properties, related to reflexive transitive closures, that rely on
-- the K rule
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.WithK

-- Symmetric closures of binary relations
import Relation.Binary.Construct.Closure.Symmetric

-- Symmetric transitive closures of binary relations
import Relation.Binary.Construct.Closure.SymmetricTransitive

-- Transitive closures
import Relation.Binary.Construct.Closure.Transitive

-- Some code related to transitive closures that relies on the K rule
import Relation.Binary.Construct.Closure.Transitive.WithK

-- Composition of two binary relations
import Relation.Binary.Construct.Composition

-- The binary relation defined by a constant
import Relation.Binary.Construct.Constant

-- Many properties which hold for `∼` also hold for `flip ∼`. Unlike
-- the module `Relation.Binary.Construct.Flip.Ord` this module does not
-- flip the underlying equality.
import Relation.Binary.Construct.Flip.EqAndOrd

-- Many properties which hold for `∼` also hold for `flip ∼`. Unlike
-- the module `Relation.Binary.Construct.Flip.EqAndOrd` this module
-- flips both the relation and the underlying equality.
import Relation.Binary.Construct.Flip.Ord

-- Every respectful unary relation induces a preorder. No claim is
-- made that this preorder is unique.
import Relation.Binary.Construct.FromPred

-- Every respectful binary relation induces a preorder. No claim is
-- made that this preorder is unique.
import Relation.Binary.Construct.FromRel

-- Intersection of two binary relations
import Relation.Binary.Construct.Intersection

-- Conversion of binary operators to binary relations via the left
-- natural order.
import Relation.Binary.Construct.NaturalOrder.Left

-- Conversion of binary operators to binary relations via the right
-- natural order.
import Relation.Binary.Construct.NaturalOrder.Right

-- The empty binary relation
import Relation.Binary.Construct.Never

-- Conversion of _≤_ to _<_
import Relation.Binary.Construct.NonStrictToStrict

-- Many properties which hold for `_∼_` also hold for `_∼_ on f`
import Relation.Binary.Construct.On

-- Conversion of < to ≤, along with a number of properties
import Relation.Binary.Construct.StrictToNonStrict

-- Substituting equalities for binary relations
import Relation.Binary.Construct.Subst.Equality

-- Union of two binary relations
import Relation.Binary.Construct.Union

-- Properties of binary relations
import Relation.Binary.Definitions

-- Heterogeneous equality
import Relation.Binary.HeterogeneousEquality

-- Quotients for Heterogeneous equality
import Relation.Binary.HeterogeneousEquality.Quotients

-- Example of a Quotient: ℤ as (ℕ × ℕ / ∼)
import Relation.Binary.HeterogeneousEquality.Quotients.Examples

-- Heterogeneously-indexed binary relations
import Relation.Binary.Indexed.Heterogeneous

-- Indexed binary relations
import Relation.Binary.Indexed.Heterogeneous.Bundles

-- Instantiates indexed binary structures at an index to the equivalent
-- non-indexed structures.
import Relation.Binary.Indexed.Heterogeneous.Construct.At

-- Creates trivially indexed records from their non-indexed counterpart.
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial

-- Indexed binary relations
import Relation.Binary.Indexed.Heterogeneous.Definitions

-- Indexed binary relations
import Relation.Binary.Indexed.Heterogeneous.Structures

-- Homogeneously-indexed binary relations
import Relation.Binary.Indexed.Homogeneous

-- Homogeneously-indexed binary relations
import Relation.Binary.Indexed.Homogeneous.Bundles

-- Instantiating homogeneously indexed bundles at a particular index
import Relation.Binary.Indexed.Homogeneous.Construct.At

-- Homogeneously-indexed binary relations
import Relation.Binary.Indexed.Homogeneous.Definitions

-- Homogeneously-indexed binary relations
import Relation.Binary.Indexed.Homogeneous.Structures

-- Order-theoretic lattices
import Relation.Binary.Lattice

-- Bundles for order-theoretic lattices
import Relation.Binary.Lattice.Bundles

-- Definitions for order-theoretic lattices
import Relation.Binary.Lattice.Definitions

-- Properties satisfied by bounded join semilattices
import Relation.Binary.Lattice.Properties.BoundedJoinSemilattice

-- Properties satisfied by bounded lattice
import Relation.Binary.Lattice.Properties.BoundedLattice

-- Properties satisfied by bounded meet semilattices
import Relation.Binary.Lattice.Properties.BoundedMeetSemilattice

-- Properties for distributive lattice
import Relation.Binary.Lattice.Properties.DistributiveLattice

-- Properties satisfied by Heyting Algebra
import Relation.Binary.Lattice.Properties.HeytingAlgebra

-- Properties satisfied by join semilattices
import Relation.Binary.Lattice.Properties.JoinSemilattice

-- Properties satisfied by lattices
import Relation.Binary.Lattice.Properties.Lattice

-- Properties satisfied by meet semilattices
import Relation.Binary.Lattice.Properties.MeetSemilattice

-- Structures for order-theoretic lattices
import Relation.Binary.Lattice.Structures

-- Order morphisms
import Relation.Binary.Morphism

-- Bundles for morphisms between binary relations
import Relation.Binary.Morphism.Bundles

-- The composition of morphisms between binary relations
import Relation.Binary.Morphism.Construct.Composition

-- Constant morphisms between binary relations
import Relation.Binary.Morphism.Construct.Constant

-- The identity morphism for binary relations
import Relation.Binary.Morphism.Construct.Identity

-- Basic definitions for morphisms between algebraic structures
import Relation.Binary.Morphism.Definitions

-- Consequences of a monomorphism between orders
import Relation.Binary.Morphism.OrderMonomorphism

-- Consequences of a monomorphism between binary relations
import Relation.Binary.Morphism.RelMonomorphism

-- Order morphisms
import Relation.Binary.Morphism.Structures

-- Apartness properties
import Relation.Binary.Properties.ApartnessRelation

-- Properties satisfied by decidable total orders
import Relation.Binary.Properties.DecTotalOrder

-- Properties satisfied by posets
import Relation.Binary.Properties.Poset

-- Properties satisfied by preorders
import Relation.Binary.Properties.Preorder

-- Additional properties for setoids
import Relation.Binary.Properties.Setoid

-- Properties satisfied by strict partial orders
import Relation.Binary.Properties.StrictPartialOrder

-- Properties satisfied by strict partial orders
import Relation.Binary.Properties.StrictTotalOrder

-- Properties satisfied by total orders
import Relation.Binary.Properties.TotalOrder

-- Propositional (intensional) equality
import Relation.Binary.PropositionalEquality

-- Propositional (intensional) equality - Algebraic structures
import Relation.Binary.PropositionalEquality.Algebra

-- Propositional equality
import Relation.Binary.PropositionalEquality.Properties

-- Some code related to propositional equality that relies on the K
-- rule
import Relation.Binary.PropositionalEquality.WithK

-- The basic code for equational reasoning with three relations:
-- equality and apartness
import Relation.Binary.Reasoning.Base.Apartness

-- The basic code for equational reasoning with two relations:
-- equality and some other ordering.
import Relation.Binary.Reasoning.Base.Double

-- The basic code for equational reasoning with a non-reflexive relation
import Relation.Binary.Reasoning.Base.Partial

-- The basic code for equational reasoning with a single relation
import Relation.Binary.Reasoning.Base.Single

-- The basic code for equational reasoning with three relations:
-- equality, strict ordering and non-strict ordering.
import Relation.Binary.Reasoning.Base.Triple

-- Convenient syntax for "equational reasoning" in multiple Setoids.
import Relation.Binary.Reasoning.MultiSetoid

-- Convenient syntax for "equational reasoning" using a partial order
import Relation.Binary.Reasoning.PartialOrder

-- Convenient syntax for reasoning with a partial setoid
import Relation.Binary.Reasoning.PartialSetoid

-- Convenient syntax for "equational reasoning" using a preorder
import Relation.Binary.Reasoning.Preorder

-- Convenient syntax for reasoning with a setoid
import Relation.Binary.Reasoning.Setoid

-- Convenient syntax for "equational reasoning" using a strict partial
-- order.
import Relation.Binary.Reasoning.StrictPartialOrder

-- Syntax for the building blocks of equational reasoning modules
import Relation.Binary.Reasoning.Syntax

-- Helpers intended to ease the development of "tactics" which use
-- proof by reflection
import Relation.Binary.Reflection

-- Concepts from rewriting theory
-- Definitions are based on "Term Rewriting Systems" by J.W. Klop
import Relation.Binary.Rewriting

-- Structures for homogeneous binary relations
import Relation.Binary.Structures

-- Ways to give instances of certain structures where some fields can
-- be given in terms of others
import Relation.Binary.Structures.Biased

-- Typeclasses for use with instance arguments
import Relation.Binary.TypeClasses

-- Heterogeneous N-ary Relations
import Relation.Nary

-- Operations on nullary relations (like negation and decidability)
import Relation.Nullary

-- Notation for freely adding extrema to any set
import Relation.Nullary.Construct.Add.Extrema

-- Notation for freely adding an infimum to any set
import Relation.Nullary.Construct.Add.Infimum

-- Notation for adding an additional point to any set
import Relation.Nullary.Construct.Add.Point

-- Notation for freely adding a supremum to any set
import Relation.Nullary.Construct.Add.Supremum

-- Operations on and properties of decidable relations
import Relation.Nullary.Decidable

-- Negation indexed by a Level
import Relation.Nullary.Indexed

-- Properties of indexed negation
import Relation.Nullary.Indexed.Negation

-- Properties related to negation
import Relation.Nullary.Negation

-- Properties of the `Reflects` construct
import Relation.Nullary.Reflects

-- A universe of proposition functors, along with some properties
import Relation.Nullary.Universe

-- Unary relations
import Relation.Unary

-- Algebraic properties of constructions over unary relations
import Relation.Unary.Algebra

-- Closures of a unary relation with respect to a binary one.
import Relation.Unary.Closure.Base

-- Closure of a unary relation with respect to a preorder
import Relation.Unary.Closure.Preorder

-- Closures of a unary relation with respect to a strict partial order
import Relation.Unary.Closure.StrictPartialOrder

-- Some properties imply others
import Relation.Unary.Consequences

-- Indexed unary relations
import Relation.Unary.Indexed

-- Polymorphic versions of standard definitions in Relation.Unary
import Relation.Unary.Polymorphic

-- Properties of polymorphic versions of standard definitions in
-- Relation.Unary
import Relation.Unary.Polymorphic.Properties

-- Predicate transformers
import Relation.Unary.PredicateTransformer

-- Properties of constructions over unary relations
import Relation.Unary.Properties

-- Equality of unary relations
import Relation.Unary.Relation.Binary.Equality

-- Order properties of the subset relations _⊆_ and _⊂_
import Relation.Unary.Relation.Binary.Subset

-- ANSI escape codes
import System.Console.ANSI

-- A simple tactic for used to automatically compute the function
-- argument to cong.
import Tactic.Cong

-- Reflection-based solver for monoid equalities
import Tactic.MonoidSolver

-- A solver that uses reflection to automatically obtain and solve
-- equations over rings.
import Tactic.RingSolver

-- Almost commutative rings
import Tactic.RingSolver.Core.AlmostCommutativeRing

-- A type for expressions over a raw ring.
import Tactic.RingSolver.Core.Expression

-- Simple implementation of sets of ℕ.
import Tactic.RingSolver.Core.NatSet

-- Sparse polynomials in a commutative ring, encoded in Horner normal
-- form.
import Tactic.RingSolver.Core.Polynomial.Base

-- Some specialised instances of the ring solver
import Tactic.RingSolver.Core.Polynomial.Homomorphism

-- Homomorphism proofs for addition over polynomials
import Tactic.RingSolver.Core.Polynomial.Homomorphism.Addition

-- Homomorphism proofs for constants over polynomials
import Tactic.RingSolver.Core.Polynomial.Homomorphism.Constants

-- Homomorphism proofs for exponentiation over polynomials
import Tactic.RingSolver.Core.Polynomial.Homomorphism.Exponentiation

-- Lemmas for use in proving the polynomial homomorphism.
import Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas

-- Homomorphism proofs for multiplication over polynomials
import Tactic.RingSolver.Core.Polynomial.Homomorphism.Multiplication

-- Homomorphism proofs for negation over polynomials
import Tactic.RingSolver.Core.Polynomial.Homomorphism.Negation

-- Homomorphism proofs for variables and constants over polynomials
import Tactic.RingSolver.Core.Polynomial.Homomorphism.Variables

-- Bundles of parameters for passing to the Ring Solver
import Tactic.RingSolver.Core.Polynomial.Parameters

-- Polynomial reasoning
import Tactic.RingSolver.Core.Polynomial.Reasoning

-- "Evaluating" a polynomial, using Horner's method.
import Tactic.RingSolver.Core.Polynomial.Semantics

-- An implementation of the ring solver that requires you to manually
-- pass the equation you wish to solve.
import Tactic.RingSolver.NonReflective

-- Format strings for Printf and Scanf
import Text.Format

-- Format strings for Printf and Scanf
import Text.Format.Generic

-- Printf
import Text.Printf

-- Generic printf function.
import Text.Printf.Generic

-- Regular expressions
import Text.Regex

-- Regular expressions: basic types and semantics
import Text.Regex.Base

-- Regular expressions: Brzozowski derivative
import Text.Regex.Derivative.Brzozowski

-- Properties of regular expressions and their semantics
import Text.Regex.Properties

-- Regular expressions: search algorithms
import Text.Regex.Search

-- Regular expressions: smart constructors
-- Computing the Brzozowski derivative of a regular expression may lead
-- to a blow-up in the size of the expression. To keep it tractable it
-- is crucial to use smart constructors.
import Text.Regex.SmartConstructors

-- Regular expressions acting on strings
import Text.Regex.String

-- Fancy display functions for List-based tables
import Text.Tabular.Base

-- Fancy display functions for List-based tables
import Text.Tabular.List

-- Fancy display functions for Vec-based tables
import Text.Tabular.Vec

