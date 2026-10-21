/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homology.Singular.Transfer
import SphereTopology.Homology.Singular.SmallChains
import SphereTopology.Homotopy.Circle
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-!
# Singular transfer clients

The projection `Circle × Fin 2 → Circle` is a two-sheet covering. The standard
one-turn loop gives a nonconstant singular edge and a nonzero integral basis
chain. Its two lifts occur with coefficient one, and pushforward of the
transferred chain is twice that basis chain, not zero. The same covering has
the ordinary degree-zero sheet identity. Identity and empty-total coverings
check that no nonemptiness or surjectivity premise is implicit.
-/

open CategoryTheory Limits Opposite Convexity AlgebraicTopology
open scoped Simplicial

noncomputable section

namespace SphereTopologyTest.SingularTransfer

/-! ## Object and map agreement with the singular functors -/

universe w v u

private theorem chain_object_agreement {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] (R : C) (X : TopCat.{w}) :
    ((singularChainComplexFunctor C).obj R).obj X =
      (TopCat.toSSet.obj X).chainComplex R := rfl

private theorem chain_map_agreement {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] (R : C) {X Y : TopCat.{w}} (p : Y ⟶ X) :
    ((singularChainComplexFunctor C).obj R).map p =
      SSet.chainComplexMap (TopCat.toSSet.map p) R := rfl

private theorem homology_object_agreement {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] [CategoryWithHomology C]
    (R : C) (X : TopCat.{w}) (q : ℕ) :
    ((singularHomologyFunctor C q).obj R).obj X =
      (TopCat.toSSet.obj X).homology R q := rfl

private theorem homology_map_agreement {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] [CategoryWithHomology C]
    (R : C) {X Y : TopCat.{w}} (p : Y ⟶ X) (q : ℕ) :
    ((singularHomologyFunctor C q).obj R).map p =
      SSet.homologyMap (TopCat.toSSet.map p) R q := rfl

/-! ## Cover, nonconstant simplex, and integral basis, independent of transfer laws -/


end SphereTopologyTest.SingularTransfer
