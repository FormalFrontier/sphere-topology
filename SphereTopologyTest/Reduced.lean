/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

import SphereTopology.Homology.Singular.Reduced
import Mathlib.Analysis.Convex.Contractible

/-!
# Reduced regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace SphereTopologyTest

universe u

private theorem case001 {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (AlgebraicTopology.integralSingularHomologyFunctor 0).map f ≫
        Y.singularHomology₀ε AlgebraicTopology.integerCoefficients =
      X.singularHomology₀ε AlgebraicTopology.integerCoefficients :=
  TopCat.singularHomologyZeroAugmentation_naturality f

private theorem case002 {X Y : TopCat.{u}} (f : X ⟶ Y) :
    TopCat.reducedSingularHomologyZeroMap f ≫
        TopCat.reducedSingularHomologyZeroι Y =
      TopCat.reducedSingularHomologyZeroι X ≫
        (AlgebraicTopology.integralSingularHomologyFunctor 0).map f := by
  simp

private theorem case003 (X : TopCat.{u}) :
    TopCat.reducedSingularHomologyZeroMap (𝟙 X) = 𝟙 _ := by
  simp

private theorem case004 {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.reducedSingularHomologyZeroMap (f ≫ g) =
      TopCat.reducedSingularHomologyZeroMap f ≫
        TopCat.reducedSingularHomologyZeroMap g :=
  TopCat.reducedSingularHomologyZeroMap_comp f g

private theorem case005 {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    TopCat.reducedSingularHomologyZeroMap f =
      TopCat.reducedSingularHomologyZeroMap g :=
  TopCat.reducedSingularHomologyZeroMap_eq_of_homotopy H

private theorem case006 {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (n : ℕ) :
    TopCat.reducedSingularHomologyMap f n =
      TopCat.reducedSingularHomologyMap g n :=
  TopCat.reducedSingularHomologyMap_eq_of_homotopy H n

private noncomputable def case007 (X : TopCat.{u}) :
    TopCat.reducedSingularHomology X 0 ≅
      TopCat.reducedSingularHomologyZero X :=
  TopCat.reducedSingularHomologyZeroIso X

private noncomputable def case008 (X : TopCat.{u}) (n : ℕ) :
    TopCat.reducedSingularHomology X (n + 1) ≅
      AlgebraicTopology.integralSingularHomology X (n + 1) :=
  TopCat.reducedSingularHomologyIsoOfNeZero X (n + 1) (Nat.succ_ne_zero n)

private theorem case009 {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    TopCat.reducedSingularHomologyMap f (n + 1) ≫
        (TopCat.reducedSingularHomologyIsoOfNeZero Y (n + 1)
          (Nat.succ_ne_zero n)).hom =
      (TopCat.reducedSingularHomologyIsoOfNeZero X (n + 1)
          (Nat.succ_ne_zero n)).hom ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.integralSingularChainMap f) (n + 1) :=
  TopCat.reducedSingularHomologyMap_isoOfNeZero f (n + 1) (Nat.succ_ne_zero n)

private theorem case010 : IsZero
    (TopCat.reducedSingularHomologyZero TopCat.emptySpace.{u}) :=
  TopCat.isZero_reducedSingularHomologyZero_empty

private theorem case011 (n : ℕ) :
    IsZero (TopCat.reducedSingularHomology TopCat.onePointSpace.{u} n) :=
  TopCat.isZero_reducedSingularHomology_onePoint n

private theorem case012 :
    IsZero (TopCat.reducedSingularHomologyZero (TopCat.of ℝ)) :=
  TopCat.isZero_reducedSingularHomologyZero_of_contractible (TopCat.of ℝ)

private theorem case013 :
    TopCat.twoPointReducedBasis ≫
        TopCat.reducedSingularHomologyZeroι TopCat.twoPointSpace =
      TopCat.singularHomologyZeroPoint TopCat.twoPointSpace false -
        TopCat.singularHomologyZeroPoint TopCat.twoPointSpace true := by
  simp [TopCat.twoPointReducedBasisClass]

private noncomputable def case014 :
    TopCat.reducedSingularHomologyZero TopCat.twoPointSpace ≅ ModuleCat.of ℤ ℤ :=
  TopCat.reducedSingularHomologyZeroTwoPointIntegerIso

private theorem case015 :
    TopCat.reducedSingularHomologyZeroTwoPointIntegerIso.inv ≫
        TopCat.reducedSingularHomologyZeroMap TopCat.twoPointSwap ≫
        TopCat.reducedSingularHomologyZeroTwoPointIntegerIso.hom =
      -(𝟙 (ModuleCat.of ℤ ℤ)) :=
  TopCat.reducedSingularHomologyZeroTwoPointIntegerIso_swap

private theorem case016 :
    TopCat.reducedSingularHomologyZeroTwoPointIso.inv ≫
        TopCat.reducedSingularHomologyZeroMap (𝟙 TopCat.twoPointSpace) ≫
        TopCat.reducedSingularHomologyZeroTwoPointIso.hom =
      𝟙 TopCat.singularHomologyIntegerCoefficients :=
  TopCat.reducedSingularHomologyZeroTwoPointIso_id

end SphereTopologyTest
