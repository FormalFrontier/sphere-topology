/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

import SphereTopology.Homology.Singular.Circle

/-!
# Circle regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap

noncomputable section

namespace SphereTopologyTest

open SphereTopology

private theorem case001 : sphere1 =
    TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := rfl

private theorem case002 : circleEastPunctured ⊔ circleWestPunctured = ⊤ :=
  circlePunctured_join

private theorem case003 : circleWestPunctured ⊔ circleEastPunctured = ⊤ :=
  circlePunctured_join_reversed

private theorem case004 : eastPoint ≠ westPoint := eastPoint_ne_westPoint

private noncomputable def case005 :
    ((TopologicalSpace.Opens.toTopCat sphere1).obj circleEastPunctured : Type) ≃ₜ ℝ :=
  circleEastPuncturedHomeomorph

private noncomputable def case006 :
    ((TopologicalSpace.Opens.toTopCat sphere1).obj circleWestPunctured : Type) ≃ₜ ℝ :=
  circleWestPuncturedHomeomorph

private theorem case007 : ContractibleSpace
    ((TopologicalSpace.Opens.toTopCat sphere1).obj circleEastPunctured : Type) :=
  circleEastPunctured_contractibleSpace

private theorem case008 : ContractibleSpace
    ((TopologicalSpace.Opens.toTopCat sphere1).obj circleWestPunctured : Type) :=
  circleWestPunctured_contractibleSpace

private theorem case009 : IsZero (TopCat.reducedSingularHomology
    ((TopologicalSpace.Opens.toTopCat sphere1).obj circleEastPunctured) 0) :=
  isZero_reducedSingularHomology_circleEastPunctured 0

private theorem case010 : IsZero (TopCat.reducedSingularHomology
    ((TopologicalSpace.Opens.toTopCat sphere1).obj circleWestPunctured) 1) :=
  isZero_reducedSingularHomology_circleWestPunctured 1

private theorem case011 (p : circlePunctureIntersection) : (p.1.1 : E2) 1 ≠ 0 :=
  circlePunctureIntersection_second_ne_zero p

private theorem case012 (p : circlePunctureIntersection) :
    circlePunctureIntersectionComponent p = false ↔ 0 < (p.1.1 : E2) 1 :=
  circlePunctureIntersectionComponent_eq_false_iff p

private theorem case013 (p : circlePunctureIntersection) :
    circlePunctureIntersectionComponent p = true ↔ (p.1.1 : E2) 1 < 0 :=
  circlePunctureIntersectionComponent_eq_true_iff p

private theorem case014 : circlePunctureIntersectionComponent
    (circlePunctureIntersectionRepresentative false) = false := by simp

private theorem case015 : circlePunctureIntersectionComponent
    (circlePunctureIntersectionRepresentative true) = true := by simp

private theorem case016 : 0 < ((circlePunctureIntersectionRepresentative false).1.1 : E2) 1 := by
  norm_num

private theorem case017 : ((circlePunctureIntersectionRepresentative true).1.1 : E2) 1 < 0 := by
  norm_num

private theorem case018 (t : unitInterval) (p : circlePunctureIntersection) :
    circlePunctureIntersectionRadialVector t p ∈ Metric.sphere (0 : E2) 1 :=
  mem_sphere_zero_iff_norm.mpr (circlePunctureIntersectionRadialVector_norm t p)

private theorem case019 (p : circlePunctureIntersection) :
    circlePunctureIntersectionRadialPoint 0 p =
      circlePunctureIntersectionRepresentative
        (circlePunctureIntersectionComponent p) :=
  circlePunctureIntersectionRadialPoint_zero p

private theorem case020 (p : circlePunctureIntersection) :
    circlePunctureIntersectionRadialPoint 1 p = p :=
  circlePunctureIntersectionRadialPoint_one p

private noncomputable def case021 : circlePunctureIntersection ≃ₕ TopCat.twoPointSpace :=
  circlePunctureIntersectionHomotopyEquiv

private theorem case022 (p : circlePunctureIntersectionReversed) :
    circlePunctureIntersectionComponent
        (circlePunctureIntersectionSwapHomeomorph p) = false ↔
      0 < (p.1.1 : E2) 1 :=
  circlePunctureIntersectionReversedComponent_eq_false_iff p

private noncomputable def case023 :
    TopCat.reducedSingularHomology sphere1 1 ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularHomologyOneSphereOneIntegerIso

private noncomputable def case024 :
    TopCat.reducedSingularHomology sphere1 1 ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularHomologyOneSphereOneIntegerIsoReversed

private theorem case025 : reducedSingularHomologyOneSphereOneIntegerIso.hom =
    AlgebraicTopology.twoOpenReducedMayerVietorisδZero
      circleEastPunctured circleWestPunctured circlePunctured_join ≫
    (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
      circlePunctureIntersectionHomotopyEquiv 0).hom ≫
    TopCat.reducedSingularHomologyZeroTwoPointIntegerIso.hom :=
  reducedSingularHomologyOneSphereOneIntegerIso_hom

private theorem case026 :
    AlgebraicTopology.twoOpenReducedMayerVietorisδZero
        circleEastPunctured circleWestPunctured circlePunctured_join ≫
      TopCat.reducedSingularHomologyMap
        (AlgebraicTopology.twoOpenIntersectionSwapMap
          circleEastPunctured circleWestPunctured) 0 =
      -(AlgebraicTopology.twoOpenReducedMayerVietorisδZero
        circleWestPunctured circleEastPunctured circlePunctured_join_reversed) :=
  circleReducedMayerVietoris_swap_eq_neg

-- A genuine lifted-universe consumer of the geometric equivalence and the
-- arbitrary-universe reduced-homology transport API.
private noncomputable def case027 :
    TopCat.reducedSingularHomology
        (TopCat.of (ULift circlePunctureIntersection)) 0 ≅
      TopCat.reducedSingularHomology
        (TopCat.of (ULift TopCat.twoPointSpace)) 0 :=
  TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
    circlePunctureIntersectionHomotopyEquivULift 0

end SphereTopologyTest
