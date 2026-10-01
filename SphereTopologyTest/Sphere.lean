/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

import SphereTopology.Homology.Singular.Sphere

/-!
# Sphere regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open CategoryTheory CategoryTheory.Limits ContinuousMap

noncomputable section

namespace SphereTopologyTest

open SphereTopology

private theorem case001 : sphere2NorthPoint ≠ sphere2SouthPoint :=
  sphere2NorthPoint_ne_southPoint

private theorem case002 : sphere2NorthPunctured ⊔ sphere2SouthPunctured = ⊤ :=
  sphere2Punctured_join

private theorem case003 : sphere2SouthPunctured ⊔ sphere2NorthPunctured = ⊤ :=
  sphere2Punctured_join_reversed

private noncomputable def case004 :
    ((TopologicalSpace.Opens.toTopCat sphere2).obj
      sphere2NorthPunctured : Type) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  sphere2NorthPuncturedHomeomorph

private noncomputable def case005 :
    ((TopologicalSpace.Opens.toTopCat sphere2).obj
      sphere2SouthPunctured : Type) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  sphere2SouthPuncturedHomeomorph

private theorem case006 : ContractibleSpace
    ((TopologicalSpace.Opens.toTopCat sphere2).obj
      sphere2NorthPunctured : Type) :=
  sphere2NorthPunctured_contractibleSpace

private theorem case007 : ContractibleSpace
    ((TopologicalSpace.Opens.toTopCat sphere2).obj
      sphere2SouthPunctured : Type) :=
  sphere2SouthPunctured_contractibleSpace

private theorem case008 (n : ℕ) : IsZero (TopCat.reducedSingularHomology
    ((TopologicalSpace.Opens.toTopCat sphere2).obj
      sphere2NorthPunctured) n) :=
  isZero_reducedSingularHomology_sphere2NorthPunctured n

private theorem case009 (n : ℕ) : IsZero (TopCat.reducedSingularHomology
    ((TopologicalSpace.Opens.toTopCat sphere2).obj
      sphere2SouthPunctured) n) :=
  isZero_reducedSingularHomology_sphere2SouthPunctured n

private theorem case010 (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionRadialPoint 0 p =
      sphere2EquatorToPunctureIntersection
        (sphere2PunctureIntersectionToEquator p) :=
  sphere2PunctureIntersectionRadialPoint_zero p

private theorem case011 (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionRadialPoint 1 p = p :=
  sphere2PunctureIntersectionRadialPoint_one p

private theorem case012 (t : unitInterval) (p : sphere2Equator) :
    sphere2PunctureIntersectionRadialPoint t
      (sphere2EquatorToPunctureIntersection p) =
      sphere2EquatorToPunctureIntersection p :=
  sphere2PunctureIntersectionRadialPoint_fixed t p

private theorem case013 (p : sphere2Equator) :
    sphere2PunctureIntersectionToEquator
      (sphere2EquatorToPunctureIntersection p) = p :=
  sphere2PunctureIntersectionToEquator_inclusion p

private noncomputable def case014 : sphere2PunctureIntersection ≃ₕ sphere2Equator :=
  sphere2PunctureIntersectionEquatorHomotopyEquiv

private noncomputable def case015 : sphere2Equator ≃ₜ (sphere1 : Type) :=
  sphere2EquatorHomeomorphSphere1

private theorem case016 (p : sphere2Equator) :
    ((sphere2EquatorHomeomorphSphere1 p : sphere1).1 : E2) 0 =
      (p.1.1 : E3) 0 := by
  rfl

private theorem case017 (p : sphere2Equator) :
    ((sphere2EquatorHomeomorphSphere1 p : sphere1).1 : E2) 1 =
      (p.1.1 : E3) 1 := by
  rfl

private noncomputable def case018 : sphere2PunctureIntersection ≃ₕ (sphere1 : Type) :=
  sphere2PunctureIntersectionSphere1HomotopyEquiv

private theorem case019 : IsIso (AlgebraicTopology.twoOpenMayerVietorisδ
    sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1) :=
  sphere2MayerVietorisδOne_isIso

-- The reversed order is a genuine acyclic-cover consumer as well.
private theorem case020 : IsIso (AlgebraicTopology.twoOpenMayerVietorisδ
    sphere2SouthPunctured sphere2NorthPunctured
      sphere2Punctured_join_reversed 1) := by
  have hN₁ : IsZero (AlgebraicTopology.integralSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured) 1) :=
    (isZero_reducedSingularHomology_sphere2NorthPunctured 1).of_iso
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured)
        1 (by simp)).symm
  have hS₁ : IsZero (AlgebraicTopology.integralSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured) 1) :=
    (isZero_reducedSingularHomology_sphere2SouthPunctured 1).of_iso
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured)
        1 (by simp)).symm
  have hN₂ : IsZero (AlgebraicTopology.integralSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured) 2) :=
    (isZero_reducedSingularHomology_sphere2NorthPunctured 2).of_iso
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured)
        2 (by simp)).symm
  have hS₂ : IsZero (AlgebraicTopology.integralSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured) 2) :=
    (isZero_reducedSingularHomology_sphere2SouthPunctured 2).of_iso
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured)
        2 (by simp)).symm
  exact AlgebraicTopology.twoOpenMayerVietorisδ_isIso_of_isZero_outer
    sphere2SouthPunctured sphere2NorthPunctured sphere2Punctured_join_reversed 1
    ((biprod_isZero_iff _ _).2 ⟨hS₂, hN₂⟩)
    ((biprod_isZero_iff _ _).2 ⟨hS₁, hN₁⟩)

private noncomputable def case021 :
    TopCat.reducedSingularHomology sphere2 2 ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularHomologyTwoSphereTwoIntegerIso

private theorem case022 : reducedSingularHomologyTwoSphereTwoIntegerIso.hom =
    (TopCat.reducedSingularHomologyIsoOfNeZero sphere2 2 (by simp)).hom ≫
    AlgebraicTopology.twoOpenMayerVietorisδ
      sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1 ≫
    (AlgebraicTopology.twoOpenIntersectionHomologyIso
      sphere2NorthPunctured sphere2SouthPunctured 1).inv ≫
    (TopCat.reducedSingularHomologyIsoOfNeZero
      ((TopologicalSpace.Opens.toTopCat sphere2).obj
        (sphere2NorthPunctured ⊓ sphere2SouthPunctured)) 1
      (by simp)).inv ≫
    (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
      sphere2PunctureIntersectionSphere1HomotopyEquiv 1).hom ≫
    reducedSingularHomologyOneSphereOneIntegerIso.hom :=
  reducedSingularHomologyTwoSphereTwoIntegerIso_hom_explicit

-- A genuine lifted-universe reduced-homology transport client.
private noncomputable def case023 :
    TopCat.reducedSingularHomology
        (TopCat.of (ULift sphere2PunctureIntersection)) 1 ≅
      TopCat.reducedSingularHomology
        (TopCat.of (ULift sphere2Equator)) 1 :=
  TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
    sphere2PunctureIntersectionEquatorHomotopyEquivULift 1

end SphereTopologyTest
