/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

import SphereTopology.Homology.Singular.SphereAntipodal

/-!
# SphereAntipodal regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace SphereTopologyTest

open SphereTopology

universe u

private theorem case001 : sphere2Antipodal sphere2NorthPoint = sphere2SouthPoint :=
  sphere2Antipodal_north

private theorem case002 : sphere2Antipodal sphere2SouthPoint = sphere2NorthPoint :=
  sphere2Antipodal_south

private theorem case003 : Set.MapsTo sphere2Antipodal sphere2NorthPunctured
    sphere2SouthPunctured :=
  sphere2Antipodal_mapsTo_north_south

private theorem case004 : Set.MapsTo sphere2Antipodal sphere2SouthPunctured
    sphere2NorthPunctured :=
  sphere2Antipodal_mapsTo_south_north

private theorem case005 : sphere2PunctureIntersectionAntipodalInduced =
    TopCat.ofHom sphere2PunctureIntersectionAntipodal :=
  sphere2PunctureIntersectionAntipodalInduced_eq

private theorem case006 : ContinuousMap.Homotopic sphere2PunctureIntersectionAntipodal
    (ContinuousMap.id sphere2PunctureIntersection) :=
  sphere2PunctureIntersectionAntipodal_homotopic_id

private theorem case007 : IsIso (AlgebraicTopology.twoOpenMayerVietorisδ
    sphere2SouthPunctured sphere2NorthPunctured
    sphere2Punctured_join_reversed 1) :=
  sphere2MayerVietorisδOne_reversed_isIso

private theorem case008 : HomologicalComplex.homologyMap
      (AlgebraicTopology.integralSingularChainMap sphere2Antipodal) 2 =
    -𝟙 _ :=
  integralSingularHomologyMap_sphere2Antipodal_two

private theorem case009 : TopCat.reducedSingularHomologyMap sphere2Antipodal 2 = -𝟙 _ :=
  reducedSingularHomologyMap_sphere2Antipodal_two

private theorem case010 : reducedSingularHomologyTwoSphereTwoIntegerIso.inv ≫
      TopCat.reducedSingularHomologyMap sphere2Antipodal 2 ≫
      reducedSingularHomologyTwoSphereTwoIntegerIso.hom =
    -𝟙 (ModuleCat.of ℤ ℤ) :=
  reducedSingularHomologyTwoSphereTwoIntegerIso_antipodal

private theorem case011 : ¬ ContinuousMap.Homotopic (ContinuousMap.id sphere2)
    sphere2Antipodal.hom :=
  sphere2_id_not_homotopic_antipodal

/-- The generic theorem can be instantiated on the degenerate ordered cover,
but only with its explicit transported-intersection identity and mono
hypotheses; neither condition is silently inferred. -/
private theorem case012 {X : TopCat.{u}} (n : ℕ)
    (hTransport :
      HomologicalComplex.homologyMap
          (AlgebraicTopology.integralSingularChainMap
            (AlgebraicTopology.twoOpenIntersectionMap (𝟙 X)
              (⊤ : TopologicalSpace.Opens X) ⊤ ⊤ ⊤
              (by simp) (by simp))) n ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.integralSingularChainMap
            (AlgebraicTopology.twoOpenIntersectionSwapMap
              (⊤ : TopologicalSpace.Opens X) ⊤)) n = 𝟙 _)
    [Mono (AlgebraicTopology.twoOpenMayerVietorisδ
      (⊤ : TopologicalSpace.Opens X) ⊤ (by simp) n)] :
    HomologicalComplex.homologyMap
        (AlgebraicTopology.integralSingularChainMap (𝟙 X)) (n + 1) =
      -𝟙 _ := by
  exact
    AlgebraicTopology.integralSingularHomologyMap_eq_neg_id_of_twoOpen_swap
      (f := 𝟙 X) (U := ⊤) (V := ⊤)
      (hU := by simp) (hV := by simp)
      (hUV := sup_idem (⊤ : TopologicalSpace.Opens X))
      (hVU := sup_idem (⊤ : TopologicalSpace.Opens X))
      (n := n) hTransport

end SphereTopologyTest
