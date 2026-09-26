/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism; earlier client expression is credited in README.md.
module

import SphereTopology

/-!
# Ordinary aggregate-import clients

These private consumers use only the advertised ordinary root import. They test
actual conclusions, data interfaces, empty cases and literal sphere models. The
existing focused clients separately retain the full ordered-cover and universe
regressions. No source repository is a dependency of this library.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped RealInnerProductSpace
open AlgebraicTopology SphereTopology

namespace SphereTopologyPublicClient

universe u

private theorem normalize {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : C(X, E)) (hV : ∀ x, V x ≠ 0) (x : X) :
    ‖ContinuousMap.normalizeOfNoZero V hV x‖ = 1 := by
  simp

private noncomputable def orthogonalHomotopy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : C(Metric.sphere (0 : E) 1, E))
    (hV : ∀ p, V p ≠ 0) (hOrth : ∀ p, inner ℝ p.1 (V p) = 0) :
    ContinuousMap.Homotopy (ContinuousMap.id (Metric.sphere (0 : E) 1))
      (Metric.Sphere.antipodal (E := E)) :=
  Metric.Sphere.homotopyAntipodalOfNowhereZeroOrthogonal V hV hOrth

private theorem subdivisionZero (X : TopCat) (c : SingularChainFinsupp X 0) :
    singularSubdivision X 0 c = c :=
  singularSubdivision_degree_zero X c

private theorem subdivisionBoundary (X : TopCat) (n : ℕ)
    (c : SingularChainFinsupp X (n + 1)) :
    singularFinsuppBoundary X n (singularSubdivision X (n + 1) c) =
      singularSubdivision X n (singularFinsuppBoundary X n c) :=
  singularSubdivision_boundary X n c

private theorem coverInclusion {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) (hU : IsOpenCover U) :
    QuasiIso (smallSingularChainInclusion U) :=
  quasiIso_smallSingularChainInclusion U hU

private theorem emptyCover :
    let X : TopCat := TopCat.of Empty
    let U : Empty → Opens X := Empty.elim
    QuasiIso (smallSingularChainInclusion U) := by
  dsimp
  apply quasiIso_smallSingularChainInclusion
  rw [IsOpenCover]
  ext x
  exact x.elim

private noncomputable def reducedConnecting {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    TopCat.reducedSingularHomology X 1 ⟶
      TopCat.reducedSingularHomology ((Opens.toTopCat X).obj (U ⊓ V)) 0 :=
  twoOpenReducedMayerVietorisδZero U V hUV

private theorem emptyReducedZero :
    IsZero (TopCat.reducedSingularHomology TopCat.emptySpace 0) :=
  TopCat.isZero_reducedSingularHomologyZero_empty

private theorem disconnectedPathEndpoints {X : Type*} [TopologicalSpace X]
    [TotallyDisconnectedSpace X] {x y : X} (p : Path x y) : x = y :=
  TopCat.path_endpoints_eq_of_totallyDisconnected p

private theorem circleModel :
    sphere1 = TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := rfl

private theorem sphereModel :
    sphere2 = TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := rfl

private noncomputable def circleHomology :
    TopCat.reducedSingularHomology sphere1 1 ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularHomologyOneSphereOneIntegerIso

private noncomputable def sphereHomology :
    TopCat.reducedSingularHomology sphere2 2 ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularHomologyTwoSphereTwoIntegerIso

private theorem antipodalAction :
    TopCat.reducedSingularHomologyMap sphere2Antipodal 2 = -𝟙 _ :=
  reducedSingularHomologyMap_sphere2Antipodal_two

private theorem antipodalCoordinate :
    reducedSingularHomologyTwoSphereTwoIntegerIso.inv ≫
      TopCat.reducedSingularHomologyMap sphere2Antipodal 2 ≫
      reducedSingularHomologyTwoSphereTwoIntegerIso.hom =
    -𝟙 (ModuleCat.of ℤ ℤ) :=
  reducedSingularHomologyTwoSphereTwoIntegerIso_antipodal

private theorem nonhomotopy :
    ¬ ContinuousMap.Homotopic (ContinuousMap.id sphere2) sphere2Antipodal.hom :=
  sphere2_id_not_homotopic_antipodal

private theorem hairyBall (V : C(sphere2, E3))
    (hOrth : ∀ p, inner ℝ p.1 (V p) = 0) : ∃ p, V p = 0 :=
  sphere2_exists_zero_of_orthogonal_field V hOrth

-- The concrete bundling/model step used by the accepted downstream source adapter.
private theorem unbundledField
    (V : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (hContinuous : Continuous V) (hOrth : ∀ p, inner ℝ p.1 (V p) = 0) :
    ∃ p, V p = 0 := by
  let bundled : C(sphere2, E3) := ⟨V, hContinuous⟩
  obtain ⟨p, hp⟩ := sphere2_exists_zero_of_orthogonal_field bundled hOrth
  exact ⟨p, hp⟩

private theorem zeroField : ∃ p : sphere2, (ContinuousMap.const sphere2 (0 : E3)) p = 0 := by
  apply sphere2_exists_zero_of_orthogonal_field (ContinuousMap.const sphere2 (0 : E3))
  intro p
  simp

end SphereTopologyPublicClient
