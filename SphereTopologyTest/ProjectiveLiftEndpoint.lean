/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Geometry.Projectivization
import SphereTopology.Homotopy.Sphere
import FundamentalGroupoids.Topology.Covering.Monodromy
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A projective loop from three faces of a cube

The product space `ℝ × (ℝ × ℝ)` carries its product maximum norm. Three face
segments join `(1, (0, 0))` to its antipode on the unit sphere. Their projection
to real projective space is a based loop. Covering-lift uniqueness identifies
these segments with the lift of that loop, whose endpoint is the antipode.
Monodromy then distinguishes the loop's fundamental-group class from the identity,
without a projective fundamental-group classification. A separate cardinal-rank
computation verifies the rank-greater-than-two hypothesis for this space.

The Euclidean equatorial rotation is already supplied by
`SphereTopology.sphere2EquatorHalfTurnHomotopy` in
`SphereTopology.Homology.Singular.SphereAntipodal`; this example instead concerns
the product maximum norm.

## References

* Mathlib's product norm, path, dimension and covering-lift APIs.
* Fundamental Groupoids, `FundamentalGroupoids.Topology.Covering.Monodromy`,
  for the endpoint characterization of monodromy on a represented path.
-/

@[expose] public section

noncomputable section

namespace SphereTopologyTest.ProjectiveLiftEndpoint

private abbrev CubeSpace := ℝ × (ℝ × ℝ)

private abbrev CubeSphere := Metric.sphere (0 : CubeSpace) 1

private def pole : CubeSphere :=
  ⟨(1, (0, 0)), mem_sphere_zero_iff_norm.mpr (by norm_num [Prod.norm_mk])⟩

private def firstCorner : CubeSphere :=
  ⟨(1, (1, 0)), mem_sphere_zero_iff_norm.mpr (by norm_num [Prod.norm_mk])⟩

private def secondCorner : CubeSphere :=
  ⟨(-1, (1, 0)), mem_sphere_zero_iff_norm.mpr (by norm_num [Prod.norm_mk])⟩

private theorem firstFace_mem (t : unitInterval) :
    (1, ((t : ℝ), 0)) ∈ Metric.sphere (0 : CubeSpace) 1 := by
  apply mem_sphere_zero_iff_norm.mpr
  rw [Prod.norm_mk, Prod.norm_mk, norm_one, norm_zero,
    Real.norm_of_nonneg t.2.1, max_eq_left t.2.1, max_eq_left t.2.2]

private theorem middleFace_mem (t : unitInterval) :
    (1 - 2 * (t : ℝ), (1, 0)) ∈ Metric.sphere (0 : CubeSpace) 1 := by
  have hcoord : |1 - 2 * (t : ℝ)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [t.2.1, t.2.2]
  apply mem_sphere_zero_iff_norm.mpr
  rw [Prod.norm_mk, Prod.norm_mk, norm_one, norm_zero,
    max_eq_left zero_le_one, Real.norm_eq_abs, max_eq_right hcoord]

private theorem lastFace_mem (t : unitInterval) :
    (-1, (1 - (t : ℝ), 0)) ∈ Metric.sphere (0 : CubeSpace) 1 := by
  have hcoord₀ : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  have hcoord₁ : 1 - (t : ℝ) ≤ 1 := sub_le_self _ t.2.1
  apply mem_sphere_zero_iff_norm.mpr
  rw [Prod.norm_mk, Prod.norm_mk, norm_neg, norm_one, norm_zero,
    Real.norm_of_nonneg hcoord₀, max_eq_left hcoord₀, max_eq_left hcoord₁]

private def firstFace : Path pole firstCorner where
  toFun t := ⟨(1, ((t : ℝ), 0)), firstFace_mem t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk (continuous_subtype_val.prodMk continuous_const)
  source' := by
    apply Subtype.ext
    norm_num [pole]
  target' := by
    apply Subtype.ext
    norm_num [firstCorner]

private def middleFace : Path firstCorner secondCorner where
  toFun t := ⟨(1 - 2 * (t : ℝ), (1, 0)), middleFace_mem t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.sub (continuous_const.mul continuous_subtype_val)).prodMk
      (continuous_const.prodMk continuous_const)
  source' := by
    apply Subtype.ext
    norm_num [firstCorner]
  target' := by
    apply Subtype.ext
    norm_num [secondCorner]

private def lastFace : Path secondCorner (-pole) where
  toFun t := ⟨(-1, (1 - (t : ℝ), 0)), lastFace_mem t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk
      ((continuous_const.sub continuous_subtype_val).prodMk continuous_const)
  source' := by
    apply Subtype.ext
    norm_num [secondCorner]
  target' := by
    apply Subtype.ext
    norm_num [pole]

private def antipodalPath : Path pole (-pole) :=
  (firstFace.trans middleFace).trans lastFace

private abbrev projection : C(CubeSphere, Projectivization ℝ CubeSpace) :=
  Metric.Sphere.toProjectivization

private theorem covering : IsCoveringMap projection :=
  (Metric.Sphere.isQuotientCoveringMap_toProjectivization (E := CubeSpace)).isCoveringMap

private def projectedLoop : Path (projection pole) (projection pole) :=
  (antipodalPath.map projection.continuous).cast rfl
    (Metric.Sphere.toProjectivization_neg pole).symm

private theorem projection_antipodalPath :
    projection ∘ antipodalPath = (projectedLoop : unitInterval → Projectivization ℝ CubeSpace) :=
  rfl

private theorem antipodalPath_eq_liftPath :
    antipodalPath.toContinuousMap =
      covering.liftPath projectedLoop.toContinuousMap pole projectedLoop.source :=
  (covering.eq_liftPath_iff' projectedLoop.source).mpr
    ⟨projection_antipodalPath, antipodalPath.source⟩

private theorem liftPath_endpoint :
    covering.liftPath projectedLoop.toContinuousMap pole projectedLoop.source 1 = -pole := by
  rw [← antipodalPath_eq_liftPath]
  exact antipodalPath.target

private def projectedClass : FundamentalGroup (Projectivization ℝ CubeSpace) (projection pole) :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk projectedLoop)

private theorem projectedClass_ne_one : projectedClass ≠ 1 := by
  intro h
  have hend := covering.monodromy_mk_apply_eq_of_lift projectedLoop
    (⟨pole, rfl⟩ : projection ⁻¹' {projection pole})
    antipodalPath.toContinuousMap projection_antipodalPath antipodalPath.source
  change (covering.monodromy projectedClass
    (⟨pole, rfl⟩ : projection ⁻¹' {projection pole}) : CubeSphere) = antipodalPath 1 at hend
  rw [h, FundamentalGroup.one_def, covering.monodromy_refl] at hend
  exact (ne_neg_of_mem_unit_sphere ℝ pole) (hend.trans antipodalPath.target)

private theorem rank_cubeSpace : Module.rank ℝ CubeSpace = 3 := by
  simp only [CubeSpace, rank_prod', CommSemiring.rank_self]
  norm_num

private theorem two_lt_rank_cubeSpace : 2 < Module.rank ℝ CubeSpace := by
  rw [rank_cubeSpace]
  norm_num

private theorem simplyConnected_cubeSphere : SimplyConnectedSpace CubeSphere :=
  simplyConnectedSpace_unitSphere two_lt_rank_cubeSpace

end SphereTopologyTest.ProjectiveLiftEndpoint
