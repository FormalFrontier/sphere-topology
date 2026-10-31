/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Geometry.ForwardRayMap
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# A forward-ray map for a real translation

The ambient translation `F(x) = x + 1` on the closed unit ball in `ℝ` is
continuous and avoids the inclusion. Its forward-ray sphere map takes zero to
`-1`. This is not retraction data: at the boundary point `1`, the image `F(1) = 2`
lies outside the ball, so no boundary-image condition is asserted.
-/

noncomputable section

namespace SphereTopologyTest

local notation "B" => Metric.closedBall (0 : ℝ) 1

private def translation : C(B, ℝ) :=
  ContinuousMap.subtypeVal B + ContinuousMap.const B 1

private theorem translation_ne (x : B) : translation x ≠ (x : ℝ) :=
  ne_of_gt (lt_add_one (x : ℝ))

private def zeroPoint : B :=
  ⟨0, Metric.mem_closedBall_self zero_le_one⟩

private def translationRayMap : C(B, Metric.sphere (0 : ℝ) 1) :=
  (⟨0, 1⟩ : EuclideanGeometry.Sphere ℝ).rayInterMap translation translation_ne

private theorem translationRayMap_zero : (translationRayMap zeroPoint : ℝ) = -1 := by
  rw [translationRayMap, EuclideanGeometry.Sphere.coe_rayInterMap_apply,
    EuclideanGeometry.Sphere.rayInter_eq_smul_vsub_vadd,
    EuclideanGeometry.Sphere.rayInterParameter_eq]
  norm_num [translation, zeroPoint, vsub_eq_sub, vadd_eq_add, Real.inner_apply, smul_eq_mul]

end SphereTopologyTest
