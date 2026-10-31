/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homotopy.Disk
import Mathlib.Tactic.NormNum

/-!
# Boundary images without an interior image bound

On the complex closed unit disk, the continuous map
`z ↦ ((2 * (1 - ‖(z : ℂ)‖) : ℝ) : ℂ)` vanishes on the sphere boundary,
but takes the value `2` at zero, outside the disk. Thus the boundary-image
hypothesis of `Complex.exists_fixedPoint_closedBall_of_boundary_mapsTo` does
not require a closed-ball self-map.
-/

noncomputable section

namespace SphereTopologyTest

local notation "B" => Metric.closedBall (0 : ℂ) 1

@[simps]
private def radialBump : C(B, ℂ) where
  toFun z := ((2 * (1 - ‖(z : ℂ)‖) : ℝ) : ℂ)
  continuous_toFun :=
    Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_const.sub continuous_subtype_val.norm))

private def zeroPoint : B :=
  ⟨0, Metric.mem_closedBall_self zero_le_one⟩

/-- The boundary-image condition allows this map, although its value at zero
lies outside the closed unit disk. -/
private theorem radialBump_boundary_only :
    (∀ y : Metric.sphere (0 : ℂ) 1,
      radialBump ((ContinuousMap.inclusion
        (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1)) :
          C(Metric.sphere (0 : ℂ) 1, B)) y) ∈ B) ∧
    radialBump zeroPoint = (2 : ℂ) ∧ radialBump zeroPoint ∉ B := by
  have hvalue : radialBump zeroPoint = (2 : ℂ) := by
    norm_num [radialBump_apply, zeroPoint]
  refine ⟨?_, hvalue, ?_⟩
  · intro y
    have hy : ‖(y : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
    rw [radialBump_apply]
    change ((2 * (1 - ‖(y : ℂ)‖) : ℝ) : ℂ) ∈ B
    simpa only [hy, sub_self, mul_zero, Complex.ofReal_zero] using
      (Metric.mem_closedBall_self (x := (0 : ℂ)) zero_le_one)
  · rw [hvalue, mem_closedBall_zero_iff]
    norm_num

end SphereTopologyTest
