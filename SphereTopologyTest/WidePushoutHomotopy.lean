/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homotopy.CircleBouquet
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# A moving height homotopy on the countable circle bouquet

On every original circle the family is `t + Im(z)`, and the common-point
family is `t`. Descent gives a homotopy from the height map to its translate
by one. Both its circle dependence and its time dependence are nonconstant.
This is an unbased homotopy: the common point moves from zero to one.

The point-wedge setting follows J. Peter May, *A Concise Course in Algebraic
Topology*, Chapter 2, §8, p. 19. The based/unbased distinction is discussed
in Chapter 2, §4, p. 14. The height family is a separate construction, not a
fundamental-group computation or a contraction claim.
-/

noncomputable section

namespace SphereTopologyTest

private def circleHeight : C(Circle, ℝ) :=
  ⟨fun z ↦ (z : ℂ).im, Complex.continuous_im.comp continuous_subtype_val⟩

private def bouquetHeight : C(CircleBouquet.space.{0, 0} ℕ, ℝ) :=
  (CircleBouquet.desc.{0, 0} (Y := TopCat.of ℝ) 0 (fun _ ↦ circleHeight)
    (fun _ ↦ by simp [circleHeight])).hom

private theorem bouquetHeight_inclusion (i : ℕ) (z : Circle) :
    bouquetHeight (CircleBouquet.inclusion.{0, 0} i z) = (z : ℂ).im :=
  congrArg (fun a : C(Circle, ℝ) ↦ a z)
    (CircleBouquet.inclusion_desc.{0, 0} (Y := TopCat.of ℝ) 0 (fun _ ↦ circleHeight)
      (fun _ ↦ by simp [circleHeight]) i)

private theorem bouquetHeight_basepoint :
    bouquetHeight (CircleBouquet.basepoint.{0, 0} ℕ) = 0 :=
  CircleBouquet.desc_basepoint.{0, 0} (Y := TopCat.of ℝ) 0 (fun _ ↦ circleHeight)
    (fun _ ↦ by simp [circleHeight])

private def timeValue : C(unitInterval, ℝ) :=
  ⟨fun t ↦ t.val, continuous_subtype_val⟩

private def movingCircleHeight : C(unitInterval × Circle, ℝ) :=
  ⟨fun z ↦ (z.1 : ℝ) + (z.2 : ℂ).im,
    (continuous_subtype_val.comp continuous_fst).add
      (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd))⟩

private def heightTranslate : C(CircleBouquet.space.{0, 0} ℕ, ℝ) :=
  bouquetHeight + ContinuousMap.const (CircleBouquet.space.{0, 0} ℕ) (1 : ℝ)

private def heightHeadHomotopy : ContinuousMap.Homotopy
    (ContinuousMap.const PUnit.{1} (bouquetHeight (CircleBouquet.basepoint.{0, 0} ℕ)))
    (ContinuousMap.const PUnit.{1} (heightTranslate (CircleBouquet.basepoint.{0, 0} ℕ))) where
  toContinuousMap := timeValue.comp ContinuousMap.fst
  map_zero_left _ := by simp [timeValue, bouquetHeight_basepoint]
  map_one_left _ := by simp [timeValue, heightTranslate, bouquetHeight_basepoint]

private def heightFactorHomotopy (i : ℕ) : ContinuousMap.Homotopy
    (bouquetHeight.comp (CircleBouquet.inclusion.{0, 0} i))
    (heightTranslate.comp (CircleBouquet.inclusion.{0, 0} i)) where
  toContinuousMap := movingCircleHeight
  map_zero_left z := by simp [movingCircleHeight, bouquetHeight_inclusion]
  map_one_left z := by
    simp [movingCircleHeight, heightTranslate, bouquetHeight_inclusion, add_comm]

/-- Glue the moving head and nonconstant circle homotopies through the public
wide-pushout homotopy construction, without a fixed-common-point condition. -/
private def heightHomotopy : ContinuousMap.Homotopy bouquetHeight heightTranslate :=
  CircleBouquet.homotopy heightHeadHomotopy heightFactorHomotopy
    (fun _ t ↦ by
      change (t : ℝ) + ((1 : Circle) : ℂ).im = (t : ℝ)
      simp)

private def circleNorth : Circle :=
  ⟨Complex.I, mem_sphere_zero_iff_norm.mpr (by simp)⟩

/-- One use checks the two nonconstant directions: the common point moves
from zero to one, while the height on an original circle distinguishes one
from the unit imaginary point at time zero. -/
private theorem heightHomotopy_values :
    heightHomotopy (0, CircleBouquet.basepoint.{0, 0} ℕ) = 0 ∧
    heightHomotopy (1, CircleBouquet.basepoint.{0, 0} ℕ) = 1 ∧
    heightHomotopy (0, CircleBouquet.inclusion.{0, 0} 0 (1 : Circle)) = 0 ∧
    heightHomotopy (0, CircleBouquet.inclusion.{0, 0} 0 circleNorth) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (heightHomotopy.map_zero_left _).trans bouquetHeight_basepoint
  · simpa [heightTranslate, bouquetHeight_basepoint] using
      heightHomotopy.map_one_left (CircleBouquet.basepoint.{0, 0} ℕ)
  · exact (heightHomotopy.map_zero_left _).trans (by
      rw [bouquetHeight_inclusion]
      simp)
  · exact (heightHomotopy.map_zero_left _).trans (by
      rw [bouquetHeight_inclusion]
      simp [circleNorth])

end SphereTopologyTest
