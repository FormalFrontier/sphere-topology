/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homotopy.Circle

/-!
# Standard circle fundamental-group coordinates and the zero-period boundary

The period-one example is the complex unit circle with its counterclockwise
one-turn loop, not a constant path. Negative periods keep the signed generator
normalization. The zero-period example explains the nonzero hypothesis.

The models and lifting constructions come from Mathlib; the positive loop and
endpoint convention follow J. Peter May, *A Concise Course in Algebraic Topology*,
Chapter 1, §5, pp. 8–9.
-/

noncomputable section

open scoped unitInterval

namespace SphereTopologyTest

/-- At period one the prescribed generator is nonidentity and its complex image is
exactly the counterclockwise loop from May's circle calculation. -/
private theorem period_one_generator :
    FundamentalGroup.fromPath ⟦AddCircle.loop 1 1⟧ ≠
        (1 : FundamentalGroup (AddCircle (1 : ℝ)) 0) ∧
      (∀ t : I, (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
          (AddCircle.loop 1 1 t) : ℂ) =
        Complex.exp ((2 * Real.pi * (t : ℝ) : ℝ) * Complex.I)) ∧
      Circle.fundamentalGroupEquivInt (FundamentalGroup.fromPath ⟦Circle.loop 1⟧) =
        Multiplicative.ofAdd (1 : ℤ) := by
  refine ⟨AddCircle.loop_one_ne_one one_ne_zero, ?_,
    Circle.fundamentalGroupEquivInt_loop 1⟩
  intro t
  rw [AddCircle.homeomorphCircle_loop one_ne_zero]
  simpa only [Int.cast_one, mul_one] using Circle.coe_loop_apply 1 t

/-- The negative-period signed generator has a decreasing real lift but positive
integer coordinate, and its signed-period complex image is still counterclockwise. -/
private theorem negative_period_generator :
    (AddCircle.fundamentalGroupEquivInt (T := (-1 : ℝ)) (neg_ne_zero.mpr one_ne_zero)
        (FundamentalGroup.fromPath ⟦AddCircle.loop (-1) 1⟧)).toAdd = 1 ∧
      (∀ t : I, (AddCircle.isCoveringMap_coe (-1 : ℝ)).liftPath
          (AddCircle.loop (-1) 1).toContinuousMap 0 (AddCircle.loop (-1) 1).source t =
        -(t : ℝ)) ∧
      (∀ t : I, AddCircle.homeomorphCircle (neg_ne_zero.mpr one_ne_zero)
        (AddCircle.loop (-1) 1 t) = Circle.loop 1 t) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [AddCircle.fundamentalGroupEquivInt_loop, toAdd_ofAdd]
  · intro t
    rw [AddCircle.liftPath_loop]
    simp [Path.segment_apply, AffineMap.lineMap_apply_ring]
  · exact fun t ↦ AddCircle.homeomorphCircle_loop (neg_ne_zero.mpr one_ne_zero) 1 t

/-- Clockwise traversal has negative rather than positive coordinate. -/
private theorem clockwise_generator :
    (Circle.fundamentalGroupEquivInt
      (FundamentalGroup.fromPath ⟦Circle.loop (-1)⟧)).toAdd = -1 ∧
      FundamentalGroup.fromPath ⟦Circle.loop (-1)⟧ =
        (FundamentalGroup.fromPath ⟦Circle.loop 1⟧)⁻¹ := by
  constructor
  · simp only [Circle.fundamentalGroupEquivInt_loop, toAdd_ofAdd]
  · apply Circle.fundamentalGroupEquivInt.injective
    simpa only [map_inv, Circle.fundamentalGroupEquivInt_loop] using ofAdd_neg (1 : ℤ)

/-- The zero-period covering still exists, but it cannot yield integer fundamental-group
coordinates: its fundamental group is trivial. -/
private theorem zero_period_boundary :
    IsCoveringMap ((↑) : ℝ → AddCircle (0 : ℝ)) ∧
      Subsingleton (FundamentalGroup (AddCircle (0 : ℝ)) 0) ∧
      ¬ Nonempty (FundamentalGroup (AddCircle (0 : ℝ)) 0 ≃* Multiplicative ℤ) := by
  refine ⟨AddCircle.isCoveringMap_coe 0, ?_⟩
  have : Subsingleton (AddSubgroup.zmultiples (0 : ℝ)) := by
    rw [AddSubgroup.zmultiples_zero_eq_bot]
    infer_instance
  let e := (AddCircle.isAddQuotientCoveringMap_coe (0 : ℝ)).fundamentalGroupEquiv
    (x := (0 : AddCircle (0 : ℝ))) ⟨(0 : ℝ), rfl⟩
  have : Subsingleton (FundamentalGroup (AddCircle (0 : ℝ)) 0) :=
    e.injective.subsingleton
  refine ⟨inferInstance, ?_⟩
  rintro ⟨f⟩
  have h : Multiplicative.ofAdd (0 : ℤ) = Multiplicative.ofAdd (1 : ℤ) :=
    f.symm.injective (Subsingleton.elim _ _)
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (congrArg Multiplicative.toAdd h)

end SphereTopologyTest
