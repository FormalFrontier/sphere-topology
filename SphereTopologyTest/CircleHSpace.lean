/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle
import SphereTopology.Homotopy.HSpaceFundamentalGroup
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Circle coordinates and H-space loop multiplication

Verification of signed-period coordinates, the zero-period boundary and the
comparison of pointwise H-space loop multiplication with concatenation on the
complex unit circle. The integer coordinates are supplied by
`FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle`; the H-space
comparison is supplied by `SphereTopology.Homotopy.HSpaceFundamentalGroup`.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §5,
  pp. 8–9, for integer loops and lifted-endpoint coordinates.
* Formal Frontier Agents' circle-coordinate and H-space formalizations, using
  Mathlib's circle, covering, path and homotopy APIs; see `docs/CREDITS.md`.
-/

@[expose] public section

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

end

/-!
# H-space loop multiplication and a full turn in the circle

A full turn in the complex unit circle is geometrically nonconstant: its
midpoint is `Circle.exp Real.pi`, which differs from its source `1`. This is not
a claim that its fundamental-group class is nonidentity.

Chronological concatenation is distinguished from fundamental-group
multiplication: the class of `p.trans q` is `[q] * [p]`. The circle examples
use the H-space comparison and commutativity directly, without its integer
fundamental-group calculator.
-/

noncomputable section

namespace SphereTopologyTest

/-- One full counterclockwise turn in the complex unit circle. -/
private def circleFullTurn : Path (1 : Circle) 1 := Circle.loop 1

@[simp]
private theorem circleFullTurn_apply (t : unitInterval) :
    circleFullTurn t = Circle.exp (2 * Real.pi * (t : ℝ)) := by
  simp only [circleFullTurn, Circle.loop_apply, Int.cast_one, mul_one]

private def halfTime : unitInterval := ⟨(1 : ℝ) / 2, by norm_num⟩

private theorem circleFullTurn_half_ne_one : circleFullTurn halfTime ≠ (1 : Circle) := by
  have h : 2 * Real.pi * (halfTime : ℝ) = Real.pi := by
    dsimp [halfTime]
    ring
  simpa only [circleFullTurn_apply, h] using Circle.exp_pi_ne_one

private theorem circleFullTurn_ne_refl : circleFullTurn ≠ Path.refl (1 : Circle) := by
  intro h
  have hv := congrArg (fun p : Path (1 : Circle) 1 => p halfTime) h
  exact circleFullTurn_half_ne_one (by simpa using hv)

-- A use of pointwise loop multiplication through its strict-unit agreement API.
private theorem loopMul_circleFullTurn_refl :
    HSpace.loopMul circleFullTurn (Path.refl (1 : Circle)) = circleFullTurn := by
  rw [HSpace.loopMul_toHSpace]
  apply DFunLike.ext _ _
  intro t
  exact mul_one (circleFullTurn t)

-- Circle instances of the based-homotopy and quotient comparisons.
example : Path.Homotopic
    (HSpace.loopMul circleFullTurn circleFullTurn.symm)
    (circleFullTurn.trans circleFullTurn.symm) :=
  HSpace.loopMul_homotopic_trans _ _

example : (FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (HSpace.loopMul circleFullTurn circleFullTurn.symm)) :
      FundamentalGroup Circle (1 : Circle)) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleFullTurn.symm) *
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleFullTurn) :=
  FundamentalGroup.fromPath_loopMul _ _

-- Arbitrary classes, rather than a tautological comparison of a class with itself.
example (a b : FundamentalGroup Circle (1 : Circle)) : a * b = b * a :=
  FundamentalGroup.mul_comm a b

example : IsMulCommutative (FundamentalGroup Circle (1 : Circle)) := inferInstance

-- The same nonconstant loop also satisfies the strict-unit agreement.
example :
    @HSpace.loopMul Circle _ (IsTopologicalGroup.toHSpace Circle)
        circleFullTurn circleFullTurn.symm =
      (circleFullTurn.mul circleFullTurn.symm).cast
        (one_mul (1 : Circle)).symm (one_mul (1 : Circle)).symm :=
  HSpace.loopMul_toHSpace circleFullTurn circleFullTurn.symm

example : Path.Homotopic
    ((circleFullTurn.mul circleFullTurn.symm).cast
      (one_mul (1 : Circle)).symm (one_mul (1 : Circle)).symm)
    (circleFullTurn.trans circleFullTurn.symm) :=
  Path.mul_homotopic_trans _ _

end SphereTopologyTest

end

end
