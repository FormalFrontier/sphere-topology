/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homotopy.HSpaceFundamentalGroup
import SphereTopology.Homotopy.Circle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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
