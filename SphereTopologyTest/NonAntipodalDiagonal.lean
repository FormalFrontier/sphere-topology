/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homotopy.Sphere
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

/-!
# An off-diagonal non-antipodal pair on the complex unit circle

The perpendicular pair `1, I` lies in the non-antipodal-pair subspace but not
in the diagonal. The inverse homotopy equivalence returns its first coordinate.
-/

private theorem exists_offDiagonalPair :
    ∃ z : {z : Metric.sphere (0 : ℂ) 1 × Metric.sphere (0 : ℂ) 1 //
        (z.1 : ℂ) ≠ -(z.2 : ℂ)},
      z.val.1 ≠ z.val.2 ∧
        ((Metric.Sphere.diagonalHomotopyEquiv (E := ℂ)).symm z : ℂ) = 1 := by
  let p : Metric.sphere (0 : ℂ) 1 := ⟨1, by simp⟩
  let q : Metric.sphere (0 : ℂ) 1 := ⟨Complex.I, by simp⟩
  have hpq : (p : ℂ) ≠ -(q : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [p, q] at hre
  let z : {z : Metric.sphere (0 : ℂ) 1 × Metric.sphere (0 : ℂ) 1 //
      (z.1 : ℂ) ≠ -(z.2 : ℂ)} := ⟨(p, q), hpq⟩
  refine ⟨z, ?_, ?_⟩
  · intro h
    have hre := congrArg (fun w : Metric.sphere (0 : ℂ) 1 => Complex.re (w : ℂ)) h
    norm_num [z, p, q] at hre
  · rw [Metric.Sphere.diagonalHomotopyEquiv_symm_apply]
