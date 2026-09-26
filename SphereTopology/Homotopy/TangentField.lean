/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker A, Prism. See README.md for internal reuse.
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# Homotopies from tangent fields on a sphere

This module normalizes nowhere-zero continuous vector-valued maps and constructs
an explicit homotopy from the identity of a real metric unit sphere to its
antipodal map. The homotopy rotates each point through an orthogonal unit field.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace ContinuousMap

/-- Pointwise normalization of a nowhere-zero continuous vector-valued map. -/
noncomputable def normalizeOfNoZero
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : C(X, E)) (hV : ∀ x, V x ≠ 0) : C(X, E) where
  toFun x := NormedSpace.normalize (V x)
  continuous_toFun := by
    change Continuous ((fun x => ‖V x‖)⁻¹ • (V : X → E))
    exact (V.continuous.norm.inv₀ (fun x hx => hV x (norm_eq_zero.mp hx))).smul V.continuous

@[simp] theorem norm_normalizeOfNoZero
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : C(X, E)) (hV : ∀ x, V x ≠ 0) (x : X) :
    ‖normalizeOfNoZero V hV x‖ = 1 :=
  NormedSpace.norm_normalize (hV x)

end ContinuousMap

namespace Metric.Sphere

/-- The antipodal continuous self-map of a unit sphere. -/
def antipodal
    {E : Type*} [NormedAddCommGroup E] :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1) where
  toFun p := -p
  continuous_toFun := continuous_neg

/-- An orthogonal unit field rotates the identity map of a unit sphere to the
antipodal map. -/
noncomputable def homotopyAntipodalOfUnitOrthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : C(Metric.sphere (0 : E) 1, E))
    (hW_norm : ∀ p, ‖W p‖ = 1)
    (hW_orth : ∀ p, inner ℝ p.1 (W p) = 0) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (Metric.sphere (0 : E) 1))
      (antipodal (E := E)) where
  toFun q := ⟨
    Real.cos (Real.pi * q.1.1) • q.2.1 + Real.sin (Real.pi * q.1.1) • W q.2,
    mem_sphere_zero_iff_norm.mpr (by
      rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)]
      rw [norm_add_sq_real, norm_smul, norm_smul, mem_sphere_zero_iff_norm.mp q.2.2, hW_norm,
        mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      have h₁ : inner ℝ (Real.cos (Real.pi * q.1.1) • q.2.1)
          (Real.sin (Real.pi * q.1.1) • W q.2) = 0 := by
        rw [real_inner_smul_left, real_inner_smul_right, hW_orth, mul_zero, mul_zero]
      rw [h₁, mul_zero, add_zero]
      nlinarith [Real.cos_sq_add_sin_sq (Real.pi * q.1.1)])⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  map_zero_left x := by
    ext
    simp
  map_one_left x := by
    ext
    simp [antipodal]

/-- A nowhere-zero orthogonal field can first be normalized and then used to
rotate the identity map to the antipodal map. -/
noncomputable def homotopyAntipodalOfNowhereZeroOrthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : C(Metric.sphere (0 : E) 1, E))
    (hV_ne : ∀ p, V p ≠ 0)
    (hV_orth : ∀ p, inner ℝ p.1 (V p) = 0) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (Metric.sphere (0 : E) 1))
      (antipodal (E := E)) := by
  let W := ContinuousMap.normalizeOfNoZero V hV_ne
  apply homotopyAntipodalOfUnitOrthogonal W
    (ContinuousMap.norm_normalizeOfNoZero V hV_ne)
  intro p
  change inner ℝ p.1 (‖V p‖⁻¹ • V p) = 0
  rw [real_inner_smul_right, hV_orth, mul_zero]

end Metric.Sphere
