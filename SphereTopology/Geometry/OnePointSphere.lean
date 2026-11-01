/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Geometry.Stereographic
public import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Algebra.BigOperators.Fin

/-!
# One-point compactification in last-axis sphere coordinates

Appending a zero last coordinate identifies `EuclideanSpace 𝕜 (Fin n)` isometrically
with the orthogonal complement of the last unit vector, for `𝕜 = ℝ` or `ℂ`.
Over `ℝ`, extending this identification to one-point compactifications and composing
with Mathlib's inverse stereographic projection gives
`EuclideanSpace.onePointHomeomorphSphere`. Its point at infinity is the specified
last-axis north pole.

The stereographic normalization has forward factor `2 / (1 - p_last)`. Thus the
finite-point sphere coordinates have denominator `‖x‖ ^ 2 + 4`, and the finite zero
maps to the antipode of the north pole. All constructions include `n = 0`: the
finite zero and infinity map to the points with last coordinates `-1` and `1`.
The sphere homeomorphism is real; the complex-linear coordinate identification
alone does not give a one-point compactification onto a complex unit sphere.

## References

* Joseph Myers, Sébastien Gouëzel and Heather Macbeth's Euclidean-space and `PiLp`
  formalizations in Mathlib's `Analysis.InnerProductSpace.PiL2` and
  `Analysis.Normed.Lp.PiLp` supply the coordinate model and its norm.
* Heather Macbeth's stereographic sphere charts in
  `Mathlib.Geometry.Manifold.Instances.Sphere` supply the projection and inverse.
* Bjørn Kjos-Hanssen and Oliver Nash's
  `Mathlib.Topology.Compactification.OnePoint.Sphere` supplies the hyperplane-to-sphere
  homeomorphism; Mathlib's `OnePoint.Basic` supplies `Homeomorph.onePointCongr`.
-/

@[expose] public section

open scoped OnePoint

noncomputable section

namespace EuclideanSpace

section Coordinates

variable (𝕜 : Type*) [RCLike 𝕜]

/-- Orthogonality to the last unit vector is equivalent to a zero last coordinate. -/
theorem mem_single_last_orthogonal_iff (n : ℕ)
    (w : EuclideanSpace 𝕜 (Fin (n + 1))) :
    w ∈ (𝕜 ∙ (single (Fin.last n) (1 : 𝕜)))ᗮ ↔ w (Fin.last n) = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_single_left]
  simp

/-- Append a zero last coordinate to identify Euclidean space with the orthogonal
complement of the last unit vector. The inverse restricts to `Fin.castSucc`. -/
def snocZeroLinearIsometryEquiv (n : ℕ) :
    EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜]
      (𝕜 ∙ (single (Fin.last n) (1 : 𝕜)))ᗮ where
  toFun x := ⟨WithLp.toLp 2 (Fin.snoc (fun i : Fin n ↦ x i) 0), by
    apply (mem_single_last_orthogonal_iff 𝕜 n _).2
    simp only [Fin.snoc_last]⟩
  invFun w := WithLp.toLp 2
    (fun i : Fin n ↦ (w : EuclideanSpace 𝕜 (Fin (n + 1))) i.castSucc)
  left_inv := by
    intro x
    apply PiLp.ext
    intro i
    change (Fin.snoc (fun j : Fin n ↦ x j) 0 : Fin (n + 1) → 𝕜) i.castSucc = x i
    simp only [Fin.snoc_castSucc]
  right_inv := by
    intro w
    apply Subtype.ext
    apply PiLp.ext
    intro i
    change (Fin.snoc
      (fun j : Fin n ↦ (w : EuclideanSpace 𝕜 (Fin (n + 1))) j.castSucc) 0 :
        Fin (n + 1) → 𝕜) i = (w : EuclideanSpace 𝕜 (Fin (n + 1))) i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [Fin.snoc_last]
      exact ((mem_single_last_orthogonal_iff 𝕜 n _).1 w.property).symm
    · simp only [Fin.snoc_castSucc]
  map_add' := by
    intro x y
    apply Subtype.ext
    apply PiLp.ext
    intro i
    change (Fin.snoc (fun j : Fin n ↦ (x + y) j) 0 : Fin (n + 1) → 𝕜) i =
      (Fin.snoc (fun j : Fin n ↦ x j) 0 : Fin (n + 1) → 𝕜) i +
        (Fin.snoc (fun j : Fin n ↦ y j) 0 : Fin (n + 1) → 𝕜) i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, PiLp.add_apply, add_zero]
  map_smul' := by
    intro c x
    apply Subtype.ext
    apply PiLp.ext
    intro i
    change (Fin.snoc (fun j : Fin n ↦ (c • x) j) 0 : Fin (n + 1) → 𝕜) i =
      c • (Fin.snoc (fun j : Fin n ↦ x j) 0 : Fin (n + 1) → 𝕜) i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, PiLp.smul_apply, smul_zero]
  norm_map' := by
    intro x
    change ‖WithLp.toLp 2
      (Fin.snoc (fun i : Fin n ↦ x i) 0 : Fin (n + 1) → 𝕜)‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
    simp

/-- Appending zero preserves each of the first `n` coordinates, in order. -/
@[simp]
theorem snocZeroLinearIsometryEquiv_apply_castSucc (n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin n)) (i : Fin n) :
    (snocZeroLinearIsometryEquiv 𝕜 n x : EuclideanSpace 𝕜 (Fin (n + 1))) i.castSucc =
      x i := by
  change (Fin.snoc (fun j : Fin n ↦ x j) 0 : Fin (n + 1) → 𝕜) i.castSucc = x i
  simp only [Fin.snoc_castSucc]

/-- The appended coordinate is zero. -/
@[simp]
theorem snocZeroLinearIsometryEquiv_apply_last (n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    (snocZeroLinearIsometryEquiv 𝕜 n x : EuclideanSpace 𝕜 (Fin (n + 1))) (Fin.last n) =
      0 := by
  change (Fin.snoc (fun j : Fin n ↦ x j) 0 : Fin (n + 1) → 𝕜) (Fin.last n) = 0
  simp only [Fin.snoc_last]

/-- The inverse coordinate identification restricts to the first `n` coordinates. -/
@[simp]
theorem snocZeroLinearIsometryEquiv_symm_apply (n : ℕ)
    (w : (𝕜 ∙ (single (Fin.last n) (1 : 𝕜)))ᗮ) (i : Fin n) :
    (snocZeroLinearIsometryEquiv 𝕜 n).symm w i =
      (w : EuclideanSpace 𝕜 (Fin (n + 1))) i.castSucc := by
  rfl

end Coordinates

/-- The last unit vector, bundled as a point of the real metric unit sphere. -/
def northPoint (n : ℕ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨single (Fin.last n) 1, by
    rw [mem_sphere_zero_iff_norm]
    simp only [single, PiLp.norm_single, norm_one]⟩

/-- The north pole has exactly the specified last unit vector as its underlying vector. -/
theorem coe_northPoint (n : ℕ) :
    (northPoint n : EuclideanSpace ℝ (Fin (n + 1))) = single (Fin.last n) 1 := by
  rfl

/-- Every coordinate before the last coordinate of the north pole is zero. -/
@[simp]
theorem northPoint_apply_castSucc (n : ℕ) (i : Fin n) :
    (northPoint n : EuclideanSpace ℝ (Fin (n + 1))) i.castSucc = 0 := by
  rw [coe_northPoint]
  exact PiLp.single_eq_of_ne 2 (Fin.castSucc_ne_last i) 1

/-- The last coordinate of the north pole is one. -/
@[simp]
theorem northPoint_apply_last (n : ℕ) :
    (northPoint n : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) = 1 := by
  rw [coe_northPoint]
  exact PiLp.single_eq_same 2 (Fin.last n) 1

/-- Extend the append-zero-last isometry to one-point compactifications, then use
Mathlib's hyperplane-to-unit-sphere homeomorphism at the last-axis north pole. -/
def onePointHomeomorphSphere (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (snocZeroLinearIsometryEquiv ℝ n).toHomeomorph.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere (norm_eq_of_mem_sphere (northPoint n)))

/-- Infinity maps to the specified last-axis north pole. -/
@[simp]
theorem onePointHomeomorphSphere_apply_infty (n : ℕ) :
    onePointHomeomorphSphere n ∞ = northPoint n := by
  rfl

/-- A finite point is sent to inverse stereographic projection of its append-zero-last
image, with Mathlib's normalization. -/
theorem onePointHomeomorphSphere_apply_coe (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    onePointHomeomorphSphere n (x : OnePoint (EuclideanSpace ℝ (Fin n))) =
      (stereographic (norm_eq_of_mem_sphere (northPoint n))).symm
        (snocZeroLinearIsometryEquiv ℝ n x) := by
  rfl

/-- The finite zero maps to the antipode of the specified north pole, also when `n = 0`. -/
@[simp]
theorem onePointHomeomorphSphere_apply_zero (n : ℕ) :
    onePointHomeomorphSphere n
      ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) =
        -northPoint n := by
  rw [onePointHomeomorphSphere_apply_coe, map_zero]
  exact stereographic_symm_apply_zero (northPoint n)

private theorem coe_onePointHomeomorphSphere_apply_coe (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (onePointHomeomorphSphere n (x : OnePoint (EuclideanSpace ℝ (Fin n))) :
        EuclideanSpace ℝ (Fin (n + 1))) =
      (‖x‖ ^ 2 + 4)⁻¹ •
        ((4 : ℝ) • (snocZeroLinearIsometryEquiv ℝ n x :
          EuclideanSpace ℝ (Fin (n + 1))) +
          (‖x‖ ^ 2 - 4) • (northPoint n : EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hnorth : ‖(single (Fin.last n) 1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [coe_northPoint] using (norm_eq_of_mem_sphere (northPoint n))
  have hnorm :
      ‖(snocZeroLinearIsometryEquiv ℝ n x : EuclideanSpace ℝ (Fin (n + 1)))‖ = ‖x‖ :=
    (Submodule.norm_coe (snocZeroLinearIsometryEquiv ℝ n x)).trans
      ((snocZeroLinearIsometryEquiv ℝ n).norm_map x)
  rw [onePointHomeomorphSphere_apply_coe]
  change (stereoInvFun hnorth (snocZeroLinearIsometryEquiv ℝ n x) :
      EuclideanSpace ℝ (Fin (n + 1))) =
    (‖x‖ ^ 2 + 4)⁻¹ •
      ((4 : ℝ) • (snocZeroLinearIsometryEquiv ℝ n x :
        EuclideanSpace ℝ (Fin (n + 1))) +
        (‖x‖ ^ 2 - 4) • (single (Fin.last n) 1 : EuclideanSpace ℝ (Fin (n + 1))))
  simpa only [← Submodule.norm_coe, hnorm] using
    (stereoInvFun_apply hnorth (snocZeroLinearIsometryEquiv ℝ n x))

/-- The first `n` sphere coordinates of a finite point have numerator `4 * x i`. -/
theorem onePointHomeomorphSphere_apply_coe_castSucc (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (onePointHomeomorphSphere n (x : OnePoint (EuclideanSpace ℝ (Fin n))) :
        EuclideanSpace ℝ (Fin (n + 1))) i.castSucc =
      4 * x i / (‖x‖ ^ 2 + 4) := by
  rw [coe_onePointHomeomorphSphere_apply_coe]
  simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
    snocZeroLinearIsometryEquiv_apply_castSucc, northPoint_apply_castSucc,
    mul_zero, add_zero, div_eq_mul_inv]
  ring

/-- The last sphere coordinate of a finite point has numerator `‖x‖ ^ 2 - 4`. -/
theorem onePointHomeomorphSphere_apply_coe_last (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (onePointHomeomorphSphere n (x : OnePoint (EuclideanSpace ℝ (Fin n))) :
        EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) =
      (‖x‖ ^ 2 - 4) / (‖x‖ ^ 2 + 4) := by
  rw [coe_onePointHomeomorphSphere_apply_coe]
  simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
    snocZeroLinearIsometryEquiv_apply_last, northPoint_apply_last,
    mul_zero, zero_add, mul_one, div_eq_mul_inv]
  ring

/-- The inverse homeomorphism sends the north pole to infinity. -/
@[simp]
theorem onePointHomeomorphSphere_symm_apply_northPoint (n : ℕ) :
    (onePointHomeomorphSphere n).symm (northPoint n) = ∞ := by
  apply (onePointHomeomorphSphere n).symm_apply_eq.mpr
  exact (onePointHomeomorphSphere_apply_infty n).symm

/-- Away from the north pole, the inverse is the finite vector with coordinates
`2 * p_i / (1 - p_last)`, in the order indexed by `Fin.castSucc`. -/
theorem onePointHomeomorphSphere_symm_apply_of_ne (n : ℕ)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hp : p ≠ northPoint n) :
    (onePointHomeomorphSphere n).symm p =
      ((WithLp.toLp 2 (fun i : Fin n ↦
        2 * (p : EuclideanSpace ℝ (Fin (n + 1))) i.castSucc /
          (1 - (p : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n))) :
            EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) := by
  -- Keep the chart and the coordinate isometry over the same hyperplane.
  have hnorth : ‖(single (Fin.last n) 1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [coe_northPoint] using (norm_eq_of_mem_sphere (northPoint n))
  have hinner :
      inner ℝ (single (Fin.last n) 1 : EuclideanSpace ℝ (Fin (n + 1)))
          (p : EuclideanSpace ℝ (Fin (n + 1))) =
        (p : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) := by
    simp only [inner_single_left, map_one, one_mul]
  have hcoords :
      (snocZeroLinearIsometryEquiv ℝ n).symm (stereographic hnorth p) =
        WithLp.toLp 2 (fun i : Fin n ↦
          2 * (p : EuclideanSpace ℝ (Fin (n + 1))) i.castSucc /
            (1 - (p : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n))) := by
    ext i
    let u : (ℝ ∙ (single (Fin.last n) 1 : EuclideanSpace ℝ (Fin (n + 1))))ᗮ :=
      ⟨single i.castSucc 1, by
        rw [mem_single_last_orthogonal_iff]
        exact PiLp.single_eq_of_ne 2 (Fin.castSucc_ne_last i).symm 1⟩
    -- Test the projection against the corresponding unit vector in the hyperplane.
    have hproj :
        (((ℝ ∙ (single (Fin.last n) 1 :
            EuclideanSpace ℝ (Fin (n + 1))))ᗮ.orthogonalProjectionOnto
            (p : EuclideanSpace ℝ (Fin (n + 1))) :
              EuclideanSpace ℝ (Fin (n + 1))) i.castSucc) =
          (p : EuclideanSpace ℝ (Fin (n + 1))) i.castSucc := by
      simpa only [Submodule.coe_inner, u, inner_single_left, map_one, one_mul] using
        (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left u
          (p : EuclideanSpace ℝ (Fin (n + 1))))
    rw [snocZeroLinearIsometryEquiv_symm_apply, stereographic_apply]
    simp only [Submodule.coe_smul, PiLp.smul_apply, smul_eq_mul,
      hinner, hproj, div_eq_mul_inv]
    ring
  apply (onePointHomeomorphSphere n).symm_apply_eq.mpr
  rw [← hcoords, onePointHomeomorphSphere_apply_coe]
  change p = (stereographic hnorth).symm
    ((snocZeroLinearIsometryEquiv ℝ n)
      ((snocZeroLinearIsometryEquiv ℝ n).symm (stereographic hnorth p)))
  rw [(snocZeroLinearIsometryEquiv ℝ n).apply_symm_apply]
  change p = stereoInvFun hnorth
    (stereoToFun (single (Fin.last n) 1 : EuclideanSpace ℝ (Fin (n + 1)))
      (p : EuclideanSpace ℝ (Fin (n + 1))))
  exact (stereo_left_inv hnorth (x := p)
    (fun h ↦ hp (Subtype.ext (h.trans (coe_northPoint n).symm)))).symm

end EuclideanSpace
