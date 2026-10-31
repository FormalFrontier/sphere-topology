/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The forward intersection of a closed-ball ray with its sphere

For distinct points `q` and `x` in the closed ball of a sphere `s`, the ray starting
at `q` and passing through `x` has a unique intersection with `s` at or after `x`.
`EuclideanGeometry.Sphere.rayInterParameter` gives its real parameter, and
`EuclideanGeometry.Sphere.rayInter` gives the point. The formulas are defined for
all pairs of points and every real radius. The parameter bound and sphere
membership require only the second point's closed-ball membership and
distinctness. For a closed-ball start and a distinct second point, a strictly
positive parameter gives a point on the sphere if and only if it equals the upper
root, without restricting the second point to the closed ball. This does not
assert that the upper root is strictly positive for every direction. The boundary
point identity holds for every closed-ball start, including the diagonal; the
boundary parameter identity requires distinctness.

This extends the boundary-start construction `EuclideanGeometry.Sphere.secondInter`
to closed-ball starts. For distinct closed-ball pairs with `q` on the sphere, it
selects the far intersection, not the initial point `q`. The agreement theorem
identifies the two constructions for a boundary start and a closed-ball second
point, including zero direction, when both return `q`. The total forward formula
also returns `q` for an outward direction from a boundary start. The formulas are
jointly continuous on the whole off-diagonal, without closed-ball or
discriminant-sign hypotheses.

## Implementation notes

The parameter and point are total data, with formula, affine-span, and geometric
characterization lemmas below, along with joint continuity off the diagonal.
No sphere-valued bundled map or fixed-point application is constructed here.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §6, p. 10:
  the disk argument motivates continuing from a point's image through the point to
  the boundary. The quadratic formula here completes that geometric step; it is
  not a formula printed in the source.
* Joseph Myers's `EuclideanGeometry.Sphere.secondInter` formalization in Mathlib
  supplies the boundary-start specialization and the canonical affine sphere API.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace EuclideanGeometry

universe u v

variable {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- The upper quadratic-root parameter for continuing from `q` through `x` to the
sphere `s`. This is a total real formula: division and `Real.sqrt` are used also
outside the geometric domain. -/
def Sphere.rayInterParameter (s : Sphere P) (q x : P) : ℝ :=
  let d := x -ᵥ q
  let A := ‖d‖ ^ 2
  let B := ⟪q -ᵥ s.center, d⟫_ℝ
  let C := ‖q -ᵥ s.center‖ ^ 2 - s.radius ^ 2
  (-B + Real.sqrt (B ^ 2 - A * C)) / A

/-- The total formula for the forward sphere intersection along the line from
`q` through `x`, with the upper quadratic-root parameter. -/
def Sphere.rayInter (s : Sphere P) (q x : P) : P :=
  s.rayInterParameter q x • (x -ᵥ q) +ᵥ q

/-- The quadratic formula for the forward-intersection parameter. -/
theorem Sphere.rayInterParameter_eq (s : Sphere P) (q x : P) :
    s.rayInterParameter q x =
      (-⟪q -ᵥ s.center, x -ᵥ q⟫_ℝ +
        Real.sqrt (⟪q -ᵥ s.center, x -ᵥ q⟫_ℝ ^ 2 -
          ‖x -ᵥ q‖ ^ 2 * (‖q -ᵥ s.center‖ ^ 2 - s.radius ^ 2))) / ‖x -ᵥ q‖ ^ 2 :=
  rfl

/-- The forward-intersection point in terms of its parameter and direction. -/
theorem Sphere.rayInter_eq_smul_vsub_vadd (s : Sphere P) (q x : P) :
    s.rayInter q x = s.rayInterParameter q x • (x -ᵥ q) +ᵥ q :=
  rfl

/-- The total parameter formula is zero on the diagonal. -/
@[simp]
theorem Sphere.rayInterParameter_self (s : Sphere P) (q : P) :
    s.rayInterParameter q q = 0 := by
  simp [s.rayInterParameter_eq]

/-- The total point formula returns the starting point on the diagonal. -/
@[simp]
theorem Sphere.rayInter_self (s : Sphere P) (q : P) : s.rayInter q q = q := by
  simp [s.rayInter_eq_smul_vsub_vadd]

/-- Even outside the closed ball, the point formula lies on the line through its
supplied points. -/
theorem Sphere.rayInter_mem_affineSpan (s : Sphere P) (q x : P) :
    s.rayInter q x ∈ line[ℝ, q, x] := by
  rw [s.rayInter_eq_smul_vsub_vadd]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

private theorem Sphere.norm_smul_vsub_vadd_sq_sub_radius_sq (s : Sphere P)
    (q x : P) (t : ℝ) :
    ‖(t • (x -ᵥ q) +ᵥ q) -ᵥ s.center‖ ^ 2 - s.radius ^ 2 =
      ‖x -ᵥ q‖ ^ 2 * t ^ 2 + 2 * ⟪q -ᵥ s.center, x -ᵥ q⟫_ℝ * t +
        (‖q -ᵥ s.center‖ ^ 2 - s.radius ^ 2) := by
  rw [vadd_vsub_assoc, norm_add_sq_real, real_inner_smul_left, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm (x -ᵥ q) (q -ᵥ s.center)]
  ring

omit [InnerProductSpace ℝ V] in
private theorem Sphere.norm_vsub_sq_sub_radius_sq_nonpos {s : Sphere P} {p : P}
    (hp : p ∈ Metric.closedBall s.center s.radius) :
    ‖p -ᵥ s.center‖ ^ 2 - s.radius ^ 2 ≤ 0 := by
  apply sub_nonpos.mpr
  apply (sq_le_sq₀ (norm_nonneg _) (Metric.nonneg_of_mem_closedBall hp)).2
  simpa only [Metric.mem_closedBall, dist_eq_norm_vsub V] using hp

private theorem Sphere.quadratic_at_one_nonpos {s : Sphere P} {q x : P}
    (hx : x ∈ Metric.closedBall s.center s.radius) :
    ‖x -ᵥ q‖ ^ 2 + 2 * ⟪q -ᵥ s.center, x -ᵥ q⟫_ℝ +
      (‖q -ᵥ s.center‖ ^ 2 - s.radius ^ 2) ≤ 0 := by
  have h := s.norm_smul_vsub_vadd_sq_sub_radius_sq q x 1
  simp only [one_smul, vsub_vadd, one_pow, mul_one] at h
  rw [← h]
  exact Sphere.norm_vsub_sq_sub_radius_sq_nonpos hx

private theorem Sphere.smul_vsub_vadd_mem_iff_quadratic_eq_zero (s : Sphere P)
    (hr : 0 ≤ s.radius) (q x : P) (t : ℝ) :
    t • (x -ᵥ q) +ᵥ q ∈ s ↔
      ‖x -ᵥ q‖ ^ 2 * t ^ 2 + 2 * ⟪q -ᵥ s.center, x -ᵥ q⟫_ℝ * t +
        (‖q -ᵥ s.center‖ ^ 2 - s.radius ^ 2) = 0 := by
  rw [mem_sphere, dist_eq_norm_vsub V, ← sq_eq_sq₀ (norm_nonneg _) hr,
    ← sub_eq_zero, s.norm_smul_vsub_vadd_sq_sub_radius_sq]

private theorem quadratic_upperRoot_eq_zero {a b c : ℝ} (ha : a ≠ 0)
    (hD : 0 ≤ b ^ 2 - a * c) :
    a * ((-b + Real.sqrt (b ^ 2 - a * c)) / a) ^ 2 +
      2 * b * ((-b + Real.sqrt (b ^ 2 - a * c)) / a) + c = 0 := by
  have hdisc : discrim (a / 2) b (c / 2) =
      Real.sqrt (b ^ 2 - a * c) * Real.sqrt (b ^ 2 - a * c) := by
    calc
      discrim (a / 2) b (c / 2) = b ^ 2 - a * c := by rw [discrim]; ring
      _ = Real.sqrt (b ^ 2 - a * c) * Real.sqrt (b ^ 2 - a * c) :=
        (Real.mul_self_sqrt hD).symm
  have hroot := (quadratic_eq_zero_iff (a := a / 2) (b := b) (c := c / 2)
    (div_ne_zero ha two_ne_zero) hdisc
    ((-b + Real.sqrt (b ^ 2 - a * c)) / a)).mpr
      (Or.inl (by rw [show 2 * (a / 2) = a by ring]))
  linear_combination 2 * hroot

private theorem add_sq_le_discrim_of_nonpos_at_one {a b c : ℝ} (ha : 0 ≤ a)
    (h1 : a + 2 * b + c ≤ 0) : (a + b) ^ 2 ≤ b ^ 2 - a * c := by
  calc
    (a + b) ^ 2 = b ^ 2 - a * c + a * (a + 2 * b + c) := by ring
    _ ≤ b ^ 2 - a * c + 0 :=
      add_le_add le_rfl (mul_nonpos_of_nonneg_of_nonpos ha h1)
    _ = b ^ 2 - a * c := add_zero _

private theorem one_le_quadratic_upperRoot {a b c : ℝ} (ha : 0 < a)
    (h1 : a + 2 * b + c ≤ 0) :
    1 ≤ (-b + Real.sqrt (b ^ 2 - a * c)) / a := by
  apply (le_div_iff₀ ha).mpr
  have hs := Real.le_sqrt_of_sq_le (add_sq_le_discrim_of_nonpos_at_one ha.le h1)
  linarith only [hs]

private theorem quadratic_eq_zero_iff_eq_upperRoot_of_pos {a b c t : ℝ}
    (ha : 0 < a) (hc : c ≤ 0) (ht : 0 < t) :
    a * t ^ 2 + 2 * b * t + c = 0 ↔
      t = (-b + Real.sqrt (b ^ 2 - a * c)) / a := by
  have hac : a * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hc
  have hcomp : b ^ 2 ≤ b ^ 2 - a * c := by linarith only [hac]
  have hD : 0 ≤ b ^ 2 - a * c := (sq_nonneg b).trans hcomp
  constructor
  · intro h
    have hhalf : a / 2 * (t * t) + b * t + c / 2 = 0 := by
      linear_combination h / 2
    have hdisc : discrim (a / 2) b (c / 2) =
        Real.sqrt (b ^ 2 - a * c) * Real.sqrt (b ^ 2 - a * c) := by
      calc
        discrim (a / 2) b (c / 2) = b ^ 2 - a * c := by rw [discrim]; ring
        _ = Real.sqrt (b ^ 2 - a * c) * Real.sqrt (b ^ 2 - a * c) :=
          (Real.mul_self_sqrt hD).symm
    have hroots := (quadratic_eq_zero_iff (a := a / 2) (b := b) (c := c / 2)
      (div_ne_zero ha.ne' two_ne_zero) hdisc t).mp hhalf
    rw [show 2 * (a / 2) = a by ring] at hroots
    rcases hroots with hupper | hlower
    · exact hupper
    · have hs : -b ≤ Real.sqrt (b ^ 2 - a * c) :=
        Real.le_sqrt_of_sq_le (by simpa only [neg_sq] using hcomp)
      have ht0 : t ≤ 0 := by
        rw [hlower]
        exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) ha.le
      exact (ht.not_ge ht0).elim
  · rintro rfl
    exact quadratic_upperRoot_eq_zero ha.ne' hD

/-- For a second point in the closed ball, the upper root lies at or after that
point, for any distinct starting point. -/
theorem Sphere.one_le_rayInterParameter {s : Sphere P} {q x : P}
    (hx : x ∈ Metric.closedBall s.center s.radius) (hne : q ≠ x) :
    1 ≤ s.rayInterParameter q x := by
  have hA : 0 < ‖x -ᵥ q‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (vsub_ne_zero.mpr hne.symm))
  rw [s.rayInterParameter_eq]
  exact one_le_quadratic_upperRoot hA (Sphere.quadratic_at_one_nonpos hx)

/-- Continuing through a closed-ball point from any distinct start by the upper
root reaches the sphere. This includes the closed-ball starts of May's disk
argument, §6. -/
theorem Sphere.rayInter_mem {s : Sphere P} {q x : P}
    (hx : x ∈ Metric.closedBall s.center s.radius) (hne : q ≠ x) :
    s.rayInter q x ∈ s := by
  have hA : 0 < ‖x -ᵥ q‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (vsub_ne_zero.mpr hne.symm))
  have hD : 0 ≤ ⟪q -ᵥ s.center, x -ᵥ q⟫_ℝ ^ 2 -
      ‖x -ᵥ q‖ ^ 2 * (‖q -ᵥ s.center‖ ^ 2 - s.radius ^ 2) :=
    (sq_nonneg (‖x -ᵥ q‖ ^ 2 + ⟪q -ᵥ s.center, x -ᵥ q⟫_ℝ)).trans
      (add_sq_le_discrim_of_nonpos_at_one hA.le (Sphere.quadratic_at_one_nonpos hx))
  rw [s.rayInter_eq_smul_vsub_vadd,
    s.smul_vsub_vadd_mem_iff_quadratic_eq_zero (Metric.nonneg_of_mem_closedBall hx),
    s.rayInterParameter_eq]
  exact quadratic_upperRoot_eq_zero hA.ne' hD

/-- For a closed-ball start and a distinct second point, a strictly positive
parameter gives a point on the sphere if and only if it equals the upper root.
The second point is unrestricted; the upper root need not be strictly positive. -/
theorem Sphere.smul_vsub_vadd_mem_iff_eq_rayInterParameter {s : Sphere P} {q x : P}
    (hq : q ∈ Metric.closedBall s.center s.radius) (hne : q ≠ x)
    {t : ℝ} (ht : 0 < t) :
    t • (x -ᵥ q) +ᵥ q ∈ s ↔ t = s.rayInterParameter q x := by
  rw [s.smul_vsub_vadd_mem_iff_quadratic_eq_zero (Metric.nonneg_of_mem_closedBall hq),
    s.rayInterParameter_eq]
  exact quadratic_eq_zero_iff_eq_upperRoot_of_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (vsub_ne_zero.mpr hne.symm)))
    (Sphere.norm_vsub_sq_sub_radius_sq_nonpos hq) ht

/-- If the second point is on the sphere and distinct from a closed-ball start,
its forward-intersection parameter is one. No open-ball hypothesis is imposed. -/
theorem Sphere.rayInterParameter_eq_one_of_mem {s : Sphere P} {q x : P}
    (hq : q ∈ Metric.closedBall s.center s.radius) (hx : x ∈ s) (hne : q ≠ x) :
    s.rayInterParameter q x = 1 := by
  have h := (Sphere.smul_vsub_vadd_mem_iff_eq_rayInterParameter hq hne
    (show (0 : ℝ) < 1 by norm_num)).1 (by simpa only [one_smul, vsub_vadd] using hx)
  exact h.symm

/-- A second point on the sphere is fixed by the forward-intersection formula
for every closed-ball start, including the diagonal. This is the boundary identity
needed in May's disk argument, §6. -/
theorem Sphere.rayInter_eq_of_mem {s : Sphere P} {q x : P}
    (hq : q ∈ Metric.closedBall s.center s.radius) (hx : x ∈ s) :
    s.rayInter q x = x := by
  by_cases hne : q = x
  · subst x
    exact s.rayInter_self q
  · rw [s.rayInter_eq_smul_vsub_vadd, Sphere.rayInterParameter_eq_one_of_mem hq hx hne,
      one_smul, vsub_vadd]

/-- The total parameter formula is jointly continuous off the diagonal. Neither
closed-ball memberships nor nonnegativity of the discriminant are needed. -/
theorem Sphere.continuousOn_rayInterParameter (s : Sphere P) :
    ContinuousOn (fun p : P × P => s.rayInterParameter p.1 p.2)
      {p | p.1 ≠ p.2} := by
  intro p hp
  have hd : ContinuousAt (fun p : P × P => p.2 -ᵥ p.1) p :=
    continuousAt_snd.vsub continuousAt_fst
  have hc : ContinuousAt (fun p : P × P => p.1 -ᵥ s.center) p :=
    continuousAt_fst.vsub continuousAt_const
  have hA := hd.norm.pow 2
  have hB : ContinuousAt (fun p : P × P => ⟪p.1 -ᵥ s.center, p.2 -ᵥ p.1⟫_ℝ) p :=
    hc.inner hd
  have hC := (hc.norm.pow 2).sub (continuousAt_const (y := s.radius ^ 2))
  have hA0 : ‖p.2 -ᵥ p.1‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (vsub_ne_zero.mpr hp.symm))
  simpa only [s.rayInterParameter_eq, Pi.div_def, Pi.add_def, Pi.neg_def, Pi.pow_def,
    Pi.sub_def, Pi.mul_def] using
    ((hB.neg.add ((hB.pow 2).sub (hA.mul hC)).sqrt).div hA hA0).continuousWithinAt

/-- The total point formula is jointly continuous off the diagonal, independently
of closed-ball memberships and including boundary starting points. -/
theorem Sphere.continuousOn_rayInter (s : Sphere P) :
    ContinuousOn (fun p : P × P => s.rayInter p.1 p.2) {p | p.1 ≠ p.2} := by
  have hd : Continuous (fun p : P × P => p.2 -ᵥ p.1) :=
    continuous_snd.vsub continuous_fst
  simpa only [s.rayInter_eq_smul_vsub_vadd, Pi.vadd_def', Pi.smul_def'] using
    (s.continuousOn_rayInterParameter.smul hd.continuousOn).vadd continuous_fst.continuousOn

/-- For a boundary start and a closed-ball second point, the forward intersection
agrees with Mathlib's `Sphere.secondInter`, including zero direction, when both
return `q`. For distinct such pairs, this is the far intersection, not `q`. -/
theorem Sphere.rayInter_eq_secondInter {s : Sphere P} {q x : P}
    (hq : q ∈ s) (hx : x ∈ Metric.closedBall s.center s.radius) :
    s.rayInter q x = s.secondInter q (x -ᵥ q) := by
  have hB : ⟪q -ᵥ s.center, x -ᵥ q⟫_ℝ ≤ 0 := by
    have h := inner_nonneg_of_dist_le_radius hq (Metric.mem_closedBall.mp hx)
    rw [← neg_vsub_eq_vsub_rev x q, inner_neg_left, real_inner_comm] at h
    linarith
  have hC : ‖q -ᵥ s.center‖ ^ 2 - s.radius ^ 2 = 0 := by
    rw [norm_vsub_center_eq_radius hq, sub_self]
  rw [s.rayInter_eq_smul_vsub_vadd, s.rayInterParameter_eq, hC, mul_zero, sub_zero,
    Real.sqrt_sq_eq_abs, abs_of_nonpos hB, Sphere.secondInter,
    real_inner_comm (x -ᵥ q) (q -ᵥ s.center), real_inner_self_eq_norm_sq]
  congr 2
  ring

end EuclideanGeometry
