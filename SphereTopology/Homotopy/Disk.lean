/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.CircleDegree
import SphereTopology.Homotopy.Sphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Closed complex disks and circle boundary degree

The boundary restriction of a continuous map from the complex closed unit disk
into the circle has degree zero. Consequently, no such map restricts to the
identity on the boundary. Every continuous self-map of a nonempty complex
closed ball has a fixed point.

The disk is `Metric.closedBall (0 : ℂ) 1`, and its boundary inclusion is the
stock `ContinuousMap.inclusion` associated to `Metric.sphere_subset_closedBall`.
The circle and degree are the existing `Circle` and `Circle.degree`.

The proof contracts the convex closed ball, postcomposes by the given map,
and restricts the nullhomotopy to the boundary. Free-homotopy invariance of
degree gives zero; the identity has degree one. No basedness is required.
The fixed-point theorem uses this degree obstruction via normalized displacement,
followed by affine transport to arbitrary nonempty complex closed balls.

## Limitations

The fixed-point theorem concerns complex closed balls, not higher-dimensional
disks. The degree obstruction uses the unit-circle boundary and asserts no
converse extension criterion for circle maps of degree zero.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §6,
  p. 10, for the disk non-retraction theorem, and §7 for circle-map degree.
* Mathlib's convex-set contractibility and nullhomotopy composition APIs,
  together with `SphereTopology.Homotopy.CircleDegree`, supply the underlying
  objects and comparison APIs.
-/

@[expose] public section

namespace Circle

/-- The restriction to the boundary of a circle-valued disk map has degree zero.
This is the degree obstruction underlying May, Chapter 1, §6, p. 10, using §7. -/
theorem degree_comp_closedBall_inclusion
    (G : C(Metric.closedBall (0 : ℂ) 1, Circle)) :
    degree (G.comp
      (ContinuousMap.inclusion
        (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1)) :
          C(Circle, Metric.closedBall (0 : ℂ) 1))) = 0 := by
  let : ContractibleSpace (Metric.closedBall (0 : ℂ) 1) :=
    (convex_closedBall (0 : ℂ) 1).contractibleSpace
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have hG : G.Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using
      (id_nullhomotopic (Metric.closedBall (0 : ℂ) 1)).comp_right G
  obtain ⟨c, hc⟩ := hG.comp_left
    (ContinuousMap.inclusion
      (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1)) :
        C(Circle, Metric.closedBall (0 : ℂ) 1))
  exact (degree_eq_of_homotopic hc).trans (degree_const c)

/-- No continuous disk map is the identity on its boundary.
This is May's disk non-retraction theorem, Chapter 1, §6, p. 10, for the
complex closed unit disk. -/
theorem comp_closedBall_inclusion_ne_id
    (G : C(Metric.closedBall (0 : ℂ) 1, Circle)) :
    G.comp
      (ContinuousMap.inclusion
        (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1)) :
          C(Circle, Metric.closedBall (0 : ℂ) 1)) ≠
      ContinuousMap.id Circle := by
  intro h
  have hdeg := congrArg degree h
  exact zero_ne_one
    ((degree_comp_closedBall_inclusion G).symm.trans (hdeg.trans degree_id))

end Circle

namespace Complex

/-- Transfer the unit-disk fixed-point theorem to nonempty complex closed balls. -/
private theorem exists_fixedPoint_closedBall_of_unit
    (hunit : ∀ g : C(Metric.closedBall (0 : ℂ) 1, Metric.closedBall (0 : ℂ) 1),
      ∃ z, g z = z)
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (f : C(Metric.closedBall c r, Metric.closedBall c r)) :
    ∃ z, f z = z := by
  by_cases hr0 : r = 0
  · subst r
    let z : Metric.closedBall c 0 := ⟨c, Metric.mem_closedBall_self le_rfl⟩
    refine ⟨z, Subtype.ext ?_⟩
    simpa only [Metric.closedBall_zero, Set.mem_singleton_iff] using (f z).property
  · let e : ℂ ≃ₜ ℂ :=
      (Homeomorph.smulOfNeZero r hr0).trans
        (IsometryEquiv.constVAdd c).toHomeomorph
    have he : e '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall c r := by
      change ((fun z : ℂ => c +ᵥ z) ∘ (fun z : ℂ => r • z)) ''
        Metric.closedBall (0 : ℂ) 1 = Metric.closedBall c r
      rw [Set.image_comp, Set.image_smul, Set.image_vadd]
      exact affinity_unitClosedBall hr c
    let eball : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall c r :=
      (e.image _).trans (Homeomorph.setCongr he)
    obtain ⟨z, hz⟩ := hunit
      ((toContinuousMap eball.symm).comp (f.comp (toContinuousMap eball)))
    refine ⟨eball z, ?_⟩
    exact eball.symm_apply_eq.mp hz

-- An antipodal normalized displacement would put the image outside the unit disk.
private theorem normalize_sub_ne_neg_of_norm_le_one {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {z w : E}
    (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1) (hzw : z - w ≠ 0) :
    NormedSpace.normalize (z - w) ≠ -z := by
  intro h
  have hpos : 0 < ‖z - w‖ := norm_pos_iff.mpr hzw
  have hdiff : z - w = -(‖z - w‖ • z) := by
    calc
      z - w = ‖z - w‖ • NormedSpace.normalize (z - w) :=
        (NormedSpace.norm_smul_normalize (z - w)).symm
      _ = -(‖z - w‖ • z) := by rw [h, smul_neg]
  have hw_eq : w = (1 + ‖z - w‖) • z := by
    calc
      w = z - (z - w) := by abel
      _ = z - -(‖z - w‖ • z) := congrArg (fun u : E => z - u) hdiff
      _ = z + ‖z - w‖ • z := sub_neg_eq_add z _
      _ = (1 + ‖z - w‖) • z := by rw [add_smul, one_smul]
  have hn : ‖w‖ = 1 + ‖z - w‖ := by
    simpa only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg zero_le_one (norm_nonneg (z - w))), hz, mul_one]
      using congrArg norm hw_eq
  linarith

private theorem exists_fixedPoint_unitClosedBall
    (f : C(Metric.closedBall (0 : ℂ) 1, Metric.closedBall (0 : ℂ) 1)) :
    ∃ z, f z = z := by
  by_contra hfixed
  let V : C(Metric.closedBall (0 : ℂ) 1, ℂ) :=
    ⟨fun z => (z : ℂ) - (f z : ℂ),
      continuous_subtype_val.sub (continuous_subtype_val.comp f.continuous)⟩
  have hV : ∀ z, V z ≠ 0 := by
    intro z hz
    change (z : ℂ) - (f z : ℂ) = 0 at hz
    exact hfixed ⟨z, Subtype.ext (sub_eq_zero.mp hz).symm⟩
  let N := ContinuousMap.normalizeOfNoZero V hV
  let G : C(Metric.closedBall (0 : ℂ) 1, Circle) := {
    toFun z := ⟨N z, mem_sphere_zero_iff_norm.mpr
      (ContinuousMap.norm_normalizeOfNoZero V hV z)⟩
    continuous_toFun := N.continuous.subtype_mk _ }
  let inclusion : C(Circle, Metric.closedBall (0 : ℂ) 1) :=
    ContinuousMap.inclusion
      (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1))
  let g := G.comp inclusion
  have hnonantipodal : ∀ z, g z ≠ -(ContinuousMap.id Circle z) := by
    intro z hz
    have hn : NormedSpace.normalize ((z : ℂ) - (f (inclusion z) : ℂ)) = -(z : ℂ) := by
      change N (inclusion z) = -(z : ℂ)
      exact congrArg (fun w : Circle => (w : ℂ)) hz
    exact normalize_sub_ne_neg_of_norm_le_one (Circle.norm_coe z)
      (mem_closedBall_zero_iff.mp (f (inclusion z)).property) (hV (inclusion z)) hn
  let H : g.Homotopy (ContinuousMap.id Circle) :=
    Metric.Sphere.homotopyOfNonAntipodal (E := ℂ) g (ContinuousMap.id Circle) hnonantipodal
  have hdegree : Circle.degree g = 1 :=
    (Circle.degree_eq_of_homotopic ⟨H⟩).trans Circle.degree_id
  exact zero_ne_one ((Circle.degree_comp_closedBall_inclusion G).symm.trans hdegree)

/-- Every continuous self-map of a nonempty complex closed ball has a fixed point.
This is the disk case of Brouwer's fixed-point theorem. The unit-disk statement is
May, Chapter 1, §6, p. 10; arbitrary centers and nonnegative radii follow by affine
transport and the radius-zero singleton case. -/
theorem exists_fixedPoint_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (f : C(Metric.closedBall c r, Metric.closedBall c r)) :
    ∃ z, f z = z := by
  exact exists_fixedPoint_closedBall_of_unit exists_fixedPoint_unitClosedBall c hr f

end Complex
