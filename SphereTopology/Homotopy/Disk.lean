/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.CircleDegree
import SphereTopology.Geometry.ForwardRayMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Closed complex disks and circle boundary degree

The boundary restriction of a continuous map from the complex closed unit disk
into the circle has degree zero. Consequently, no such map restricts to the
identity on the boundary. A continuous complex-valued map on a closed ball
of nonnegative radius has a fixed point if its boundary images lie in that
ball; no bound is imposed on its interior values.

The disk is `Metric.closedBall (0 : ℂ) 1`, and its boundary inclusion is the
stock `ContinuousMap.inclusion` associated to `Metric.sphere_subset_closedBall`.
The circle and degree are the existing `Circle` and `Circle.degree`.

## Main results

* `Circle.degree_comp_closedBall_inclusion`: a circle-valued map on the closed
  unit disk has boundary restriction of degree zero.
* `Circle.comp_closedBall_inclusion_ne_id`: there is no retraction of the closed
  unit disk onto its circle boundary.
* `Complex.exists_fixedPoint_closedBall_of_boundary_mapsTo`: a complex-valued
  continuous map on a closed ball, with arbitrary center and nonnegative radius,
  has a fixed point if its boundary images lie in that ball.
* `Complex.exists_fixedPoint_closedBall`: the continuous self-map specialization.

The degree-zero boundary restriction is proved by contracting the convex closed
ball, postcomposing by the given map, and restricting the nullhomotopy to the
boundary. Free-homotopy invariance of degree gives zero; the identity has degree
one. No basedness is required. If a complex-valued disk map has no fixed point,
the forward-ray map from its image through each point is circle-valued. The
boundary-image condition makes it the identity on the boundary, contradicting
the degree obstruction. Affine transport and the radius-zero singleton case give
the result for arbitrary centers and nonnegative radii. This generalizes May's
unit-disk self-map theorem and follows his forward-ray construction, using circle
degree rather than his fundamental-group obstruction.

## Limitations

The fixed-point theorem concerns complex closed balls, not higher-dimensional
disks. The degree obstruction uses the unit-circle boundary and asserts no
converse extension criterion for circle maps of degree zero.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §6,
  p. 10, for the closed unit disk self-map theorem and its forward-ray and
  non-retraction argument, and §7 for circle-map degree.
* `SphereTopology.Geometry.ForwardRayMap` supplies the continuous sphere-valued
  forward-ray map and its boundary identity under a boundary-only image condition.
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

/-- Transfer the boundary-only unit-disk fixed-point theorem to complex closed balls. -/
private theorem exists_fixedPoint_closedBall_of_unit
    (hunit : ∀ g : C(Metric.closedBall (0 : ℂ) 1, ℂ),
      (∀ y : Metric.sphere (0 : ℂ) 1,
        g ((ContinuousMap.inclusion
          (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1)) :
            C(Metric.sphere (0 : ℂ) 1, Metric.closedBall (0 : ℂ) 1)) y) ∈
          Metric.closedBall (0 : ℂ) 1) →
      ∃ z : Metric.closedBall (0 : ℂ) 1, g z = (z : ℂ))
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (F : C(Metric.closedBall c r, ℂ))
    (hboundary : ∀ y : Metric.sphere c r,
      F ((ContinuousMap.inclusion
        (Metric.sphere_subset_closedBall (x := c) (ε := r)) :
          C(Metric.sphere c r, Metric.closedBall c r)) y) ∈
        Metric.closedBall c r) :
    ∃ z : Metric.closedBall c r, F z = (z : ℂ) := by
  by_cases hr0 : r = 0
  · subst r
    let z : Metric.closedBall c 0 := ⟨c, Metric.mem_closedBall_self le_rfl⟩
    have h := hboundary ⟨c, by simp only [Metric.sphere_zero, Set.mem_singleton_iff]⟩
    change F z ∈ Metric.closedBall c 0 at h
    exact ⟨z, by simpa only [Metric.closedBall_zero, Set.mem_singleton_iff] using h⟩
  · let e : ℂ ≃ₜ ℂ :=
      (Homeomorph.smulOfNeZero r hr0).trans
        (IsometryEquiv.constVAdd c).toHomeomorph
    have he : e '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall c r := by
      change ((fun z : ℂ => c +ᵥ z) ∘ (fun z : ℂ => r • z)) ''
        Metric.closedBall (0 : ℂ) 1 = Metric.closedBall c r
      rw [Set.image_comp, Set.image_smul, Set.image_vadd]
      exact affinity_unitClosedBall hr c
    have hs : e '' Metric.sphere (0 : ℂ) 1 = Metric.sphere c r := by
      change ((fun z : ℂ => c +ᵥ z) ∘ (fun z : ℂ => r • z)) ''
        Metric.sphere (0 : ℂ) 1 = Metric.sphere c r
      rw [Set.image_comp, Set.image_smul, Set.image_vadd, smul_sphere' hr0]
      simp only [smul_zero, Real.norm_of_nonneg hr, mul_one, Metric.vadd_sphere,
        vadd_eq_add, add_zero]
    let eball : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall c r :=
      (e.image _).trans (Homeomorph.setCongr he)
    let g : C(Metric.closedBall (0 : ℂ) 1, ℂ) :=
      (toContinuousMap e.symm).comp (F.comp (toContinuousMap eball))
    let inclusion : C(Metric.sphere (0 : ℂ) 1, Metric.closedBall (0 : ℂ) 1) :=
      ContinuousMap.inclusion
        (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1))
    have hg (y : Metric.sphere (0 : ℂ) 1) :
        g (inclusion y) ∈ Metric.closedBall (0 : ℂ) 1 := by
      let y' : Metric.sphere c r :=
        ⟨e (y : ℂ), hs ▸ Set.mem_image_of_mem e y.property⟩
      change F (eball (inclusion y)) ∈ e.symm ⁻¹' Metric.closedBall (0 : ℂ) 1
      rw [← e.image_eq_preimage_symm, he]
      exact hboundary y'
    obtain ⟨z, hz⟩ := hunit g hg
    refine ⟨eball z, ?_⟩
    change e.symm (F (eball z)) = (z : ℂ) at hz
    exact e.symm_apply_eq.mp hz

private theorem exists_fixedPoint_unitClosedBall
    (F : C(Metric.closedBall (0 : ℂ) 1, ℂ))
    (hboundary : ∀ y : Metric.sphere (0 : ℂ) 1,
      F ((ContinuousMap.inclusion
        (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1)) :
          C(Metric.sphere (0 : ℂ) 1, Metric.closedBall (0 : ℂ) 1)) y) ∈
        Metric.closedBall (0 : ℂ) 1) :
    ∃ z : Metric.closedBall (0 : ℂ) 1, F z = (z : ℂ) := by
  by_contra hfixed
  have hF : ∀ x, F x ≠ (x : ℂ) := fun x h => hfixed ⟨x, h⟩
  let s : EuclideanGeometry.Sphere ℂ := ⟨0, 1⟩
  apply Circle.comp_closedBall_inclusion_ne_id (s.rayInterMap F hF)
  exact s.rayInterMap_comp_inclusion F hF hboundary

/-- A continuous complex-valued map on a closed ball with nonnegative radius has a
fixed point if it sends the sphere boundary into that ball. No image bound is
required at interior points.

This generalizes the closed unit disk self-map theorem in May, Chapter 1, §6,
p. 10, to arbitrary centers, nonnegative radii and a boundary-only image condition.
The ordinary closed-ball self-map theorem is a specialization. -/
theorem exists_fixedPoint_closedBall_of_boundary_mapsTo
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (F : C(Metric.closedBall c r, ℂ))
    (hboundary : ∀ y : Metric.sphere c r,
      F ((ContinuousMap.inclusion
        (Metric.sphere_subset_closedBall (x := c) (ε := r)) :
          C(Metric.sphere c r, Metric.closedBall c r)) y) ∈
        Metric.closedBall c r) :
    ∃ x : Metric.closedBall c r, F x = (x : ℂ) := by
  exact exists_fixedPoint_closedBall_of_unit exists_fixedPoint_unitClosedBall c hr F hboundary

/-- Every continuous self-map of a nonempty complex closed ball has a fixed point.
This is the disk case of Brouwer's fixed-point theorem. The unit-disk statement is
May, Chapter 1, §6, p. 10; arbitrary centers and nonnegative radii follow by affine
transport and the radius-zero singleton case. -/
theorem exists_fixedPoint_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (f : C(Metric.closedBall c r, Metric.closedBall c r)) :
    ∃ z, f z = z := by
  obtain ⟨z, hz⟩ := exists_fixedPoint_closedBall_of_boundary_mapsTo c hr
    ((ContinuousMap.subtypeVal _).comp f)
    (fun y => (f (ContinuousMap.inclusion
      (Metric.sphere_subset_closedBall (x := c) (ε := r)) y)).property)
  exact ⟨z, Subtype.ext hz⟩

end Complex
