/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.Projectivization
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Covering.Quotient

/-!
# The unit sphere projection to real projective space

A unit vector determines its real line, giving a continuous map from the metric
unit sphere to `Projectivization ℝ E` with its quotient topology from nonzero
vectors. The sphere uses the given norm on `E`; no inner product, dimension,
completeness or nonemptiness assumption is imposed. In the zero vector space both
the sphere and projectivization are empty.

The unit sphere in `ℝ`, with Mathlib's multiplication and scalar action, is the
two-element group acting by the identity and negation. The sphere projection is a
quotient covering for this action. This formulation also includes the two-point
unit sphere in `ℝ` mapping to its one-point projectivization.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §2,
  gives the antipodal sphere covering of real projective space. The formulation
  here extends the finite Euclidean setting to arbitrary real normed spaces with
  their original norm.
* Mathlib's projectivization and quotient-topology APIs supply the target and its
  maker. Its normed sphere actions, radial decomposition
  `homeomorphUnitSphereProd`, and quotient-covering API supply the standard
  scalar-action and radial approach to the covering statement.
-/

@[expose] public section

universe w

namespace Metric.Sphere

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Send a unit vector, for the given norm on `E`, to the real line it represents. -/
noncomputable def toProjectivization : C(Metric.sphere (0 : E) 1, Projectivization ℝ E) where
  toFun p := Projectivization.mk ℝ (p : E) (ne_zero_of_mem_unit_sphere p)
  continuous_toFun :=
    (Projectivization.continuous_mk' ℝ (V := E)).comp
      (continuous_subtype_val.subtype_mk (fun p : Metric.sphere (0 : E) 1 =>
        ne_zero_of_mem_unit_sphere p))

/-- The sphere projection is the projective point represented by that unit vector. -/
@[simp]
theorem toProjectivization_apply (p : Metric.sphere (0 : E) 1) :
    toProjectivization p =
      Projectivization.mk ℝ (p : E) (ne_zero_of_mem_unit_sphere p) :=
  rfl

/-- The unit sphere projection is a quotient map, including when both spaces are empty. -/
theorem isQuotientMap_toProjectivization :
    Topology.IsQuotientMap (toProjectivization (E := E)) := by
  let r : {v : E // v ≠ 0} → Metric.sphere (0 : E) 1 :=
    fun v => (homeomorphUnitSphereProd E v).1
  have hr : Continuous r :=
    continuous_fst.comp (homeomorphUnitSphereProd E).continuous
  have hcomp : toProjectivization (E := E) ∘ r = Projectivization.mk' ℝ := by
    funext v
    rw [Function.comp_apply, toProjectivization_apply, Projectivization.mk'_eq_mk,
      Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 ‖(v : E)‖⁻¹ (inv_ne_zero (norm_ne_zero_iff.mpr v.2)), ?_⟩
    exact (homeomorphUnitSphereProd_apply_fst_coe E v).symm
  apply Topology.IsQuotientMap.of_comp hr (toProjectivization (E := E)).continuous
  rw [hcomp]
  exact Projectivization.isQuotientMap_mk' ℝ

/-- Two unit vectors represent the same real projective point exactly when they lie
in the same orbit under scalar multiplication by the real unit sphere. -/
theorem toProjectivization_eq_iff_mem_orbit {p q : Metric.sphere (0 : E) 1} :
    toProjectivization p = toProjectivization q ↔
      p ∈ MulAction.orbit (Metric.sphere (0 : ℝ) 1) q := by
  rw [toProjectivization_apply, toProjectivization_apply,
    Projectivization.mk_eq_mk_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [Units.smul_def] at ha
    -- A scalar relating two unit vectors must itself have norm one.
    have ha_norm : ‖(a : ℝ)‖ = 1 := by
      have hnorm := congrArg (fun x : E => ‖x‖) ha
      simpa only [norm_smul, mem_sphere_zero_iff_norm.mp q.property,
        mem_sphere_zero_iff_norm.mp p.property, mul_one] using hnorm
    refine ⟨⟨(a : ℝ), mem_sphere_zero_iff_norm.mpr ha_norm⟩, ?_⟩
    exact Subtype.ext ha
  · rintro ⟨a, ha⟩
    refine ⟨unitSphereToUnits ℝ a, ?_⟩
    rw [Units.smul_def, unitSphereToUnits_apply_coe]
    exact congrArg (fun x : Metric.sphere (0 : E) 1 => (x : E)) ha

/-- Two unit vectors represent the same real projective point exactly when they
are equal or antipodal. -/
theorem toProjectivization_eq_iff_eq_or_eq_neg {p q : Metric.sphere (0 : E) 1} :
    toProjectivization p = toProjectivization q ↔ p = q ∨ p = -q := by
  rw [toProjectivization_eq_iff_mem_orbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨a, ha⟩
    have ha_sign : (a : ℝ) = -1 ∨ (a : ℝ) = 1 := by
      simpa only [Real.sphere_eq_pair (0 : ℝ) (r := 1) zero_le_one,
        zero_sub, zero_add, Set.mem_insert_iff, Set.mem_singleton_iff] using a.property
    have ha_coe : (a : ℝ) • (q : E) = (p : E) :=
      congrArg (fun x : Metric.sphere (0 : E) 1 => (x : E)) ha
    rcases ha_sign with ha_sign | ha_sign
    · right
      apply Subtype.ext
      simpa only [ha_sign, neg_one_smul, coe_neg_sphere] using ha_coe.symm
    · left
      apply Subtype.ext
      simpa only [ha_sign, one_smul] using ha_coe.symm
  · rintro (h | h)
    · exact ⟨1, (one_smul _ q).trans h.symm⟩
    · refine ⟨(-1 : Metric.sphere (0 : ℝ) 1), ?_⟩
      rw [h]
      apply Subtype.ext
      change ((-1 : Metric.sphere (0 : ℝ) 1) : ℝ) • (q : E) = -(q : E)
      simp

/-- Negating a unit vector does not change its real projective point. -/
theorem toProjectivization_neg (p : Metric.sphere (0 : E) 1) :
    toProjectivization (-p) = toProjectivization p :=
  toProjectivization_eq_iff_eq_or_eq_neg.mpr (Or.inr rfl)

open Topology

/-- Every point of a real unit sphere has a neighborhood disjoint from all its
nonidentity translates by the real unit sphere's scalar action. -/
private theorem exists_nhds_image_smul_eq_one (p : Metric.sphere (0 : E) 1) :
    ∃ U ∈ 𝓝 p, ∀ g : Metric.sphere (0 : ℝ) 1,
      (((g • ·) '' U) ∩ U).Nonempty → g = 1 := by
  refine ⟨Metric.ball p 1, Metric.ball_mem_nhds p zero_lt_one, ?_⟩
  intro g h
  have hg : (g : ℝ) = -1 ∨ (g : ℝ) = 1 := by
    simpa only [Real.sphere_eq_pair 0 zero_le_one, zero_sub, zero_add,
      Set.mem_insert_iff, Set.mem_singleton_iff] using g.property
  rcases hg with hg | hg
  · obtain ⟨_, ⟨x, hx, rfl⟩, hgx⟩ := h
    have hx' : dist (x : E) (p : E) < 1 := hx
    have hgx' : dist ((g : ℝ) • (x : E)) (p : E) < 1 := hgx
    rw [hg, neg_one_smul] at hgx'
    have hdist : dist (x : E) (-(x : E)) = 2 := by
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ (x : E), norm_smul,
        mem_sphere_zero_iff_norm.mp x.property, Real.norm_of_nonneg zero_le_two, mul_one]
    have hlt : dist (x : E) (-(x : E)) < 2 :=
      (dist_triangle_right _ _ (p : E)).trans_lt (by
        simpa only [one_add_one_eq_two] using add_lt_add hx' hgx')
    exact (ne_of_lt hlt hdist).elim
  · exact Subtype.ext hg

/-- The unit sphere projection is a quotient covering for the scalar action of
`Metric.sphere (0 : ℝ) 1`, whose elements act by the identity and negation.

This is the real-normed-space form of the antipodal covering in May,
Chapter 3, §2; it requires neither a dimension bound nor a nonempty sphere. -/
theorem isQuotientCoveringMap_toProjectivization :
    IsQuotientCoveringMap (toProjectivization (E := E)) (Metric.sphere (0 : ℝ) 1) := by
  exact
    { toIsQuotientMap := isQuotientMap_toProjectivization
      toContinuousConstSMul := inferInstance
      apply_eq_iff_mem_orbit := toProjectivization_eq_iff_mem_orbit
      disjoint := exists_nhds_image_smul_eq_one }

end Metric.Sphere
