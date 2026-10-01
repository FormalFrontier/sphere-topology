/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

public import SphereTopology.Homology.Singular.Circle
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Constructions

/-!
# Reduced integral homology of the standard two-sphere

This module equips the literal unit sphere in `EuclideanSpace ℝ (Fin 3)` with
the ordered north/south puncture cover.  Stereographic projection contracts
the two opens.  On their intersection, the explicit normalized homotopy

`(x,y,z) ↦ (x,y,t*z) / ‖(x,y,t*z)‖`

deforms the twice-punctured sphere onto the equator while fixing the equator
pointwise.  The equator is then identified with the standard oriented circle
by retaining coordinates zero and one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap
open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- Real Euclidean three-space, with coordinate order `(x, y, z)`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The vector `(0, 0, 1)` in `E3`, with the third coordinate indexed by `2`. -/
def sphere2NorthVector : E3 := PiLp.single 2 2 1

@[simp] lemma sphere2NorthVector_norm : ‖sphere2NorthVector‖ = 1 := by
  simp [sphere2NorthVector]

/-- The north pole `(0, 0, 1)` bundled as a point of the metric unit two-sphere. -/
def sphere2NorthPoint : Metric.sphere (0 : E3) 1 := ⟨sphere2NorthVector, by
  rw [mem_sphere_zero_iff_norm]
  exact sphere2NorthVector_norm⟩

/-- The south pole `(0, 0, -1)`, defined as the antipode of the north pole. -/
def sphere2SouthPoint : Metric.sphere (0 : E3) 1 := -sphere2NorthPoint

@[simp] lemma sphere2NorthPoint_first : ((sphere2NorthPoint : E3) 0) = 0 := by
  simp [sphere2NorthPoint, sphere2NorthVector]

@[simp] lemma sphere2NorthPoint_second : ((sphere2NorthPoint : E3) 1) = 0 := by
  simp [sphere2NorthPoint, sphere2NorthVector]

@[simp] lemma sphere2NorthPoint_third : ((sphere2NorthPoint : E3) 2) = 1 := by
  simp [sphere2NorthPoint, sphere2NorthVector]

@[simp] lemma sphere2SouthPoint_first : ((sphere2SouthPoint : E3) 0) = 0 := by
  simp [sphere2SouthPoint]

@[simp] lemma sphere2SouthPoint_second : ((sphere2SouthPoint : E3) 1) = 0 := by
  simp [sphere2SouthPoint]

@[simp] lemma sphere2SouthPoint_third : ((sphere2SouthPoint : E3) 2) = -1 := by
  simp [sphere2SouthPoint]

lemma sphere2NorthPoint_ne_southPoint : sphere2NorthPoint ≠ sphere2SouthPoint := by
  intro h
  have := congrArg (fun p : Metric.sphere (0 : E3) 1 => (p.1 : E3) 2) h
  norm_num at this

/-- The literal standard metric two-sphere. -/
abbrev sphere2 : TopCat :=
  TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

/-- The first open in the ordered cover: the complement of the north pole. -/
def sphere2NorthPunctured : TopologicalSpace.Opens sphere2 :=
  ⟨{sphere2NorthPoint}ᶜ, isOpen_compl_singleton⟩

/-- The second open in the ordered cover: the complement of the south pole. -/
def sphere2SouthPunctured : TopologicalSpace.Opens sphere2 :=
  ⟨{sphere2SouthPoint}ᶜ, isOpen_compl_singleton⟩

lemma sphere2Punctured_join :
    sphere2NorthPunctured ⊔ sphere2SouthPunctured = ⊤ := by
  ext p
  change (p ≠ sphere2NorthPoint ∨ p ≠ sphere2SouthPoint) ↔ True
  simp only [iff_true]
  by_contra h
  rcases not_or.mp h with ⟨hn, hs⟩
  exact sphere2NorthPoint_ne_southPoint
    ((not_ne_iff.mp hn).symm.trans (not_ne_iff.mp hs))

lemma sphere2Punctured_join_reversed :
    sphere2SouthPunctured ⊔ sphere2NorthPunctured = ⊤ := by
  rw [sup_comm]
  exact sphere2Punctured_join

/-- Stereographic coordinates on the north-punctured sphere. -/
noncomputable def sphere2NorthPuncturedHomeomorph :
    ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured : Type) ≃ₜ
      EuclideanSpace ℝ (Fin 2) := by
  letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  exact (Homeomorph.setCongr (by simp [sphere2NorthPunctured])).trans
    (stereographic' 2 sphere2NorthPoint).toHomeomorphSourceTarget |>.trans
    (Homeomorph.setCongr (stereographic'_target sphere2NorthPoint)) |>.trans
    (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 2)))

/-- Stereographic coordinates on the south-punctured sphere. -/
noncomputable def sphere2SouthPuncturedHomeomorph :
    ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured : Type) ≃ₜ
      EuclideanSpace ℝ (Fin 2) := by
  letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  exact (Homeomorph.setCongr (by simp [sphere2SouthPunctured])).trans
    (stereographic' 2 sphere2SouthPoint).toHomeomorphSourceTarget |>.trans
    (Homeomorph.setCongr (stereographic'_target sphere2SouthPoint)) |>.trans
    (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 2)))

/-- The literal intersection of the ordered north/south puncture cover. -/
abbrev sphere2PunctureIntersection :=
  ((TopologicalSpace.Opens.toTopCat sphere2).obj
    (sphere2NorthPunctured ⊓ sphere2SouthPunctured) : Type)

/-- The literal equator, as a subtype of the literal standard two-sphere. -/
abbrev sphere2Equator :=
  {p : Metric.sphere (0 : E3) 1 // (p.1 : E3) 2 = 0}

lemma sphere2_eq_north_or_south_of_first_second_eq_zero
    (p : Metric.sphere (0 : E3) 1)
    (hx : (p.1 : E3) 0 = 0) (hy : (p.1 : E3) 1 = 0) :
    p = sphere2NorthPoint ∨ p = sphere2SouthPoint := by
  have hnorm : ‖(p.1 : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  have hsq := EuclideanSpace.real_norm_sq_eq (p.1 : E3)
  rw [hnorm, Fin.sum_univ_three, hx, hy] at hsq
  norm_num at hsq
  rcases sq_eq_one_iff.mp hsq.symm with hz | hz
  · left
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [sphere2NorthPoint, sphere2NorthVector, hx, hy, hz]
  · right
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [sphere2SouthPoint, sphere2NorthPoint, sphere2NorthVector, hx, hy, hz]

lemma sphere2PunctureIntersection_first_second_not_both_zero
    (p : sphere2PunctureIntersection) :
    ¬ ((p.1.1 : E3) 0 = 0 ∧ (p.1.1 : E3) 1 = 0) := by
  rintro ⟨hx, hy⟩
  rcases sphere2_eq_north_or_south_of_first_second_eq_zero p.1 hx hy with hn | hs
  · exact p.2.1 hn
  · exact p.2.2 hs

/-- Before normalization, scale only the third coordinate by the homotopy
parameter.  The first two coordinates remain unchanged. -/
def sphere2PunctureIntersectionLinearVector
    (t : unitInterval) (p : sphere2PunctureIntersection) : E3 :=
  WithLp.toLp 2 ![(p.1.1 : E3) 0, (p.1.1 : E3) 1,
    (t : ℝ) * (p.1.1 : E3) 2]

@[simp] lemma sphere2PunctureIntersectionLinearVector_first
    (t : unitInterval) (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionLinearVector t p 0 = (p.1.1 : E3) 0 := by
  simp [sphere2PunctureIntersectionLinearVector]

@[simp] lemma sphere2PunctureIntersectionLinearVector_second
    (t : unitInterval) (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionLinearVector t p 1 = (p.1.1 : E3) 1 := by
  simp [sphere2PunctureIntersectionLinearVector]

lemma sphere2PunctureIntersectionLinearVector_third
    (t : unitInterval) (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionLinearVector t p 2 =
      (t : ℝ) * (p.1.1 : E3) 2 := by
  simp [sphere2PunctureIntersectionLinearVector]

lemma sphere2PunctureIntersectionLinearVector_ne_zero
    (t : unitInterval) (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionLinearVector t p ≠ 0 := by
  intro h
  apply sphere2PunctureIntersection_first_second_not_both_zero p
  constructor
  · have h0 := congrArg (fun v : E3 => v 0) h
    simpa using h0
  · have h1 := congrArg (fun v : E3 => v 1) h
    simpa using h1

/-- The normalized equatorial-deformation vector. -/
def sphere2PunctureIntersectionRadialVector
    (t : unitInterval) (p : sphere2PunctureIntersection) : E3 :=
  ‖sphere2PunctureIntersectionLinearVector t p‖⁻¹ •
    sphere2PunctureIntersectionLinearVector t p

lemma sphere2PunctureIntersectionRadialVector_norm
    (t : unitInterval) (p : sphere2PunctureIntersection) :
    ‖sphere2PunctureIntersectionRadialVector t p‖ = 1 := by
  rw [sphere2PunctureIntersectionRadialVector, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr
    (sphere2PunctureIntersectionLinearVector_ne_zero t p)

lemma sphere2PunctureIntersectionRadialVector_first_second_not_both_zero
    (t : unitInterval) (p : sphere2PunctureIntersection) :
    ¬ (sphere2PunctureIntersectionRadialVector t p 0 = 0 ∧
      sphere2PunctureIntersectionRadialVector t p 1 = 0) := by
  rintro ⟨hx, hy⟩
  apply sphere2PunctureIntersection_first_second_not_both_zero p
  have hn : ‖sphere2PunctureIntersectionLinearVector t p‖⁻¹ ≠ 0 :=
    inv_ne_zero (norm_ne_zero_iff.mpr
      (sphere2PunctureIntersectionLinearVector_ne_zero t p))
  constructor
  · rw [sphere2PunctureIntersectionRadialVector, PiLp.smul_apply,
      smul_eq_mul, sphere2PunctureIntersectionLinearVector_first] at hx
    exact (mul_eq_zero.mp hx).resolve_left hn
  · rw [sphere2PunctureIntersectionRadialVector, PiLp.smul_apply,
      smul_eq_mul, sphere2PunctureIntersectionLinearVector_second] at hy
    exact (mul_eq_zero.mp hy).resolve_left hn

/-- The normalized homotopy stays on the literal twice-punctured sphere. -/
def sphere2PunctureIntersectionRadialPoint
    (t : unitInterval) (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersection :=
  ⟨⟨sphere2PunctureIntersectionRadialVector t p,
      mem_sphere_zero_iff_norm.mpr
        (sphere2PunctureIntersectionRadialVector_norm t p)⟩, by
    constructor <;> intro h
    · apply sphere2PunctureIntersectionRadialVector_first_second_not_both_zero t p
      constructor
      · have := congrArg (fun q : Metric.sphere (0 : E3) 1 => (q.1 : E3) 0) h
        simpa using this
      · have := congrArg (fun q : Metric.sphere (0 : E3) 1 => (q.1 : E3) 1) h
        simpa using this
    · apply sphere2PunctureIntersectionRadialVector_first_second_not_both_zero t p
      constructor
      · have := congrArg (fun q : Metric.sphere (0 : E3) 1 => (q.1 : E3) 0) h
        simpa using this
      · have := congrArg (fun q : Metric.sphere (0 : E3) 1 => (q.1 : E3) 1) h
        simpa using this⟩

lemma continuous_sphere2PunctureIntersectionLinearVector :
    Continuous (fun q : unitInterval × sphere2PunctureIntersection =>
      sphere2PunctureIntersectionLinearVector q.1 q.2) := by
  unfold sphere2PunctureIntersectionLinearVector
  apply (PiLp.continuous_toLp 2 _).comp
  fun_prop

lemma continuous_sphere2PunctureIntersectionRadialPoint :
    Continuous (fun q : unitInterval × sphere2PunctureIntersection =>
      sphere2PunctureIntersectionRadialPoint q.1 q.2) := by
  have hlin := continuous_sphere2PunctureIntersectionLinearVector
  have hnorm : Continuous (fun q : unitInterval × sphere2PunctureIntersection =>
      ‖sphere2PunctureIntersectionLinearVector q.1 q.2‖) := hlin.norm
  exact ((hnorm.inv₀ fun q => norm_ne_zero_iff.mpr
      (sphere2PunctureIntersectionLinearVector_ne_zero q.1 q.2)).smul hlin).subtype_mk _
    |>.subtype_mk _

/-- The jointly continuous map obtained by normalizing `(x, y, t * z)` on the
twice-punctured sphere. At time zero it projects to the equator; at time one it
is the identity, and equatorial points remain fixed throughout. -/
def sphere2PunctureIntersectionRadialHomotopyMap :
    C(unitInterval × sphere2PunctureIntersection, sphere2PunctureIntersection) :=
  ⟨fun q => sphere2PunctureIntersectionRadialPoint q.1 q.2,
    continuous_sphere2PunctureIntersectionRadialPoint⟩

lemma sphere2PunctureIntersectionRadialVector_zero_third
    (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionRadialVector 0 p 2 = 0 := by
  simp [sphere2PunctureIntersectionRadialVector,
    sphere2PunctureIntersectionLinearVector_third]

/-- Evaluation of the radial homotopy at its equatorial endpoint. -/
def sphere2PunctureIntersectionRadialAtZero :
    C(sphere2PunctureIntersection, sphere2PunctureIntersection) :=
  sphere2PunctureIntersectionRadialHomotopyMap.comp
    ⟨fun p => (0, p), continuous_const.prodMk continuous_id⟩

/-- The point-valued equatorial projection underlying the continuous map. -/
def sphere2PunctureIntersectionToEquatorPoint
    (p : sphere2PunctureIntersection) : sphere2Equator :=
  ⟨(sphere2PunctureIntersectionRadialAtZero p).1,
    sphere2PunctureIntersectionRadialVector_zero_third p⟩

lemma continuous_sphere2PunctureIntersectionToEquatorPoint :
    Continuous sphere2PunctureIntersectionToEquatorPoint := by
  exact (continuous_subtype_val.comp
    sphere2PunctureIntersectionRadialAtZero.continuous).subtype_mk _

/-- Projection of the twice-punctured sphere onto the literal equator. -/
def sphere2PunctureIntersectionToEquator :
    C(sphere2PunctureIntersection, sphere2Equator) :=
  ⟨sphere2PunctureIntersectionToEquatorPoint,
    continuous_sphere2PunctureIntersectionToEquatorPoint⟩

/-- The point-valued inclusion underlying the equator continuous map. -/
def sphere2EquatorToPunctureIntersectionPoint
    (p : sphere2Equator) : sphere2PunctureIntersection :=
  ⟨p.1, by
      constructor
      · change p.1 ≠ sphere2NorthPoint
        intro h
        have hcoord := congrArg
          (fun q : Metric.sphere (0 : E3) 1 => (q.1 : E3) 2) h
        rw [p.2] at hcoord
        norm_num at hcoord
      · change p.1 ≠ sphere2SouthPoint
        intro h
        have hcoord := congrArg
          (fun q : Metric.sphere (0 : E3) 1 => (q.1 : E3) 2) h
        rw [p.2] at hcoord
        norm_num at hcoord⟩

lemma continuous_sphere2EquatorToPunctureIntersectionPoint :
    Continuous sphere2EquatorToPunctureIntersectionPoint := by
  exact continuous_subtype_val.subtype_mk _

/-- Inclusion of the literal equator into the twice-punctured sphere. -/
def sphere2EquatorToPunctureIntersection :
    C(sphere2Equator, sphere2PunctureIntersection) :=
  ⟨sphere2EquatorToPunctureIntersectionPoint,
    continuous_sphere2EquatorToPunctureIntersectionPoint⟩

lemma sphere2PunctureIntersectionRadialPoint_zero
    (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionRadialPoint 0 p =
    sphere2EquatorToPunctureIntersection
        (sphere2PunctureIntersectionToEquator p) := by
  apply Subtype.ext
  apply Subtype.ext
  change sphere2PunctureIntersectionRadialVector 0 p =
    sphere2PunctureIntersectionRadialVector 0 p
  rfl

lemma sphere2PunctureIntersectionRadialPoint_one
    (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionRadialPoint 1 p = p := by
  apply Subtype.ext
  apply Subtype.ext
  have hlin : sphere2PunctureIntersectionLinearVector 1 p = p.1.1 := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [sphere2PunctureIntersectionLinearVector]
  change ‖sphere2PunctureIntersectionLinearVector 1 p‖⁻¹ •
    sphere2PunctureIntersectionLinearVector 1 p = p.1.1
  rw [hlin]
  simp [mem_sphere_zero_iff_norm.mp p.1.2]

/-- The normalized deformation fixes every equator point at every time. -/
lemma sphere2PunctureIntersectionRadialPoint_fixed
    (t : unitInterval) (p : sphere2Equator) :
    sphere2PunctureIntersectionRadialPoint t
      (sphere2EquatorToPunctureIntersection p) =
      sphere2EquatorToPunctureIntersection p := by
  have hlin : sphere2PunctureIntersectionLinearVector t
      (sphere2EquatorToPunctureIntersection p) = p.1.1 := by
    change sphere2PunctureIntersectionLinearVector t
      (sphere2EquatorToPunctureIntersectionPoint p) = p.1.1
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [sphere2PunctureIntersectionLinearVector,
        sphere2EquatorToPunctureIntersectionPoint, p.2]
  apply Subtype.ext
  apply Subtype.ext
  change ‖sphere2PunctureIntersectionLinearVector t
      (sphere2EquatorToPunctureIntersection p)‖⁻¹ •
      sphere2PunctureIntersectionLinearVector t
        (sphere2EquatorToPunctureIntersection p) = p.1.1
  rw [hlin]
  simp [mem_sphere_zero_iff_norm.mp p.1.2]

@[simp]
lemma sphere2PunctureIntersectionToEquator_inclusion (p : sphere2Equator) :
    sphere2PunctureIntersectionToEquator
      (sphere2EquatorToPunctureIntersection p) = p := by
  apply Subtype.ext
  change (sphere2PunctureIntersectionRadialPoint 0
    (sphere2EquatorToPunctureIntersection p)).1 = p.1
  have hfixed := sphere2PunctureIntersectionRadialPoint_fixed 0 p
  change sphere2PunctureIntersectionRadialPoint 0
    (sphere2EquatorToPunctureIntersectionPoint p) =
    sphere2EquatorToPunctureIntersectionPoint p at hfixed
  have hsphere := congrArg (fun q : sphere2PunctureIntersection => q.1) hfixed
  change (sphere2PunctureIntersectionRadialPoint 0
    (sphere2EquatorToPunctureIntersectionPoint p)).1 = p.1 at hsphere
  exact hsphere

/-- The explicit normalized deformation homotopy, from equatorial projection
followed by inclusion to the identity. -/
def sphere2PunctureIntersectionRadialHomotopy :
    (sphere2EquatorToPunctureIntersection.comp
      sphere2PunctureIntersectionToEquator).Homotopy
        (ContinuousMap.id sphere2PunctureIntersection) :=
  ⟨sphere2PunctureIntersectionRadialHomotopyMap,
    sphere2PunctureIntersectionRadialPoint_zero,
    sphere2PunctureIntersectionRadialPoint_one⟩

/-- The literal twice-punctured sphere is homotopy equivalent to its literal
equator through the displayed projection, inclusion, and deformation. -/
noncomputable def sphere2PunctureIntersectionEquatorHomotopyEquiv :
    sphere2PunctureIntersection ≃ₕ sphere2Equator where
  toFun := sphere2PunctureIntersectionToEquator
  invFun := sphere2EquatorToPunctureIntersection
  left_inv := ⟨sphere2PunctureIntersectionRadialHomotopy⟩
  right_inv := by
    have h : sphere2PunctureIntersectionToEquator.comp
        sphere2EquatorToPunctureIntersection =
        ContinuousMap.id sphere2Equator := by
      apply ContinuousMap.ext
      intro p
      exact sphere2PunctureIntersectionToEquator_inclusion p
    exact h ▸ ContinuousMap.Homotopic.refl _

/-- A genuine universe-lifted client of the intersection/equator geometry. -/
noncomputable def sphere2PunctureIntersectionEquatorHomotopyEquivULift :
    ULift sphere2PunctureIntersection ≃ₕ ULift sphere2Equator :=
  Homeomorph.ulift.toHomotopyEquiv |>.trans
    sphere2PunctureIntersectionEquatorHomotopyEquiv |>.trans
    Homeomorph.ulift.symm.toHomotopyEquiv

/-- Keep coordinates zero and one of an equator point, in that order. -/
def sphere2EquatorToCircleVector (p : sphere2Equator) : E2 :=
  WithLp.toLp 2 ![(p.1.1 : E3) 0, (p.1.1 : E3) 1]

/-- Insert a circle point into the first two coordinates of `E3`; the third
coordinate is zero. -/
def sphere1ToSphere2EquatorVector (p : Metric.sphere (0 : E2) 1) : E3 :=
  WithLp.toLp 2 ![(p.1 : E2) 0, (p.1 : E2) 1, 0]

@[simp] lemma sphere2EquatorToCircleVector_first (p : sphere2Equator) :
    sphere2EquatorToCircleVector p 0 = (p.1.1 : E3) 0 := by
  simp [sphere2EquatorToCircleVector]

@[simp] lemma sphere2EquatorToCircleVector_second (p : sphere2Equator) :
    sphere2EquatorToCircleVector p 1 = (p.1.1 : E3) 1 := by
  simp [sphere2EquatorToCircleVector]

@[simp] lemma sphere1ToSphere2EquatorVector_first
    (p : Metric.sphere (0 : E2) 1) :
    sphere1ToSphere2EquatorVector p 0 = (p.1 : E2) 0 := by
  simp [sphere1ToSphere2EquatorVector]

@[simp] lemma sphere1ToSphere2EquatorVector_second
    (p : Metric.sphere (0 : E2) 1) :
    sphere1ToSphere2EquatorVector p 1 = (p.1 : E2) 1 := by
  simp [sphere1ToSphere2EquatorVector]

@[simp] lemma sphere1ToSphere2EquatorVector_third
    (p : Metric.sphere (0 : E2) 1) :
    sphere1ToSphere2EquatorVector p 2 = 0 := by
  simp [sphere1ToSphere2EquatorVector]

lemma sphere2EquatorToCircleVector_norm (p : sphere2Equator) :
    ‖sphere2EquatorToCircleVector p‖ = 1 := by
  have hpNorm : ‖(p.1.1 : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
  have hpSq := EuclideanSpace.real_norm_sq_eq (p.1.1 : E3)
  rw [hpNorm, Fin.sum_univ_three, p.2] at hpSq
  have hSq := EuclideanSpace.real_norm_sq_eq (sphere2EquatorToCircleVector p)
  rw [Fin.sum_univ_two] at hSq
  simp only [sphere2EquatorToCircleVector_first,
    sphere2EquatorToCircleVector_second] at hSq
  nlinarith [norm_nonneg (sphere2EquatorToCircleVector p)]

lemma sphere1ToSphere2EquatorVector_norm
    (p : Metric.sphere (0 : E2) 1) :
    ‖sphere1ToSphere2EquatorVector p‖ = 1 := by
  have hpNorm : ‖(p.1 : E2)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  have hpSq := EuclideanSpace.real_norm_sq_eq (p.1 : E2)
  rw [hpNorm, Fin.sum_univ_two] at hpSq
  have hSq : ‖sphere1ToSphere2EquatorVector p‖ ^ 2 = 1 := by
    calc
      ‖sphere1ToSphere2EquatorVector p‖ ^ 2 =
          ∑ i, (sphere1ToSphere2EquatorVector p i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq _
      _ = (p.1 : E2) 0 ^ 2 + (p.1 : E2) 1 ^ 2 := by
        simp [Fin.sum_univ_three, sphere1ToSphere2EquatorVector]
      _ = 1 := by nlinarith
  nlinarith [norm_nonneg (sphere1ToSphere2EquatorVector p)]

/-- The orientation-fixed coordinate homeomorphism from the equator to the
accepted standard circle: `(x,y,0)` is sent to `(x,y)`. -/
noncomputable def sphere2EquatorHomeomorphSphere1 :
    sphere2Equator ≃ₜ (sphere1 : Type) where
  toFun p := ⟨sphere2EquatorToCircleVector p,
    mem_sphere_zero_iff_norm.mpr (sphere2EquatorToCircleVector_norm p)⟩
  invFun p := ⟨⟨sphere1ToSphere2EquatorVector p,
    mem_sphere_zero_iff_norm.mpr (sphere1ToSphere2EquatorVector_norm p)⟩,
    sphere1ToSphere2EquatorVector_third p⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [sphere2EquatorToCircleVector,
      sphere1ToSphere2EquatorVector, p.2]
  right_inv p := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [sphere2EquatorToCircleVector,
      sphere1ToSphere2EquatorVector]
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold sphere2EquatorToCircleVector
    apply (PiLp.continuous_toLp 2 _).comp
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    unfold sphere1ToSphere2EquatorVector
    apply (PiLp.continuous_toLp 2 _).comp
    fun_prop

/-- The full geometric transport from the literal twice-punctured sphere to
the accepted standard circle, with the equatorial coordinate order `(x,y)`. -/
noncomputable def sphere2PunctureIntersectionSphere1HomotopyEquiv :
    sphere2PunctureIntersection ≃ₕ (sphere1 : Type) :=
  sphere2PunctureIntersectionEquatorHomotopyEquiv.trans
    sphere2EquatorHomeomorphSphere1.toHomotopyEquiv

theorem sphere2NorthPunctured_contractibleSpace :
    ContractibleSpace
      ((TopologicalSpace.Opens.toTopCat sphere2).obj
        sphere2NorthPunctured : Type) :=
  sphere2NorthPuncturedHomeomorph.contractibleSpace_iff.mpr inferInstance

theorem sphere2SouthPunctured_contractibleSpace :
    ContractibleSpace
      ((TopologicalSpace.Opens.toTopCat sphere2).obj
        sphere2SouthPunctured : Type) :=
  sphere2SouthPuncturedHomeomorph.contractibleSpace_iff.mpr inferInstance

theorem isZero_reducedSingularHomology_sphere2NorthPunctured (n : ℕ) :
    IsZero (TopCat.reducedSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere2).obj
        sphere2NorthPunctured) n) := by
  let _ := sphere2NorthPunctured_contractibleSpace
  exact TopCat.isZero_reducedSingularHomology_of_contractible _ _

theorem isZero_reducedSingularHomology_sphere2SouthPunctured (n : ℕ) :
    IsZero (TopCat.reducedSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere2).obj
        sphere2SouthPunctured) n) := by
  let _ := sphere2SouthPunctured_contractibleSpace
  exact TopCat.isZero_reducedSingularHomology_of_contractible _ _

set_option linter.style.haveILetI false in
/-- The accepted positive-degree connecting morphism for the ordered
north/south cover is an isomorphism in degree two. -/
theorem sphere2MayerVietorisδOne_isIso :
    IsIso (AlgebraicTopology.twoOpenMayerVietorisδ
      sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1) := by
  have hN₁ : IsZero (AlgebraicTopology.integralSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured) 1) :=
    (isZero_reducedSingularHomology_sphere2NorthPunctured 1).of_iso
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured)
        1 (by simp)).symm
  have hS₁ : IsZero (AlgebraicTopology.integralSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured) 1) :=
    (isZero_reducedSingularHomology_sphere2SouthPunctured 1).of_iso
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured)
        1 (by simp)).symm
  have hN₂ : IsZero (AlgebraicTopology.integralSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured) 2) :=
    (isZero_reducedSingularHomology_sphere2NorthPunctured 2).of_iso
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured)
        2 (by simp)).symm
  have hS₂ : IsZero (AlgebraicTopology.integralSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured) 2) :=
    (isZero_reducedSingularHomology_sphere2SouthPunctured 2).of_iso
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured)
        2 (by simp)).symm
  exact AlgebraicTopology.twoOpenMayerVietorisδ_isIso_of_isZero_outer
    sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1
    ((biprod_isZero_iff _ _).2 ⟨hN₂, hS₂⟩)
    ((biprod_isZero_iff _ _).2 ⟨hN₁, hS₁⟩)

/-- Positive-degree reduced Mayer--Vietoris for the ordered north/south cover,
with its target identified with the literal puncture intersection. -/
noncomputable def sphere2ReducedMayerVietorisIso :
    TopCat.reducedSingularHomology sphere2 2 ≅
      TopCat.reducedSingularHomology
        ((TopologicalSpace.Opens.toTopCat sphere2).obj
          (sphere2NorthPunctured ⊓ sphere2SouthPunctured)) 1 := by
  letI := sphere2MayerVietorisδOne_isIso
  exact TopCat.reducedSingularHomologyIsoOfNeZero sphere2 2 (by simp) ≪≫
    asIso (AlgebraicTopology.twoOpenMayerVietorisδ
      sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1) ≪≫
    (AlgebraicTopology.twoOpenIntersectionHomologyIso
      sphere2NorthPunctured sphere2SouthPunctured 1).symm ≪≫
    (TopCat.reducedSingularHomologyIsoOfNeZero
      ((TopologicalSpace.Opens.toTopCat sphere2).obj
        (sphere2NorthPunctured ⊓ sphere2SouthPunctured)) 1 (by simp)).symm

theorem sphere2ReducedMayerVietorisIso_hom :
    sphere2ReducedMayerVietorisIso.hom =
      (TopCat.reducedSingularHomologyIsoOfNeZero sphere2 2 (by simp)).hom ≫
      AlgebraicTopology.twoOpenMayerVietorisδ
        sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1 ≫
      (AlgebraicTopology.twoOpenIntersectionHomologyIso
        sphere2NorthPunctured sphere2SouthPunctured 1).inv ≫
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((TopologicalSpace.Opens.toTopCat sphere2).obj
          (sphere2NorthPunctured ⊓ sphere2SouthPunctured)) 1
        (by simp)).inv := by
  rfl

/-- The fixed-coordinate reduced integral homology computation
`H̃₂(S²; ℤ) ≅ ℤ` for the literal standard two-sphere. -/
noncomputable def reducedSingularHomologyTwoSphereTwoIntegerIso :
    TopCat.reducedSingularHomology sphere2 2 ≅ ModuleCat.of ℤ ℤ :=
  sphere2ReducedMayerVietorisIso ≪≫
    TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
      sphere2PunctureIntersectionSphere1HomotopyEquiv 1 ≪≫
    reducedSingularHomologyOneSphereOneIntegerIso

/-- The computation uses the accepted ordered connecting morphism, then the
literal intersection/equator transport, the coordinate-ordered equator/circle
transport, and finally the accepted fixed circle integer coordinate. -/
theorem reducedSingularHomologyTwoSphereTwoIntegerIso_hom :
    reducedSingularHomologyTwoSphereTwoIntegerIso.hom =
      sphere2ReducedMayerVietorisIso.hom ≫
      (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
        sphere2PunctureIntersectionSphere1HomotopyEquiv 1).hom ≫
      reducedSingularHomologyOneSphereOneIntegerIso.hom := by
  rfl

/-- Fully expanded comparison with the accepted positive-degree connecting
morphism and the fixed circle coordinate. -/
theorem reducedSingularHomologyTwoSphereTwoIntegerIso_hom_explicit :
    reducedSingularHomologyTwoSphereTwoIntegerIso.hom =
      (TopCat.reducedSingularHomologyIsoOfNeZero sphere2 2 (by simp)).hom ≫
      AlgebraicTopology.twoOpenMayerVietorisδ
        sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1 ≫
      (AlgebraicTopology.twoOpenIntersectionHomologyIso
        sphere2NorthPunctured sphere2SouthPunctured 1).inv ≫
      (TopCat.reducedSingularHomologyIsoOfNeZero
        ((TopologicalSpace.Opens.toTopCat sphere2).obj
          (sphere2NorthPunctured ⊓ sphere2SouthPunctured)) 1
        (by simp)).inv ≫
      (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
        sphere2PunctureIntersectionSphere1HomotopyEquiv 1).hom ≫
      reducedSingularHomologyOneSphereOneIntegerIso.hom := by
  rw [reducedSingularHomologyTwoSphereTwoIntegerIso_hom,
    sphere2ReducedMayerVietorisIso_hom]
  simp only [Category.assoc]

end SphereTopology
