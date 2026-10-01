/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

public import SphereTopology.Homology.Singular.ReducedMayerVietoris
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Constructions

/-!
# Reduced integral homology of the standard circle

This module gives the standard unit circle in the Euclidean plane an ordered
east/west two-puncture cover.  Stereographic projection identifies each
punctured open with the real line.  The twice-punctured intersection is
explicitly homotopy equivalent to the two-point space: `false` is the upper
component and `true` is the lower component.  The resulting reduced
Mayer--Vietoris isomorphism computes `H̃₁(S¹; ℤ)` as `ℤ` with that fixed
component order.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap
open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The real Euclidean plane, with coordinates indexed by `0` and `1`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The vector `(1, 0)` in the Euclidean plane. -/
def eastVector : E2 := PiLp.single 2 0 1

@[simp] lemma eastVector_norm : ‖eastVector‖ = 1 := by
  simp [eastVector]

/-- The east pole `(1, 0)`, bundled as a point of the metric unit circle. -/
def eastPoint : Metric.sphere (0 : E2) 1 := ⟨eastVector, by
  rw [mem_sphere_zero_iff_norm]
  exact show ‖eastVector‖ = 1 by
    simp [eastVector]⟩

@[simp] lemma eastPoint_first : ((eastPoint : E2) 0) = 1 := by
  simp [eastPoint, eastVector]

@[simp] lemma eastPoint_second : ((eastPoint : E2) 1) = 0 := by
  simp [eastPoint, eastVector]

/-- The west pole `(-1, 0)`, defined as the antipode of `eastPoint`. -/
def westPoint : Metric.sphere (0 : E2) 1 := -eastPoint
/-- The vector `(0, 1)` in the Euclidean plane. -/
def northVector : E2 := PiLp.single 2 1 1
/-- The north pole `(0, 1)`, bundled as a point of the metric unit circle. -/
def northPoint : Metric.sphere (0 : E2) 1 := ⟨northVector, by
  rw [mem_sphere_zero_iff_norm]
  simp [northVector]⟩
/-- The south pole `(0, -1)`, defined as the antipode of `northPoint`. -/
def southPoint : Metric.sphere (0 : E2) 1 := -northPoint

lemma eastPoint_ne_westPoint : eastPoint ≠ westPoint := by
  intro h
  have := congrArg (fun p : Metric.sphere (0 : E2) 1 => (p.1 : E2) 0) h
  norm_num [eastPoint, eastVector, westPoint] at this

/-- The literal metric unit circle in `E2`, viewed as an object of `TopCat`. -/
abbrev sphere1 : TopCat := TopCat.of (Metric.sphere (0 : E2) 1)

/-- The complement of the east pole, first in the ordered east/west open cover. -/
def circleEastPunctured : TopologicalSpace.Opens sphere1 :=
  ⟨{eastPoint}ᶜ, isOpen_compl_singleton⟩

/-- The complement of the west pole, second in the ordered east/west open cover. -/
def circleWestPunctured : TopologicalSpace.Opens sphere1 :=
  ⟨{westPoint}ᶜ, isOpen_compl_singleton⟩

lemma circlePunctured_join : circleEastPunctured ⊔ circleWestPunctured = ⊤ := by
  ext p
  change (p ≠ eastPoint ∨ p ≠ westPoint) ↔ True
  simp only [iff_true]
  by_contra h
  rcases not_or.mp h with ⟨he, hw⟩
  exact eastPoint_ne_westPoint ((not_ne_iff.mp he).symm.trans (not_ne_iff.mp hw))

/-- Identify the one-coordinate Euclidean space with `ℝ` by its unique coordinate. -/
noncomputable def euclideanLineHomeomorphReal :
    EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
  (PiLp.equivOfUnique 2 ℝ (fun (_ : Fin 1) ↦ ℝ)).toHomeomorph

/-- The east-pole stereographic chart, followed by the identification of
one-dimensional Euclidean space with `ℝ`. Its domain omits the east pole. -/
noncomputable def circleEastPuncturedHomeomorph :
    ((TopologicalSpace.Opens.toTopCat sphere1).obj circleEastPunctured : Type) ≃ₜ ℝ := by
  letI : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  exact (Homeomorph.setCongr (by simp [circleEastPunctured])).trans
    (stereographic' 1 eastPoint).toHomeomorphSourceTarget |>.trans
    (Homeomorph.setCongr (stereographic'_target eastPoint)) |>.trans
    (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 1))) |>.trans
    euclideanLineHomeomorphReal

/-- The west-pole stereographic chart, followed by the identification of
one-dimensional Euclidean space with `ℝ`. Its domain omits the west pole. -/
noncomputable def circleWestPuncturedHomeomorph :
    ((TopologicalSpace.Opens.toTopCat sphere1).obj circleWestPunctured : Type) ≃ₜ ℝ := by
  letI : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  exact (Homeomorph.setCongr (by simp [circleWestPunctured])).trans
    (stereographic' 1 westPoint).toHomeomorphSourceTarget |>.trans
    (Homeomorph.setCongr (stereographic'_target westPoint)) |>.trans
    (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 1))) |>.trans
    euclideanLineHomeomorphReal

/-- The circle with both east and west poles removed, as the subtype underlying
the intersection of the two punctured opens. -/
abbrev circlePunctureIntersection :=
  ((TopologicalSpace.Opens.toTopCat sphere1).obj
    (circleEastPunctured ⊓ circleWestPunctured) : Type)

lemma circle_eq_east_or_west_of_second_eq_zero
    (p : Metric.sphere (0 : E2) 1) (hp : (p.1 : E2) 1 = 0) :
    p = eastPoint ∨ p = westPoint := by
  have hnorm : ‖(p.1 : E2)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  have hsq := EuclideanSpace.real_norm_sq_eq (p.1 : E2)
  rw [hnorm, Fin.sum_univ_two, hp] at hsq
  norm_num at hsq
  rcases sq_eq_one_iff.mp hsq.symm with hx | hx
  · left
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [eastPoint, eastVector, hx, hp]
  · right
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [westPoint, eastPoint, eastVector, hx, hp]

lemma circlePunctureIntersection_second_ne_zero
    (p : circlePunctureIntersection) : (p.1.1 : E2) 1 ≠ 0 := by
  intro hp
  rcases circle_eq_east_or_west_of_second_eq_zero p.1 hp with he | hw
  · exact p.2.1 he
  · exact p.2.2 hw

/-- The pinned component order: `false` is the upper semicircle and `true` is
the lower semicircle. -/
def circlePunctureIntersectionComponent (p : circlePunctureIntersection) : Bool :=
  if 0 < (p.1.1 : E2) 1 then false else true

lemma circlePunctureIntersectionComponent_eq_false_iff
    (p : circlePunctureIntersection) :
    circlePunctureIntersectionComponent p = false ↔ 0 < (p.1.1 : E2) 1 := by
  simp [circlePunctureIntersectionComponent]

lemma circlePunctureIntersectionComponent_eq_true_iff
    (p : circlePunctureIntersection) :
    circlePunctureIntersectionComponent p = true ↔ (p.1.1 : E2) 1 < 0 := by
  by_cases h : 0 < (p.1.1 : E2) 1
  · simp [circlePunctureIntersectionComponent, h, not_lt_of_ge h.le]
  · have hlt : (p.1.1 : E2) 1 < 0 :=
      lt_of_le_of_ne (le_of_not_gt h)
        (circlePunctureIntersection_second_ne_zero p)
    simp [circlePunctureIntersectionComponent, h, hlt]

lemma continuous_circlePunctureIntersectionComponent :
    Continuous circlePunctureIntersectionComponent := by
  rw [continuous_bool_rng false]
  have hc : Continuous (fun p : circlePunctureIntersection => (p.1.1 : E2) 1) := by
    fun_prop
  have hfiber : circlePunctureIntersectionComponent ⁻¹' {false} =
      {p | 0 < (p.1.1 : E2) 1} := by
    ext p
    simp [circlePunctureIntersectionComponent_eq_false_iff]
  rw [hfiber]
  refine ⟨?_, isOpen_lt continuous_const hc⟩
  have hcompl : {p : circlePunctureIntersection | 0 < (p.1.1 : E2) 1}ᶜ =
      {p | (p.1.1 : E2) 1 < 0} := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    exact not_lt.trans (le_iff_lt_or_eq.trans (or_iff_left
      (circlePunctureIntersection_second_ne_zero p)))
  apply isOpen_compl_iff.mp
  rw [hcompl]
  exact isOpen_lt hc continuous_const

/-- The continuous component map to the discrete two-point space: upper points
map to `false`, and lower points map to `true`. -/
def circlePunctureIntersectionToTwoPoint :
    C(circlePunctureIntersection, TopCat.twoPointSpace) :=
  ⟨circlePunctureIntersectionComponent,
    continuous_circlePunctureIntersectionComponent⟩

/-- Choose the north pole for `false` and the south pole for `true`, each with
its proof of membership in the twice-punctured circle. -/
def circlePunctureIntersectionRepresentative : Bool → circlePunctureIntersection
  | false => ⟨northPoint, by
      constructor <;> intro h
      · have := congrArg (fun p : Metric.sphere (0 : E2) 1 => (p.1 : E2) 1) h
        norm_num [northPoint, northVector, eastPoint, eastVector] at this
      · have := congrArg (fun p : Metric.sphere (0 : E2) 1 => (p.1 : E2) 1) h
        norm_num [northPoint, northVector, westPoint, eastPoint, eastVector] at this⟩
  | true => ⟨southPoint, by
      constructor <;> intro h
      · have := congrArg (fun p : Metric.sphere (0 : E2) 1 => (p.1 : E2) 1) h
        norm_num [southPoint, northPoint, northVector, eastPoint, eastVector] at this
      · have := congrArg (fun p : Metric.sphere (0 : E2) 1 => (p.1 : E2) 1) h
        norm_num [southPoint, northPoint, northVector, westPoint, eastPoint, eastVector] at this⟩

/-- The continuous choice of north/south representatives, inverse to the
component map up to the radial homotopy. -/
def circlePunctureIntersectionFromTwoPoint :
    C(TopCat.twoPointSpace, circlePunctureIntersection) :=
  ⟨circlePunctureIntersectionRepresentative, continuous_of_discreteTopology⟩

@[simp] lemma circlePunctureIntersectionComponent_representative (b : Bool) :
    circlePunctureIntersectionComponent
      (circlePunctureIntersectionRepresentative b) = b := by
  cases b <;> simp [circlePunctureIntersectionComponent,
    circlePunctureIntersectionRepresentative, northPoint, northVector,
    southPoint]

@[simp] lemma circlePunctureIntersectionRepresentative_false_second :
    (circlePunctureIntersectionRepresentative false).1.1 1 = 1 := by
  rfl

@[simp] lemma circlePunctureIntersectionRepresentative_true_second :
    (circlePunctureIntersectionRepresentative true).1.1 1 = -1 := by
  rfl

/-- Interpolate linearly from the chosen component representative at `t = 0`
to `p` at `t = 1`, before normalization. The second coordinate stays nonzero. -/
def circlePunctureIntersectionLinearVector
    (t : unitInterval) (p : circlePunctureIntersection) : E2 :=
  (1 - (t : ℝ)) •
      (circlePunctureIntersectionRepresentative
        (circlePunctureIntersectionComponent p)).1.1 +
    (t : ℝ) • p.1.1

lemma circlePunctureIntersectionLinearVector_second_pos_of_component_false
    (t : unitInterval) (p : circlePunctureIntersection)
    (hp : circlePunctureIntersectionComponent p = false) :
    0 < circlePunctureIntersectionLinearVector t p 1 := by
  have hpy := (circlePunctureIntersectionComponent_eq_false_iff p).mp hp
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  simp only [circlePunctureIntersectionLinearVector, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  rw [hp]
  simp only [circlePunctureIntersectionRepresentative_false_second, mul_one]
  by_cases ht : (t : ℝ) = 0
  · simp [ht]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht1)
      (mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hpy)

lemma circlePunctureIntersectionLinearVector_second_neg_of_component_true
    (t : unitInterval) (p : circlePunctureIntersection)
    (hp : circlePunctureIntersectionComponent p = true) :
    circlePunctureIntersectionLinearVector t p 1 < 0 := by
  have hpy := (circlePunctureIntersectionComponent_eq_true_iff p).mp hp
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  simp only [circlePunctureIntersectionLinearVector, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  rw [hp]
  simp only [circlePunctureIntersectionRepresentative_true_second, mul_neg, mul_one]
  by_cases ht : (t : ℝ) = 0
  · simp [ht]
  · have hsum := add_neg_of_nonpos_of_neg (neg_nonpos.mpr (sub_nonneg.mpr ht1))
        (mul_neg_of_pos_of_neg (lt_of_le_of_ne ht0 (Ne.symm ht)) hpy)
    nlinarith

lemma circlePunctureIntersectionLinearVector_second_ne_zero
    (t : unitInterval) (p : circlePunctureIntersection) :
    circlePunctureIntersectionLinearVector t p 1 ≠ 0 := by
  cases hp : circlePunctureIntersectionComponent p
  · exact ne_of_gt
      (circlePunctureIntersectionLinearVector_second_pos_of_component_false t p hp)
  · exact ne_of_lt
      (circlePunctureIntersectionLinearVector_second_neg_of_component_true t p hp)

lemma circlePunctureIntersectionLinearVector_ne_zero
    (t : unitInterval) (p : circlePunctureIntersection) :
    circlePunctureIntersectionLinearVector t p ≠ 0 := by
  intro h
  have := congrArg (fun v : E2 => v 1) h
  exact circlePunctureIntersectionLinearVector_second_ne_zero t p (by simpa using this)

/-- Normalize the nonzero interpolating vector to norm one. This retains its
upper/lower component because normalization uses a positive scalar. -/
def circlePunctureIntersectionRadialVector
    (t : unitInterval) (p : circlePunctureIntersection) : E2 :=
  ‖circlePunctureIntersectionLinearVector t p‖⁻¹ •
    circlePunctureIntersectionLinearVector t p

lemma circlePunctureIntersectionRadialVector_norm
    (t : unitInterval) (p : circlePunctureIntersection) :
    ‖circlePunctureIntersectionRadialVector t p‖ = 1 := by
  rw [circlePunctureIntersectionRadialVector, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr
    (circlePunctureIntersectionLinearVector_ne_zero t p)

lemma circlePunctureIntersectionRadialVector_second_ne_zero
    (t : unitInterval) (p : circlePunctureIntersection) :
    circlePunctureIntersectionRadialVector t p 1 ≠ 0 := by
  rw [circlePunctureIntersectionRadialVector, PiLp.smul_apply, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr
    (circlePunctureIntersectionLinearVector_ne_zero t p)))
    (circlePunctureIntersectionLinearVector_second_ne_zero t p)

/-- The normalized interpolating vector as a point of the twice-punctured circle;
its nonzero second coordinate excludes both removed poles. -/
def circlePunctureIntersectionRadialPoint
    (t : unitInterval) (p : circlePunctureIntersection) :
    circlePunctureIntersection :=
  ⟨⟨circlePunctureIntersectionRadialVector t p,
      mem_sphere_zero_iff_norm.mpr
        (circlePunctureIntersectionRadialVector_norm t p)⟩, by
    constructor <;> intro h
    · have := congrArg (fun q : Metric.sphere (0 : E2) 1 => (q.1 : E2) 1) h
      exact circlePunctureIntersectionRadialVector_second_ne_zero t p (by
        simpa [eastPoint, eastVector] using this)
    · have := congrArg (fun q : Metric.sphere (0 : E2) 1 => (q.1 : E2) 1) h
      exact circlePunctureIntersectionRadialVector_second_ne_zero t p (by
        simpa [westPoint, eastPoint, eastVector] using this)⟩

lemma continuous_circlePunctureIntersectionLinearVector :
    Continuous (fun q : unitInterval × circlePunctureIntersection =>
      circlePunctureIntersectionLinearVector q.1 q.2) := by
  have hrep : Continuous (fun p : circlePunctureIntersection =>
      (circlePunctureIntersectionRepresentative
        (circlePunctureIntersectionComponent p)).1.1) := by
    exact continuous_subtype_val.comp (continuous_subtype_val.comp
      ((circlePunctureIntersectionFromTwoPoint.comp
        circlePunctureIntersectionToTwoPoint).continuous))
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hrep.comp continuous_snd)).add
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))

lemma continuous_circlePunctureIntersectionRadialPoint :
    Continuous (fun q : unitInterval × circlePunctureIntersection =>
      circlePunctureIntersectionRadialPoint q.1 q.2) := by
  have hlin := continuous_circlePunctureIntersectionLinearVector
  have hnorm : Continuous (fun q : unitInterval × circlePunctureIntersection =>
      ‖circlePunctureIntersectionLinearVector q.1 q.2‖) := hlin.norm
  exact ((hnorm.inv₀ fun q => norm_ne_zero_iff.mpr
      (circlePunctureIntersectionLinearVector_ne_zero q.1 q.2)).smul hlin).subtype_mk _
    |>.subtype_mk _

/-- Bundle the radial interpolation as a jointly continuous map of time and
point. Time zero selects the component representative; time one returns the point. -/
def circlePunctureIntersectionRadialHomotopyMap :
    C(unitInterval × circlePunctureIntersection, circlePunctureIntersection) :=
  ⟨fun q => circlePunctureIntersectionRadialPoint q.1 q.2,
    continuous_circlePunctureIntersectionRadialPoint⟩

lemma circlePunctureIntersectionRadialPoint_zero
    (p : circlePunctureIntersection) :
    circlePunctureIntersectionRadialPoint 0 p =
      circlePunctureIntersectionRepresentative
        (circlePunctureIntersectionComponent p) := by
  apply Subtype.ext
  apply Subtype.ext
  simp [circlePunctureIntersectionRadialPoint,
    circlePunctureIntersectionRadialVector,
    circlePunctureIntersectionLinearVector]

lemma circlePunctureIntersectionRadialPoint_one
    (p : circlePunctureIntersection) :
    circlePunctureIntersectionRadialPoint 1 p = p := by
  apply Subtype.ext
  apply Subtype.ext
  simp [circlePunctureIntersectionRadialPoint,
    circlePunctureIntersectionRadialVector,
    circlePunctureIntersectionLinearVector,
    mem_sphere_zero_iff_norm.mp p.1.2]

/-- The homotopy from the component-representative composite to the identity,
using normalized straight-line interpolation within each component. -/
def circlePunctureIntersectionRadialHomotopy :
    (circlePunctureIntersectionFromTwoPoint.comp
      circlePunctureIntersectionToTwoPoint).Homotopy
        (ContinuousMap.id circlePunctureIntersection) :=
  ⟨circlePunctureIntersectionRadialHomotopyMap,
    circlePunctureIntersectionRadialPoint_zero,
    circlePunctureIntersectionRadialPoint_one⟩

/-- The homotopy equivalence with the two-point space given by the component map
and north/south representatives, ordered as `false`/`true`. -/
noncomputable def circlePunctureIntersectionHomotopyEquiv :
    circlePunctureIntersection ≃ₕ TopCat.twoPointSpace where
  toFun := circlePunctureIntersectionToTwoPoint
  invFun := circlePunctureIntersectionFromTwoPoint
  left_inv := ⟨circlePunctureIntersectionRadialHomotopy⟩
  right_inv := by
    have h : circlePunctureIntersectionToTwoPoint.comp
        circlePunctureIntersectionFromTwoPoint =
        ContinuousMap.id TopCat.twoPointSpace := by
      ext b
      change circlePunctureIntersectionComponent
        (circlePunctureIntersectionRepresentative b) = b
      exact circlePunctureIntersectionComponent_representative b
    exact h ▸ ContinuousMap.Homotopic.refl _

/-- Transport the component homotopy equivalence to `ULift` on both sides via
the canonical `ULift` homeomorphisms, without changing the component order. -/
noncomputable def circlePunctureIntersectionHomotopyEquivULift :
    ULift circlePunctureIntersection ≃ₕ ULift TopCat.twoPointSpace :=
  Homeomorph.ulift.toHomotopyEquiv |>.trans
    circlePunctureIntersectionHomotopyEquiv |>.trans
    Homeomorph.ulift.symm.toHomotopyEquiv

theorem circleEastPunctured_contractibleSpace :
    ContractibleSpace
      ((TopologicalSpace.Opens.toTopCat sphere1).obj circleEastPunctured : Type) :=
  circleEastPuncturedHomeomorph.contractibleSpace_iff.mpr inferInstance

theorem circleWestPunctured_contractibleSpace :
    ContractibleSpace
      ((TopologicalSpace.Opens.toTopCat sphere1).obj circleWestPunctured : Type) :=
  circleWestPuncturedHomeomorph.contractibleSpace_iff.mpr inferInstance

theorem isZero_reducedSingularHomology_circleEastPunctured (n : ℕ) :
    IsZero (TopCat.reducedSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere1).obj circleEastPunctured) n) := by
  let _ := circleEastPunctured_contractibleSpace
  exact TopCat.isZero_reducedSingularHomology_of_contractible _ _

theorem isZero_reducedSingularHomology_circleWestPunctured (n : ℕ) :
    IsZero (TopCat.reducedSingularHomology
      ((TopologicalSpace.Opens.toTopCat sphere1).obj circleWestPunctured) n) := by
  let _ := circleWestPunctured_contractibleSpace
  exact TopCat.isZero_reducedSingularHomology_of_contractible _ _

/-- Identify the circle's first reduced integral singular homology with `ℤ`.
The coordinate uses the east/west ordered Mayer--Vietoris connecting map and
the two-point basis `[false] - [true]`, with `false` the upper component. -/
noncomputable def reducedSingularHomologyOneSphereOneIntegerIso :
    TopCat.reducedSingularHomology sphere1 1 ≅ ModuleCat.of ℤ ℤ :=
  AlgebraicTopology.twoOpenReducedMayerVietorisIsoOfAcyclicOpens
      circleEastPunctured circleWestPunctured circlePunctured_join
      (isZero_reducedSingularHomology_circleEastPunctured 0)
      (isZero_reducedSingularHomology_circleWestPunctured 0)
      (isZero_reducedSingularHomology_circleEastPunctured 1)
      (isZero_reducedSingularHomology_circleWestPunctured 1) ≪≫
    TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
      circlePunctureIntersectionHomotopyEquiv 0 ≪≫
    TopCat.reducedSingularHomologyZeroTwoPointIntegerIso

theorem reducedSingularHomologyOneSphereOneIntegerIso_hom :
    reducedSingularHomologyOneSphereOneIntegerIso.hom =
      AlgebraicTopology.twoOpenReducedMayerVietorisδZero
        circleEastPunctured circleWestPunctured circlePunctured_join ≫
      (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
        circlePunctureIntersectionHomotopyEquiv 0).hom ≫
      TopCat.reducedSingularHomologyZeroTwoPointIntegerIso.hom := by
  rfl

lemma circlePunctured_join_reversed :
    circleWestPunctured ⊔ circleEastPunctured = ⊤ := by
  rw [sup_comm]
  exact circlePunctured_join

/-- The same literal intersection with the puncture order reversed. -/
abbrev circlePunctureIntersectionReversed :=
  ((TopologicalSpace.Opens.toTopCat sphere1).obj
    (circleWestPunctured ⊓ circleEastPunctured) : Type)

/-- The sign-free identity homeomorphism between the two meet orderings. -/
def circlePunctureIntersectionSwapHomeomorph :
    circlePunctureIntersectionReversed ≃ₜ circlePunctureIntersection :=
  Homeomorph.setCongr (by
    ext p
    simp only [circleEastPunctured, circleWestPunctured]
    exact and_comm)

/-- The upper/lower equivalence for the reversed ordered cover.  It uses the
same Boolean order, so `false` is still upper and `true` is still lower. -/
noncomputable def circlePunctureIntersectionReversedHomotopyEquiv :
    circlePunctureIntersectionReversed ≃ₕ TopCat.twoPointSpace :=
  circlePunctureIntersectionSwapHomeomorph.toHomotopyEquiv.trans
    circlePunctureIntersectionHomotopyEquiv

theorem circlePunctureIntersectionReversedComponent_eq_false_iff
    (p : circlePunctureIntersectionReversed) :
    circlePunctureIntersectionComponent
        (circlePunctureIntersectionSwapHomeomorph p) = false ↔
      0 < (p.1.1 : E2) 1 :=
  circlePunctureIntersectionComponent_eq_false_iff _

theorem circlePunctureIntersectionReversedComponent_eq_true_iff
    (p : circlePunctureIntersectionReversed) :
    circlePunctureIntersectionComponent
        (circlePunctureIntersectionSwapHomeomorph p) = true ↔
      (p.1.1 : E2) 1 < 0 :=
  circlePunctureIntersectionComponent_eq_true_iff _

/-- The reversed-cover circle computation, retained as an order/sign client.
Its coordinate still means upper minus lower; the accepted ordered-cover swap
theorem below records the negation of the connecting morphism. -/
noncomputable def reducedSingularHomologyOneSphereOneIntegerIsoReversed :
    TopCat.reducedSingularHomology sphere1 1 ≅ ModuleCat.of ℤ ℤ :=
  AlgebraicTopology.twoOpenReducedMayerVietorisIsoOfAcyclicOpens
      circleWestPunctured circleEastPunctured circlePunctured_join_reversed
      (isZero_reducedSingularHomology_circleWestPunctured 0)
      (isZero_reducedSingularHomology_circleEastPunctured 0)
      (isZero_reducedSingularHomology_circleWestPunctured 1)
      (isZero_reducedSingularHomology_circleEastPunctured 1) ≪≫
    TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
      circlePunctureIntersectionReversedHomotopyEquiv 0 ≪≫
    TopCat.reducedSingularHomologyZeroTwoPointIntegerIso

theorem reducedSingularHomologyOneSphereOneIntegerIsoReversed_hom :
    reducedSingularHomologyOneSphereOneIntegerIsoReversed.hom =
      AlgebraicTopology.twoOpenReducedMayerVietorisδZero
        circleWestPunctured circleEastPunctured circlePunctured_join_reversed ≫
      (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
        circlePunctureIntersectionReversedHomotopyEquiv 0).hom ≫
      TopCat.reducedSingularHomologyZeroTwoPointIntegerIso.hom := by
  rfl

theorem circleReducedMayerVietoris_swap_eq_neg :
    AlgebraicTopology.twoOpenReducedMayerVietorisδZero
        circleEastPunctured circleWestPunctured circlePunctured_join ≫
      TopCat.reducedSingularHomologyMap
        (AlgebraicTopology.twoOpenIntersectionSwapMap
          circleEastPunctured circleWestPunctured) 0 =
      -(AlgebraicTopology.twoOpenReducedMayerVietorisδZero
        circleWestPunctured circleEastPunctured circlePunctured_join_reversed) :=
  AlgebraicTopology.twoOpenReducedMayerVietorisδZero_swap_eq_neg
    circleEastPunctured circleWestPunctured circlePunctured_join
      circlePunctured_join_reversed

end SphereTopology
