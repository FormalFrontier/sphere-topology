/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Geometry.SpherePinch
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Coordinate reflections of positive-dimensional spheres

A coordinate reflection is the restriction of the linear reflection in the
orthogonal complement of a coordinate line to the metric unit sphere. It
negates that coordinate and fixes the last-axis north pole. Its pullback along
`Cube.collapseToSphere` is exactly the corresponding `GenLoop.symmAt`, and this
characteristic determines the continuous sphere map uniquely.

Under `GenLoop.sphereHomeomorph`, reversal of a generalized loop is
precomposition by this geometric reflection. The coordinate unit vector
witnesses that the reflection is not the identity. The two reflection/identity
folds of the sphere pinch are nonconstant, as seen on the identity legs at the
quarter-points of the cube.

The parameter `n` describes the sphere of dimension `n + 1`, including the
circle at `n = 0`. Every `i : Fin (n + 1)` is allowed. Targets of the
function-space comparison have only a topology, in an independent universe.

## References

* Mathlib's `Submodule.reflection`, due to Zhouhang Zhou, Frédéric Dupuis and
  Heather Macbeth, supplies the linear reflection and its involution laws.
* Roberto Alvarez's generalized loops supply coordinate reversal.
* Fundamental Groupoids supplies the increasing real coordinates of the open
  cube, used by this library's last-axis cube/sphere comparison.
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval Topology OnePoint

namespace Metric.Sphere

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin ((n + 1) + 1))
local notation "S" => Metric.sphere (0 : E) 1
local notation "a" => EuclideanSpace.northPoint (n + 1)
local notation "Q" =>
  (Subtype.mk (Cube.collapseToSphere (n + 1))
    (fun t ht ↦ Iff.mpr (Cube.collapseToSphere_eq_northPoint_iff (n + 1) t) ht) :
      GenLoop (Fin (n + 1)) S a)

/-- Reflect the positive-dimensional unit sphere in the coordinate hyperplane
orthogonal to axis `i.castSucc`. This restricts Mathlib's linear reflection and
does not reflect the last ambient axis. -/
def coordinateReflection (i : Fin (n + 1)) : S ≃ₜ S := by
  let r : E ≃ₗᵢ[ℝ] E :=
    (ℝ ∙ (EuclideanSpace.single i.castSucc (1 : ℝ) : E))ᗮ.reflection
  exact r.toHomeomorph.subtype
    (p := fun z : E ↦ z ∈ Metric.sphere (0 : E) 1)
    (q := fun z : E ↦ z ∈ Metric.sphere (0 : E) 1)
    (fun z ↦ by
      change z ∈ Metric.sphere (0 : E) 1 ↔ r z ∈ Metric.sphere (0 : E) 1
      simp only [mem_sphere_zero_iff_norm, r.norm_map])

/-- Each coordinate reflection fixes the specified last-axis north pole. -/
@[simp]
theorem coordinateReflection_northPoint (i : Fin (n + 1)) :
    coordinateReflection n i a = a := by
  apply Subtype.ext
  change (ℝ ∙ (EuclideanSpace.single i.castSucc (1 : ℝ) : E))ᗮ.reflection
    (a : E) = (a : E)
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
    EuclideanSpace.inner_single_left]
  simp

/-- The underlying vector is the reflection in the ambient coordinate hyperplane. -/
theorem coe_coordinateReflection (i : Fin (n + 1)) (z : S) :
    (coordinateReflection n i z : E) =
      (ℝ ∙ (EuclideanSpace.single i.castSucc (1 : ℝ) : E))ᗮ.reflection (z : E) := by
  rfl

/-- The chosen coordinate changes sign and all other ambient coordinates,
including the last coordinate, are unchanged. -/
theorem coordinateReflection_apply (i : Fin (n + 1)) (z : S)
    (j : Fin ((n + 1) + 1)) :
    (coordinateReflection n i z : E) j =
      ite (j = i.castSucc) (-(z : E) j) ((z : E) j) := by
  rw [coe_coordinateReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul,
    EuclideanSpace.single, PiLp.norm_single, norm_one, one_pow, div_one, two_smul,
    PiLp.neg_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases h : j = i.castSucc
  · subst j
    simp only [PiLp.single_eq_same, ite_true]
    ring
  · simp only [PiLp.single_eq_of_ne 2 h, ite_eq_right h]
    ring

/-- Reflecting twice in the same coordinate hyperplane is the identity. -/
theorem coordinateReflection_involutive (i : Fin (n + 1)) :
    Function.Involutive (coordinateReflection n i : S → S) := by
  intro z
  apply Subtype.ext
  simp only [coe_coordinateReflection]
  exact Submodule.reflection_involutive _ _

/-- Pullback along the original cube collapse is exactly reversal of that
collapse in the selected raw generalized-loop coordinate. -/
theorem coordinateReflection_comp_collapseToSphere (i : Fin (n + 1)) :
    (coordinateReflection n i : C(S, S)).comp (Cube.collapseToSphere (n + 1)) =
      Subtype.val (GenLoop.symmAt i Q) := by
  apply ContinuousMap.ext
  intro t
  let t' : I^(Fin (n + 1)) := fun j ↦ if j = i then σ (t i) else t j
  change coordinateReflection n i (Cube.collapseToSphere (n + 1) t) =
    Cube.collapseToSphere (n + 1) t'
  have hb : t' ∈ Cube.boundary (Fin (n + 1)) ↔ t ∈ Cube.boundary (Fin (n + 1)) := by
    change (∃ j, t' j = 0 ∨ t' j = 1) ↔ (∃ j, t j = 0 ∨ t j = 1)
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      by_cases hji : j = i
      · subst j
        simpa only [t', ite_true, unitInterval.symm_eq_zero,
          unitInterval.symm_eq_one, or_comm] using hj
      · simpa only [t', ite_eq_right hji] using hj
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      by_cases hji : j = i
      · subst j
        simpa only [t', ite_true, unitInterval.symm_eq_zero,
          unitInterval.symm_eq_one, or_comm] using hj
      · simpa only [t', ite_eq_right hji] using hj
  by_cases ht : t ∈ Cube.boundary (Fin (n + 1))
  · rw [(Cube.collapseToSphere_eq_northPoint_iff (n + 1) t).mpr ht,
      (Cube.collapseToSphere_eq_northPoint_iff (n + 1) t').mpr (hb.mpr ht),
      coordinateReflection_northPoint]
  · let u : ((Cube.boundary (Fin (n + 1)))ᶜ : Set (I^(Fin (n + 1)))) := ⟨t, ht⟩
    let u' : ((Cube.boundary (Fin (n + 1)))ᶜ : Set (I^(Fin (n + 1)))) :=
      ⟨t', fun h ↦ ht (hb.mp h)⟩
    let x : EuclideanSpace ℝ (Fin (n + 1)) :=
      WithLp.toLp 2 (Cube.boundaryComplHomeomorphPi (Fin (n + 1)) u)
    let x' : EuclideanSpace ℝ (Fin (n + 1)) :=
      WithLp.toLp 2 (Cube.boundaryComplHomeomorphPi (Fin (n + 1)) u')
    have hx (j : Fin (n + 1)) : x' j = if j = i then -x j else x j := by
      change Cube.boundaryComplHomeomorphPi (Fin (n + 1)) u' j =
        if j = i then -Cube.boundaryComplHomeomorphPi (Fin (n + 1)) u j
        else Cube.boundaryComplHomeomorphPi (Fin (n + 1)) u j
      simp only [Cube.boundaryComplHomeomorphPi_apply]
      by_cases hji : j = i
      · subst j
        simpa only [u', u, t', ite_true, unitInterval.coe_symm_eq] using
          (Cube.openIntervalOrderIsoReal_one_sub
            ⟨(t i : ℝ), (Cube.mem_boundary_compl_iff.mp u.property) i⟩)
      · simp only [u', u, t', ite_eq_right hji]
    have hnorm : ‖x'‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro j _
      rw [hx j]
      split_ifs <;> simp only [norm_neg]
    have hQ : Cube.collapseToSphere (n + 1) t =
        EuclideanSpace.onePointHomeomorphSphere (n + 1)
          (x : OnePoint (EuclideanSpace ℝ (Fin (n + 1)))) :=
      (Cube.collapseToSphere_apply_coe (n + 1) u).trans
        (Cube.onePointBoundaryComplHomeomorphSphere_apply_coe (n + 1) u)
    have hQ' : Cube.collapseToSphere (n + 1) t' =
        EuclideanSpace.onePointHomeomorphSphere (n + 1)
          (x' : OnePoint (EuclideanSpace ℝ (Fin (n + 1)))) :=
      (Cube.collapseToSphere_apply_coe (n + 1) u').trans
        (Cube.onePointBoundaryComplHomeomorphSphere_apply_coe (n + 1) u')
    rw [hQ, hQ']
    apply Subtype.ext
    apply PiLp.ext
    intro j
    rw [coordinateReflection_apply]
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · rw [ite_eq_right (Fin.castSucc_ne_last i).symm,
        EuclideanSpace.onePointHomeomorphSphere_apply_coe_last,
        EuclideanSpace.onePointHomeomorphSphere_apply_coe_last, hnorm]
    · simp only [Fin.castSucc_inj,
        EuclideanSpace.onePointHomeomorphSphere_apply_coe_castSucc, hx k, hnorm]
      split_ifs <;> ring

/-- The raw cube-reversal characteristic determines the continuous sphere map;
no separate basedness hypothesis is needed in positive dimensions. -/
theorem coordinateReflection_unique (i : Fin (n + 1)) (k : C(S, S))
    (h : k.comp (Cube.collapseToSphere (n + 1)) =
      Subtype.val (GenLoop.symmAt i Q)) :
    k = (coordinateReflection n i : C(S, S)) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := Cube.surjective_collapseToSphere (n + 1) z
  exact congrArg (fun f : C(I^(Fin (n + 1)), S) ↦ f t)
    (h.trans (coordinateReflection_comp_collapseToSphere n i).symm)

/-- The coordinate unit point is not north, is sent to its distinct antipode,
and witnesses that this reflection is not the identity map. -/
theorem coordinateReflection_nondegenerate (i : Fin (n + 1)) :
    let e : S := ⟨EuclideanSpace.single i.castSucc (1 : ℝ), by
      rw [mem_sphere_zero_iff_norm]
      simp only [EuclideanSpace.single, PiLp.norm_single, norm_one]⟩
    e ≠ a ∧ coordinateReflection n i e = -e ∧ -e ≠ e ∧
      (coordinateReflection n i : C(S, S)) ≠ ContinuousMap.id S := by
  let e : S := ⟨EuclideanSpace.single i.castSucc (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm]
    simp only [EuclideanSpace.single, PiLp.norm_single, norm_one]⟩
  change e ≠ a ∧ coordinateReflection n i e = -e ∧ -e ≠ e ∧
    (coordinateReflection n i : C(S, S)) ≠ ContinuousMap.id S
  have he : (e : E) i.castSucc = 1 := PiLp.single_eq_same 2 i.castSucc 1
  have hanti : coordinateReflection n i e = -e := by
    apply Subtype.ext
    rw [coe_coordinateReflection, coe_neg_sphere]
    exact Submodule.reflection_orthogonalComplement_singleton_eq_neg _
  have hne : -e ≠ e := by
    intro h
    have hv := congrArg (fun z : S ↦ (z : E) i.castSucc) h
    simp only [coe_neg_sphere, PiLp.neg_apply, he] at hv
    norm_num at hv
  refine ⟨?_, hanti, hne, ?_⟩
  · intro h
    have hv := congrArg (fun z : S ↦ (z : E) i.castSucc) h
    simp only [he, EuclideanSpace.northPoint_apply_castSucc] at hv
    norm_num at hv
  · intro h
    exact hne (hanti.symm.trans (congrArg (fun f : C(S, S) ↦ f e) h))

end Metric.Sphere

namespace GenLoop

variable (n : ℕ)

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1

/-- Reversal on any cube axis corresponds, under the existing based
function-space homeomorphism, to geometric coordinate-reflection precomposition.
The target has an independent universe and needs only a topology. -/
theorem sphereHomeomorph_symmAt {X : Type v} [TopologicalSpace X]
    (i : Fin (n + 1)) (x : X) (p : GenLoop (Fin (n + 1)) X x) :
    (sphereHomeomorph (n + 1) x (symmAt i p)).val =
      (sphereHomeomorph (n + 1) x p).val.comp
        (Metric.Sphere.coordinateReflection n i : C(S, S)) := by
  have heval (q : GenLoop (Fin (n + 1)) X x) (t : I^(Fin (n + 1))) :
      (sphereHomeomorph (n + 1) x q).val (Cube.collapseToSphere (n + 1) t) = q t := by
    simpa only [Homeomorph.symm_apply_apply] using
      (sphereHomeomorph_symm_apply_apply (n + 1) x
        (sphereHomeomorph (n + 1) x q) t).symm
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := Cube.surjective_collapseToSphere (n + 1) z
  have hr := congrArg (fun f : C(I^(Fin (n + 1)), S) ↦ f t)
    (Metric.Sphere.coordinateReflection_comp_collapseToSphere n i)
  change Metric.Sphere.coordinateReflection n i (Cube.collapseToSphere (n + 1) t) =
    Cube.collapseToSphere (n + 1) (fun j ↦ if j = i then σ (t i) else t j) at hr
  change (sphereHomeomorph (n + 1) x (symmAt i p)).val
    (Cube.collapseToSphere (n + 1) t) =
      (sphereHomeomorph (n + 1) x p).val
        (Metric.Sphere.coordinateReflection n i (Cube.collapseToSphere (n + 1) t))
  rw [hr, heval, heval]
  rfl

end GenLoop

namespace Metric.Sphere

variable (n : ℕ)

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1
local notation "a" => EuclideanSpace.northPoint (n + 1)

section Pinch

variable (i : Fin (n + 1))

local notation "D" => (fun _ : Fin 2 ↦ TopCat.of S)
local notation "α" =>
  (fun j : Fin 2 ↦ (TopCat.const a : TopCat.of (PUnit : Type) ⟶ D j))
local notation "Id" =>
  (Subtype.mk (ContinuousMap.id S) rfl : {F : C(S, S) // F a = a})
local notation "ρ" =>
  (Subtype.mk (coordinateReflection n i : C(S, S))
    (coordinateReflection_northPoint n i) : {F : C(S, S) // F a = a})
local notation "L" =>
  (ContinuousMap.comp
    (TopCat.widePushoutDesc α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) ρ Id))
      (fun j _ ↦ Subtype.property (ite (j = 0) ρ Id)))
    (pinch n))
local notation "R" =>
  (ContinuousMap.comp
    (TopCat.widePushoutDesc α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) Id ρ))
      (fun j _ ↦ Subtype.property (ite (j = 0) Id ρ)))
    (pinch n))

/-- The right quarter-point uses the identity leg of the reflection/identity
fold, and the left quarter-point uses the identity leg of the identity/reflection
fold. Both values are the nonnorth collapsed center, so neither endpoint is the
constant map. No fixedness assertion about the collapsed center is needed. -/
theorem pinch_coinverse_nondegenerate :
    let c : I^(Fin (n + 1)) := fun _ ↦ Set.projIcc 0 1 zero_le_one (1 / 2)
    let tL := Function.update c (0 : Fin (n + 1))
      (Set.projIcc 0 1 zero_le_one (1 / 4))
    let tR := Function.update c (0 : Fin (n + 1))
      (Set.projIcc 0 1 zero_le_one (3 / 4))
    let z := Cube.collapseToSphere (n + 1) c
    let sL := Cube.collapseToSphere (n + 1) tL
    let sR := Cube.collapseToSphere (n + 1) tR
    z ≠ a ∧ L sR = z ∧ R sL = z ∧
      L ≠ ContinuousMap.const S a ∧ R ≠ ContinuousMap.const S a := by
  let c : I^(Fin (n + 1)) := fun _ ↦ Set.projIcc 0 1 zero_le_one (1 / 2)
  let tL := Function.update c (0 : Fin (n + 1))
    (Set.projIcc 0 1 zero_le_one (1 / 4))
  let tR := Function.update c (0 : Fin (n + 1))
    (Set.projIcc 0 1 zero_le_one (3 / 4))
  let z := Cube.collapseToSphere (n + 1) c
  let sL := Cube.collapseToSphere (n + 1) tL
  let sR := Cube.collapseToSphere (n + 1) tR
  change z ≠ a ∧ L sR = z ∧ R sL = z ∧
    L ≠ ContinuousMap.const S a ∧ R ≠ ContinuousMap.const S a
  have hc : Set.projIcc 0 1 zero_le_one (1 / 2) = (⟨1 / 2, by norm_num⟩ : I) := by
    apply Subtype.ext
    norm_num [Set.coe_projIcc]
  have hqL : Set.projIcc 0 1 zero_le_one (1 / 4) = (⟨1 / 4, by norm_num⟩ : I) := by
    apply Subtype.ext
    norm_num [Set.coe_projIcc]
  have hqR : Set.projIcc 0 1 zero_le_one (3 / 4) = (⟨3 / 4, by norm_num⟩ : I) := by
    apply Subtype.ext
    norm_num [Set.coe_projIcc]
  have hp := pinch_nondegenerate n
  dsimp only at hp
  have hz : z ≠ a := by
    simpa only [z, c, hc] using hp.1
  have hleft : pinch n sL = TopCat.Hom.hom (WidePushout.ι α 0) z := by
    simpa only [sL, tL, z, c, hc, hqL] using hp.2.1
  have hright : pinch n sR = TopCat.Hom.hom (WidePushout.ι α 1) z := by
    simpa only [sR, tR, z, c, hc, hqR] using hp.2.2.1
  have hL : L sR = z := by
    rw [ContinuousMap.comp_apply, hright]
    simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false, ContinuousMap.id_apply] using
      (TopCat.widePushoutDesc_ι α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) ρ Id))
        (fun j _ ↦ Subtype.property (ite (j = 0) ρ Id)) 1 z)
  have hR : R sL = z := by
    rw [ContinuousMap.comp_apply, hleft]
    simpa only [ite_true, ContinuousMap.id_apply] using
      (TopCat.widePushoutDesc_ι α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) Id ρ))
        (fun j _ ↦ Subtype.property (ite (j = 0) Id ρ)) 0 z)
  refine ⟨hz, hL, hR, ?_, ?_⟩
  · intro h
    exact hz (hL.symm.trans (congrArg (fun f : C(S, S) ↦ f sR) h))
  · intro h
    exact hz (hR.symm.trans (congrArg (fun f : C(S, S) ↦ f sL) h))

end Pinch

end Metric.Sphere
