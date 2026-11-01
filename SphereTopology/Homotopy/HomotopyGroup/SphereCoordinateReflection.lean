/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Geometry.SphereCoordinateReflection
public import SphereTopology.Homotopy.HomotopyGroup.SpherePinch

/-!
# Coordinate reflections and sphere pinch coinverses

Precomposition with a coordinate reflection represents the existing inverse in
`HomotopyGroup` under `HomotopyGroup.equivSphereClasses`. This holds for every
based continuous map to an independently universed topological space and for
every cube coordinate of a positive-dimensional sphere.

Folding reflection and identity, in either order, after `Metric.Sphere.pinch`
is homotopic to the north constant relative to the singleton north pole. The
right-times-left order of `Metric.Sphere.pinch_fold_class` gives `u * u⁻¹` and
`u⁻¹ * u`, respectively. Only group cancellation is used, also for the circle;
the reflection axis need not be the axis used to construct the pinch.

## Limitations

These results concern positive-dimensional spheres, with `n = 0` giving the
circle. They assert relative homotopy without choosing homotopies, and do not
specify a zero-sphere pinch, orientation or a complete cogroup structure.

## References

* Mathlib's generalized loops and homotopy groups, due to Roberto Alvarez,
  supply coordinate reversal and `HomotopyGroup.inv_spec` for every axis.
* The coordinate-reflection comparison is provided by
  `GenLoop.sphereHomeomorph_symmAt`. The sphere-class and relative-homotopy
  comparisons are those of `SphereTopology.Homotopy.HomotopyGroup.Sphere`.
* The original sphere pinch and its right-times-left fold-class formula are
  those of `SphereTopology.Homotopy.HomotopyGroup.SpherePinch`.
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Metric.Sphere

variable (n : ℕ)

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1
local notation "a" => EuclideanSpace.northPoint (n + 1)

/-- Precomposition with any coordinate reflection represents the inverse in the
existing homotopy group, not an inverse operation transported to sphere maps. -/
theorem coordinateReflection_precomp_class {X : Type v} [TopologicalSpace X]
    (i : Fin (n + 1)) (x : X) (F : {F : C(S, X) // F a = x}) :
    (HomotopyGroup.equivSphereClasses (n + 1) x).symm
      (ZerothHomotopy.mk
        (⟨F.val.comp (coordinateReflection n i : C(S, S)),
          (congrArg F.val (coordinateReflection_northPoint n i)).trans F.property⟩ :
          {H : C(S, X) // H a = x})) =
      ((HomotopyGroup.equivSphereClasses (n + 1) x).symm
        (ZerothHomotopy.mk F))⁻¹ := by
  let p := (GenLoop.sphereHomeomorph (n + 1) x).symm F
  let H : {H : C(S, X) // H a = x} :=
    ⟨F.val.comp (coordinateReflection n i : C(S, S)),
      (congrArg F.val (coordinateReflection_northPoint n i)).trans F.property⟩
  have hmap : GenLoop.sphereHomeomorph (n + 1) x (GenLoop.symmAt i p) = H := by
    apply Subtype.ext
    exact (GenLoop.sphereHomeomorph_symmAt n i x p).trans
      (congrArg (fun G : {G : C(S, X) // G a = x} ↦
        G.val.comp (coordinateReflection n i : C(S, S)))
        ((GenLoop.sphereHomeomorph (n + 1) x).apply_symm_apply F))
  have hloop : (GenLoop.sphereHomeomorph (n + 1) x).symm H =
      GenLoop.symmAt i p := by
    rw [← hmap, Homeomorph.symm_apply_apply]
  -- Compose the representative equalities directly, keeping the group structure
  -- on the named homotopy group rather than its unfolded quotient type.
  exact (HomotopyGroup.equivSphereClasses_symm_mk (n + 1) x H).trans
    ((congrArg (fun q : GenLoop (Fin (n + 1)) X x ↦
      (⟦q⟧ : HomotopyGroup (Fin (n + 1)) X x)) hloop).trans
      ((HomotopyGroup.inv_spec (i := i) (p := p)).symm.trans
        (congrArg (fun q : HomotopyGroup (Fin (n + 1)) X x ↦ q⁻¹)
          (HomotopyGroup.equivSphereClasses_symm_mk (n + 1) x F).symm)))

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

/-- Folding reflection on the left and identity on the right after the original
pinch is nullhomotopic relative to north. The endpoint class is `u * u⁻¹` with
the existing right-times-left convention. Every reflection axis is allowed. -/
theorem pinch_coordinateReflection_id_homotopicRel :
    ContinuousMap.HomotopicRel L (ContinuousMap.const S a) ({a} : Set S) := by
  let H : {H : C(S, S) // H a = a} := ⟨L, pinch_fold_northPoint n a ρ Id⟩
  let constMap : {H : C(S, S) // H a = a} := ⟨ContinuousMap.const S a, rfl⟩
  have hρ :
      (HomotopyGroup.equivSphereClasses (n + 1) a).symm (ZerothHomotopy.mk ρ) =
        ((HomotopyGroup.equivSphereClasses (n + 1) a).symm
          (ZerothHomotopy.mk Id))⁻¹ := by
    simpa only [ContinuousMap.id_comp] using coordinateReflection_precomp_class n i a Id
  apply (ZerothHomotopy.sphere_mk_eq_mk_iff_homotopicRel (n + 1) a H constMap).mp
  apply (HomotopyGroup.equivSphereClasses (n + 1) a).symm.injective
  calc
    _ = (HomotopyGroup.equivSphereClasses (n + 1) a).symm (ZerothHomotopy.mk Id) *
        (HomotopyGroup.equivSphereClasses (n + 1) a).symm (ZerothHomotopy.mk ρ) :=
      pinch_fold_class n a ρ Id
    _ = 1 := by rw [hρ, mul_inv_cancel]
    _ = _ := ((HomotopyGroup.equivSphereClasses_symm_const (n + 1) a).trans
      HomotopyGroup.one_def.symm).symm

/-- Folding identity on the left and reflection on the right after the original
pinch is nullhomotopic relative to north. The endpoint class is `u⁻¹ * u`;
no commutativity is used, including for the circle. -/
theorem pinch_id_coordinateReflection_homotopicRel :
    ContinuousMap.HomotopicRel R (ContinuousMap.const S a) ({a} : Set S) := by
  let H : {H : C(S, S) // H a = a} := ⟨R, pinch_fold_northPoint n a Id ρ⟩
  let constMap : {H : C(S, S) // H a = a} := ⟨ContinuousMap.const S a, rfl⟩
  have hρ :
      (HomotopyGroup.equivSphereClasses (n + 1) a).symm (ZerothHomotopy.mk ρ) =
        ((HomotopyGroup.equivSphereClasses (n + 1) a).symm
          (ZerothHomotopy.mk Id))⁻¹ := by
    simpa only [ContinuousMap.id_comp] using coordinateReflection_precomp_class n i a Id
  apply (ZerothHomotopy.sphere_mk_eq_mk_iff_homotopicRel (n + 1) a H constMap).mp
  apply (HomotopyGroup.equivSphereClasses (n + 1) a).symm.injective
  calc
    _ = (HomotopyGroup.equivSphereClasses (n + 1) a).symm (ZerothHomotopy.mk ρ) *
        (HomotopyGroup.equivSphereClasses (n + 1) a).symm (ZerothHomotopy.mk Id) :=
      pinch_fold_class n a Id ρ
    _ = 1 := by rw [hρ, inv_mul_cancel]
    _ = _ := ((HomotopyGroup.equivSphereClasses_symm_const (n + 1) a).trans
      HomotopyGroup.one_def.symm).symm

end Pinch

end Metric.Sphere
