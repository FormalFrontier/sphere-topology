/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Geometry.SpherePinch
import Mathlib.Tactic.NormNum

/-!
# Compact-open continuity of sphere pinch folding

`Metric.Sphere.pinchFold` folds a pair of north-based sphere maps by pointed
descent after `Metric.Sphere.pinch`, with the first map on the left and the
second on the right. It is a function on the compact-open based-map subtype,
not an operation defined by transport through generalized loops or classes.
For `n : ℕ`, the sphere dimension is `n + 1`, including the circle at `n = 0`.

The characteristic API gives evaluation, the pole value, both closed half-cube
formulas, and agreement with raw coordinate-zero concatenation. Joint continuity
preserves simultaneous paths of based maps. The sphere-valued identity/constant
folds in opposite orders differ at the left quarter-point of the cube.

## Limitations

Mapping spaces carry the ordinary compact-open topology and its subtype topology,
without a compactly generated modification. Only positive-dimensional spheres
are included. No group operation on classes or full cogroup structure is defined.
Targets require only a topology, with no separation, local compactness, algebra,
or well-pointedness assumption.

## References

* Mathlib's generalized loops, due to Roberto Alvarez, supply `transAt`,
  the continuous `toLoop` and `fromLoop`, and `fromLoop_trans_toLoop`.
  Mathlib also supplies `Path.continuous_trans` and the `Joined` product/map API.
* The sphere-map homeomorphism and pinch geometry are those of
  `SphereTopology.Homotopy.HomotopyGroup.Sphere` and
  `SphereTopology.Geometry.SpherePinch`, including the raw fold comparison,
  closed-half computations, and quarter-point nondegeneracy.
* `TopCat.widePushoutDesc` supplies descent to independently universed targets.
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval Topology

namespace Metric.Sphere

variable (n : ℕ)

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1
local notation "a" => EuclideanSpace.northPoint (n + 1)
local notation "D" => (fun _ : Fin 2 ↦ TopCat.of S)
local notation "α" =>
  (fun j : Fin 2 ↦ (TopCat.const a : TopCat.of (PUnit : Type) ⟶ D j))

section Fold

variable {X : Type v} [TopologicalSpace X] (x : X)

local notation "B" => {F : C(S, X) // F a = x}

/-- Fold a pair of north-based sphere maps by their pointed descent after the
sphere pinch, with the first map on the left and the second on the right.
This is a function on the existing compact-open subtype, not a multiplication
on homotopy classes. -/
def pinchFold : B × B → B :=
  fun p ↦
    ⟨ContinuousMap.comp
      (TopCat.widePushoutDesc α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) p.1 p.2))
        (fun j _ ↦ Subtype.property (ite (j = 0) p.1 p.2)))
      (pinch n),
      pinch_fold_northPoint n x p.1 p.2⟩

/-- Forgetting the pole constraint gives the specified descent composed with
`Metric.Sphere.pinch`. -/
theorem coe_pinchFold (F G : B) :
    (pinchFold n x (F, G)).val =
      ContinuousMap.comp
        (TopCat.widePushoutDesc α
          (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
          (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
          (fun j _ ↦ Subtype.property (ite (j = 0) F G)))
        (pinch n) := by
  rfl

/-- Evaluate a fold by applying the pointed descent to the pinched point. -/
theorem pinchFold_apply (F G : B) (s : S) :
    (pinchFold n x (F, G)).val s =
      TopCat.widePushoutDesc α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G)) (pinch n s) := by
  rfl

/-- Folding preserves the prescribed last-axis north-pole value. -/
@[simp]
theorem pinchFold_northPoint (F G : B) :
    (pinchFold n x (F, G)).val a = x := by
  exact (pinchFold n x (F, G)).property

/-- On the left closed half-cube, folding evaluates the first map at the
compressed coordinate used by `GenLoop.transAt`. -/
theorem pinchFold_apply_collapseToSphere_of_le (F G : B)
    (t : I^(Fin (n + 1))) (ht : (t 0 : ℝ) ≤ 1 / 2) :
    (pinchFold n x (F, G)).val (Cube.collapseToSphere (n + 1) t) =
      F.val (Cube.collapseToSphere (n + 1)
        (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0)))) := by
  exact pinch_fold_apply_collapseToSphere_of_le n x F G t ht

/-- On the right closed half-cube, including its shared midpoint, folding
evaluates the second map at the compressed coordinate. -/
theorem pinchFold_apply_collapseToSphere_of_ge (F G : B)
    (t : I^(Fin (n + 1))) (ht : 1 / 2 ≤ (t 0 : ℝ)) :
    (pinchFold n x (F, G)).val (Cube.collapseToSphere (n + 1) t) =
      G.val (Cube.collapseToSphere (n + 1)
        (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0 - 1)))) := by
  exact pinch_fold_apply_collapseToSphere_of_ge n x F G t ht

/-- The fold agrees with raw coordinate-zero concatenation under the existing
sphere-map homeomorphism. This characterizes the specified fold; it does not
define it by transport. -/
theorem pinchFold_eq_sphereHomeomorph_transAt (F G : B) :
    pinchFold n x (F, G) =
      GenLoop.sphereHomeomorph (n + 1) x
        (GenLoop.transAt (0 : Fin (n + 1))
          ((GenLoop.sphereHomeomorph (n + 1) x).symm F)
          ((GenLoop.sphereHomeomorph (n + 1) x).symm G)) := by
  apply Subtype.ext
  exact pinch_fold n x F G

/-- Folding after the sphere pinch is jointly continuous on the ordinary
compact-open north-based subtype, for every positive sphere dimension and
an arbitrary topological target in an independent universe. -/
theorem continuous_pinchFold : Continuous (pinchFold n x) := by
  let e := GenLoop.sphereHomeomorph (n + 1) x
  have hF : Continuous (fun p : B × B ↦
      GenLoop.toLoop (0 : Fin (n + 1)) (e.symm p.1)) :=
    (GenLoop.continuous_toLoop (0 : Fin (n + 1))).comp
      (e.symm.continuous.comp continuous_fst)
  have hG : Continuous (fun p : B × B ↦
      GenLoop.toLoop (0 : Fin (n + 1)) (e.symm p.2)) :=
    (GenLoop.continuous_toLoop (0 : Fin (n + 1))).comp
      (e.symm.continuous.comp continuous_snd)
  -- Concatenate paths in the lower-dimensional loop space, then compare with
  -- the specified raw fold. No continuity theorem for `transAt` is needed.
  have h := e.continuous.comp
    ((GenLoop.continuous_fromLoop (0 : Fin (n + 1))).comp
      (Path.continuous_trans.comp (hF.prodMk hG)))
  apply h.congr
  rintro ⟨F, G⟩
  simpa only [Function.comp_apply, GenLoop.fromLoop_trans_toLoop] using
    (pinchFold_eq_sphereHomeomorph_transAt n x F G).symm

/-- Simultaneous paths of the two based factors give a path of their folded
maps in the same compact-open subtype. -/
theorem pinchFold_joined {F₀ F₁ G₀ G₁ : B}
    (hF : Joined F₀ F₁) (hG : Joined G₀ G₁) :
    Joined (pinchFold n x (F₀, G₀)) (pinchFold n x (F₁, G₁)) := by
  exact (hF.prod hG).map (continuous_pinchFold n x)

end Fold

/-- The sphere-valued identity/constant folds in the two orders differ at the
original left quarter-point: one takes the nonnorth collapsed-center value,
the other takes north. This uses the existing quarter-point witness. -/
theorem pinchFold_id_const_ne_const_id :
    let Fid : {F : C(S, S) // F a = a} := ⟨ContinuousMap.id S, rfl⟩
    let Fconst : {F : C(S, S) // F a = a} := ⟨ContinuousMap.const S a, rfl⟩
    let c : I^(Fin (n + 1)) := fun _ ↦ Set.projIcc 0 1 zero_le_one (1 / 2)
    let t := Function.update c (0 : Fin (n + 1))
      (Set.projIcc 0 1 zero_le_one (1 / 4))
    let s := Cube.collapseToSphere (n + 1) t
    let z := Cube.collapseToSphere (n + 1) c
    z ≠ a ∧
      (pinchFold n a (Fid, Fconst)).val s = z ∧
      (pinchFold n a (Fconst, Fid)).val s = a ∧
      pinchFold n a (Fid, Fconst) ≠ pinchFold n a (Fconst, Fid) := by
  let Fid : {F : C(S, S) // F a = a} := ⟨ContinuousMap.id S, rfl⟩
  let Fconst : {F : C(S, S) // F a = a} := ⟨ContinuousMap.const S a, rfl⟩
  let c : I^(Fin (n + 1)) := fun _ ↦ Set.projIcc 0 1 zero_le_one (1 / 2)
  let t := Function.update c (0 : Fin (n + 1))
    (Set.projIcc 0 1 zero_le_one (1 / 4))
  let s := Cube.collapseToSphere (n + 1) t
  let z := Cube.collapseToSphere (n + 1) c
  have hcenter : (Set.projIcc 0 1 zero_le_one (1 / 2) : I) =
      ⟨1 / 2, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [Set.coe_projIcc]
  have hquarter : (Set.projIcc 0 1 zero_le_one (1 / 4) : I) =
      ⟨1 / 4, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [Set.coe_projIcc]
  have hz : z ≠ a := by
    simpa only [z, c, hcenter] using (pinch_nondegenerate n).1
  have hs : pinch n s = (WidePushout.ι α (0 : Fin 2)).hom z := by
    simpa only [s, t, z, c, hcenter, hquarter] using (pinch_nondegenerate n).2.1
  have hF : (pinchFold n a (Fid, Fconst)).val s = z := by
    rw [pinchFold_apply n a Fid Fconst s, hs]
    simpa only [ite_true, Fid, ContinuousMap.id_apply] using
      (TopCat.widePushoutDesc_ι α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) Fid Fconst))
        (fun j _ ↦ Subtype.property (ite (j = 0) Fid Fconst)) 0 z)
  have hG : (pinchFold n a (Fconst, Fid)).val s = a := by
    rw [pinchFold_apply n a Fconst Fid s, hs]
    simpa only [ite_true, Fconst, ContinuousMap.const_apply] using
      (TopCat.widePushoutDesc_ι α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) Fconst Fid))
        (fun j _ ↦ Subtype.property (ite (j = 0) Fconst Fid)) 0 z)
  refine ⟨hz, hF, hG, ?_⟩
  intro h
  apply hz
  calc
    z = (pinchFold n a (Fid, Fconst)).val s := hF.symm
    _ = (pinchFold n a (Fconst, Fid)).val s :=
      congrArg (fun F : {F : C(S, S) // F a = a} ↦ F.val s) h
    _ = a := hG

end Metric.Sphere
