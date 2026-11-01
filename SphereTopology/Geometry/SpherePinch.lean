/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.HomotopyGroup.Sphere
public import SphereTopology.Topology.WidePushout
import Mathlib.Tactic.NormNum

/-!
# Positive-dimensional sphere pinch

`Metric.Sphere.pinch n` is a continuous map from the real `(n + 1)`-sphere to
its two-factor point-wide-pushout. It extends the generalized loop that first
traverses the left inclusion of `Cube.collapseToSphere (n + 1)` and then the
right inclusion, using `GenLoop.transAt` on cube coordinate zero. The pole is
the existing last-axis `EuclideanSpace.northPoint (n + 1)`; no sphere or wedge
carrier is introduced.

The characteristic statements describe the pullback, its two closed half-cubes,
explicit quarter-point values, and descent to arbitrary independently universed
targets by `TopCat.widePushoutDesc`. The closed-half formulas also compute raw
folds. The two iterated folds of the original three-factor inclusions are distinct
maps: the left nesting visits three pairwise distinct nonhead values at cube
times `1/8`, `3/8` and `3/4`, and the two nestings differ at time `3/8`.

## Limitations

Only positive-dimensional spheres are included. No orientation, complete cogroup
structure or compactly generated mapping-space model is asserted.

## References

* Mathlib's generalized loops and concatenation, due to Roberto Alvarez, supply
  the coordinate-zero concatenation and its compression coordinates.
* Fundamental Groupoids supplies based postcomposition of generalized loops.
* This library supplies the last-axis cube/sphere comparison and the existing
  point-wide-pushout inclusions, retractions and independently universed descent.
-/

@[expose] public section

noncomputable section

universe v w

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval Topology

namespace Metric.Sphere

variable (n : ℕ)

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1
local notation "a" => EuclideanSpace.northPoint (n + 1)
local notation "D" => (fun _ : Fin 2 ↦ TopCat.of S)
local notation "α" =>
  (fun j : Fin 2 ↦ (TopCat.const a : TopCat.of (PUnit : Type) ⟶ D j))
local notation "W" => (widePushout (TopCat.of (PUnit : Type)) D α : TopCat)
local notation "b" => WidePushout.head α PUnit.unit
local notation "ι" => (fun j : Fin 2 ↦ TopCat.Hom.hom (WidePushout.ι α j))

-- This only packages the existing collapse and its boundary theorem.
local notation "Q" =>
  (Subtype.mk (Cube.collapseToSphere (n + 1))
    (fun t ht ↦ Iff.mpr (Cube.collapseToSphere_eq_northPoint_iff (n + 1) t) ht) :
      GenLoop (Fin (n + 1)) S a)
local notation "K" => GenLoop.transAt (0 : Fin (n + 1))
  (GenLoop.map (ι 0) (TopCat.widePushout_point_ι_point (X := D) (fun _ : Fin 2 ↦ a) 0) Q)
  (GenLoop.map (ι 1) (TopCat.widePushout_point_ι_point (X := D) (fun _ : Fin 2 ↦ a) 1) Q)

/-- Pinch the positive-dimensional sphere to the existing two-factor
point-wide-pushout, traversing the left factor before the right factor in cube
coordinate zero. The north pole is on the last ambient axis. -/
def pinch : C(S, W) :=
  Subtype.val (GenLoop.sphereHomeomorph (n + 1) b K)

/-- The pinch sends the specified north pole to the pushout head. -/
@[simp]
theorem pinch_northPoint : pinch n a = b := by
  exact Subtype.property (GenLoop.sphereHomeomorph (n + 1) b K)

/-- Pulling back the pinch along the cube collapse gives the specified raw
coordinate-zero concatenation of the two inclusions of that collapse. -/
theorem pinch_comp_collapseToSphere :
    (pinch n).comp (Cube.collapseToSphere (n + 1)) = Subtype.val K := by
  change (GenLoop.sphereHomeomorph (n + 1) b K).val.comp
    (Cube.collapseToSphere (n + 1)) = Subtype.val K
  calc
    _ = ((GenLoop.sphereHomeomorph (n + 1) b).symm
        (GenLoop.sphereHomeomorph (n + 1) b K)).val :=
      (GenLoop.coe_sphereHomeomorph_symm_apply (n + 1) b
        (GenLoop.sphereHomeomorph (n + 1) b K)).symm
    _ = Subtype.val K := congrArg Subtype.val
      ((GenLoop.sphereHomeomorph (n + 1) b).symm_apply_apply K)

/-- The raw cube pullback characterizes the pinch among continuous maps. -/
theorem pinch_unique (k : C(S, W))
    (h : k.comp (Cube.collapseToSphere (n + 1)) = Subtype.val K) : k = pinch n := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := Cube.surjective_collapseToSphere (n + 1) z
  exact congrArg (fun f : C(I^(Fin (n + 1)), W) ↦ f t)
    (h.trans (pinch_comp_collapseToSphere n).symm)

private theorem pinch_concat_apply (t : I^(Fin (n + 1))) :
    K t =
      if (t 0 : ℝ) ≤ 1 / 2 then
        ι 0 (Cube.collapseToSphere (n + 1)
          (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0))))
      else
        ι 1 (Cube.collapseToSphere (n + 1)
          (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0 - 1)))) := by
  rfl

/-- On the left closed half-cube, the pinch is the left inclusion after the
compression coordinates used by `GenLoop.transAt`. -/
theorem pinch_apply_collapseToSphere_of_le (t : I^(Fin (n + 1)))
    (ht : (t 0 : ℝ) ≤ 1 / 2) :
    pinch n (Cube.collapseToSphere (n + 1) t) =
      ι 0 (Cube.collapseToSphere (n + 1)
        (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0)))) := by
  change ((pinch n).comp (Cube.collapseToSphere (n + 1))) t = _
  rw [pinch_comp_collapseToSphere]
  exact (pinch_concat_apply n t).trans (ite_eq_left ht)

private theorem pinch_collapse_update_endpoint (t : I^(Fin (n + 1))) (s : I)
    (hs : s = 0 ∨ s = 1) :
    Cube.collapseToSphere (n + 1) (Function.update t 0 s) = a := by
  apply (Cube.collapseToSphere_eq_northPoint_iff (n + 1) _).mpr
  exact ⟨0, by simpa only [Function.update_self] using hs⟩

/-- On the right closed half-cube, including the shared midpoint, the pinch is
the right inclusion after the compression coordinates used by `GenLoop.transAt`. -/
theorem pinch_apply_collapseToSphere_of_ge (t : I^(Fin (n + 1)))
    (ht : 1 / 2 ≤ (t 0 : ℝ)) :
    pinch n (Cube.collapseToSphere (n + 1) t) =
      ι 1 (Cube.collapseToSphere (n + 1)
        (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0 - 1)))) := by
  calc
    pinch n (Cube.collapseToSphere (n + 1) t) = K t :=
      congrArg (fun f : C(I^(Fin (n + 1)), W) ↦ f t)
        (pinch_comp_collapseToSphere n)
    _ = _ := by
      rw [pinch_concat_apply]
      by_cases hle : (t 0 : ℝ) ≤ 1 / 2
      · have heq : (t 0 : ℝ) = 1 / 2 := le_antisymm hle ht
        have hleft : Cube.collapseToSphere (n + 1)
            (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0))) = a := by
          apply pinch_collapse_update_endpoint n t
          right
          apply projIcc_eq_one.mpr
          rw [heq]
          norm_num
        have hright : Cube.collapseToSphere (n + 1)
            (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0 - 1))) = a := by
          apply pinch_collapse_update_endpoint n t
          left
          apply projIcc_eq_zero.mpr
          rw [heq]
          norm_num
        rw [ite_eq_left hle, hleft, hright]
        exact (TopCat.widePushout_point_ι_point (X := D) (fun _ : Fin 2 ↦ a) 0).trans
          (TopCat.widePushout_point_ι_point (X := D) (fun _ : Fin 2 ↦ a) 1).symm
      · rw [ite_eq_right hle]

/-- The separating midpoint slice of the cube maps to the pushout head. -/
theorem pinch_apply_collapseToSphere_midpoint (t : I^(Fin (n + 1)))
    (ht : (t 0 : ℝ) = 1 / 2) :
    pinch n (Cube.collapseToSphere (n + 1) t) = b := by
  have hleft : Cube.collapseToSphere (n + 1)
      (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0))) = a := by
    apply pinch_collapse_update_endpoint n t
    right
    apply projIcc_eq_one.mpr
    rw [ht]
    norm_num
  rw [pinch_apply_collapseToSphere_of_le n t ht.le, hleft]
  exact TopCat.widePushout_point_ι_point (X := D) (fun _ : Fin 2 ↦ a) 0

/-- The quarter and three-quarter updates of the cube center map to distinct,
non-head values in the left and right factors, both over the collapsed center. -/
theorem pinch_nondegenerate :
    let c : I^(Fin (n + 1)) := fun _ ↦ ⟨1 / 2, by norm_num⟩
    let tL := Function.update c 0 (⟨1 / 4, by norm_num⟩ : I)
    let tR := Function.update c 0 (⟨3 / 4, by norm_num⟩ : I)
    let z := Cube.collapseToSphere (n + 1) c
    z ≠ a ∧
      pinch n (Cube.collapseToSphere (n + 1) tL) = ι 0 z ∧
      pinch n (Cube.collapseToSphere (n + 1) tR) = ι 1 z ∧
      pinch n (Cube.collapseToSphere (n + 1) tL) ≠ b ∧
      pinch n (Cube.collapseToSphere (n + 1) tR) ≠ b ∧
      pinch n (Cube.collapseToSphere (n + 1) tL) ≠
        pinch n (Cube.collapseToSphere (n + 1) tR) := by
  let c : I^(Fin (n + 1)) := fun _ ↦ ⟨1 / 2, by norm_num⟩
  let tL := Function.update c 0 (⟨1 / 4, by norm_num⟩ : I)
  let tR := Function.update c 0 (⟨3 / 4, by norm_num⟩ : I)
  let z := Cube.collapseToSphere (n + 1) c
  have hz : z ≠ a := by
    intro h
    have hc : c ∉ Cube.boundary (Fin (n + 1)) :=
      Cube.mem_boundary_compl_iff.mpr (fun _ ↦ by norm_num [c])
    exact hc ((Cube.collapseToSphere_eq_northPoint_iff (n + 1) c).mp h)
  have hLc : Function.update tL 0
      (Set.projIcc 0 1 zero_le_one ((2 : ℝ) * (tL 0 : ℝ))) = c := by
    have hp : Set.projIcc 0 1 zero_le_one ((2 : ℝ) * (tL 0 : ℝ)) = c 0 := by
      apply Subtype.ext
      norm_num [Set.coe_projIcc, tL, c]
    rw [hp]
    simp [tL]
  have hRc : Function.update tR 0
      (Set.projIcc 0 1 zero_le_one ((2 : ℝ) * (tR 0 : ℝ) - 1)) = c := by
    have hp : Set.projIcc 0 1 zero_le_one ((2 : ℝ) * (tR 0 : ℝ) - 1) = c 0 := by
      apply Subtype.ext
      norm_num [Set.coe_projIcc, tR, c]
    rw [hp]
    simp [tR]
  have hL : pinch n (Cube.collapseToSphere (n + 1) tL) = ι 0 z := by
    simpa only [hLc] using
      (pinch_apply_collapseToSphere_of_le n tL (by norm_num [tL]))
  have hR : pinch n (Cube.collapseToSphere (n + 1) tR) = ι 1 z := by
    simpa only [hRc] using
      (pinch_apply_collapseToSphere_of_ge n tR (by norm_num [tR]))
  refine ⟨hz, hL, hR, ?_, ?_, ?_⟩
  · intro h
    apply hz
    calc
      z = (TopCat.widePushoutPointRetraction D (fun _ : Fin 2 ↦ a) 0).hom (ι 0 z) :=
        (TopCat.widePushoutPointRetraction_ι_apply D (fun _ : Fin 2 ↦ a) 0 z).symm
      _ = (TopCat.widePushoutPointRetraction D (fun _ : Fin 2 ↦ a) 0).hom b :=
        congrArg (TopCat.widePushoutPointRetraction D (fun _ : Fin 2 ↦ a) 0).hom
          (hL.symm.trans h)
      _ = a := TopCat.widePushoutPointRetraction_head_apply D
        (fun _ : Fin 2 ↦ a) 0 PUnit.unit
  · intro h
    apply hz
    calc
      z = (TopCat.widePushoutPointRetraction D (fun _ : Fin 2 ↦ a) 1).hom (ι 1 z) :=
        (TopCat.widePushoutPointRetraction_ι_apply D (fun _ : Fin 2 ↦ a) 1 z).symm
      _ = (TopCat.widePushoutPointRetraction D (fun _ : Fin 2 ↦ a) 1).hom b :=
        congrArg (TopCat.widePushoutPointRetraction D (fun _ : Fin 2 ↦ a) 1).hom
          (hR.symm.trans h)
      _ = a := TopCat.widePushoutPointRetraction_head_apply D
        (fun _ : Fin 2 ↦ a) 1 PUnit.unit
  · intro h
    apply hz
    calc
      z = (TopCat.widePushoutPointRetraction D (fun _ : Fin 2 ↦ a) 0).hom (ι 0 z) :=
        (TopCat.widePushoutPointRetraction_ι_apply D (fun _ : Fin 2 ↦ a) 0 z).symm
      _ = (TopCat.widePushoutPointRetraction D (fun _ : Fin 2 ↦ a) 0).hom (ι 1 z) :=
        congrArg (TopCat.widePushoutPointRetraction D (fun _ : Fin 2 ↦ a) 0).hom
          (hL.symm.trans (h.trans hR))
      _ = a := TopCat.widePushoutPointRetraction_ι_of_ne_apply D
        (fun _ : Fin 2 ↦ a) 0 1 (by decide) z

section Fold

/-- Descending pointed factor maps after the pinch is still based at the north pole. -/
public theorem pinch_fold_northPoint {X : Type v} [TopologicalSpace X] (x : X)
    (F G : {F : C(S, X) // F a = x}) :
    (ContinuousMap.comp
      (TopCat.widePushoutDesc α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G)))
      (pinch n)) a = x :=
  (congrArg
    (TopCat.widePushoutDesc α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G)))
    (pinch_northPoint n)).trans
    (TopCat.widePushoutDesc_head α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G)) PUnit.unit)

/-- On the left closed half-cube, folding after the pinch evaluates the first
factor map at the compressed cube coordinate. -/
theorem pinch_fold_apply_collapseToSphere_of_le
    {X : Type v} [TopologicalSpace X] (x : X)
    (F G : {F : C(S, X) // F a = x}) (t : I^(Fin (n + 1)))
    (ht : (t 0 : ℝ) ≤ 1 / 2) :
    (ContinuousMap.comp
      (TopCat.widePushoutDesc α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G)))
      (pinch n)) (Cube.collapseToSphere (n + 1) t) =
      F.val (Cube.collapseToSphere (n + 1)
        (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0)))) := by
  rw [ContinuousMap.comp_apply, pinch_apply_collapseToSphere_of_le n t ht]
  simpa only [ite_true] using
    (TopCat.widePushoutDesc_ι α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G)) 0
      (Cube.collapseToSphere (n + 1)
        (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0)))))

/-- On the right closed half-cube, folding after the pinch evaluates the second
factor map at the compressed cube coordinate. -/
theorem pinch_fold_apply_collapseToSphere_of_ge
    {X : Type v} [TopologicalSpace X] (x : X)
    (F G : {F : C(S, X) // F a = x}) (t : I^(Fin (n + 1)))
    (ht : 1 / 2 ≤ (t 0 : ℝ)) :
    (ContinuousMap.comp
      (TopCat.widePushoutDesc α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G)))
      (pinch n)) (Cube.collapseToSphere (n + 1) t) =
      G.val (Cube.collapseToSphere (n + 1)
        (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0 - 1)))) := by
  rw [ContinuousMap.comp_apply, pinch_apply_collapseToSphere_of_ge n t ht]
  simpa only [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] using
    (TopCat.widePushoutDesc_ι α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G)) 1
      (Cube.collapseToSphere (n + 1)
        (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0 - 1)))))

/-- Descent of arbitrary pointed factor maps after the pinch is exactly the
sphere extension of their raw coordinate-zero concatenation. The target has
an independent universe and needs only a topology. -/
public theorem pinch_fold {X : Type v} [TopologicalSpace X] (x : X)
    (F G : {F : C(S, X) // F a = x}) :
    ContinuousMap.comp
      (TopCat.widePushoutDesc α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G)))
      (pinch n) =
      (GenLoop.sphereHomeomorph (n + 1) x
        (GenLoop.transAt (0 : Fin (n + 1))
          ((GenLoop.sphereHomeomorph (n + 1) x).symm F)
          ((GenLoop.sphereHomeomorph (n + 1) x).symm G))).val := by
  let d : C(W, X) := TopCat.widePushoutDesc α
    (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
    (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
    (fun j _ ↦ Subtype.property (ite (j = 0) F G))
  have hd : d b = x :=
    TopCat.widePushoutDesc_head α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G)) PUnit.unit
  have hL :
      GenLoop.map d hd
        (GenLoop.map (ι 0)
          (TopCat.widePushout_point_ι_point (X := D) (fun _ : Fin 2 ↦ a) 0) Q) =
        (GenLoop.sphereHomeomorph (n + 1) x).symm F := by
    apply GenLoop.ext
    intro t
    change d (WidePushout.ι α 0 (Cube.collapseToSphere (n + 1) t)) =
      ((GenLoop.sphereHomeomorph (n + 1) x).symm F) t
    rw [GenLoop.sphereHomeomorph_symm_apply_apply]
    simpa only [ite_true] using
      (TopCat.widePushoutDesc_ι α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G)) 0
        (Cube.collapseToSphere (n + 1) t))
  have hR :
      GenLoop.map d hd
        (GenLoop.map (ι 1)
          (TopCat.widePushout_point_ι_point (X := D) (fun _ : Fin 2 ↦ a) 1) Q) =
        (GenLoop.sphereHomeomorph (n + 1) x).symm G := by
    apply GenLoop.ext
    intro t
    change d (WidePushout.ι α 1 (Cube.collapseToSphere (n + 1) t)) =
      ((GenLoop.sphereHomeomorph (n + 1) x).symm G) t
    rw [GenLoop.sphereHomeomorph_symm_apply_apply]
    simpa only [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] using
      (TopCat.widePushoutDesc_ι α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G)) 1
        (Cube.collapseToSphere (n + 1) t))
  have hK : GenLoop.map d hd K =
      GenLoop.transAt (0 : Fin (n + 1))
        ((GenLoop.sphereHomeomorph (n + 1) x).symm F)
        ((GenLoop.sphereHomeomorph (n + 1) x).symm G) := by
    rw [GenLoop.map_transAt, hL, hR]
  calc
    d.comp (pinch n) =
        (GenLoop.sphereHomeomorph (n + 1) x (GenLoop.map d hd K)).val :=
      (congrArg Subtype.val (GenLoop.sphereHomeomorph_map (n + 1) d hd K)).symm
    _ = _ := congrArg
      (fun p : GenLoop (Fin (n + 1)) X x ↦
        (GenLoop.sphereHomeomorph (n + 1) x p).val) hK

/-- Descent of the two pointed factor maps commutes with raw postcomposition,
including when source and target lie in independent universes. -/
public theorem pinch_fold_postcomp {X : Type v} [TopologicalSpace X] (x : X)
    (F G : {F : C(S, X) // F a = x}) {Y : Type w} [TopologicalSpace Y] {y : Y}
    (h : C(X, Y)) (hy : h x = y) :
    ContinuousMap.comp h
      (TopCat.widePushoutDesc α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G))) =
      TopCat.widePushoutDesc α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) y)
        (fun j : Fin 2 ↦ ContinuousMap.comp h (Subtype.val (ite (j = 0) F G)))
        (fun j _ ↦ Eq.trans (congrArg h (Subtype.property (ite (j = 0) F G))) hy) := by
  apply TopCat.widePushoutDesc_unique
  · intro p
    exact (congrArg h (TopCat.widePushoutDesc_head α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G)) p)).trans hy
  · intro j s
    exact congrArg h (TopCat.widePushoutDesc_ι α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G)) j s)

/-- Folding after the pinch commutes with raw based postcomposition, without
separation, local compactness or well-pointedness assumptions on either target. -/
public theorem pinch_postcomp {X : Type v} [TopologicalSpace X] (x : X)
    (F G : {F : C(S, X) // F a = x}) {Y : Type w} [TopologicalSpace Y] {y : Y}
    (h : C(X, Y)) (hy : h x = y) :
    ContinuousMap.comp h
      (ContinuousMap.comp
        (TopCat.widePushoutDesc α
          (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
          (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
          (fun j _ ↦ Subtype.property (ite (j = 0) F G)))
        (pinch n)) =
      ContinuousMap.comp
        (TopCat.widePushoutDesc α
          (ContinuousMap.const (TopCat.of (PUnit : Type)) y)
          (fun j : Fin 2 ↦ ContinuousMap.comp h (Subtype.val (ite (j = 0) F G)))
          (fun j _ ↦ Eq.trans (congrArg h (Subtype.property (ite (j = 0) F G))) hy))
        (pinch n) := by
  rw [← ContinuousMap.comp_assoc, pinch_fold_postcomp n x F G h hy]

end Fold

section ThreeFactors

local notation "D₃" => (fun _ : Fin 3 ↦ TopCat.of S)
local notation "β" =>
  (fun j : Fin 3 ↦ (TopCat.const a : TopCat.of (PUnit : Type) ⟶ D₃ j))
local notation "V" => (widePushout (TopCat.of (PUnit : Type)) D₃ β : TopCat)
local notation "b₃" => WidePushout.head β PUnit.unit
local notation "ι₃" => (fun j : Fin 3 ↦ TopCat.Hom.hom (WidePushout.ι β j))
local notation "I₃" =>
  (fun j : Fin 3 ↦
    (Subtype.mk (ι₃ j)
      (TopCat.widePushout_point_ι_point (X := D₃) (fun _ : Fin 3 ↦ a) j) :
        {F : C(S, V) // F a = b₃}))
local notation "P₃" =>
  (fun (F G : {F : C(S, V) // F a = b₃}) ↦
    (Subtype.mk
      (ContinuousMap.comp
        (TopCat.widePushoutDesc α
          (ContinuousMap.const (TopCat.of (PUnit : Type)) b₃)
          (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
          (fun j _ ↦ Subtype.property (ite (j = 0) F G)))
        (pinch n))
      (pinch_fold_northPoint n b₃ F G) : {F : C(S, V) // F a = b₃}))
local notation "L₃" => Subtype.val (P₃ (P₃ (I₃ 0) (I₃ 1)) (I₃ 2))
local notation "R₃" => Subtype.val (P₃ (I₃ 0) (P₃ (I₃ 1) (I₃ 2)))

/-- The original three-factor caller is not reflexivity: the same maps visit
three distinct nonhead inclusion values and differ at cube time three-eighths. -/
theorem pinch_coassoc_nondegenerate :
    let c : I^(Fin (n + 1)) := fun _ ↦ Set.projIcc 0 1 zero_le_one (1 / 2)
    let t : I → I^(Fin (n + 1)) := fun s ↦ Function.update c 0 s
    let e : I := Set.projIcc 0 1 zero_le_one (1 / 8)
    let u : I := Set.projIcc 0 1 zero_le_one (3 / 8)
    let v : I := Set.projIcc 0 1 zero_le_one (3 / 4)
    let z := Cube.collapseToSphere (n + 1) c
    let zR := Cube.collapseToSphere (n + 1) (t v)
    z ≠ a ∧ zR ≠ a ∧
      (∀ j : Fin 3, ι₃ j z ≠ b₃) ∧
      (∀ i j : Fin 3, i ≠ j → ι₃ i z ≠ ι₃ j z) ∧
      L₃ (Cube.collapseToSphere (n + 1) (t e)) = ι₃ 0 z ∧
      L₃ (Cube.collapseToSphere (n + 1) (t u)) = ι₃ 1 z ∧
      L₃ (Cube.collapseToSphere (n + 1) (t v)) = ι₃ 2 z ∧
      R₃ (Cube.collapseToSphere (n + 1) (t u)) = ι₃ 0 zR ∧
      L₃ (Cube.collapseToSphere (n + 1) (t u)) ≠
        R₃ (Cube.collapseToSphere (n + 1) (t u)) := by
  let c : I^(Fin (n + 1)) := fun _ ↦ Set.projIcc 0 1 zero_le_one (1 / 2)
  let t : I → I^(Fin (n + 1)) := fun s ↦ Function.update c 0 s
  let e : I := Set.projIcc 0 1 zero_le_one (1 / 8)
  let u : I := Set.projIcc 0 1 zero_le_one (3 / 8)
  let v : I := Set.projIcc 0 1 zero_le_one (3 / 4)
  let z := Cube.collapseToSphere (n + 1) c
  let zR := Cube.collapseToSphere (n + 1) (t v)
  let l : I := Set.projIcc 0 1 zero_le_one (1 / 4)
  let m : I := Set.projIcc 0 1 zero_le_one (1 / 2)
  have htm : t m = c := Function.update_eq_self 0 c
  have hz : z ≠ a := by
    intro h
    have hc : c ∉ Cube.boundary (Fin (n + 1)) :=
      Cube.mem_boundary_compl_iff.mpr (fun _ ↦ by norm_num [c, Set.coe_projIcc])
    exact hc ((Cube.collapseToSphere_eq_northPoint_iff (n + 1) c).mp h)
  have hzR : zR ≠ a := by
    intro h
    have hc : t v ∉ Cube.boundary (Fin (n + 1)) := by
      apply Cube.mem_boundary_compl_iff.mpr
      intro i
      by_cases hi : i = 0
      · subst i
        norm_num [t, v, Set.coe_projIcc]
      · simp only [t, Function.update_of_ne hi]
        norm_num [c, Set.coe_projIcc]
    exact hc ((Cube.collapseToSphere_eq_northPoint_iff (n + 1) (t v)).mp h)
  have hleft (F G : {F : C(S, V) // F a = b₃}) (s r : I)
      (hs : (s : ℝ) ≤ 1 / 2)
      (hr : Set.projIcc 0 1 zero_le_one (2 * (s : ℝ)) = r) :
      (P₃ F G).val (Cube.collapseToSphere (n + 1) (t s)) =
        F.val (Cube.collapseToSphere (n + 1) (t r)) := by
    simpa only [t, Function.update_self, hr, Function.update_idem] using
      (pinch_fold_apply_collapseToSphere_of_le n b₃ F G (t s)
        (by simpa only [t, Function.update_self] using hs))
  have hright (F G : {F : C(S, V) // F a = b₃}) (s r : I)
      (hs : 1 / 2 ≤ (s : ℝ))
      (hr : Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - 1) = r) :
      (P₃ F G).val (Cube.collapseToSphere (n + 1) (t s)) =
        G.val (Cube.collapseToSphere (n + 1) (t r)) := by
    simpa only [t, Function.update_self, hr, Function.update_idem] using
      (pinch_fold_apply_collapseToSphere_of_ge n b₃ F G (t s)
        (by simpa only [t, Function.update_self] using hs))
  have hel : Set.projIcc 0 1 zero_le_one (2 * (e : ℝ)) = l := by
    apply Subtype.ext
    norm_num [e, l, Set.coe_projIcc]
  have hlm : Set.projIcc 0 1 zero_le_one (2 * (l : ℝ)) = m := by
    apply Subtype.ext
    norm_num [l, m, Set.coe_projIcc]
  have huv : Set.projIcc 0 1 zero_le_one (2 * (u : ℝ)) = v := by
    apply Subtype.ext
    norm_num [u, v, Set.coe_projIcc]
  have hvm : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1) = m := by
    apply Subtype.ext
    norm_num [v, m, Set.coe_projIcc]
  have hLe : L₃ (Cube.collapseToSphere (n + 1) (t e)) = ι₃ 0 z := by
    calc
      _ = (P₃ (I₃ 0) (I₃ 1)).val (Cube.collapseToSphere (n + 1) (t l)) :=
        hleft (P₃ (I₃ 0) (I₃ 1)) (I₃ 2) e l
          (by norm_num [e, Set.coe_projIcc]) hel
      _ = ι₃ 0 z := by
        simpa only [htm] using
          (hleft (I₃ 0) (I₃ 1) l m (by norm_num [l, Set.coe_projIcc]) hlm)
  have hLu : L₃ (Cube.collapseToSphere (n + 1) (t u)) = ι₃ 1 z := by
    calc
      _ = (P₃ (I₃ 0) (I₃ 1)).val (Cube.collapseToSphere (n + 1) (t v)) :=
        hleft (P₃ (I₃ 0) (I₃ 1)) (I₃ 2) u v
          (by norm_num [u, Set.coe_projIcc]) huv
      _ = ι₃ 1 z := by
        simpa only [htm] using
          (hright (I₃ 0) (I₃ 1) v m (by norm_num [v, Set.coe_projIcc]) hvm)
  have hLv : L₃ (Cube.collapseToSphere (n + 1) (t v)) = ι₃ 2 z := by
    simpa only [htm] using
      (hright (P₃ (I₃ 0) (I₃ 1)) (I₃ 2) v m
        (by norm_num [v, Set.coe_projIcc]) hvm)
  have hRu : R₃ (Cube.collapseToSphere (n + 1) (t u)) = ι₃ 0 zR :=
    hleft (I₃ 0) (P₃ (I₃ 1) (I₃ 2)) u v
      (by norm_num [u, Set.coe_projIcc]) huv
  refine ⟨hz, hzR, ?_, ?_, hLe, hLu, hLv, hRu, ?_⟩
  · intro j h
    apply hz
    calc
      z = (TopCat.widePushoutPointRetraction D₃ (fun _ : Fin 3 ↦ a) j).hom
          (ι₃ j z) :=
        (TopCat.widePushoutPointRetraction_ι_apply D₃ (fun _ : Fin 3 ↦ a) j z).symm
      _ = (TopCat.widePushoutPointRetraction D₃ (fun _ : Fin 3 ↦ a) j).hom b₃ :=
        congrArg (TopCat.widePushoutPointRetraction D₃ (fun _ : Fin 3 ↦ a) j).hom h
      _ = a := TopCat.widePushoutPointRetraction_head_apply D₃
        (fun _ : Fin 3 ↦ a) j PUnit.unit
  · intro i j hij h
    apply hz
    calc
      z = (TopCat.widePushoutPointRetraction D₃ (fun _ : Fin 3 ↦ a) i).hom
          (ι₃ i z) :=
        (TopCat.widePushoutPointRetraction_ι_apply D₃ (fun _ : Fin 3 ↦ a) i z).symm
      _ = (TopCat.widePushoutPointRetraction D₃ (fun _ : Fin 3 ↦ a) i).hom
          (ι₃ j z) :=
        congrArg (TopCat.widePushoutPointRetraction D₃ (fun _ : Fin 3 ↦ a) i).hom h
      _ = a := TopCat.widePushoutPointRetraction_ι_of_ne_apply D₃
        (fun _ : Fin 3 ↦ a) i j (Ne.symm hij) z
  · intro h
    apply hz
    calc
      z = (TopCat.widePushoutPointRetraction D₃ (fun _ : Fin 3 ↦ a) 1).hom
          (ι₃ 1 z) :=
        (TopCat.widePushoutPointRetraction_ι_apply D₃ (fun _ : Fin 3 ↦ a) 1 z).symm
      _ = (TopCat.widePushoutPointRetraction D₃ (fun _ : Fin 3 ↦ a) 1).hom
          (ι₃ 0 zR) :=
        congrArg (TopCat.widePushoutPointRetraction D₃ (fun _ : Fin 3 ↦ a) 1).hom
          (hLu.symm.trans (h.trans hRu))
      _ = a := TopCat.widePushoutPointRetraction_ι_of_ne_apply D₃
        (fun _ : Fin 3 ↦ a) 1 0 (by decide) zR

end ThreeFactors

end Metric.Sphere
