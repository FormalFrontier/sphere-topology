/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.HomotopyGroup.Sphere
public import FundamentalGroupoids.Topology.Category.TopCat.Limits.WidePushout
public import SphereTopology.Topology.WidePushoutRetraction
import SphereTopology.Topology.WidePushout.Separation
import SphereTopology.Topology.WidePushout.Compactness
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
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
The pinch is surjective and is a quotient map onto its given categorical target.

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

/-- The pinch reaches every point of its given two-factor point-wide-pushout. -/
theorem surjective_pinch : Function.Surjective (pinch n) := by
  intro y
  obtain ⟨j, z, rfl⟩ := Concrete.widePushout_exists_rep' α y
  obtain ⟨u, rfl⟩ := Cube.surjective_collapseToSphere (n + 1) z
  have h0 : 0 ≤ (u 0 : ℝ) := (u 0).property.1
  have h1 : (u 0 : ℝ) ≤ 1 := (u 0).property.2
  fin_cases j
  · let s : I := ⟨(u 0 : ℝ) / 2, by constructor <;> linarith⟩
    let t : I^(Fin (n + 1)) := Function.update u 0 s
    have ht : (t 0 : ℝ) ≤ 1 / 2 := by
      simp only [t, Function.update_self]
      change (u 0 : ℝ) / 2 ≤ 1 / 2
      linarith
    have hp : Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ)) = u 0 := by
      have heq : 2 * (t 0 : ℝ) = (u 0 : ℝ) := by
        simp only [t, Function.update_self]
        change 2 * ((u 0 : ℝ) / 2) = (u 0 : ℝ)
        linarith
      rw [heq, Set.projIcc_val]
    refine ⟨Cube.collapseToSphere (n + 1) t, ?_⟩
    rw [pinch_apply_collapseToSphere_of_le n t ht, hp]
    simp only [t, Function.update_idem, Function.update_eq_self]
    rfl
  · let s : I := ⟨((u 0 : ℝ) + 1) / 2, by constructor <;> linarith⟩
    let t : I^(Fin (n + 1)) := Function.update u 0 s
    have ht : 1 / 2 ≤ (t 0 : ℝ) := by
      simp only [t, Function.update_self]
      change 1 / 2 ≤ ((u 0 : ℝ) + 1) / 2
      linarith
    have hp : Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - 1) = u 0 := by
      have heq : 2 * (t 0 : ℝ) - 1 = (u 0 : ℝ) := by
        simp only [t, Function.update_self]
        change 2 * (((u 0 : ℝ) + 1) / 2) - 1 = (u 0 : ℝ)
        linarith
      rw [heq, Set.projIcc_val]
    refine ⟨Cube.collapseToSphere (n + 1) t, ?_⟩
    rw [pinch_apply_collapseToSphere_of_ge n t ht, hp]
    simp only [t, Function.update_idem, Function.update_eq_self]
    rfl

/-- The pinch is a quotient map for the topology of its given categorical
point-wide-pushout. -/
theorem isQuotientMap_pinch : Topology.IsQuotientMap (pinch n) :=
  Topology.IsQuotientMap.of_surjective_continuous (surjective_pinch n) (pinch n).continuous

private theorem pinch_compression_boundary (t : I^(Fin (n + 1))) (c : ℝ)
    (hc : c = 0 ∨ c = 1)
    (htc : 0 ≤ 2 * (t 0 : ℝ) - c ∧ 2 * (t 0 : ℝ) - c ≤ 1)
    (h : Function.update t 0
      (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - c)) ∈
        Cube.boundary (Fin (n + 1))) :
    t ∈ Cube.boundary (Fin (n + 1)) ∨ (t 0 : ℝ) = 1 / 2 := by
  obtain ⟨i, hi⟩ := h
  by_cases hi0 : i = 0
  · subst i
    have hend : 2 * (t 0 : ℝ) - c = 0 ∨ 2 * (t 0 : ℝ) - c = 1 := by
      rcases hi with hi | hi
      · left
        have hp : Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - c) = 0 := by
          simpa only [Function.update_self] using hi
        exact le_antisymm (projIcc_eq_zero.mp hp) htc.1
      · right
        have hp : Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - c) = 1 := by
          simpa only [Function.update_self] using hi
        exact le_antisymm htc.2 (projIcc_eq_one.mp hp)
    rcases hc with rfl | rfl
    · rcases hend with he | he
      · left
        refine ⟨0, Or.inl ?_⟩
        apply Subtype.ext
        change (t 0 : ℝ) = 0
        linarith
      · right
        linarith
    · rcases hend with he | he
      · right
        linarith
      · left
        refine ⟨0, Or.inr ?_⟩
        apply Subtype.ext
        change (t 0 : ℝ) = 1
        linarith
  · left
    exact ⟨i, by simpa only [Function.update_of_ne hi0] using hi⟩

/-- Exactly the points with zero first ambient coordinate map to the pushout head. -/
theorem pinch_eq_head_iff (z : S) :
    pinch n z = b ↔ (z : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 0 = 0 := by
  obtain ⟨t, rfl⟩ := Cube.surjective_collapseToSphere (n + 1) z
  have hzero :
      (Cube.collapseToSphere (n + 1) t :
        EuclideanSpace ℝ (Fin ((n + 1) + 1))) 0 = 0 ↔
      t ∈ Cube.boundary (Fin (n + 1)) ∨ (t 0 : ℝ) = 1 / 2 := by
    simpa only [Fin.castSucc_zero] using
      Cube.collapseToSphere_apply_castSucc_eq_zero_iff (n + 1) t (0 : Fin (n + 1))
  rw [hzero]
  constructor
  · intro h
    by_cases ht : (t 0 : ℝ) ≤ 1 / 2
    · have hp : Cube.collapseToSphere (n + 1)
          (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0))) = a :=
        (TopCat.widePushout_point_ι_eq_head_iff (X := D)
          (fun _ : Fin 2 ↦ a) 0 _).mp
            ((pinch_apply_collapseToSphere_of_le n t ht).symm.trans h)
      exact pinch_compression_boundary n t 0 (Or.inl rfl)
        ⟨by linarith [(t 0).property.1], by linarith⟩
        (by simpa only [sub_zero] using
          (Cube.collapseToSphere_eq_northPoint_iff (n + 1) _).mp hp)
    · have ht' : 1 / 2 ≤ (t 0 : ℝ) := (not_le.mp ht).le
      have hp : Cube.collapseToSphere (n + 1)
          (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * t 0 - 1))) = a :=
        (TopCat.widePushout_point_ι_eq_head_iff (X := D)
          (fun _ : Fin 2 ↦ a) 1 _).mp
            ((pinch_apply_collapseToSphere_of_ge n t ht').symm.trans h)
      exact pinch_compression_boundary n t 1 (Or.inr rfl)
        ⟨by linarith, by linarith [(t 0).property.2]⟩
        ((Cube.collapseToSphere_eq_northPoint_iff (n + 1) _).mp hp)
  · rintro (ht | ht)
    · rw [(Cube.collapseToSphere_eq_northPoint_iff (n + 1) t).mpr ht,
        pinch_northPoint]
    · exact pinch_apply_collapseToSphere_midpoint n t ht

private theorem pinch_eq_of_same_compression (t u : I^(Fin (n + 1)))
    (j : Fin 2) (c : ℝ)
    (htc : 0 ≤ 2 * (t 0 : ℝ) - c ∧ 2 * (t 0 : ℝ) - c ≤ 1)
    (huc : 0 ≤ 2 * (u 0 : ℝ) - c ∧ 2 * (u 0 : ℝ) - c ≤ 1)
    (htn : pinch n (Cube.collapseToSphere (n + 1) t) ≠ b)
    (hun : pinch n (Cube.collapseToSphere (n + 1) u) ≠ b)
    (hpt : pinch n (Cube.collapseToSphere (n + 1) t) =
      ι j (Cube.collapseToSphere (n + 1)
        (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - c)))))
    (hpu : pinch n (Cube.collapseToSphere (n + 1) u) =
      ι j (Cube.collapseToSphere (n + 1)
        (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - c)))))
    (h : pinch n (Cube.collapseToSphere (n + 1) t) =
      pinch n (Cube.collapseToSphere (n + 1) u)) :
    Cube.collapseToSphere (n + 1) t = Cube.collapseToSphere (n + 1) u := by
  let t' := Function.update t 0
    (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - c))
  let u' := Function.update u 0
    (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - c))
  have hct : Cube.collapseToSphere (n + 1) t' ≠ a := by
    intro he
    apply htn
    calc
      pinch n (Cube.collapseToSphere (n + 1) t) =
          ι j (Cube.collapseToSphere (n + 1) t') := hpt
      _ = b := by
        rw [he]
        exact TopCat.widePushout_point_ι_point (X := D) (fun _ : Fin 2 ↦ a) j
  have hcu : Cube.collapseToSphere (n + 1) u' ≠ a := by
    intro he
    apply hun
    calc
      pinch n (Cube.collapseToSphere (n + 1) u) =
          ι j (Cube.collapseToSphere (n + 1) u') := hpu
      _ = b := by
        rw [he]
        exact TopCat.widePushout_point_ι_point (X := D) (fun _ : Fin 2 ↦ a) j
  have ht' : t' ∈ (Cube.boundary (Fin (n + 1)))ᶜ :=
    fun hm ↦ hct ((Cube.collapseToSphere_eq_northPoint_iff (n + 1) t').mpr hm)
  have hu' : u' ∈ (Cube.boundary (Fin (n + 1)))ᶜ :=
    fun hm ↦ hcu ((Cube.collapseToSphere_eq_northPoint_iff (n + 1) u').mpr hm)
  have hq : Cube.collapseToSphere (n + 1) t' =
      Cube.collapseToSphere (n + 1) u' :=
    (TopCat.isEmbedding_widePushout_point_ι D (fun _ : Fin 2 ↦ a) j).injective
      (hpt.symm.trans (h.trans hpu))
  have hinterior :
      (⟨t', ht'⟩ : ((Cube.boundary (Fin (n + 1)))ᶜ : Set (I^(Fin (n + 1))))) =
        ⟨u', hu'⟩ := by
    apply OnePoint.coe_injective
    apply (Cube.onePointBoundaryComplHomeomorphSphere (n + 1)).injective
    simpa only [← Cube.collapseToSphere_apply_coe] using hq
  have he : t' = u' := congrArg Subtype.val hinterior
  have htu : t = u := by
    funext i
    by_cases hi : i = 0
    · subst i
      apply Subtype.ext
      have he0 :
          (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - c) : ℝ) =
            (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - c) : ℝ) := by
        simpa only [t', u', Function.update_self] using
          congrArg (fun v : I^(Fin (n + 1)) ↦ (v 0 : ℝ)) he
      have hproj_t : (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - c) : ℝ) =
          2 * (t 0 : ℝ) - c :=
        congrArg Subtype.val (Set.projIcc_of_mem zero_le_one htc)
      have hproj_u : (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - c) : ℝ) =
          2 * (u 0 : ℝ) - c :=
        congrArg Subtype.val (Set.projIcc_of_mem zero_le_one huc)
      rw [hproj_t, hproj_u] at he0
      change (t 0 : ℝ) = (u 0 : ℝ)
      linarith
    · simpa only [t', u', Function.update_of_ne hi] using congrFun he i
  exact congrArg (Cube.collapseToSphere (n + 1)) htu

/-- Two points have the same pinch value exactly when they are equal or both
have zero first ambient coordinate. -/
theorem pinch_eq_pinch_iff (z w : S) :
    pinch n z = pinch n w ↔
      z = w ∨
        ((z : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 0 = 0 ∧
          (w : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 0 = 0) := by
  constructor
  · intro h
    by_cases hz : (z : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 0 = 0
    · right
      exact ⟨hz, (pinch_eq_head_iff n w).mp
        (h.symm.trans ((pinch_eq_head_iff n z).mpr hz))⟩
    · left
      have hzn : pinch n z ≠ b := fun he ↦ hz ((pinch_eq_head_iff n z).mp he)
      have hwn : pinch n w ≠ b := fun he ↦ hzn (h.trans he)
      have index_eq (j k : Fin 2) (x y : S)
          (hx : ι j x ≠ b) (he : ι j x = ι k y) : j = k := by
        have hxa : x ≠ a := by
          intro ha
          apply hx
          rw [ha]
          exact TopCat.widePushout_point_ι_point (X := D) (fun _ : Fin 2 ↦ a) j
        exact congrArg Sigma.fst
          ((TopCat.widePushout_point_ι_eq_ι_iff_of_ne (X := D)
            (fun _ : Fin 2 ↦ a) hxa).mp he)
      obtain ⟨t, rfl⟩ := Cube.surjective_collapseToSphere (n + 1) z
      obtain ⟨u, rfl⟩ := Cube.surjective_collapseToSphere (n + 1) w
      by_cases ht : (t 0 : ℝ) ≤ 1 / 2
      · have hL := pinch_apply_collapseToSphere_of_le n t ht
        by_cases hu : (u 0 : ℝ) ≤ 1 / 2
        · have huL := pinch_apply_collapseToSphere_of_le n u hu
          exact pinch_eq_of_same_compression n t u 0 0
            ⟨by linarith [(t 0).property.1], by linarith⟩
            ⟨by linarith [(u 0).property.1], by linarith⟩ hzn hwn
            (by simpa only [sub_zero] using hL)
            (by simpa only [sub_zero] using huL) h
        · have huR := pinch_apply_collapseToSphere_of_ge n u (not_le.mp hu).le
          have h01 : (0 : Fin 2) = 1 := index_eq 0 1 _ _
            (fun hb ↦ hzn (hL.trans hb)) (hL.symm.trans (h.trans huR))
          exact ((by decide : (0 : Fin 2) ≠ 1) h01).elim
      · have ht' : 1 / 2 ≤ (t 0 : ℝ) := (not_le.mp ht).le
        have hR := pinch_apply_collapseToSphere_of_ge n t ht'
        by_cases hu : (u 0 : ℝ) ≤ 1 / 2
        · have huL := pinch_apply_collapseToSphere_of_le n u hu
          have h10 : (1 : Fin 2) = 0 := index_eq 1 0 _ _
            (fun hb ↦ hzn (hR.trans hb)) (hR.symm.trans (h.trans huL))
          exact ((by decide : (1 : Fin 2) ≠ 0) h10).elim
        · have hu' : 1 / 2 ≤ (u 0 : ℝ) := (not_le.mp hu).le
          have huR := pinch_apply_collapseToSphere_of_ge n u hu'
          exact pinch_eq_of_same_compression n t u 1 1
            ⟨by linarith, by linarith [(t 0).property.2]⟩
            ⟨by linarith, by linarith [(u 0).property.2]⟩ hzn hwn hR huR h
  · rintro (rfl | ⟨hz, hw⟩)
    · rfl
    · exact ((pinch_eq_head_iff n z).mpr hz).trans
        ((pinch_eq_head_iff n w).mpr hw).symm

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
