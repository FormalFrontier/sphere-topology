/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Geometry.SpherePinch
import Mathlib.Tactic.FinCases

/-!
# Sphere pinch on homotopy classes

The left-then-right convention of `Metric.Sphere.pinch` corresponds to the
**right class times the left class** under Mathlib's existing
`HomotopyGroup.mul_spec`. No multiplication on sphere-map components is defined
by transport. Each of the two existing factor retractions composed with the
pinch is homotopic to the identity relative to the specified north pole.
In sphere dimension at least two, exchanging two based factor maps after the
pinch preserves relative homotopy. In particular, the original factor swap
after the pinch is homotopic to the pinch relative to the north pole.

## Limitations

The counits and cocommutativity assert relative homotopy, without choosing
homotopy data. Cocommutativity is restricted to sphere dimensions at least two;
the fold-class order in dimension one remains unchanged. A full cogroup
structure, a pinch on the zero-dimensional sphere, and source coverage are not
asserted. Targets of the folded-map results have independent universe and
require only a topology.

## References

* Mathlib's homotopy groups, due to Roberto Alvarez, supply their existing
  multiplication, including its reversed concatenation convention, and
  commutativity in dimensions at least two.
* The sphere-class comparison and the boundary-relative to pole-relative
  homotopy comparison are those of `SphereTopology.Homotopy.HomotopyGroup.Sphere`.
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits

namespace Metric.Sphere

variable (n : ℕ)

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1
local notation "a" => EuclideanSpace.northPoint (n + 1)
local notation "D" => (fun _ : Fin 2 ↦ TopCat.of S)
local notation "α" =>
  (fun j : Fin 2 ↦ (TopCat.const a : TopCat.of (PUnit : Type) ⟶ D j))

section Fold

/-- The class of folding `F` on the left and `G` on the right is the existing
class of `G` times the existing class of `F`. The order is not commuted, also
in dimension one. -/
public theorem pinch_fold_class {X : Type v} [TopologicalSpace X] (x : X)
    (F G : {F : C(S, X) // F a = x}) :
    (HomotopyGroup.equivSphereClasses (n + 1) x).symm
      (ZerothHomotopy.mk
        (Subtype.mk
          (ContinuousMap.comp
            (TopCat.widePushoutDesc α
              (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
              (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
              (fun j _ ↦ Subtype.property (ite (j = 0) F G)))
            (pinch n))
          (pinch_fold_northPoint n x F G) : {H : C(S, X) // H a = x})) =
      (HomotopyGroup.equivSphereClasses (n + 1) x).symm (ZerothHomotopy.mk G) *
      (HomotopyGroup.equivSphereClasses (n + 1) x).symm (ZerothHomotopy.mk F) := by
  let H : {H : C(S, X) // H a = x} :=
    ⟨(TopCat.widePushoutDesc α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G))).comp (pinch n),
      pinch_fold_northPoint n x F G⟩
  have hloop : (GenLoop.sphereHomeomorph (n + 1) x).symm H =
      GenLoop.transAt (0 : Fin (n + 1))
        ((GenLoop.sphereHomeomorph (n + 1) x).symm F)
        ((GenLoop.sphereHomeomorph (n + 1) x).symm G) := by
    apply (GenLoop.sphereHomeomorph (n + 1) x).injective
    apply Subtype.ext
    exact (congrArg Subtype.val
      ((GenLoop.sphereHomeomorph (n + 1) x).apply_symm_apply H)).trans
      (pinch_fold n x F G)
  have hquot :
      (⟦(GenLoop.sphereHomeomorph (n + 1) x).symm H⟧ :
        HomotopyGroup (Fin (n + 1)) X x) =
      (⟦GenLoop.transAt (0 : Fin (n + 1))
        ((GenLoop.sphereHomeomorph (n + 1) x).symm F)
        ((GenLoop.sphereHomeomorph (n + 1) x).symm G)⟧ :
        HomotopyGroup (Fin (n + 1)) X x) :=
    congrArg (fun p : GenLoop (Fin (n + 1)) X x ↦
      (⟦p⟧ : HomotopyGroup (Fin (n + 1)) X x)) hloop
  have hmul := (HomotopyGroup.mul_spec (i := (0 : Fin (n + 1)))
    (p := (GenLoop.sphereHomeomorph (n + 1) x).symm G)
    (q := (GenLoop.sphereHomeomorph (n + 1) x).symm F)).symm
  exact (HomotopyGroup.equivSphereClasses_symm_mk (n + 1) x H).trans
    (hquot.trans (hmul.trans
      (congrArg₂ (fun p q : HomotopyGroup (Fin (n + 1)) X x ↦ p * q)
        (HomotopyGroup.equivSphereClasses_symm_mk (n + 1) x G).symm
        (HomotopyGroup.equivSphereClasses_symm_mk (n + 1) x F).symm)))

end Fold

/-- Each of the two existing factor retractions after the pinch is homotopic to
the identity relative to the singleton north pole. No counit homotopy is an input. -/
theorem pinch_retraction_homotopicRel (j : Fin 2) :
    ((TopCat.widePushoutPointRetraction D (fun _ ↦ a) j).hom.comp (pinch n)).HomotopicRel
      (ContinuousMap.id S) ({a} : Set S) := by
  classical
  let r := (TopCat.widePushoutPointRetraction D (fun _ ↦ a) j).hom
  let idMap : {H : C(S, S) // H a = a} := ⟨ContinuousMap.id S, rfl⟩
  let constMap : {H : C(S, S) // H a = a} := ⟨ContinuousMap.const S a, rfl⟩
  let F := if j = 0 then idMap else constMap
  let G := if j = 0 then constMap else idMap
  have hr : r =
      TopCat.widePushoutDesc α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
        (fun i : Fin 2 ↦ Subtype.val (ite (i = 0) F G))
        (fun i _ ↦ Subtype.property (ite (i = 0) F G)) := by
    apply TopCat.widePushoutDesc_unique
    · intro p
      exact TopCat.widePushoutPointRetraction_head_apply D (fun _ ↦ a) j p
    · intro i t
      fin_cases j <;> fin_cases i
      · simp only [F]
        exact TopCat.widePushoutPointRetraction_ι_apply D (fun _ ↦ a) 0 t
      · simp only [G]
        exact TopCat.widePushoutPointRetraction_ι_of_ne_apply D (fun _ ↦ a)
          0 1 (by decide) t
      · simp only [F]
        exact TopCat.widePushoutPointRetraction_ι_of_ne_apply D (fun _ ↦ a)
          1 0 (by decide) t
      · simp only [G]
        exact TopCat.widePushoutPointRetraction_ι_apply D (fun _ ↦ a) 1 t
  have hbase : (r.comp (pinch n)) a = a := by
    rw [ContinuousMap.comp_apply, pinch_northPoint]
    exact TopCat.widePushoutPointRetraction_head_apply D (fun _ ↦ a) j PUnit.unit
  let H : {H : C(S, S) // H a = a} := ⟨r.comp (pinch n), hbase⟩
  have hclass :
      (HomotopyGroup.equivSphereClasses (n + 1) a).symm (ZerothHomotopy.mk H) =
        (HomotopyGroup.equivSphereClasses (n + 1) a).symm (ZerothHomotopy.mk G) *
        (HomotopyGroup.equivSphereClasses (n + 1) a).symm (ZerothHomotopy.mk F) := by
    simpa only [H, hr] using pinch_fold_class n a F G
  have hconst :
      (HomotopyGroup.equivSphereClasses (n + 1) a).symm
        (ZerothHomotopy.mk constMap) =
      (1 : HomotopyGroup (Fin (n + 1)) S a) := by
    exact (HomotopyGroup.equivSphereClasses_symm_const (n + 1) a).trans
      HomotopyGroup.one_def.symm
  apply (ZerothHomotopy.sphere_mk_eq_mk_iff_homotopicRel (n + 1) a H idMap).mp
  apply (HomotopyGroup.equivSphereClasses (n + 1) a).symm.injective
  rw [hclass]
  by_cases hj : j = 0
  · simp only [F, G, ite_eq_left hj, hconst, one_mul]
  · simp only [F, G, ite_eq_right hj, hconst, mul_one]

section Cocommutativity

local notation "S₂" =>
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (((n + 1) + 1) + 1))) 1
local notation "a₂" => EuclideanSpace.northPoint ((n + 1) + 1)
local notation "D₂" => (fun _ : Fin 2 ↦ TopCat.of S₂)
local notation "α₂" =>
  (fun j : Fin 2 ↦ (TopCat.const a₂ : TopCat.of (PUnit : Type) ⟶ D₂ j))

/-- In sphere dimension `n + 2`, folding two based maps after the pinch is
homotopic, relative to the specified north pole, to folding them in the opposite
order. This follows from Mathlib's higher homotopy-group commutativity and
`pinch_fold_class`. -/
theorem pinch_fold_homotopicRel_swap
    {X : Type v} [TopologicalSpace X] (x : X)
    (F G : {F : C(S₂, X) // F a₂ = x}) :
    (ContinuousMap.comp
      (TopCat.widePushoutDesc α₂
        (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G)))
      (pinch (n + 1))).HomotopicRel
      (ContinuousMap.comp
        (TopCat.widePushoutDesc α₂
          (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
          (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) G F))
          (fun j _ ↦ Subtype.property (ite (j = 0) G F)))
        (pinch (n + 1)))
      ({a₂} : Set S₂) := by
  let H : {H : C(S₂, X) // H a₂ = x} :=
    ⟨(TopCat.widePushoutDesc α₂
      (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G))).comp (pinch (n + 1)),
      pinch_fold_northPoint (n + 1) x F G⟩
  let K : {H : C(S₂, X) // H a₂ = x} :=
    ⟨(TopCat.widePushoutDesc α₂
      (ContinuousMap.const (TopCat.of (PUnit : Type)) x)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) G F))
      (fun j _ ↦ Subtype.property (ite (j = 0) G F))).comp (pinch (n + 1)),
      pinch_fold_northPoint (n + 1) x G F⟩
  apply (ZerothHomotopy.sphere_mk_eq_mk_iff_homotopicRel ((n + 1) + 1) x H K).mp
  apply (HomotopyGroup.equivSphereClasses ((n + 1) + 1) x).symm.injective
  have hcomm := mul_comm
    ((HomotopyGroup.equivSphereClasses ((n + 1) + 1) x).symm (ZerothHomotopy.mk G))
    ((HomotopyGroup.equivSphereClasses ((n + 1) + 1) x).symm (ZerothHomotopy.mk F))
  exact (pinch_fold_class (n + 1) x F G).trans
    (hcomm.trans (pinch_fold_class (n + 1) x G F).symm)

local notation "W₂" => (widePushout (TopCat.of (PUnit : Type)) D₂ α₂ : TopCat)
local notation "b₂" => WidePushout.head α₂ PUnit.unit

/-- In sphere dimension `n + 2`, exchanging the two original pushout factors
after the pinch is homotopic to the pinch relative to the specified north pole.
The factor exchange is the categorical descent fixing the head and swapping
the inclusions. -/
theorem pinch_homotopicRel_swap :
    (((WidePushout.desc (arrows := α₂)
      (WidePushout.head α₂)
      (fun j : Fin 2 ↦
        WidePushout.ι α₂ ((Equiv.swap (0 : Fin 2) 1) j))
      (fun j ↦
        WidePushout.arrow_ι α₂ ((Equiv.swap (0 : Fin 2) 1) j))).hom).comp
      (pinch (n + 1))).HomotopicRel
      (pinch (n + 1)) ({a₂} : Set S₂) := by
  let F : {F : C(S₂, W₂) // F a₂ = b₂} :=
    ⟨(WidePushout.ι α₂ 0).hom,
      TopCat.widePushout_point_ι_point (X := D₂) (fun _ : Fin 2 ↦ a₂) 0⟩
  let G : {F : C(S₂, W₂) // F a₂ = b₂} :=
    ⟨(WidePushout.ι α₂ 1).hom,
      TopCat.widePushout_point_ι_point (X := D₂) (fun _ : Fin 2 ↦ a₂) 1⟩
  have hid : ContinuousMap.id W₂ =
      TopCat.widePushoutDesc α₂
        (ContinuousMap.const (TopCat.of (PUnit : Type)) b₂)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G)) := by
    apply TopCat.widePushoutDesc_unique
    · intro p
      cases p
      rfl
    · intro j z
      fin_cases j <;> rfl
  have hswap :
      (WidePushout.desc (arrows := α₂)
        (WidePushout.head α₂)
        (fun j : Fin 2 ↦
          WidePushout.ι α₂ ((Equiv.swap (0 : Fin 2) 1) j))
        (fun j ↦
          WidePushout.arrow_ι α₂ ((Equiv.swap (0 : Fin 2) 1) j))).hom =
      TopCat.widePushoutDesc α₂
        (ContinuousMap.const (TopCat.of (PUnit : Type)) b₂)
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) G F))
        (fun j _ ↦ Subtype.property (ite (j = 0) G F)) := by
    apply TopCat.widePushoutDesc_unique
    · intro p
      cases p
      exact congrArg (fun k : TopCat.of (PUnit : Type) ⟶ W₂ ↦ k PUnit.unit)
        (WidePushout.head_desc α₂ _ _ _)
    · intro j z
      have hj := congrArg (fun k : D₂ j ⟶ W₂ ↦ k.hom z)
        (WidePushout.ι_desc α₂
          (WidePushout.head α₂)
          (fun i : Fin 2 ↦
            WidePushout.ι α₂ ((Equiv.swap (0 : Fin 2) 1) i))
          (fun i ↦
            WidePushout.arrow_ι α₂ ((Equiv.swap (0 : Fin 2) 1) i)) j)
      simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at hj
      fin_cases j
      · simpa [G] using hj
      · simpa [F] using hj
  have h := pinch_fold_homotopicRel_swap n b₂ G F
  rw [← hswap, ← hid, ContinuousMap.id_comp] at h
  exact h

end Cocommutativity

end Metric.Sphere
