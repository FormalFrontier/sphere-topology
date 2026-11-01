/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.PointMap
public import FundamentalGroupoids.Topology.Homotopy.WidePushout
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Point-relative equivalences and contractions of wide pushouts

Maps preserving chosen points descend by `TopCat.widePushoutDesc`. Relative
inverse homotopies of the factors give relative inverse homotopies of the
resulting maps, and hence an ordinary `ContinuousMap.HomotopyEquiv`.
The selected relative homotopies retain their head and factor equations.

Contractions fixing the chosen points give a contraction fixing the common
head. Supplying these fixed-point contractions is stronger than merely
assuming that each factor is contractible. No finiteness, separation,
cofibration or nonempty-index hypothesis is imposed.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  p. 19, for the point-wedge setting. The supplied relative contractions used
  here are stronger data than ordinary contractibility in that discussion.
* `FundamentalGroupoids.Topology.Homotopy.WidePushout` supplies homotopy descent.
* Mathlib supplies relative homotopies and homotopy equivalences.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w z

namespace TopCat

variable {J : Type w} {X : J → TopCat.{max u w}} {Y : J → TopCat.{max v w}}
  (x : ∀ j, X j) (y : ∀ j, Y j)

set_option quotPrecheck false in
local notation "aX" => (fun j : J ↦ (TopCat.const (x j) :
  TopCat.of PUnit ⟶ X j))
set_option quotPrecheck false in
local notation "aY" => (fun j : J ↦ (TopCat.const (y j) :
  TopCat.of PUnit ⟶ Y j))
set_option quotPrecheck false in
local notation "WX" => (widePushout (TopCat.of PUnit) X aX : TopCat)
set_option quotPrecheck false in
local notation "WY" => (widePushout (TopCat.of PUnit) Y aY : TopCat)
set_option quotPrecheck false in
local notation "hx" => (WidePushout.head aX PUnit.unit)
set_option quotPrecheck false in
local notation "hy" => (WidePushout.head aY PUnit.unit)

/-- Descent of point-preserving factor maps sends the common head to the common head.
This is `widePushoutDesc_point_head` specialized to `PUnit.unit`. -/
@[deprecated widePushoutDesc_point_head (since := "2026-10-30")]
theorem widePushoutPointDesc_head (f : ∀ j, C(X j, Y j))
    (hf : ∀ j, f j (x j) = y j) :
    widePushoutDesc aX (ContinuousMap.const _ hy)
      (fun j ↦ (WidePushout.ι aY j).hom.comp (f j))
      (widePushoutDesc_point_condition x y f hf) hx = hy :=
  widePushoutDesc_point_head x y f hf PUnit.unit

private theorem point_inverse (f : ∀ j, C(X j, Y j))
    (hf : ∀ j, f j (x j) = y j) (g : ∀ j, C(Y j, X j))
    (L : ∀ j, ContinuousMap.HomotopyRel ((g j).comp (f j))
      (ContinuousMap.id (X j)) {x j}) (j : J) : g j (y j) = x j := by
  simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply, hf j] using
    (L j).fst_eq_snd (x := x j) (by simp)

section InverseHomotopy

variable (f : ∀ j, C(X j, Y j)) (hf : ∀ j, f j (x j) = y j)
  (g : ∀ j, C(Y j, X j))
  (L : ∀ j, ContinuousMap.HomotopyRel ((g j).comp (f j))
    (ContinuousMap.id (X j)) {x j})

set_option quotPrecheck false in
local notation "F" => widePushoutDesc aX (ContinuousMap.const _ hy)
  (fun j ↦ (WidePushout.ι aY j).hom.comp (f j))
  (widePushoutDesc_point_condition x y f hf)
set_option quotPrecheck false in
local notation "G" => widePushoutDesc aY (ContinuousMap.const _ hx)
  (fun j ↦ (WidePushout.ι aX j).hom.comp (g j))
  (by exact widePushoutDesc_point_condition y x g (point_inverse x y f hf g L))

/-- Relative left-inverse homotopies of chosen-point factor maps descend to the
wide pushouts. Inverse point preservation is derived from the supplied data. -/
def widePushoutPointCompHomotopy :
    ContinuousMap.HomotopyRel ((G).comp (F)) (ContinuousMap.id WX) {hx} := by
  have hGF : (G) ((F) hx) = hx := by
    exact (congrArg (fun z : WY ↦ (G) z)
      (widePushoutDesc_point_head x y f hf PUnit.unit)).trans
      (widePushoutDesc_point_head y x g (by exact point_inverse x y f hf g L) PUnit.unit)
  refine widePushoutPointHomotopyRel x hGF (fun j ↦ ?_)
  exact ContinuousMap.HomotopyRel.cast
    ((L j).compContinuousMap (WidePushout.ι aX j).hom)
    (by ext z; simp [ContinuousMap.comp_apply])
    (by ext z; rfl)

/-- The selected left-inverse homotopy fixes the common head at all times. -/
@[simp] theorem widePushoutPointCompHomotopy_head (t : unitInterval) :
    widePushoutPointCompHomotopy x y f hf g L (t, hx) = hx := by
  exact ((widePushoutPointCompHomotopy x y f hf g L).eq_snd t (x := hx)
    (by simp)).trans (ContinuousMap.id_apply hx)

/-- The selected left-inverse homotopy restricts to the supplied factor homotopy. -/
@[simp] theorem widePushoutPointCompHomotopy_ι (j : J) (t : unitInterval) (z : X j) :
    widePushoutPointCompHomotopy x y f hf g L (t, WidePushout.ι aX j z) =
      WidePushout.ι aX j (L j (t, z)) := by
  exact (widePushoutPointHomotopyRel_ι x
    ((widePushoutPointCompHomotopy x y f hf g L).fst_eq_snd (x := hx) (by simp))
    _ j t z).trans (by rfl)

/-- Point-preserving factor maps with supplied point-relative inverse homotopies
induce an ordinary homotopy equivalence of their wide pushouts. The chosen
relative witnesses are supplied separately by `widePushoutPointCompHomotopy`. -/
def widePushoutPointHomotopyEquiv
    (R : ∀ j, ContinuousMap.HomotopyRel ((f j).comp (g j))
      (ContinuousMap.id (Y j)) {y j}) : ContinuousMap.HomotopyEquiv WX WY where
  toFun := F
  invFun := G
  left_inv := ⟨(widePushoutPointCompHomotopy x y f hf g L).toHomotopy⟩
  right_inv := by
    exact ⟨(widePushoutPointCompHomotopy y x g
      (point_inverse x y f hf g L) f R).toHomotopy⟩

variable (R : ∀ j, ContinuousMap.HomotopyRel ((f j).comp (g j))
  (ContinuousMap.id (Y j)) {y j})

/-- The induced equivalence preserves the common head. -/
@[simp] theorem widePushoutPointHomotopyEquiv_head :
    widePushoutPointHomotopyEquiv x y f hf g L R hx = hy := by
  change (F) hx = hy
  exact widePushoutDesc_point_head x y f hf PUnit.unit

/-- The inverse equivalence preserves the common head. -/
@[simp] theorem widePushoutPointHomotopyEquiv_symm_head :
    (widePushoutPointHomotopyEquiv x y f hf g L R).symm hy = hx := by
  change (G) hy = hx
  exact widePushoutDesc_point_head y x g (point_inverse x y f hf g L) PUnit.unit

/-- The equivalence restricts to the prescribed map on each factor. -/
@[simp] theorem widePushoutPointHomotopyEquiv_ι (j : J) (z : X j) :
    widePushoutPointHomotopyEquiv x y f hf g L R (WidePushout.ι aX j z) =
      WidePushout.ι aY j (f j z) := by
  simp [widePushoutPointHomotopyEquiv]

/-- The inverse equivalence restricts to the prescribed inverse factor map. -/
@[simp] theorem widePushoutPointHomotopyEquiv_symm_ι (j : J) (z : Y j) :
    (widePushoutPointHomotopyEquiv x y f hf g L R).symm (WidePushout.ι aY j z) =
      WidePushout.ι aX j (g j z) := by
  simp [widePushoutPointHomotopyEquiv, ContinuousMap.HomotopyEquiv.symm]

end InverseHomotopy

section Contraction

/-- Supplied contractions fixing the chosen points give a contraction of their
wide pushout fixing the common head. Ordinary contractibility alone does not
provide contractions fixing the specified points. -/
def widePushoutPointContraction
    (K : ∀ j, ContinuousMap.HomotopyRel (ContinuousMap.id (X j))
      (ContinuousMap.const (X j) (x j)) {x j}) :
    ContinuousMap.HomotopyRel (ContinuousMap.id WX) (ContinuousMap.const WX hx) {hx} := by
  refine widePushoutPointHomotopyRel x rfl (fun j ↦ ?_)
  exact ContinuousMap.HomotopyRel.cast
    ((K j).compContinuousMap (WidePushout.ι aX j).hom)
    (by ext z; rfl)
    (by ext z; exact widePushoutPoint_ι_basepoint x j)

variable (K : ∀ j, ContinuousMap.HomotopyRel (ContinuousMap.id (X j))
  (ContinuousMap.const (X j) (x j)) {x j})

/-- The chosen contraction fixes the common head at every time. -/
@[simp] theorem widePushoutPointContraction_head (t : unitInterval) :
    widePushoutPointContraction x K (t, hx) = hx := by
  exact ((widePushoutPointContraction x K).eq_snd t (x := hx)
    (by simp)).trans (ContinuousMap.const_apply hx hx)

/-- The chosen contraction restricts to the supplied contraction on each factor. -/
@[simp] theorem widePushoutPointContraction_ι (j : J) (t : unitInterval) (z : X j) :
    widePushoutPointContraction x K (t, WidePushout.ι aX j z) =
      WidePushout.ι aX j (K j (t, z)) := by
  exact (widePushoutPointHomotopyRel_ι x
    (f := ContinuousMap.id WX) (g := ContinuousMap.const WX hx) rfl _ j t z).trans (by rfl)

include K in
/-- A wide pushout is contractible when supplied with contractions of its factors
fixing their chosen attaching points. This also includes an empty index family. -/
theorem contractibleSpace_widePushout_point_of_contractions : ContractibleSpace WX :=
  (contractible_iff_id_nullhomotopic WX).mpr
    ⟨hx, ⟨(widePushoutPointContraction x K).toHomotopy⟩⟩

end Contraction

end TopCat
