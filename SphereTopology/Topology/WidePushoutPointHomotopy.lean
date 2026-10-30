/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushoutHomotopy
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Point-relative homotopies of wide pushouts

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
  p. 19, for point wedges and the distinction from ordinary contractibility.
* `SphereTopology.Topology.WidePushoutHomotopy` supplies homotopy descent.
* Mathlib supplies relative homotopies and homotopy equivalences.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

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

/-- A factor inclusion sends its chosen point to the common head. -/
@[simp] theorem widePushoutPoint_ι_basepoint (j : J) : WidePushout.ι aX j (x j) = hx := by
  calc
    _ = WidePushout.ι aX j (aX j PUnit.unit) :=
      (congrArg (fun z : X j ↦ WidePushout.ι aX j z)
        (TopCat.const_apply (X := TopCat.of PUnit.{max u w + 1}) (x j) PUnit.unit)).symm
    _ = (aX j ≫ WidePushout.ι aX j) PUnit.unit :=
      (TopCat.comp_app (aX j) (WidePushout.ι aX j) PUnit.unit).symm
    _ = hx := congrArg
      (fun k : TopCat.of PUnit.{max u w + 1} ⟶ WX ↦ k PUnit.unit)
      (WidePushout.arrow_ι aX j)

private theorem pointDesc_condition (f : ∀ j, C(X j, Y j))
    (hf : ∀ j, f j (x j) = y j) (j : J) (b : PUnit.{max u w + 1}) :
    ((WidePushout.ι aY j).hom.comp (f j)) (aX j b) =
      (ContinuousMap.const _ hy) b := by
  change WidePushout.ι aY j (f j (x j)) = hy
  rw [hf j]
  exact widePushoutPoint_ι_basepoint y j

/-- Descent of point-preserving factor maps sends the common head to the common head. -/
@[simp] theorem widePushoutPointDesc_head (f : ∀ j, C(X j, Y j))
    (hf : ∀ j, f j (x j) = y j) :
    widePushoutDesc aX (ContinuousMap.const _ hy)
      (fun j ↦ (WidePushout.ι aY j).hom.comp (f j))
      (by exact pointDesc_condition x y f hf) hx = hy := by
  exact (widePushoutDesc_head aX (ContinuousMap.const _ hy)
    (fun j ↦ (WidePushout.ι aY j).hom.comp (f j))
    (pointDesc_condition x y f hf) PUnit.unit).trans
      (ContinuousMap.const_apply (α := PUnit.{max u w + 1}) hy PUnit.unit)

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
  (fun j ↦ (WidePushout.ι aY j).hom.comp (f j)) (by exact pointDesc_condition x y f hf)
set_option quotPrecheck false in
local notation "G" => widePushoutDesc aY (ContinuousMap.const _ hx)
  (fun j ↦ (WidePushout.ι aX j).hom.comp (g j))
  (by exact pointDesc_condition y x g (point_inverse x y f hf g L))

/-- Relative left-inverse homotopies of chosen-point factor maps descend to the
wide pushouts. Inverse point preservation is derived from the supplied data. -/
def widePushoutPointCompHomotopy :
    ContinuousMap.HomotopyRel ((G).comp (F)) (ContinuousMap.id WX) {hx} := by
  have hGF : (G) ((F) hx) = hx := by
    exact (congrArg (fun z : WY ↦ (G) z) (widePushoutPointDesc_head x y f hf)).trans
      (widePushoutPointDesc_head y x g (by exact point_inverse x y f hf g L))
  let HB : ContinuousMap.Homotopy (((G).comp (F)).comp (WidePushout.head aX).hom)
      ((ContinuousMap.id WX).comp (WidePushout.head aX).hom) :=
    (ContinuousMap.Homotopy.refl (ContinuousMap.const _ hx)).cast
      (by
        ext b
        cases b
        change hx = (G) ((F) hx)
        exact hGF.symm)
      (by ext b; cases b; rfl)
  let HX : ∀ j, ContinuousMap.Homotopy (((G).comp (F)).comp (WidePushout.ι aX j).hom)
      ((ContinuousMap.id WX).comp (WidePushout.ι aX j).hom) := fun j ↦
    ((ContinuousMap.Homotopy.refl (WidePushout.ι aX j).hom).comp
      (L j).toHomotopy).cast
      (by ext z; simp [ContinuousMap.comp_apply])
      (by ext z; rfl)
  have h : ∀ j t b, HX j (t, aX j b) = HB (t, b) := by
    intro j t b
    change WidePushout.ι aX j (L j (t, x j)) = hx
    rw [(L j).eq_snd t (x := x j) (by simp)]
    exact widePushoutPoint_ι_basepoint x j
  refine { toHomotopy := widePushoutHomotopy aX HB HX h, prop' := ?_ }
  intro t z hz
  have hz : z = hx := Set.mem_singleton_iff.mp hz
  subst z
  change widePushoutHomotopy aX HB HX h (t, hx) = (G) ((F) hx)
  calc
    _ = HB (t, PUnit.unit) :=
      widePushoutHomotopy_head (a₀ := (G).comp (F)) (a₁ := ContinuousMap.id WX)
        aX HB HX h t PUnit.unit
    _ = _ := by
      change hx = (G) ((F) hx)
      exact hGF.symm

/-- The selected left-inverse homotopy fixes the common head at all times. -/
@[simp] theorem widePushoutPointCompHomotopy_head (t : unitInterval) :
    widePushoutPointCompHomotopy x y f hf g L (t, hx) = hx := by
  exact ((widePushoutPointCompHomotopy x y f hf g L).eq_snd t (x := hx)
    (by simp)).trans (ContinuousMap.id_apply hx)

/-- The selected left-inverse homotopy restricts to the supplied factor homotopy. -/
@[simp] theorem widePushoutPointCompHomotopy_ι (j : J) (t : unitInterval) (z : X j) :
    widePushoutPointCompHomotopy x y f hf g L (t, WidePushout.ι aX j z) =
      WidePushout.ι aX j (L j (t, z)) := by
  change (widePushoutPointCompHomotopy x y f hf g L).toHomotopy
    (t, WidePushout.ι aX j z) = _
  dsimp only [widePushoutPointCompHomotopy]
  rw [widePushoutHomotopy_ι]
  rfl

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
  exact widePushoutPointDesc_head x y f hf

/-- The inverse equivalence preserves the common head. -/
@[simp] theorem widePushoutPointHomotopyEquiv_symm_head :
    (widePushoutPointHomotopyEquiv x y f hf g L R).symm hy = hx := by
  change (G) hy = hx
  exact widePushoutPointDesc_head y x g (point_inverse x y f hf g L)

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
  let HB : ContinuousMap.Homotopy ((ContinuousMap.id WX).comp (WidePushout.head aX).hom)
      ((ContinuousMap.const WX hx).comp (WidePushout.head aX).hom) :=
    (ContinuousMap.Homotopy.refl (ContinuousMap.const _ hx)).cast
      (by ext b; cases b; rfl) (by ext b; rfl)
  let HX : ∀ j, ContinuousMap.Homotopy ((ContinuousMap.id WX).comp (WidePushout.ι aX j).hom)
      ((ContinuousMap.const WX hx).comp (WidePushout.ι aX j).hom) := fun j ↦
    ((ContinuousMap.Homotopy.refl (WidePushout.ι aX j).hom).comp
      (K j).toHomotopy).cast
      (by ext z; rfl) (by ext z; exact widePushoutPoint_ι_basepoint x j)
  have h : ∀ j t b, HX j (t, aX j b) = HB (t, b) := by
    intro j t b
    change WidePushout.ι aX j (K j (t, x j)) = hx
    rw [(K j).eq_snd t (x := x j) (by simp)]
    exact widePushoutPoint_ι_basepoint x j
  refine { toHomotopy := widePushoutHomotopy aX HB HX h, prop' := ?_ }
  intro t z hz
  have hz : z = hx := Set.mem_singleton_iff.mp hz
  subst z
  change widePushoutHomotopy aX HB HX h (t, hx) = hx
  calc
    _ = HB (t, PUnit.unit) :=
      widePushoutHomotopy_head (a₀ := ContinuousMap.id WX)
        (a₁ := ContinuousMap.const WX hx) aX HB HX h t PUnit.unit
    _ = hx := rfl

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
  change (widePushoutPointContraction x K).toHomotopy (t, WidePushout.ι aX j z) = _
  dsimp only [widePushoutPointContraction]
  rw [widePushoutHomotopy_ι]
  rfl

include K in
/-- A wide pushout is contractible when supplied with contractions of its factors
fixing their chosen attaching points. This also includes an empty index family. -/
theorem contractibleSpace_widePushout_point_of_contractions : ContractibleSpace WX :=
  (contractible_iff_id_nullhomotopic WX).mpr
    ⟨hx, ⟨(widePushoutPointContraction x K).toHomotopy⟩⟩

end Contraction

end TopCat
