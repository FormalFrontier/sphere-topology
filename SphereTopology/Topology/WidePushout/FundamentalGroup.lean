/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.Chart
import SphereTopology.Topology.WidePushout.SubsetRetraction
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover
public import Mathlib.GroupTheory.CoprodI

/-!
# Fundamental groups of point-attached wide pushouts

An open neighborhood `C` of the common point gives the existing charts
`widePushoutPointChart a C i`, each consisting of one whole factor together
with `C`. This module regards these sets as open neighborhoods and applies
the common-overlap theorem from Fundamental Groupoids. If `C` and every
whole factor are path connected, compatible homomorphisms on `C` and these
charts descend uniquely to the fundamental group of the pushout.

The compatibility and characteristic equations use the inclusion maps from
`FundamentalGroup.openNhdsFunctor` and `FundamentalGroup.openNhdsCocone`.
There is no choice of basepoint transport in these maps. The index type may
be empty and different indices may give the same chart. The target group
has an independent universe. No separation, local path connectedness or
contractibility hypothesis is imposed on this chart universal property.

The canonical homomorphism from the coproduct of the factor fundamental groups
is induced by the original-domain factor inclusions. If each inclusion of a
factor preimage of the open core into its factor induces the trivial
fundamental-group homomorphism, the chart retractions give a homomorphism back
to the coproduct that is a left inverse to the canonical homomorphism. This
requires path connectedness of the core and whole factors, but neither simple
connectivity of the core nor a homotopy equivalence between a chart and its
factor. No surjectivity of the canonical homomorphism is asserted.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §§7–8,
  supplies the common-overlap fundamental-group theorem and the point-wedge
  setting. The arbitrary-open-core formulation here is a generalization,
  not a free-product computation.
* Fundamental Groupoids supplies the common-overlap universal property and
  inclusion functor and cocone.
* Mathlib supplies open neighborhoods, topological wide pushouts, fundamental
  groups and indexed monoid coproducts. The chart geometry and restricted
  retractions are supplied by this library's `SphereTopology.Topology.WidePushout.Chart`
  and `SphereTopology.Topology.WidePushout.SubsetRetraction`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u v z

namespace TopCat

variable {I : Type v} {X : I → TopCat.{max u v}} (a : ∀ i, X i)

local notation "P" => TopCat.of PUnit
local notation "f" => (fun i ↦ (TopCat.const (a i) : P ⟶ X i))
local notation "W" => (widePushout P X f : TopCat)
local notation "w" => WidePushout.head f PUnit.unit

/-- The existing factor-plus-core chart, regarded as an open neighborhood of
 the common point. -/
def widePushoutPointChartNhds (C : OpenNhds (X := W) w) (i : I) :
    OpenNhds (X := W) w :=
  ⟨⟨widePushoutPointChart a (C.1 : Set W) i,
    isOpen_widePushoutPointChart a C.2 C.1.isOpen i⟩,
    head_mem_widePushoutPointChart a (C.1 : Set W) i⟩

/-- Bundling the chart as a neighborhood does not change its underlying set. -/
@[simp] theorem coe_widePushoutPointChartNhds (C : OpenNhds (X := W) w) (i : I) :
    ((widePushoutPointChartNhds a C i).1 : Set W) =
      widePushoutPointChart a (C.1 : Set W) i := rfl

/-- Membership in a bundled chart is membership in its factor or in the core. -/
theorem mem_widePushoutPointChartNhds (C : OpenNhds (X := W) w) (i : I) (x : W) :
    x ∈ (widePushoutPointChartNhds a C i).1 ↔
      (∃ y : X i, WidePushout.ι f i y = x) ∨ x ∈ C.1 :=
  mem_widePushoutPointChart a (C.1 : Set W) i x

/-- The core includes into every bundled chart. -/
theorem le_widePushoutPointChartNhds (C : OpenNhds (X := W) w) (i : I) :
    C ≤ widePushoutPointChartNhds a C i :=
  subset_widePushoutPointChart a (C.1 : Set W) i

/-- Distinct chart indices have exactly the core as their infimum. -/
theorem widePushoutPointChartNhds_inf_of_ne (C : OpenNhds (X := W) w)
    (i j : I) (hij : i ≠ j) :
    widePushoutPointChartNhds a C i ⊓ widePushoutPointChartNhds a C j = C := by
  apply Subtype.ext
  apply SetLike.coe_injective
  exact widePushoutPointChart_inter_of_ne a C.2 hij

/-- The core and all charts form an open cover, including for an empty family. -/
theorem isOpenCover_widePushoutPointChartNhds (C : OpenNhds (X := W) w) :
    IsOpenCover (fun o : Option I => (o.elim C (widePushoutPointChartNhds a C)).1) := by
  have hsets : (⋃ o : Option I,
      ((o.elim C (widePushoutPointChartNhds a C)).1 : Set W)) = univ := by
    convert iUnion_widePushoutPointChart a C.2 using 1
    apply congrArg iUnion
    funext o
    cases o <;> rfl
  rw [IsOpenCover, ← SetLike.coe_set_eq, Opens.coe_iSup, Opens.coe_top]
  exact hsets

/-- A bundled chart is path connected when its core and its own factor are.
No path-connectedness assumption on any other whole factor is needed. -/
theorem isPathConnected_widePushoutPointChartNhds (C : OpenNhds (X := W) w)
    (hC : IsPathConnected (C.1 : Set W)) (i : I)
    (hi : IsPathConnected (univ : Set (X i))) :
    IsPathConnected ((widePushoutPointChartNhds a C i).1 : Set W) :=
  isPathConnected_widePushoutPointChart a C.2 hC i hi

/-- Core-compatible chart homomorphisms descend uniquely to the fundamental
 group of the point-wide-pushout. All maps in the equations are induced by
 subspace inclusions. This applies May's common-overlap theorem, Chapter 2, §7,
 using the point-chart geometry of Chapter 2, §8. -/
theorem existsUnique_widePushoutPointChart_hom (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i)))
    (G : Type z) [Group G]
    (hC : FundamentalGroup C.1 ⟨w, C.2⟩ →* G)
    (hU : ∀ i, FundamentalGroup (widePushoutPointChartNhds a C i).1
      ⟨w, (widePushoutPointChartNhds a C i).2⟩ →* G)
    (hcomp : ∀ i, (hU i).comp
      (((FundamentalGroup.openNhdsFunctor w).map
        (homOfLE (le_widePushoutPointChartNhds a C i))).hom) = hC) :
    ∃! h : FundamentalGroup W w →* G,
      h.comp (((FundamentalGroup.openNhdsCocone w).ι.app C).hom) = hC ∧
        ∀ i, h.comp (((FundamentalGroup.openNhdsCocone w).ι.app
          (widePushoutPointChartNhds a C i)).hom) = hU i :=
  FundamentalGroup.existsUnique_hom_of_isOpenCover_of_commonOverlap w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)
    (widePushoutPointChartNhds_inf_of_ne a C)
    (isOpenCover_widePushoutPointChartNhds a C) hpcC
    (fun i => isPathConnected_widePushoutPointChartNhds a C hpcC i (hpcX i))
    G hC hU hcomp

/-- Homomorphisms from the pushout fundamental group are determined by their
 restrictions to the core and the charts, including for an empty index type. -/
theorem widePushoutPointChart_hom_ext (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i)))
    {G : Type z} [Group G] {h k : FundamentalGroup W w →* G}
    (hC : h.comp (((FundamentalGroup.openNhdsCocone w).ι.app C).hom) =
      k.comp (((FundamentalGroup.openNhdsCocone w).ι.app C).hom))
    (hU : ∀ i, h.comp (((FundamentalGroup.openNhdsCocone w).ι.app
        (widePushoutPointChartNhds a C i)).hom) =
      k.comp (((FundamentalGroup.openNhdsCocone w).ι.app
        (widePushoutPointChartNhds a C i)).hom)) : h = k :=
  FundamentalGroup.hom_ext_of_isOpenCover_of_commonOverlap w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)
    (widePushoutPointChartNhds_inf_of_ne a C)
    (isOpenCover_widePushoutPointChartNhds a C) hpcC
    (fun i => isPathConnected_widePushoutPointChartNhds a C hpcC i (hpcX i)) hC hU

/-- The homomorphism obtained by gluing a core-compatible family on the charts.
Its core and chart restrictions characterize it uniquely. -/
def widePushoutPointChartFundamentalGroupDesc (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i)))
    (G : Type z) [Group G]
    (hC : FundamentalGroup C.1 ⟨w, C.2⟩ →* G)
    (hU : ∀ i, FundamentalGroup (widePushoutPointChartNhds a C i).1
      ⟨w, (widePushoutPointChartNhds a C i).2⟩ →* G)
    (hcomp : ∀ i, (hU i).comp
      (((FundamentalGroup.openNhdsFunctor w).map
        (homOfLE (le_widePushoutPointChartNhds a C i))).hom) = hC) :
    FundamentalGroup W w →* G :=
  Classical.choose (existsUnique_widePushoutPointChart_hom a C hpcC hpcX G hC hU hcomp).exists

/-- Restricting the descended homomorphism to the core recovers its input. -/
@[simp] theorem widePushoutPointChartFundamentalGroupDesc_comp_core (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i)))
    (G : Type z) [Group G]
    (hC : FundamentalGroup C.1 ⟨w, C.2⟩ →* G)
    (hU : ∀ i, FundamentalGroup (widePushoutPointChartNhds a C i).1
      ⟨w, (widePushoutPointChartNhds a C i).2⟩ →* G)
    (hcomp : ∀ i, (hU i).comp
      (((FundamentalGroup.openNhdsFunctor w).map
        (homOfLE (le_widePushoutPointChartNhds a C i))).hom) = hC) :
    (widePushoutPointChartFundamentalGroupDesc a C hpcC hpcX G hC hU hcomp).comp
      (((FundamentalGroup.openNhdsCocone w).ι.app C).hom) = hC :=
  (Classical.choose_spec
    (existsUnique_widePushoutPointChart_hom a C hpcC hpcX G hC hU hcomp).exists).1

/-- Restricting the descended homomorphism to a chart recovers its input. -/
@[simp] theorem widePushoutPointChartFundamentalGroupDesc_comp_chart (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i)))
    (G : Type z) [Group G]
    (hC : FundamentalGroup C.1 ⟨w, C.2⟩ →* G)
    (hU : ∀ i, FundamentalGroup (widePushoutPointChartNhds a C i).1
      ⟨w, (widePushoutPointChartNhds a C i).2⟩ →* G)
    (hcomp : ∀ i, (hU i).comp
      (((FundamentalGroup.openNhdsFunctor w).map
        (homOfLE (le_widePushoutPointChartNhds a C i))).hom) = hC)
    (i : I) :
    (widePushoutPointChartFundamentalGroupDesc a C hpcC hpcX G hC hU hcomp).comp
      (((FundamentalGroup.openNhdsCocone w).ι.app
        (widePushoutPointChartNhds a C i)).hom) = hU i :=
  (Classical.choose_spec
    (existsUnique_widePushoutPointChart_hom a C hpcC hpcX G hC hU hcomp).exists).2 i

/-- Any homomorphism with the specified core and chart restrictions is the
 descended homomorphism. Users need not unfold its chosen construction. -/
theorem eq_widePushoutPointChartFundamentalGroupDesc (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i)))
    (G : Type z) [Group G]
    (hC : FundamentalGroup C.1 ⟨w, C.2⟩ →* G)
    (hU : ∀ i, FundamentalGroup (widePushoutPointChartNhds a C i).1
      ⟨w, (widePushoutPointChartNhds a C i).2⟩ →* G)
    (hcomp : ∀ i, (hU i).comp
      (((FundamentalGroup.openNhdsFunctor w).map
        (homOfLE (le_widePushoutPointChartNhds a C i))).hom) = hC)
    (h : FundamentalGroup W w →* G)
    (hhC : h.comp (((FundamentalGroup.openNhdsCocone w).ι.app C).hom) = hC)
    (hhU : ∀ i, h.comp (((FundamentalGroup.openNhdsCocone w).ι.app
      (widePushoutPointChartNhds a C i)).hom) = hU i) :
    h = widePushoutPointChartFundamentalGroupDesc a C hpcC hpcX G hC hU hcomp := by
  apply widePushoutPointChart_hom_ext a C hpcC hpcX
  · exact hhC.trans
      (widePushoutPointChartFundamentalGroupDesc_comp_core a C hpcC hpcX G hC hU hcomp).symm
  · intro i
    exact (hhU i).trans
      (widePushoutPointChartFundamentalGroupDesc_comp_chart a C hpcC hpcX G hC hU hcomp i).symm

section OriginalFactors

variable {X₀ : I → TopCat.{u}} (a₀ : ∀ i, X₀ i)

-- Keep the canonical lift in each declaration's let telescope, as in PointLift.
-- This avoids universe-bearing notation quotations and private names in public types.

/-- The homomorphism from the coproduct of the factor fundamental groups induced
by the original-domain inclusions into the point-attached wide pushout.
The factors are canonically lifted by the index universe, without a smallness premise. -/
def widePushoutPointFundamentalGroupCoproductMap :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    Monoid.CoprodI (fun i ↦ FundamentalGroup (X₀ i) (a₀ i)) →*
      FundamentalGroup WL wL := by
  let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
  let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
  let aL := fun i ↦ eL i (a₀ i)
  let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
  exact Monoid.CoprodI.lift (fun i ↦ FundamentalGroup.mapOfEq
    ((WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i)))
    (widePushout_point_ι_point aL i))

/-- The coproduct homomorphism restricts to the inclusion-induced homomorphism
on every original factor. -/
@[simp] theorem widePushoutPointFundamentalGroupCoproductMap_comp_of (i : I) :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    (widePushoutPointFundamentalGroupCoproductMap a₀).comp
      (Monoid.CoprodI.of (i := i)) =
        FundamentalGroup.mapOfEq
          ((WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i)))
          (widePushout_point_ι_point aL i) := by
  exact Monoid.CoprodI.lift_comp_of _ i

-- The bundled basepoints and their images agree definitionally.
set_option backward.isDefEq.respectTransparency false in
/-- The factor chart retraction induces a homomorphism trivial on the core when
inclusion of the core's factor preimage has trivial fundamental-group image.
The factor may be presented by a homeomorphic space in an independent universe;
no connectedness of the preimage is required. -/
theorem widePushoutPointChartRetraction_comp_core_eq_one
    {Y : I → TopCat.{z}} (b : ∀ i, Y i)
    (e : ∀ i, Y i ≃ₜ X i) (he : ∀ i, e i (b i) = a i)
    (C : OpenNhds (X := W) w) (i : I)
    (hnull :
      (FundamentalGroup.map
        (ContinuousMap.subtypeVal
          (((WidePushout.ι f i).hom.comp (e i : C(Y i, X i))) ⁻¹' (C.1 : Set W)))
        ⟨b i, by
          change WidePushout.ι f i (e i (b i)) ∈ C.1
          rw [he i, widePushout_point_ι_point a i]
          exact C.2⟩).range = ⊥) :
    (FundamentalGroup.mapOfEq
      (x := (⟨w, (widePushoutPointChartNhds a C i).2⟩ :
        (widePushoutPointChartNhds a C i).1))
      (y := b i)
      ((((e i).symm : C(X i, Y i)).comp
        (widePushoutPointRetraction X a i).hom).comp
          (ContinuousMap.subtypeVal ((widePushoutPointChartNhds a C i).1 : Set W)))
      (by
        change (e i).symm (widePushoutPointRetraction X a i w) = b i
        rw [widePushoutPointRetraction_head_apply, ← he i]
        exact (e i).symm_apply_apply (b i))).comp
      (((FundamentalGroup.openNhdsFunctor w).map
        (homOfLE (le_widePushoutPointChartNhds a C i))).hom) = 1 := by
  let V : Set (Y i) :=
    ((WidePushout.ι f i).hom.comp (e i : C(Y i, X i))) ⁻¹' (C.1 : Set W)
  let x₀ : V := ⟨b i, by
    change WidePushout.ι f i (e i (b i)) ∈ C.1
    rw [he i, widePushout_point_ι_point a i]
    exact C.2⟩
  let c₀ : C.1 := ⟨w, C.2⟩
  let U := widePushoutPointChartNhds a C i
  let u₀ : U.1 := ⟨w, U.2⟩
  let R : C(W, Y i) :=
    ((e i).symm : C(X i, Y i)).comp (widePushoutPointRetraction X a i).hom
  have hR : R w = b i := by
    change (e i).symm (widePushoutPointRetraction X a i w) = b i
    rw [widePushoutPointRetraction_head_apply, ← he i]
    exact (e i).symm_apply_apply (b i)
  have hmaps : MapsTo R (C.1 : Set W) V := by
    intro z hz
    change WidePushout.ι f i (e i ((e i).symm
      (widePushoutPointRetraction X a i z))) ∈ C.1
    rw [Homeomorph.apply_symm_apply]
    exact mapsTo_widePushoutPointRetraction_preimage a C.2 i hz
  let d : C(C.1, V) :=
    ⟨fun z ↦ ⟨R z, hmaps z.property⟩,
      (R.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hd : d c₀ = x₀ := by
    apply Subtype.ext
    exact hR
  let r : C(U.1, Y i) := R.comp (ContinuousMap.subtypeVal (U.1 : Set W))
  have hr : r u₀ = b i := hR
  let j : C(C.1, U.1) := ContinuousMap.inclusion (le_widePushoutPointChartNhds a C i)
  have hfactor : r.comp j = (ContinuousMap.subtypeVal V).comp d := rfl
  have hj : FundamentalGroup.mapOfEq (x := c₀) (y := u₀) j
      (rfl : j c₀ = u₀) = FundamentalGroup.map j c₀ :=
    FundamentalGroup.mapOfEq_rfl j c₀
  have hval : FundamentalGroup.mapOfEq (x := x₀) (y := b i)
      (ContinuousMap.subtypeVal V) (rfl : ContinuousMap.subtypeVal V x₀ = b i) =
        FundamentalGroup.map (ContinuousMap.subtypeVal V) x₀ :=
    FundamentalGroup.mapOfEq_rfl (ContinuousMap.subtypeVal V) x₀
  have hv : FundamentalGroup.map (ContinuousMap.subtypeVal V) x₀ = 1 :=
    MonoidHom.range_eq_bot_iff.mp hnull
  let q₀ : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i) :=
    (FundamentalGroup.mapOfEq (x := u₀) (y := b i) r hr).comp
      (FundamentalGroup.map j c₀)
  let q₁ : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i) :=
    FundamentalGroup.mapOfEq (x := c₀) (y := b i) (r.comp j)
      (Eq.trans (congrArg r (rfl : j c₀ = u₀)) hr)
  let q₂ : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i) :=
    (FundamentalGroup.map (ContinuousMap.subtypeVal V) x₀).comp
      (FundamentalGroup.mapOfEq (x := c₀) (y := x₀) d hd)
  have h₀₁ : (q₀ : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i)) =
      (q₁ : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i)) := by
    simpa only [q₀, q₁, hj] using
      (FundamentalGroup.mapOfEq_comp r j (x := c₀) (y := u₀) (z := b i)
        (rfl : j c₀ = u₀) hr).symm
  have h₁₂ : (q₁ : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i)) =
      (q₂ : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i)) := by
    simpa only [q₁, q₂, hfactor, hval] using
      (FundamentalGroup.mapOfEq_comp (ContinuousMap.subtypeVal V) d
        (x := c₀) (y := x₀) (z := b i) hd
        (rfl : ContinuousMap.subtypeVal V x₀ = b i))
  have h₂₃ : (q₂ : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i)) =
      (1 : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i)) := by
    exact (congrArg
      (fun q : FundamentalGroup V x₀ →* FundamentalGroup (Y i) (b i) ↦
        q.comp (FundamentalGroup.mapOfEq (x := c₀) (y := x₀) d hd)) hv).trans
      (MonoidHom.one_comp _)
  rw [FundamentalGroup.openNhdsFunctor_map_hom]
  change (q₀ : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i)) =
    (1 : FundamentalGroup C.1 c₀ →* FundamentalGroup (Y i) (b i))
  exact Eq.trans h₀₁ (Eq.trans h₁₂ h₂₃)

/-- The homomorphism from the fundamental group of a point-attached wide pushout
to the coproduct of the factor fundamental groups, obtained from the chart
retractions when each core-preimage inclusion induces the trivial homomorphism.
The core and whole original factors are required to be path connected. -/
def widePushoutPointFundamentalGroupCoproductRetraction :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL),
      IsPathConnected (C.1 : Set WL) →
      (∀ i, IsPathConnected (univ : Set (X₀ i))) →
      (∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥) →
      FundamentalGroup WL wL →*
        Monoid.CoprodI (fun i ↦ FundamentalGroup (X₀ i) (a₀ i)) := by
  dsimp only
  intro C hpcC hpcX hnull
  let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
  let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
  let aL := fun i ↦ eL i (a₀ i)
  let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
  let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
  let wL := WidePushout.head sL PUnit.unit
  have hpcL : ∀ i, IsPathConnected (univ : Set (XL i)) := by
    intro i
    simpa only [preimage_univ] using
      ((eL i).symm.isPathConnected_preimage (s := (univ : Set (X₀ i)))).2 (hpcX i)
  let p : ∀ i, FundamentalGroup (widePushoutPointChartNhds aL C i).1
      ⟨wL, (widePushoutPointChartNhds aL C i).2⟩ →*
        FundamentalGroup (X₀ i) (a₀ i) := fun i ↦
    FundamentalGroup.mapOfEq
      ((((eL i).symm : C(XL i, X₀ i)).comp
        (widePushoutPointRetraction XL aL i).hom).comp
          (ContinuousMap.subtypeVal ((widePushoutPointChartNhds aL C i).1 : Set WL)))
      (by
        change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
        rw [widePushoutPointRetraction_head_apply]
        exact (eL i).symm_apply_apply (a₀ i))
  have hp : ∀ i, (p i).comp
      (((FundamentalGroup.openNhdsFunctor wL).map
        (homOfLE (le_widePushoutPointChartNhds aL C i))).hom) = 1 := by
    intro i
    exact widePushoutPointChartRetraction_comp_core_eq_one
      (a := aL) (b := a₀) eL (fun _ ↦ rfl) C i (hnull i)
  refine widePushoutPointChartFundamentalGroupDesc aL C hpcC hpcL
    (Monoid.CoprodI (fun i ↦ FundamentalGroup (X₀ i) (a₀ i))) 1
    (fun i ↦ (Monoid.CoprodI.of
      (M := fun j ↦ FundamentalGroup (X₀ j) (a₀ j)) (i := i)).comp (p i)) ?_
  intro i
  let k : FundamentalGroup (X₀ i) (a₀ i) →*
      Monoid.CoprodI (fun j ↦ FundamentalGroup (X₀ j) (a₀ j)) :=
    Monoid.CoprodI.of (M := fun j ↦ FundamentalGroup (X₀ j) (a₀ j)) (i := i)
  exact (congrArg
    (fun q : FundamentalGroup C.1 ⟨wL, C.2⟩ →* FundamentalGroup (X₀ i) (a₀ i) ↦
      k.comp q) (hp i)).trans (MonoidHom.comp_one k)

/-- The homomorphism to the coproduct is trivial on the open core. -/
@[simp] theorem widePushoutPointFundamentalGroupCoproductRetraction_comp_core :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL)
      (hpcC : IsPathConnected (C.1 : Set WL))
      (hpcX : ∀ i, IsPathConnected (univ : Set (X₀ i)))
      (hnull : ∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥),
      (widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull).comp
        (((FundamentalGroup.openNhdsCocone wL).ι.app C).hom) = 1 := by
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull
  unfold widePushoutPointFundamentalGroupCoproductRetraction
  apply widePushoutPointChartFundamentalGroupDesc_comp_core
  · exact hpcC
  · intro j
    simpa only [preimage_univ] using
      ((eL j).symm.isPathConnected_preimage (s := (univ : Set (X₀ j)))).2 (hpcX j)
  · intro j
    let k : FundamentalGroup (X₀ j) (a₀ j) →*
        Monoid.CoprodI (fun l ↦ FundamentalGroup (X₀ l) (a₀ l)) :=
      Monoid.CoprodI.of (M := fun l ↦ FundamentalGroup (X₀ l) (a₀ l)) (i := j)
    exact Eq.trans
      (congrArg
        (fun q : FundamentalGroup C.1 ⟨wL, C.2⟩ →*
            FundamentalGroup (X₀ j) (a₀ j) ↦ k.comp q)
        (widePushoutPointChartRetraction_comp_core_eq_one
          (a := aL) (b := a₀) eL (fun _ ↦ rfl) C j (hnull j)))
      (MonoidHom.comp_one k)

/-- On each chart, the homomorphism to the coproduct is the factor retraction
followed by the corresponding coproduct insertion. -/
@[simp] theorem widePushoutPointFundamentalGroupCoproductRetraction_comp_chart :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL)
      (hpcC : IsPathConnected (C.1 : Set WL))
      (hpcX : ∀ i, IsPathConnected (univ : Set (X₀ i)))
      (hnull : ∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥)
      (i : I),
      (widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull).comp
        (((FundamentalGroup.openNhdsCocone wL).ι.app
          (widePushoutPointChartNhds aL C i)).hom) =
        (Monoid.CoprodI.of (i := i)).comp
          (FundamentalGroup.mapOfEq
            ((((eL i).symm : C(XL i, X₀ i)).comp
              (widePushoutPointRetraction XL aL i).hom).comp
                (ContinuousMap.subtypeVal
                  ((widePushoutPointChartNhds aL C i).1 : Set WL)))
            (by
              change (eL i).symm
                (widePushoutPointRetraction XL aL i wL) = a₀ i
              rw [widePushoutPointRetraction_head_apply]
              exact (eL i).symm_apply_apply (a₀ i))) := by
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull i
  unfold widePushoutPointFundamentalGroupCoproductRetraction
  apply widePushoutPointChartFundamentalGroupDesc_comp_chart
  · exact hpcC
  · intro j
    simpa only [preimage_univ] using
      ((eL j).symm.isPathConnected_preimage (s := (univ : Set (X₀ j)))).2 (hpcX j)
  · intro j
    let k : FundamentalGroup (X₀ j) (a₀ j) →*
        Monoid.CoprodI (fun l ↦ FundamentalGroup (X₀ l) (a₀ l)) :=
      Monoid.CoprodI.of (M := fun l ↦ FundamentalGroup (X₀ l) (a₀ l)) (i := j)
    exact Eq.trans
      (congrArg
        (fun q : FundamentalGroup C.1 ⟨wL, C.2⟩ →*
            FundamentalGroup (X₀ j) (a₀ j) ↦ k.comp q)
        (widePushoutPointChartRetraction_comp_core_eq_one
          (a := aL) (b := a₀) eL (fun _ ↦ rfl) C j (hnull j)))
      (MonoidHom.comp_one k)

-- Dependent based-map simplifications need the unifier transparency used in
-- FundamentalGroup.retractionOfHomotopy_comp_map.
set_option backward.isDefEq.respectTransparency false in
/-- Restricting the homomorphism to the coproduct along an original factor
inclusion gives the corresponding coproduct insertion. -/
@[simp] theorem widePushoutPointFundamentalGroupCoproductRetraction_comp_inclusion :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL)
      (hpcC : IsPathConnected (C.1 : Set WL))
      (hpcX : ∀ i, IsPathConnected (univ : Set (X₀ i)))
      (hnull : ∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥)
      (i : I),
      (widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull).comp
        (FundamentalGroup.mapOfEq (ιL i) (widePushout_point_ι_point aL i)) =
          Monoid.CoprodI.of
            (M := fun j ↦ FundamentalGroup (X₀ j) (a₀ j)) (i := i) := by
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull i
  let U := widePushoutPointChartNhds aL C i
  -- The factor inclusion lands in its own chart, before passing to π₁.
  let k : C(X₀ i, U.1) :=
    ⟨fun x ↦ ⟨ιL i x, ι_mem_widePushoutPointChart aL (C.1 : Set WL) i (eL i x)⟩,
      (ιL i).continuous.subtype_mk _⟩
  have hk : k (a₀ i) = (⟨wL, U.2⟩ : U.1) := by
    apply Subtype.ext
    exact widePushout_point_ι_point aL i
  have hinc : (ContinuousMap.subtypeVal (U.1 : Set WL)).comp k = ιL i := rfl
  let j : FundamentalGroup U.1 ⟨wL, U.2⟩ →* FundamentalGroup WL wL :=
    FundamentalGroup.map (ContinuousMap.subtypeVal (U.1 : Set WL)) ⟨wL, U.2⟩
  have hι : j.comp (FundamentalGroup.mapOfEq k hk) =
      FundamentalGroup.mapOfEq (ιL i) (widePushout_point_ι_point aL i) := by
    simpa only [j, FundamentalGroup.mapOfEq_rfl, hinc] using
      (FundamentalGroup.mapOfEq_comp
        (ContinuousMap.subtypeVal (U.1 : Set WL)) k
        (x := a₀ i) (y := (⟨wL, U.2⟩ : U.1)) (z := wL) hk rfl).symm
  let r : C(U.1, X₀ i) :=
    (((eL i).symm : C(XL i, X₀ i)).comp
      (widePushoutPointRetraction XL aL i).hom).comp
        (ContinuousMap.subtypeVal (U.1 : Set WL))
  have hr : r ⟨wL, U.2⟩ = a₀ i := by
    change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
    rw [widePushoutPointRetraction_head_apply]
    exact (eL i).symm_apply_apply (a₀ i)
  have hrk : r.comp k = ContinuousMap.id (X₀ i) := by
    apply ContinuousMap.ext
    intro x
    change (eL i).symm
      (widePushoutPointRetraction XL aL i (WidePushout.ι sL i (eL i x))) = x
    rw [widePushoutPointRetraction_ι_apply]
    exact (eL i).symm_apply_apply x
  have hpk : (FundamentalGroup.mapOfEq r hr).comp
      (FundamentalGroup.mapOfEq k hk) = MonoidHom.id (FundamentalGroup (X₀ i) (a₀ i)) := by
    calc
      _ = (FundamentalGroup.mapOfEq (x := a₀ i) (y := a₀ i)
          (r.comp k) ((congrArg r hk).trans hr) :
            FundamentalGroup (X₀ i) (a₀ i) →* FundamentalGroup (X₀ i) (a₀ i)) :=
        (FundamentalGroup.mapOfEq_comp r k hk hr).symm
      _ = _ := by
        simpa only [hrk, ContinuousMap.id_apply] using
          FundamentalGroup.mapOfEq_id (a₀ i)
  let ρ : FundamentalGroup WL wL →*
      Monoid.CoprodI (fun j ↦ FundamentalGroup (X₀ j) (a₀ j)) :=
    widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull
  let o : FundamentalGroup (X₀ i) (a₀ i) →*
      Monoid.CoprodI (fun j ↦ FundamentalGroup (X₀ j) (a₀ j)) :=
    Monoid.CoprodI.of (M := fun j ↦ FundamentalGroup (X₀ j) (a₀ j)) (i := i)
  have hchart : ρ.comp j = o.comp (FundamentalGroup.mapOfEq r hr) := by
    simpa only [ρ, j, o, r, U, XL, eL, aL, sL, WL, wL,
      FundamentalGroup.openNhdsCocone_ι_app_hom] using
      (widePushoutPointFundamentalGroupCoproductRetraction_comp_chart
        a₀ C hpcC hpcX hnull i)
  calc
    _ = (ρ.comp j).comp (FundamentalGroup.mapOfEq k hk) :=
      congrArg (fun h : FundamentalGroup (X₀ i) (a₀ i) →* FundamentalGroup WL wL ↦
        ρ.comp h) hι.symm
    _ = (o.comp (FundamentalGroup.mapOfEq r hr)).comp
        (FundamentalGroup.mapOfEq k hk) :=
      congrArg (fun h : FundamentalGroup U.1 ⟨wL, U.2⟩ →*
          Monoid.CoprodI (fun j ↦ FundamentalGroup (X₀ j) (a₀ j)) ↦
        h.comp (FundamentalGroup.mapOfEq k hk)) hchart
    _ = o :=
      (congrArg (fun h : FundamentalGroup (X₀ i) (a₀ i) →*
          FundamentalGroup (X₀ i) (a₀ i) ↦ o.comp h) hpk).trans
        (MonoidHom.comp_id o)

/-- The homomorphism to the coproduct is a left inverse to the canonical
homomorphism induced by the factor inclusions. This is a split-injectivity
statement, not a claim of surjectivity, generation or uniqueness. -/
@[simp] theorem widePushoutPointFundamentalGroupCoproductRetraction_comp_coproductMap :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL)
      (hpcC : IsPathConnected (C.1 : Set WL))
      (hpcX : ∀ i, IsPathConnected (univ : Set (X₀ i)))
      (hnull : ∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥),
      (widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull).comp
        (widePushoutPointFundamentalGroupCoproductMap a₀) =
          MonoidHom.id (Monoid.CoprodI (fun i ↦ FundamentalGroup (X₀ i) (a₀ i))) := by
  dsimp only
  intro C hpcC hpcX hnull
  apply Monoid.CoprodI.ext_hom
  intro i
  rw [MonoidHom.comp_assoc, widePushoutPointFundamentalGroupCoproductMap_comp_of,
    widePushoutPointFundamentalGroupCoproductRetraction_comp_inclusion, MonoidHom.id_comp]

/-- The factor-inclusion-induced coproduct homomorphism is injective when the
open core and all whole factors are path connected, and the factor-preimage
inclusions are π₁-null. This follows from the specified left inverse, without a
generation assertion. -/
theorem widePushoutPointFundamentalGroupCoproductMap_injective :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL),
      IsPathConnected (C.1 : Set WL) →
      (∀ i, IsPathConnected (univ : Set (X₀ i))) →
      (∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥) →
      Function.Injective (widePushoutPointFundamentalGroupCoproductMap a₀) := by
  dsimp only
  intro C hpcC hpcX hnull
  have hleft : Function.LeftInverse
      (widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull)
      (widePushoutPointFundamentalGroupCoproductMap a₀) := by
    intro g
    exact DFunLike.congr_fun
      (widePushoutPointFundamentalGroupCoproductRetraction_comp_coproductMap
        a₀ C hpcC hpcX hnull) g
  exact hleft.injective

/-- Extend a family of factor fundamental-group homomorphisms to an independently
universed monoid by composing the algebraic coproduct lift with the homomorphism
from the pushout to the coproduct. No uniqueness from factor restrictions is claimed. -/
def widePushoutPointFundamentalGroupExtend (H : Type z) [Monoid H]
    (φ : ∀ i, FundamentalGroup (X₀ i) (a₀ i) →* H) :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL),
      IsPathConnected (C.1 : Set WL) →
      (∀ i, IsPathConnected (univ : Set (X₀ i))) →
      (∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥) →
      FundamentalGroup WL wL →* H := by
  dsimp only
  intro C hpcC hpcX hnull
  exact (Monoid.CoprodI.lift φ).comp
    (widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull)

/-- The extension composed with the factor-induced coproduct homomorphism is
the algebraic coproduct lift of the given family. -/
@[simp] theorem widePushoutPointFundamentalGroupExtend_comp_coproductMap
    (H : Type z) [Monoid H] (φ : ∀ i, FundamentalGroup (X₀ i) (a₀ i) →* H) :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL)
      (hpcC : IsPathConnected (C.1 : Set WL))
      (hpcX : ∀ i, IsPathConnected (univ : Set (X₀ i)))
      (hnull : ∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥),
      (widePushoutPointFundamentalGroupExtend a₀ H φ C hpcC hpcX hnull).comp
        (widePushoutPointFundamentalGroupCoproductMap a₀) = Monoid.CoprodI.lift φ := by
  dsimp only
  intro C hpcC hpcX hnull
  change ((Monoid.CoprodI.lift φ).comp
    (widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull)).comp
      (widePushoutPointFundamentalGroupCoproductMap a₀) = _
  rw [MonoidHom.comp_assoc,
    widePushoutPointFundamentalGroupCoproductRetraction_comp_coproductMap, MonoidHom.comp_id]

/-- Restricting the extension along an original factor inclusion recovers the
given homomorphism on that factor. This holds for arbitrary monoid targets. -/
@[simp] theorem widePushoutPointFundamentalGroupExtend_comp_inclusion
    (H : Type z) [Monoid H] (φ : ∀ i, FundamentalGroup (X₀ i) (a₀ i) →* H) :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL)
      (hpcC : IsPathConnected (C.1 : Set WL))
      (hpcX : ∀ i, IsPathConnected (univ : Set (X₀ i)))
      (hnull : ∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥)
      (i : I),
      (widePushoutPointFundamentalGroupExtend a₀ H φ C hpcC hpcX hnull).comp
        (FundamentalGroup.mapOfEq (ιL i) (widePushout_point_ι_point aL i)) = φ i := by
  dsimp only
  intro C hpcC hpcX hnull i
  rw [← widePushoutPointFundamentalGroupCoproductMap_comp_of a₀ i,
    ← MonoidHom.comp_assoc, widePushoutPointFundamentalGroupExtend_comp_coproductMap,
    Monoid.CoprodI.lift_comp_of]

end OriginalFactors

end TopCat
