/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.Chart
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover

/-!
# Fundamental groups of point-wide-pushout charts

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
contractibility hypothesis is imposed.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §§7–8,
  supplies the common-overlap fundamental-group theorem and the point-wedge
  setting. The arbitrary-open-core formulation here is a generalization,
  not a free-product computation.
* Fundamental Groupoids supplies the common-overlap universal property and
  inclusion functor and cocone.
* Mathlib supplies open neighborhoods, topological wide pushouts and
  fundamental groups. The chart geometry is supplied by this library's
  `SphereTopology.Topology.WidePushout.Chart`.
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

end TopCat
