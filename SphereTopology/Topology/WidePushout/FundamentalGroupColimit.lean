/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.FundamentalGroup
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.CommonOverlap

/-!
# The core–chart colimit of a point-wide-pushout fundamental group

The fundamental groups of an open core and its factor-plus-core charts form a
`WidePushoutShape` diagram. Its arrows are induced by the core-to-chart
inclusions, and its ambient cocone consists of the subtype inclusions.
The core group remains the head of the diagram, including for an empty index
type. Different indices may give the same chart.

When the core and all whole factors are path connected, this cocone is a colimit
and the raw group colimit is canonically equivalent to the ambient fundamental
group. Both directions preserve every core and chart leg. The index and factor
universes are independent; the point attachment, its fundamental group and this
raw colimit have carrier universe `max u v`.

These constructions specialize the common-overlap diagram, cocone, colimit and
comparison from Fundamental Groupoids to the point-wide-pushout charts. The
chart geometry supplies the core inclusions, pairwise intersections, the cover
by the core and charts, and path connectedness of the charts. The core remains
in the cover even when there are no charts.

No simple-connectivity or core-preimage nullity hypothesis is required. This
comparison does not identify chart groups with factor groups or assert a
free-product formula.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–8,
  supplies group colimits, the based common-overlap theorem and the point-wedge
  setting. The arbitrary-open-core formulation is a generalization.
* `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.CommonOverlap`
  supplies the common-overlap star diagram, ambient inclusion cocone, colimit
  universal property and raw-colimit comparison with their inclusion laws.
* `SphereTopology.Topology.WidePushout.FundamentalGroup` supplies the
  point-chart neighborhood geometry, open cover and path connectedness.
* `GroupTheory.Category.Grp.Colimits` supplies the raw group colimit used by
  the comparison. Mathlib supplies topological wide pushouts and fundamental
  groups.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u v

namespace TopCat

variable {I : Type v} {X : I → TopCat.{max u v}} (a : ∀ i, X i)

local notation "P" => TopCat.of PUnit
local notation "f" => (fun i ↦ (TopCat.const (a i) : P ⟶ X i))
local notation "W" => (widePushout P X f : TopCat)
local notation "w" => WidePushout.head f PUnit.unit

/-- The stock star diagram of the core and chart fundamental groups.
Its arrows are induced by the core-to-chart inclusions. No connectedness
hypothesis is needed to construct this diagram. -/
def widePushoutPointChartFundamentalGroupDiagram (C : OpenNhds (X := W) w) :
    WidePushoutShape I ⥤ GrpCat.{max u v} :=
  FundamentalGroup.commonOverlapDiagram w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)

/-- The head object is the core fundamental group at the common point. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupDiagram_obj_none
    (C : OpenNhds (X := W) w) :
    (widePushoutPointChartFundamentalGroupDiagram a C).obj none =
      GrpCat.of (FundamentalGroup C.1 ⟨w, C.2⟩) :=
  FundamentalGroup.commonOverlapDiagram_obj_none w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)

/-- A leg object is the chart fundamental group at the common point. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupDiagram_obj_some
    (C : OpenNhds (X := W) w) (i : I) :
    (widePushoutPointChartFundamentalGroupDiagram a C).obj (some i) =
      GrpCat.of (FundamentalGroup (widePushoutPointChartNhds a C i).1
        ⟨w, (widePushoutPointChartNhds a C i).2⟩) :=
  FundamentalGroup.commonOverlapDiagram_obj_some w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C) i

/-- A generating arrow is exactly the map induced by the core inclusion into
its chart, as supplied by the neighborhood fundamental-group functor. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupDiagram_map_init
    (C : OpenNhds (X := W) w) (i : I) :
    (widePushoutPointChartFundamentalGroupDiagram a C).map
        (WidePushoutShape.Hom.init i) =
      (FundamentalGroup.openNhdsFunctor w).map
        (homOfLE (le_widePushoutPointChartNhds a C i)) :=
  FundamentalGroup.commonOverlapDiagram_map_init w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C) i

/-- The inclusions of the core and charts into the point attachment
form a cocone. No connectedness hypothesis is needed for its construction. -/
def widePushoutPointChartFundamentalGroupCocone (C : OpenNhds (X := W) w) :
    Cocone (widePushoutPointChartFundamentalGroupDiagram a C) :=
  FundamentalGroup.commonOverlapCocone w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)

/-- The cocone vertex is the fundamental group of the ambient point attachment. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupCocone_pt
    (C : OpenNhds (X := W) w) :
    (widePushoutPointChartFundamentalGroupCocone a C).pt =
      GrpCat.of (FundamentalGroup W w) :=
  FundamentalGroup.commonOverlapCocone_pt w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)

/-- The head leg is exactly the core inclusion-induced map. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupCocone_ι_app_none
    (C : OpenNhds (X := W) w) :
    (widePushoutPointChartFundamentalGroupCocone a C).ι.app none =
      (FundamentalGroup.openNhdsCocone w).ι.app C :=
  FundamentalGroup.commonOverlapCocone_ι_app_none w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)

/-- A chart leg is exactly the chart inclusion-induced map. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupCocone_ι_app_some
    (C : OpenNhds (X := W) w) (i : I) :
    (widePushoutPointChartFundamentalGroupCocone a C).ι.app (some i) =
      (FundamentalGroup.openNhdsCocone w).ι.app
        (widePushoutPointChartNhds a C i) :=
  FundamentalGroup.commonOverlapCocone_ι_app_some w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C) i

/-- The core–chart inclusion cocone is a colimit when the core and all
whole factors are path connected. The head remains present for an empty family.

This is the point-chart specialization of May's common-overlap fundamental-group
universal property, Chapter 2, §§7–8. -/
def widePushoutPointChartFundamentalGroupCoconeIsColimit
    (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i))) :
    IsColimit (widePushoutPointChartFundamentalGroupCocone a C) :=
  FundamentalGroup.commonOverlapCoconeIsColimit w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)
    (widePushoutPointChartNhds_inf_of_ne a C)
    (isOpenCover_widePushoutPointChartNhds a C) hpcC
    (fun i ↦ isPathConnected_widePushoutPointChartNhds a C hpcC i (hpcX i))

/-- The raw group colimit of the core–chart star is canonically equivalent
to the fundamental group of the point attachment. Its core and chart restrictions
are the inclusion-induced maps, and characterize this equivalence.

This combines the raw group-colimit universal property with May's common-overlap
theorem, Chapter 2, §§6–8, in the arbitrary-open-core formulation. -/
def widePushoutPointChartFundamentalGroupColimitEquiv
    (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i))) :
    GrpCat.Colimits.ColimitType
      (widePushoutPointChartFundamentalGroupDiagram a C) ≃*
        FundamentalGroup W w :=
  FundamentalGroup.commonOverlapColimitEquiv w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)
    (widePushoutPointChartNhds_inf_of_ne a C)
    (isOpenCover_widePushoutPointChartNhds a C) hpcC
    (fun i ↦ isPathConnected_widePushoutPointChartNhds a C hpcC i (hpcX i))

/-- The canonical raw comparison preserves every inclusion leg, including
the core leg at `none` and each chart leg at `some i`. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupColimitEquiv_comp_ι
    (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i)))
    (o : WidePushoutShape I) :
    (widePushoutPointChartFundamentalGroupColimitEquiv a C hpcC hpcX :
      GrpCat.Colimits.ColimitType
        (widePushoutPointChartFundamentalGroupDiagram a C) →* FundamentalGroup W w).comp
        (GrpCat.Colimits.ι (widePushoutPointChartFundamentalGroupDiagram a C) o) =
      ((widePushoutPointChartFundamentalGroupCocone a C).ι.app o).hom :=
  FundamentalGroup.commonOverlapColimitEquiv_comp_ι w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)
    (widePushoutPointChartNhds_inf_of_ne a C)
    (isOpenCover_widePushoutPointChartNhds a C) hpcC
    (fun i ↦ isPathConnected_widePushoutPointChartNhds a C hpcC i (hpcX i)) o

/-- The inverse canonical comparison takes every core or chart inclusion
leg to its raw-colimit generator map. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupColimitEquiv_symm_comp_ι
    (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i)))
    (o : WidePushoutShape I) :
    ((widePushoutPointChartFundamentalGroupColimitEquiv a C hpcC hpcX).symm :
      FundamentalGroup W w →* GrpCat.Colimits.ColimitType
        (widePushoutPointChartFundamentalGroupDiagram a C)).comp
        ((widePushoutPointChartFundamentalGroupCocone a C).ι.app o).hom =
      GrpCat.Colimits.ι (widePushoutPointChartFundamentalGroupDiagram a C) o :=
  FundamentalGroup.commonOverlapColimitEquiv_symm_comp_ι w C
    (widePushoutPointChartNhds a C) (le_widePushoutPointChartNhds a C)
    (widePushoutPointChartNhds_inf_of_ne a C)
    (isOpenCover_widePushoutPointChartNhds a C) hpcC
    (fun i ↦ isPathConnected_widePushoutPointChartNhds a C hpcC i (hpcX i)) o

end TopCat
