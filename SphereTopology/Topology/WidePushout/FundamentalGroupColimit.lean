/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.FundamentalGroup
public import GroupTheory.Category.Grp.Colimits

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

The comparison uses the existing chart descent universal property and the raw
group-colimit descent and extensionality API. Its universal-property method
follows `FundamentalGroup.quotientEquivOfIsOpenCover` from Fundamental Groupoids;
that comparison instead uses the induced category retaining every inclusion
between presented neighborhoods. Here only the stock star's core-to-chart
arrows are imposed.

No simple-connectivity or core-preimage nullity hypothesis is required. This
comparison does not identify chart groups with factor groups or assert a
free-product formula.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–8,
  supplies group colimits, the based common-overlap theorem and the point-wedge
  setting. The arbitrary-open-core formulation is a generalization.
* `SphereTopology.Topology.WidePushout.FundamentalGroup` supplies the chart
  descent and uniqueness theorems, using Fundamental Groupoids' inclusion
  functor, inclusion cocone and common-overlap theorem.
* `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCoverPresentation`
  supplies the nearby inclusion-indexed comparison and its universal-property
  approach.
* `GroupTheory.Category.Grp.Colimits` supplies the existing raw group colimit
  and its universal property. Mathlib supplies `WidePushoutShape.wideSpan`,
  `WidePushoutShape.mkCocone`, topological wide pushouts and fundamental groups.
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
  WidePushoutShape.wideSpan
    ((FundamentalGroup.openNhdsFunctor w).obj C)
    (fun i ↦ (FundamentalGroup.openNhdsFunctor w).obj
      (widePushoutPointChartNhds a C i))
    (fun i ↦ (FundamentalGroup.openNhdsFunctor w).map
      (homOfLE (le_widePushoutPointChartNhds a C i)))

/-- The head object is the core fundamental group at the common point. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupDiagram_obj_none
    (C : OpenNhds (X := W) w) :
    (widePushoutPointChartFundamentalGroupDiagram a C).obj none =
      GrpCat.of (FundamentalGroup C.1 ⟨w, C.2⟩) := rfl

/-- A leg object is the chart fundamental group at the common point. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupDiagram_obj_some
    (C : OpenNhds (X := W) w) (i : I) :
    (widePushoutPointChartFundamentalGroupDiagram a C).obj (some i) =
      GrpCat.of (FundamentalGroup (widePushoutPointChartNhds a C i).1
        ⟨w, (widePushoutPointChartNhds a C i).2⟩) := rfl

/-- A generating arrow is exactly the map induced by the core inclusion into
its chart, as supplied by the neighborhood fundamental-group functor. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupDiagram_map_init
    (C : OpenNhds (X := W) w) (i : I) :
    (widePushoutPointChartFundamentalGroupDiagram a C).map
        (WidePushoutShape.Hom.init i) =
      (FundamentalGroup.openNhdsFunctor w).map
        (homOfLE (le_widePushoutPointChartNhds a C i)) := rfl

/-- The inclusions of the core and charts into the point attachment
form a cocone. No connectedness hypothesis is needed for its construction. -/
def widePushoutPointChartFundamentalGroupCocone (C : OpenNhds (X := W) w) :
    Cocone (widePushoutPointChartFundamentalGroupDiagram a C) :=
  WidePushoutShape.mkCocone
    (F := widePushoutPointChartFundamentalGroupDiagram a C)
    ((FundamentalGroup.openNhdsCocone w).ι.app C)
    (fun i ↦ (FundamentalGroup.openNhdsCocone w).ι.app
      (widePushoutPointChartNhds a C i))
    (fun i ↦ (FundamentalGroup.openNhdsCocone w).w
      (homOfLE (le_widePushoutPointChartNhds a C i)))

/-- The cocone vertex is the fundamental group of the ambient point attachment. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupCocone_pt
    (C : OpenNhds (X := W) w) :
    (widePushoutPointChartFundamentalGroupCocone a C).pt =
      GrpCat.of (FundamentalGroup W w) := rfl

/-- The head leg is exactly the core inclusion-induced map. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupCocone_ι_app_none
    (C : OpenNhds (X := W) w) :
    (widePushoutPointChartFundamentalGroupCocone a C).ι.app none =
      (FundamentalGroup.openNhdsCocone w).ι.app C := rfl

/-- A chart leg is exactly the chart inclusion-induced map. -/
@[simp]
theorem widePushoutPointChartFundamentalGroupCocone_ι_app_some
    (C : OpenNhds (X := W) w) (i : I) :
    (widePushoutPointChartFundamentalGroupCocone a C).ι.app (some i) =
      (FundamentalGroup.openNhdsCocone w).ι.app
        (widePushoutPointChartNhds a C i) := rfl

-- The star objects and neighborhood groups agree definitionally. Let the unifier
-- recognize them when `GrpCat.hom_comp` normalizes dependent cocone equations,
-- as in FundamentalGroup.retractionOfHomotopy_comp_map.
set_option backward.isDefEq.respectTransparency false in
/-- The core–chart inclusion cocone is a colimit when the core and all
whole factors are path connected. The head remains present for an empty family.

This is the point-chart specialization of May's common-overlap fundamental-group
universal property, Chapter 2, §§7–8. -/
def widePushoutPointChartFundamentalGroupCoconeIsColimit
    (C : OpenNhds (X := W) w)
    (hpcC : IsPathConnected (C.1 : Set W))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i))) :
    IsColimit (widePushoutPointChartFundamentalGroupCocone a C) := by
  have hφ (s : Cocone (widePushoutPointChartFundamentalGroupDiagram a C)) (i : I) :
      (s.ι.app (some i)).hom.comp
        (((FundamentalGroup.openNhdsFunctor w).map
          (homOfLE (le_widePushoutPointChartNhds a C i))).hom) =
        (s.ι.app none).hom := by
    simpa only [GrpCat.hom_comp, widePushoutPointChartFundamentalGroupDiagram_map_init]
      using congrArg GrpCat.Hom.hom (s.w (WidePushoutShape.Hom.init i))
  let d (s : Cocone (widePushoutPointChartFundamentalGroupDiagram a C)) :
      FundamentalGroup W w →* s.pt :=
    widePushoutPointChartFundamentalGroupDesc a C hpcC hpcX s.pt
      (s.ι.app none).hom (fun i ↦ (s.ι.app (some i)).hom) (hφ s)
  have hd (s : Cocone (widePushoutPointChartFundamentalGroupDiagram a C))
      (o : WidePushoutShape I) :
      (widePushoutPointChartFundamentalGroupCocone a C).ι.app o ≫
        GrpCat.ofHom (d s) = s.ι.app o := by
    cases o with
    | none =>
      apply GrpCat.hom_ext
      simpa only [d, GrpCat.hom_comp, GrpCat.hom_ofHom,
        widePushoutPointChartFundamentalGroupCocone_ι_app_none] using
        widePushoutPointChartFundamentalGroupDesc_comp_core a C hpcC hpcX s.pt
          (s.ι.app none).hom (fun i ↦ (s.ι.app (some i)).hom) (hφ s)
    | some i =>
      apply GrpCat.hom_ext
      simpa only [d, GrpCat.hom_comp, GrpCat.hom_ofHom,
        widePushoutPointChartFundamentalGroupCocone_ι_app_some] using
        widePushoutPointChartFundamentalGroupDesc_comp_chart a C hpcC hpcX s.pt
          (s.ι.app none).hom (fun j ↦ (s.ι.app (some j)).hom) (hφ s) i
  refine
    { desc := fun s ↦ GrpCat.ofHom (d s)
      fac := hd
      uniq := ?_ }
  intro s m hm
  apply GrpCat.hom_ext
  apply widePushoutPointChart_hom_ext a C hpcC hpcX
  · simpa only [GrpCat.hom_comp, GrpCat.hom_ofHom,
      widePushoutPointChartFundamentalGroupCocone_ι_app_none] using
      congrArg GrpCat.Hom.hom ((hm none).trans (hd s none).symm)
  · intro i
    simpa only [GrpCat.hom_comp, GrpCat.hom_ofHom,
      widePushoutPointChartFundamentalGroupCocone_ι_app_some] using
      congrArg GrpCat.Hom.hom ((hm (some i)).trans (hd s (some i)).symm)

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
        FundamentalGroup W w := by
  let F := widePushoutPointChartFundamentalGroupDiagram a C
  let γ := widePushoutPointChartFundamentalGroupCocone a C
  have hcompat : ∀ {j k : WidePushoutShape I} (b : j ⟶ k),
      (γ.ι.app k).hom.comp (F.map b).hom = (γ.ι.app j).hom := by
    intro j k b
    exact congrArg GrpCat.Hom.hom (γ.w b)
  let φ : GrpCat.Colimits.ColimitType F →* FundamentalGroup W w :=
    GrpCat.Colimits.desc (H := FundamentalGroup W w) F
      (fun o ↦ (γ.ι.app o).hom) hcompat
  have hφ (o : WidePushoutShape I) :
      φ.comp (GrpCat.Colimits.ι F o) = (γ.ι.app o).hom :=
    GrpCat.Colimits.desc_comp_ι (H := FundamentalGroup W w) F _ hcompat o
  have hι (i : I) :
      (GrpCat.Colimits.ι F (some i)).comp
        (((FundamentalGroup.openNhdsFunctor w).map
          (homOfLE (le_widePushoutPointChartNhds a C i))).hom) =
        GrpCat.Colimits.ι F none :=
    GrpCat.Colimits.ι_comp_map F (WidePushoutShape.Hom.init i)
  let ψ : FundamentalGroup W w →* GrpCat.Colimits.ColimitType F :=
    widePushoutPointChartFundamentalGroupDesc a C hpcC hpcX
      (GrpCat.Colimits.ColimitType F) (GrpCat.Colimits.ι F none)
      (fun i ↦ GrpCat.Colimits.ι F (some i)) hι
  have hψ (o : WidePushoutShape I) :
      ψ.comp (γ.ι.app o).hom = GrpCat.Colimits.ι F o := by
    cases o with
    | none =>
        exact widePushoutPointChartFundamentalGroupDesc_comp_core a C hpcC hpcX
          (GrpCat.Colimits.ColimitType F) (GrpCat.Colimits.ι F none)
          (fun i ↦ GrpCat.Colimits.ι F (some i)) hι
    | some i =>
        exact widePushoutPointChartFundamentalGroupDesc_comp_chart a C hpcC hpcX
          (GrpCat.Colimits.ColimitType F) (GrpCat.Colimits.ι F none)
          (fun j ↦ GrpCat.Colimits.ι F (some j)) hι i
  have hψφ : ψ.comp φ = MonoidHom.id (GrpCat.Colimits.ColimitType F) := by
    apply GrpCat.Colimits.hom_ext F
    intro o
    apply MonoidHom.ext
    intro x
    exact (congrArg ψ (DFunLike.congr_fun (hφ o) x)).trans
      (DFunLike.congr_fun (hψ o) x)
  have hφψ : φ.comp ψ = MonoidHom.id (FundamentalGroup W w) := by
    apply widePushoutPointChart_hom_ext a C hpcC hpcX
    · apply MonoidHom.ext
      intro x
      exact (congrArg φ (DFunLike.congr_fun (hψ none) x)).trans
        (DFunLike.congr_fun (hφ none) x)
    · intro i
      apply MonoidHom.ext
      intro x
      exact (congrArg φ (DFunLike.congr_fun (hψ (some i)) x)).trans
        (DFunLike.congr_fun (hφ (some i)) x)
  exact φ.toMulEquiv ψ hψφ hφψ

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
      ((widePushoutPointChartFundamentalGroupCocone a C).ι.app o).hom := by
  let F := widePushoutPointChartFundamentalGroupDiagram a C
  let γ := widePushoutPointChartFundamentalGroupCocone a C
  have hcompat : ∀ {j k : WidePushoutShape I} (b : j ⟶ k),
      (γ.ι.app k).hom.comp (F.map b).hom = (γ.ι.app j).hom := by
    intro j k b
    exact congrArg GrpCat.Hom.hom (γ.w b)
  change (GrpCat.Colimits.desc (H := FundamentalGroup W w) F
    (fun j ↦ (γ.ι.app j).hom) hcompat).comp
      (GrpCat.Colimits.ι F o) = (γ.ι.app o).hom
  exact GrpCat.Colimits.desc_comp_ι (H := FundamentalGroup W w) F _ hcompat o

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
      GrpCat.Colimits.ι (widePushoutPointChartFundamentalGroupDiagram a C) o := by
  let e : GrpCat.Colimits.ColimitType
      (widePushoutPointChartFundamentalGroupDiagram a C) ≃* FundamentalGroup W w :=
    widePushoutPointChartFundamentalGroupColimitEquiv a C hpcC hpcX
  apply MonoidHom.ext
  intro x
  exact (congrArg e.symm
    (DFunLike.congr_fun
      (widePushoutPointChartFundamentalGroupColimitEquiv_comp_ι a C hpcC hpcX o) x)).symm.trans
    (e.symm_apply_apply
      (GrpCat.Colimits.ι (widePushoutPointChartFundamentalGroupDiagram a C) o x))

end TopCat
