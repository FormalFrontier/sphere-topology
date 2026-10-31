/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Topology.WidePushout.SubsetRetraction
import SphereTopology.Topology.WidePushout.FundamentalGroup
import SphereTopology.Homotopy.Circle
import FundamentalGroupoids.FundamentalGroup

/-!
# A proper two-cylinder cover with nontrivial overlap

Two copies of `ℝ × Circle` are attached at `(0, 1)` in the categorical
point-attached wide pushout. The common core has inverse image
`(-1, 1) × Circle` in each factor. Adjoining each whole cylinder gives an open,
path-connected cover with intersection exactly the core; the point `(2, 1)`
in either cylinder is absent from the opposite chart.

The core uses its subspace topology. Projection through the first factor
retraction splits the section `z ↦ j_false (0, z)`. The induced based
fundamental-group maps therefore split onto the circle group, identified with
`Multiplicative ℤ`, proving that the overlap has nontrivial fundamental group.
The restrictions of the global circle projection to the charts give compatible
data for point-chart fundamental-group descent. Its descended homomorphism
still splits onto the circle group along the core section. No bouquet group
calculation is used.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  motivates the point-attached neighborhood setting. This proper-cover model
  and split-circle nontriviality argument are not assertions of its printed theorem.
* The wide-pushout chart and subset-retraction APIs of Sphere Topology,
  the induced-map APIs of Mathlib and Fundamental Groupoids, and Sphere Topology's
  circle fundamental-group calculator and point-chart fundamental-group descent
  provide the constructions used here.
-/

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

noncomputable section

namespace SphereTopologyTest

private abbrev cylinders : Bool → TopCat := fun _ ↦ TopCat.of (ℝ × Circle)
private abbrev points : ∀ i, cylinders i := fun _ ↦ (0, 1)
private abbrev arrows := fun i ↦
  (TopCat.const (points i) : TopCat.of PUnit ⟶ cylinders i)
private abbrev W := (widePushout (TopCat.of PUnit) cylinders arrows : TopCat)
private abbrev j (i : Bool) := WidePushout.ι arrows i
private abbrev R (i : Bool) := TopCat.widePushoutPointRetraction cylinders points i
private abbrev head : W := WidePushout.head arrows PUnit.unit

private def strip : Set (ℝ × Circle) := Ioo (-1) 1 ×ˢ univ

private def core : Set W :=
  {z | (R false z).1 ∈ Ioo (-1) 1 ∧ (R true z).1 ∈ Ioo (-1) 1}

private theorem preimage_core (i : Bool) : j i ⁻¹' core = strip := by
  have h0 : (0 : ℝ) ∈ Ioo (-1) 1 := ⟨by norm_num, by norm_num⟩
  cases i <;> ext x
  · change ((R false (j false x)).1 ∈ Ioo (-1) 1 ∧
      (R true (j false x)).1 ∈ Ioo (-1) 1) ↔ (x.1 ∈ Ioo (-1) 1 ∧ x.2 ∈ univ)
    rw [TopCat.widePushoutPointRetraction_ι_apply cylinders points false x,
      TopCat.widePushoutPointRetraction_ι_of_ne_apply cylinders points true false
        Bool.false_ne_true x]
    simp only [h0, mem_univ, and_true]
  · change ((R false (j true x)).1 ∈ Ioo (-1) 1 ∧
      (R true (j true x)).1 ∈ Ioo (-1) 1) ↔ (x.1 ∈ Ioo (-1) 1 ∧ x.2 ∈ univ)
    rw [TopCat.widePushoutPointRetraction_ι_of_ne_apply cylinders points false true
        (by decide) x,
      TopCat.widePushoutPointRetraction_ι_apply cylinders points true x]
    simp only [h0, mem_univ, true_and, and_true]

private theorem head_mem_core : head ∈ core := by
  change (R false head).1 ∈ Ioo (-1) 1 ∧ (R true head).1 ∈ Ioo (-1) 1
  rw [TopCat.widePushoutPointRetraction_head_apply cylinders points false PUnit.unit,
    TopCat.widePushoutPointRetraction_head_apply cylinders points true PUnit.unit]
  constructor <;> exact ⟨by norm_num, by norm_num⟩

private theorem core_eq_head_union_strips :
    core = {head} ∪ ⋃ i : Bool, j i '' strip := by
  apply Subset.antisymm
  · intro z hz
    rcases TopCat.subset_head_union_widePushoutPointSupport points core hz with hh | hf
    · exact Or.inl hh
    · right
      rcases mem_iUnion.mp hf with ⟨i, hi⟩
      rcases mem_iUnion.mp hi with ⟨_, x, rfl⟩
      exact mem_iUnion.mpr ⟨i, x, by rwa [← preimage_core i], rfl⟩
  · rintro z (hz | hz)
    · exact (mem_singleton_iff.mp hz).symm ▸ head_mem_core
    · rcases mem_iUnion.mp hz with ⟨i, x, hx, rfl⟩
      exact show x ∈ j i ⁻¹' core from (preimage_core i).symm ▸ hx

private theorem isOpen_core : IsOpen core :=
  (isOpen_Ioo.preimage (continuous_fst.comp (R false).hom.continuous)).inter
    (isOpen_Ioo.preimage (continuous_fst.comp (R true).hom.continuous))

private theorem isPathConnected_strip : IsPathConnected strip :=
  ((convex_Ioo (-1 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩).prod
    isPathConnected_univ

private theorem isPathConnected_core : IsPathConnected core :=
  (TopCat.isPathConnected_widePushout_point_preimage_iff points head_mem_core).mpr
    (fun i ↦ by rw [preimage_core]; exact isPathConnected_strip)

private abbrev chart (i : Bool) := TopCat.widePushoutPointChart points core i

private theorem open_pathConnected_charts (i : Bool) :
    IsOpen (chart i) ∧ IsPathConnected (chart i) :=
  ⟨TopCat.isOpen_widePushoutPointChart points head_mem_core isOpen_core i,
    TopCat.isPathConnected_widePushoutPointChart points head_mem_core
      isPathConnected_core i isPathConnected_univ⟩

private theorem charts_cover : chart false ∪ chart true = univ := by
  have h := TopCat.iUnion_widePushoutPointChart points head_mem_core
  apply eq_univ_of_forall
  intro z
  have hz : z ∈ ⋃ o : Option Bool, o.elim core chart := h.symm ▸ mem_univ z
  rcases mem_iUnion.mp hz with ⟨o, ho⟩
  rcases o with _ | i
  · exact Or.inl (TopCat.subset_widePushoutPointChart points core false ho)
  · cases i
    · exact Or.inl ho
    · exact Or.inr ho

private theorem charts_inter : chart false ∩ chart true = core :=
  TopCat.widePushoutPointChart_inter_of_ne points head_mem_core Bool.false_ne_true

private theorem chart_witness (i : Bool) :
    j i (2, 1) ∈ chart i ∧ j i (2, 1) ∉ chart (!i) := by
  refine ⟨TopCat.ι_mem_widePushoutPointChart points core i (2, 1), ?_⟩
  have hne : i ≠ !i := by cases i <;> decide
  change (2, 1) ∉ j i ⁻¹' chart (!i)
  rw [TopCat.preimage_ι_widePushoutPointChart_of_ne points head_mem_core hne,
    preimage_core]
  intro hw
  have hlt : (2 : ℝ) < 1 := hw.1.2
  norm_num at hlt

private def corePoint : core := ⟨head, head_mem_core⟩

private def circleSection : C(Circle, core) where
  toFun z := ⟨j false (0, z), by
    change (0, z) ∈ j false ⁻¹' core
    rw [preimage_core]
    exact ⟨⟨by norm_num, by norm_num⟩, mem_univ z⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (j false).hom.continuous.comp (continuous_const.prodMk continuous_id)

private theorem circleSection_point : circleSection 1 = corePoint := by
  apply Subtype.ext
  change j false (points false) = head
  exact TopCat.widePushout_point_ι_point points false

private def circleRetraction : C(core, Circle) :=
  ⟨fun z ↦ (R false z).2,
    continuous_snd.comp ((R false).hom.continuous.comp continuous_subtype_val)⟩

private theorem circleRetraction_point : circleRetraction corePoint = 1 := by
  change (R false head).2 = 1
  rw [TopCat.widePushoutPointRetraction_head_apply cylinders points false PUnit.unit]

private theorem circleRetraction_section :
    circleRetraction.comp circleSection = ContinuousMap.id Circle := by
  apply ContinuousMap.ext
  intro z
  exact congrArg Prod.snd
    (TopCat.widePushoutPointRetraction_ι_apply cylinders points false (0, z))

private abbrev sectionHom : FundamentalGroup Circle 1 →* FundamentalGroup core corePoint :=
  FundamentalGroup.mapOfEq circleSection circleSection_point

private abbrev retractionHom : FundamentalGroup core corePoint →* FundamentalGroup Circle 1 :=
  FundamentalGroup.mapOfEq circleRetraction circleRetraction_point

private theorem split_fundamentalGroup :
    retractionHom.comp sectionHom = MonoidHom.id (FundamentalGroup Circle 1) := by
  have hbase : (circleRetraction.comp circleSection) 1 = 1 :=
    (congrArg circleRetraction circleSection_point).trans circleRetraction_point
  have hid (f : C(Circle, Circle)) (hf : f = ContinuousMap.id Circle)
      (h₁ : f 1 = 1) :
      FundamentalGroup.mapOfEq f h₁ = MonoidHom.id (FundamentalGroup Circle 1) := by
    subst f
    apply MonoidHom.ext
    intro γ
    rw [FundamentalGroup.mapOfEq_apply]
    change (Path.Homotopic.Quotient.map γ (ContinuousMap.id Circle)).cast rfl rfl = γ
    rw [Path.Homotopic.Quotient.cast_rfl_rfl]
    exact DFunLike.congr_fun (FundamentalGroup.map_id (1 : Circle)) γ
  calc
    retractionHom.comp sectionHom =
        FundamentalGroup.mapOfEq (circleRetraction.comp circleSection) hbase := by
      apply MonoidHom.ext
      intro γ
      simp only [sectionHom, retractionHom, MonoidHom.comp_apply,
        FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_cast,
        Path.Homotopic.Quotient.cast_cast]
      exact congrArg (fun δ : FundamentalGroup Circle (circleRetraction (circleSection 1)) ↦
        Path.Homotopic.Quotient.cast δ hbase.symm hbase.symm)
        (DFunLike.congr_fun
          (FundamentalGroup.map_comp circleRetraction circleSection (1 : Circle)).symm γ)
    _ = _ := hid _ circleRetraction_section hbase

private theorem nontrivial_core_fundamentalGroup :
    Nontrivial (FundamentalGroup core corePoint) := by
  have hinj : Function.Injective sectionHom := by
    apply Function.LeftInverse.injective (g := retractionHom)
    intro γ
    exact DFunLike.congr_fun split_fundamentalGroup γ
  have : Nontrivial (FundamentalGroup Circle 1) :=
    Circle.fundamentalGroupEquivInt.toEquiv.nontrivial
  exact hinj.nontrivial

private def coreNhds : OpenNhds (X := W) head :=
  ⟨⟨core, isOpen_core⟩, head_mem_core⟩

private def circleProjection : C(W, Circle) :=
  ⟨fun z ↦ (R false z).2, continuous_snd.comp (R false).hom.continuous⟩

private def chartProjection (i : Bool) : C(chart i, Circle) :=
  circleProjection.comp (ContinuousMap.subtypeVal _)

private theorem chartProjection_point (i : Bool) :
    chartProjection i
      ((ContinuousMap.inclusion (TopCat.subset_widePushoutPointChart points core i))
        corePoint) = 1 :=
  circleRetraction_point

private abbrev chartHom (i : Bool) :
    FundamentalGroup (chart i)
      ((ContinuousMap.inclusion (TopCat.subset_widePushoutPointChart points core i))
        corePoint) →*
      FundamentalGroup Circle 1 :=
  FundamentalGroup.mapOfEq (chartProjection i) (chartProjection_point i)

private theorem chartHom_compatible (i : Bool) :
    (chartHom i).comp (((FundamentalGroup.openNhdsFunctor head).map
      (homOfLE (TopCat.le_widePushoutPointChartNhds points coreNhds i))).hom) =
        retractionHom := by
  change (chartHom i).comp
    (FundamentalGroup.map
      (ContinuousMap.inclusion (TopCat.subset_widePushoutPointChart points core i))
      corePoint) = retractionHom
  apply MonoidHom.ext
  intro γ
  simp only [chartHom, retractionHom, MonoidHom.comp_apply,
    FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply]
  rw [← Path.Homotopic.Quotient.map_comp]
  rfl

private def circleDesc : FundamentalGroup W head →* FundamentalGroup Circle 1 :=
  TopCat.widePushoutPointChartFundamentalGroupDesc points coreNhds
    isPathConnected_core (fun _ ↦ isPathConnected_univ) (FundamentalGroup Circle 1)
    retractionHom chartHom chartHom_compatible

private theorem circleDesc_core_section :
    (circleDesc.comp (((FundamentalGroup.openNhdsCocone head).ι.app coreNhds).hom)).comp
      sectionHom = MonoidHom.id (FundamentalGroup Circle 1) := by
  have hcore : circleDesc.comp
      (((FundamentalGroup.openNhdsCocone head).ι.app coreNhds).hom) = retractionHom :=
    TopCat.widePushoutPointChartFundamentalGroupDesc_comp_core points coreNhds
      isPathConnected_core (fun _ ↦ isPathConnected_univ) (FundamentalGroup Circle 1)
      retractionHom chartHom chartHom_compatible
  rw [hcore]
  exact split_fundamentalGroup

end SphereTopologyTest
