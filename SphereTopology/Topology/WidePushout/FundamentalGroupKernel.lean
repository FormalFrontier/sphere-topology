/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.FundamentalGroup
import SphereTopology.Topology.WidePushout.FundamentalGroupColimit
import GroupTheory.Category.Grp.ColimitMapKernel

/-!
# Chart defects in the fundamental group of a point-attached wide pushout

The homomorphism from the ambient fundamental group to the coproduct of the
original factor fundamental groups has a kernel measured by its chart collapses.
Each collapse is restricted to the factor-plus-core chart and transported back
along the canonical ULift homeomorphism to the original factor. The maps from
chart groups to the ambient group are the neighborhood inclusion cocone legs.

The kernel formula requires a path-connected open core, path-connected whole
original factors, and trivial fundamental-group images for the inclusions of the
original-factor preimages of the core. It requires neither simple connectivity
of the core nor path connectedness of its factor preimages. The index and factor
universes are independent, and the index type may be empty: the common head
remains present even then.

The core–chart star maps to the stock star with trivial head and original-factor
fundamental groups at its spokes. Its components are surjective: each chart
collapse has the original factor inclusion as a based section. Compatibility
uses exactly the core-preimage nullity assumption. The source and target groups
remain in their respective universes; no same-universe natural transformation
or small target colimit is needed for this family.

Consequently, the inclusion-induced coproduct map is surjective exactly when
each chart-collapse kernel is killed by its chart inclusion. Under this condition,
it forms a multiplicative equivalence with the specified retraction, and extensions
of original-factor homomorphisms to arbitrary monoid targets are unique. The target
universe is independent.

This does not assert that the chart kernels vanish, identify charts with factors
by homotopy equivalences, or give a free-product computation merely from ordinary
contractibility of chosen factor neighborhoods.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–8,
  supplies the group-colimit, common-overlap and point-wedge setting. The
  arbitrary-open-core defect formulation is a generalization.
* `SphereTopology.Topology.WidePushout.FundamentalGroup` supplies the
  inclusion-induced coproduct map, its retraction and the chart restriction laws.
* `SphereTopology.Topology.WidePushout.FundamentalGroupColimit` supplies the
  core–chart star, using Mathlib's `WidePushoutShape.wideSpan`.
* Fundamental Groupoids supplies the neighborhood inclusion cocone and
  fundamental-group maps with specified basepoint equalities. Mathlib supplies
  indexed monoid coproducts, normal closure and the canonical ULift homeomorphisms.
* `GroupTheory.Category.Grp.ColimitMapKernel` supplies the kernel formula for
  objectwise surjective compatible families of group homomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u v

namespace TopCat

variable {I : Type v} {X₀ : I → TopCat.{u}} (a₀ : ∀ i, X₀ i)

/-- With no factors, the head map identifies the point attachment with its
point head, so its fundamental group is subsingleton. -/
private theorem widePushoutPointFundamentalGroup_subsingleton_of_isEmpty [IsEmpty I] :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    Subsingleton (FundamentalGroup WL wL) := by
  intro XL eL aL sL WL wL
  have hhead : IsHomeomorph (WidePushout.head sL) :=
    isHomeomorph_widePushout_head sL
  let : Subsingleton WL := hhead.homeomorph.symm.toEquiv.subsingleton
  let : Nonempty WL := ⟨wL⟩
  infer_instance

/-- The stock star of original-factor fundamental groups, with trivial head. -/
private def widePushoutPointFactorFundamentalGroupDiagram :
    WidePushoutShape I ⥤ GrpCat.{u} :=
  WidePushoutShape.wideSpan (GrpCat.of PUnit.{u + 1})
    (fun i ↦ GrpCat.of (FundamentalGroup (X₀ i) (a₀ i)))
    (fun _ ↦ GrpCat.ofHom 1)

/-- Collapse each chart to its original factor, and send the core to the
trivial head. The source and target group universes need not coincide. -/
private def widePushoutPointChartFactorComponents :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    ∀ (C : OpenNhds (X := WL) wL) (o : WidePushoutShape I),
      (widePushoutPointChartFundamentalGroupDiagram aL C).obj o →*
        (widePushoutPointFactorFundamentalGroupDiagram a₀).obj o := by
  intro XL eL aL sL WL wL C o
  cases o with
  | none => exact 1
  | some i =>
    exact FundamentalGroup.mapOfEq
      (x := (⟨wL, (widePushoutPointChartNhds aL C i).2⟩ :
        (widePushoutPointChartNhds aL C i).1)) (y := a₀ i)
      ((((eL i).symm : C(XL i, X₀ i)).comp
        (widePushoutPointRetraction XL aL i).hom).comp
          (ContinuousMap.subtypeVal
            ((widePushoutPointChartNhds aL C i).1 : Set WL)))
      (by
        change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
        rw [widePushoutPointRetraction_head_apply]
        exact (eL i).symm_apply_apply (a₀ i))

-- As in the core-nullity helper, the bundled basepoints and their images
-- agree definitionally after unfolding the stock star.
set_option backward.isDefEq.respectTransparency false in
/-- Core-preimage nullity makes the chart collapses compatible with every
arrow of the core–chart star, in the orientation for raw colimit maps. -/
private theorem widePushoutPointChartFactorComponents_natural :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL),
      (∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥) →
      ∀ {j k : WidePushoutShape I} (b : j ⟶ k),
      (widePushoutPointChartFactorComponents a₀ C k).comp
          ((widePushoutPointChartFundamentalGroupDiagram aL C).map b).hom =
        ((widePushoutPointFactorFundamentalGroupDiagram a₀).map b).hom.comp
          (widePushoutPointChartFactorComponents a₀ C j) := by
  intro XL eL aL sL WL wL ιL C hnull j k b
  cases b with
  | id j =>
    let F := widePushoutPointChartFundamentalGroupDiagram aL C
    let G := widePushoutPointFactorFundamentalGroupDiagram a₀
    let α := widePushoutPointChartFactorComponents a₀ C j
    have hF : (F.map (WidePushoutShape.Hom.id j)).hom = MonoidHom.id (F.obj j) :=
      (congrArg GrpCat.Hom.hom (F.map_id j)).trans GrpCat.hom_id
    have hG : (G.map (WidePushoutShape.Hom.id j)).hom = MonoidHom.id (G.obj j) :=
      (congrArg GrpCat.Hom.hom (G.map_id j)).trans GrpCat.hom_id
    calc
      _ = α.comp (MonoidHom.id _) := congrArg (fun f ↦ α.comp f) hF
      _ = α := MonoidHom.comp_id α
      _ = (MonoidHom.id _).comp α := (MonoidHom.id_comp α).symm
      _ = _ := congrArg (fun f ↦ f.comp α) hG.symm
  | init i =>
    change (widePushoutPointChartFactorComponents a₀ C (some i)).comp
      (((FundamentalGroup.openNhdsFunctor wL).map
        (homOfLE (le_widePushoutPointChartNhds aL C i))).hom) = 1
    exact widePushoutPointChartRetraction_comp_core_eq_one
      (a := aL) (b := a₀) eL (fun _ ↦ rfl) C i (hnull i)

-- The section and collapse have dependent subtype basepoints, just as in
-- widePushoutPointFundamentalGroupCoproductRetraction_comp_inclusion.
set_option backward.isDefEq.respectTransparency false in
/-- The components are surjective without connectedness or nullity assumptions.
For a spoke, the own-factor inclusion into its chart is a based section. -/
private theorem widePushoutPointChartFactorComponents_surjective :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    ∀ (C : OpenNhds (X := WL) wL) (o : WidePushoutShape I),
      Function.Surjective (widePushoutPointChartFactorComponents a₀ C o) := by
  intro XL eL aL sL WL wL C o
  cases o with
  | none =>
    change Function.Surjective
      (1 : FundamentalGroup C.1 ⟨wL, C.2⟩ →* PUnit.{u + 1})
    intro x
    exact ⟨1, Subsingleton.elim _ _⟩
  | some i =>
    let U := widePushoutPointChartNhds aL C i
    let k : C(X₀ i, U.1) :=
      ⟨fun x ↦ ⟨WidePushout.ι sL i (eL i x),
          ι_mem_widePushoutPointChart aL (C.1 : Set WL) i (eL i x)⟩,
        ((WidePushout.ι sL i).hom.continuous.comp (eL i).continuous).subtype_mk _⟩
    have hk : k (a₀ i) = (⟨wL, U.2⟩ : U.1) := by
      apply Subtype.ext
      exact widePushout_point_ι_point aL i
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
        (FundamentalGroup.mapOfEq k hk) =
          MonoidHom.id (FundamentalGroup (X₀ i) (a₀ i)) := by
      calc
        _ = (FundamentalGroup.mapOfEq (x := a₀ i) (y := a₀ i)
            (r.comp k) ((congrArg r hk).trans hr) :
              FundamentalGroup (X₀ i) (a₀ i) →* FundamentalGroup (X₀ i) (a₀ i)) :=
          (FundamentalGroup.mapOfEq_comp r k hk hr).symm
        _ = _ := by
          simpa only [hrk, ContinuousMap.id_apply] using
            FundamentalGroup.mapOfEq_id (a₀ i)
    change Function.Surjective (FundamentalGroup.mapOfEq r hr)
    intro g
    exact ⟨FundamentalGroup.mapOfEq k hk g, DFunLike.congr_fun hpk g⟩

/-- If the index type is inhabited, the core inclusion image lies in the union
of the chart-collapse kernel images. Only core-preimage nullity is needed. -/
private theorem widePushoutPointChartFundamentalGroupCocone_range_core_subset
    [Nonempty I] :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X₀ i)
    let eL : ∀ i, X₀ i ≃ₜ XL i := fun i ↦ (X₀ i).uliftFunctorObjHomeo
    let aL := fun i ↦ eL i (a₀ i)
    let sL := fun i ↦ (TopCat.const (aL i) : TopCat.of PUnit ⟶ XL i)
    let WL := (widePushout (TopCat.of PUnit) XL sL : TopCat)
    let wL := WidePushout.head sL PUnit.unit
    let ιL : ∀ i, C(X₀ i, WL) := fun i ↦
      (WidePushout.ι sL i).hom.comp (eL i : C(X₀ i, XL i))
    ∀ (C : OpenNhds (X := WL) wL),
      (∀ i,
        (FundamentalGroup.map
          (ContinuousMap.subtypeVal (ιL i ⁻¹' (C.1 : Set WL)))
          ⟨a₀ i, by
            change WidePushout.ι sL i (aL i) ∈ C.1
            rw [widePushout_point_ι_point aL i]
            exact C.2⟩).range = ⊥) →
      let κ := widePushoutPointChartFundamentalGroupCocone aL C
      let α := widePushoutPointChartFactorComponents a₀ C
      Set.range ((κ.ι.app none).hom) ⊆
        ⋃ i, ((κ.ι.app (some i)).hom) '' ((α (some i)).ker : Set _) := by
  intro XL eL aL sL WL wL ιL C hnull κ α
  let i : I := Classical.choice ‹Nonempty I›
  let F := widePushoutPointChartFundamentalGroupDiagram aL C
  have hα := widePushoutPointChartFactorComponents_natural a₀ C hnull
    (WidePushoutShape.Hom.init i)
  change (α (some i)).comp (F.map (WidePushoutShape.Hom.init i)).hom = 1 at hα
  have hκ : (κ.ι.app (some i)).hom.comp (F.map (WidePushoutShape.Hom.init i)).hom =
      (κ.ι.app none).hom :=
    congrArg GrpCat.Hom.hom (κ.w (WidePushoutShape.Hom.init i))
  rintro _ ⟨x, rfl⟩
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  refine ⟨(F.map (WidePushoutShape.Hom.init i)).hom x, ?_, ?_⟩
  · exact MonoidHom.mem_ker.mpr (DFunLike.congr_fun hα x)
  · exact DFunLike.congr_fun hκ x

-- The star objects and based maps agree definitionally with the neighborhood
-- cocone legs; expose these reductions when comparing their restrictions.
set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the homomorphism to the factor-group coproduct is the normal
closure of the chart-collapse kernel images under the chart inclusions.

Each `p i` is induced by the restricted collapse transported back to the original
factor `X₀ i`, and each `γ i` is the inclusion-induced homomorphism from its chart
to the ambient point attachment. The hypotheses concern the open core, the whole
original factors and their core-preimage inclusions, not chart–factor homotopy
equivalences. This conditional defect formula does not assert that the defects
vanish or give a free-product computation from ordinary contractibility of
chosen factor neighborhoods. The index type may be empty, with its head retained. -/
theorem widePushoutPointFundamentalGroupCoproductRetraction_ker_eq_normalClosure :
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
      let U : I → OpenNhds (X := WL) wL := widePushoutPointChartNhds aL C
      let p : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup (X₀ i) (a₀ i) := fun i ↦
        FundamentalGroup.mapOfEq
          (x := (⟨wL, (U i).2⟩ : (U i).1)) (y := a₀ i)
          ((((eL i).symm : C(XL i, X₀ i)).comp
            (widePushoutPointRetraction XL aL i).hom).comp
              (ContinuousMap.subtypeVal ((U i).1 : Set WL)))
          (by
            change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
            rw [widePushoutPointRetraction_head_apply]
            exact (eL i).symm_apply_apply (a₀ i))
      let γ : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup WL wL := fun i ↦
        ((FundamentalGroup.openNhdsCocone wL).ι.app (U i)).hom
      (widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull).ker =
        Subgroup.normalClosure
          (⋃ i, γ i '' ((p i).ker : Set (FundamentalGroup (U i).1 ⟨wL, (U i).2⟩))) := by
  classical
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull U p γ
  rcases isEmpty_or_nonempty I with hI | hI
  · let := hI
    let : Subsingleton (FundamentalGroup WL wL) :=
      widePushoutPointFundamentalGroup_subsingleton_of_isEmpty a₀
    rw [Set.iUnion_of_empty, Subgroup.normalClosure_empty]
    apply bot_unique
    intro g _
    exact Subgroup.mem_bot.mpr (Subsingleton.elim _ _)
  · let := hI
    let F := widePushoutPointChartFundamentalGroupDiagram aL C
    let G := widePushoutPointFactorFundamentalGroupDiagram a₀
    let α : ∀ o, F.obj o →* G.obj o := widePushoutPointChartFactorComponents a₀ C
    have hα : ∀ {j k : WidePushoutShape I} (b : j ⟶ k),
        (α k).comp (F.map b).hom = (G.map b).hom.comp (α j) :=
      widePushoutPointChartFactorComponents_natural a₀ C hnull
    have hs : ∀ o, Function.Surjective (α o) :=
      widePushoutPointChartFactorComponents_surjective a₀ C
    let m := GrpCat.Colimits.map α hα
    have hpcL : ∀ i, IsPathConnected (univ : Set (XL i)) := by
      intro i
      simpa only [preimage_univ] using
        ((eL i).symm.isPathConnected_preimage (s := (univ : Set (X₀ i)))).2 (hpcX i)
    let e : GrpCat.Colimits.ColimitType F ≃* FundamentalGroup WL wL :=
      widePushoutPointChartFundamentalGroupColimitEquiv aL C hpcC hpcL
    let κ := widePushoutPointChartFundamentalGroupCocone aL C
    have he (o : WidePushoutShape I) :
        e.toMonoidHom.comp (GrpCat.Colimits.ι F o) = (κ.ι.app o).hom :=
      widePushoutPointChartFundamentalGroupColimitEquiv_comp_ι aL C hpcC hpcL o
    have he_fun (o : WidePushoutShape I) :
        (fun y : F.obj o ↦ e.toMonoidHom (GrpCat.Colimits.ι F o y)) =
          ((κ.ι.app o).hom : F.obj o → FundamentalGroup WL wL) := by
      funext y
      exact DFunLike.congr_fun (he o) y
    have hαsome (i : I) : α (some i) = p i := rfl
    have hκsome (i : I) : (κ.ι.app (some i)).hom = γ i := rfl
    let P := Monoid.CoprodI (fun i ↦ FundamentalGroup (X₀ i) (a₀ i))
    let ρ : FundamentalGroup WL wL →* P :=
      widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull
    let r : GrpCat.Colimits.ColimitType F →* P := ρ.comp e.toMonoidHom
    have hrcore : r.comp (GrpCat.Colimits.ι F none) = 1 := by
      change ρ.comp (e.toMonoidHom.comp (GrpCat.Colimits.ι F none)) = 1
      rw [he none]
      exact widePushoutPointFundamentalGroupCoproductRetraction_comp_core
        a₀ C hpcC hpcX hnull
    have hrchart (i : I) : r.comp (GrpCat.Colimits.ι F (some i)) =
        (Monoid.CoprodI.of (M := fun j ↦ FundamentalGroup (X₀ j) (a₀ j))
          (i := i)).comp (p i) := by
      change ρ.comp (e.toMonoidHom.comp (GrpCat.Colimits.ι F (some i))) = _
      rw [he (some i)]
      exact widePushoutPointFundamentalGroupCoproductRetraction_comp_chart
        a₀ C hpcC hpcX hnull i
    let χ : P →* GrpCat.Colimits.ColimitType G :=
      Monoid.CoprodI.lift (fun i ↦ GrpCat.Colimits.ι G (some i))
    have hm : m = χ.comp r := by
      apply GrpCat.Colimits.hom_ext F
      intro o
      change (GrpCat.Colimits.map α hα).comp (GrpCat.Colimits.ι F o) =
        χ.comp (r.comp (GrpCat.Colimits.ι F o))
      rw [GrpCat.Colimits.map_comp_ι]
      cases o with
      | none =>
        rw [hrcore, MonoidHom.comp_one]
        change (GrpCat.Colimits.ι G none).comp
          (1 : FundamentalGroup C.1 ⟨wL, C.2⟩ →* PUnit.{u + 1}) = 1
        exact MonoidHom.comp_one _
      | some i =>
        rw [hrchart]
        change (GrpCat.Colimits.ι G (some i)).comp (α (some i)) =
          ((Monoid.CoprodI.lift (fun j ↦ GrpCat.Colimits.ι G (some j))).comp
            (Monoid.CoprodI.of (i := i))).comp (p i)
        rw [Monoid.CoprodI.lift_comp_of, hαsome]
    let S : Set (GrpCat.Colimits.ColimitType F) :=
      ⋃ o, GrpCat.Colimits.ι F o '' ((α o).ker : Set (F.obj o))
    -- Generator killing gives one inclusion; factorization through χ gives the
    -- other after applying the objectwise-surjective colimit kernel formula.
    have hkill : Subgroup.normalClosure S ≤ r.ker := by
      apply Subgroup.normalClosure_le_normal
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨o, y, hy, rfl⟩
      change r (GrpCat.Colimits.ι F o y) = 1
      cases o with
      | none => exact DFunLike.congr_fun hrcore y
      | some i =>
        change y ∈ (p i).ker at hy
        have hy' : p i y = (1 : FundamentalGroup (X₀ i) (a₀ i)) :=
          (p i).mem_ker.mp hy
        calc
          r (GrpCat.Colimits.ι F (some i) y) =
              Monoid.CoprodI.of
                (M := fun j ↦ FundamentalGroup (X₀ j) (a₀ j)) (i := i) (p i y) :=
            DFunLike.congr_fun (hrchart i) y
          _ = 1 := by rw [hy', map_one]
    have hraw : r.ker = Subgroup.normalClosure S := by
      have hmker : m.ker = Subgroup.normalClosure S :=
        GrpCat.Colimits.ker_map α hα hs
      apply le_antisymm ?_ hkill
      rw [← hmker]
      intro x hx
      change m x = 1
      rw [hm, MonoidHom.comp_apply, r.mem_ker.mp hx, map_one]
    have hrρ : r.comp e.symm.toMonoidHom = ρ := by
      apply MonoidHom.ext
      intro x
      change ρ (e (e.symm x)) = ρ x
      rw [e.apply_symm_apply]
    have hker : ρ.ker = r.ker.map e.toMonoidHom := by
      rw [← hrρ]
      exact MonoidHom.ker_comp_mulEquiv r e.symm
    let T : Set (FundamentalGroup WL wL) :=
      ⋃ o, (κ.ι.app o).hom '' ((α o).ker : Set (F.obj o))
    have himage : e.toMonoidHom '' S = T := by
      dsimp only [S, T]
      rw [Set.image_iUnion]
      apply Set.iUnion_congr
      intro o
      rw [Set.image_image]
      exact congrArg (fun f : F.obj o → FundamentalGroup WL wL ↦
        f '' ((α o).ker : Set (F.obj o))) (he_fun o)
    have hkerT : ρ.ker = Subgroup.normalClosure T := by
      rw [hker, hraw, Subgroup.map_normalClosure S e.toMonoidHom e.surjective, himage]
    have hcore :=
      widePushoutPointChartFundamentalGroupCocone_range_core_subset a₀ C hnull
    change Set.range ((κ.ι.app none).hom :
        FundamentalGroup C.1 ⟨wL, C.2⟩ → FundamentalGroup WL wL) ⊆
      ⋃ i, γ i '' ((p i).ker :
        Set (FundamentalGroup (U i).1 ⟨wL, (U i).2⟩)) at hcore
    have hT : T = ⋃ i, γ i '' ((p i).ker : Set _) := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨o, y, hy, rfl⟩
        cases o with
        | none => exact hcore ⟨y, rfl⟩
        | some i =>
          change y ∈ (p i).ker at hy
          exact Set.mem_iUnion.mpr
            ⟨i, y, hy, (DFunLike.congr_fun (hκsome i) y).symm⟩
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨i, y, hy, rfl⟩
        have hy' : y ∈ (α (some i)).ker := by
          change y ∈ (p i).ker
          exact hy
        exact Set.mem_iUnion.mpr
          ⟨some i, y, hy', DFunLike.congr_fun (hκsome i) y⟩
    exact hkerT.trans (congrArg Subgroup.normalClosure hT)

/-- The original-factor coproduct map is surjective exactly when every kernel
of a chart collapse to its original factor is killed by the chart inclusion
into the ambient point attachment. The open core and whole original factors
are path connected, and the original core-preimage inclusions are π₁-null.
No path connectedness of those preimages or chart–factor equivalence is required.
This is the vanishing-defect criterion for the kernel formula above, in the
point-wedge setting of May, Chapter 2, §§6–8. The index type may be empty. -/
theorem widePushoutPointFundamentalGroupCoproductMap_surjective_iff :
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
      let U : I → OpenNhds (X := WL) wL := widePushoutPointChartNhds aL C
      let p : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup (X₀ i) (a₀ i) := fun i ↦
        FundamentalGroup.mapOfEq
          (x := (⟨wL, (U i).2⟩ : (U i).1)) (y := a₀ i)
          ((((eL i).symm : C(XL i, X₀ i)).comp
            (widePushoutPointRetraction XL aL i).hom).comp
              (ContinuousMap.subtypeVal ((U i).1 : Set WL)))
          (by
            change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
            rw [widePushoutPointRetraction_head_apply]
            exact (eL i).symm_apply_apply (a₀ i))
      let γ : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup WL wL := fun i ↦
        ((FundamentalGroup.openNhdsCocone wL).ι.app (U i)).hom
      Function.Surjective (widePushoutPointFundamentalGroupCoproductMap a₀) ↔
        ∀ i, (p i).ker ≤ (γ i).ker := by
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull U p γ
  let q := widePushoutPointFundamentalGroupCoproductMap a₀
  let ρ := widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull
  have hleft : Function.LeftInverse ρ q := by
    intro g
    exact DFunLike.congr_fun
      (widePushoutPointFundamentalGroupCoproductRetraction_comp_coproductMap
        a₀ C hpcC hpcX hnull) g
  have hsurj : Function.Surjective q ↔ Function.Injective ρ := by
    constructor
    · intro hq
      exact (hleft.rightInverse_of_surjective hq).injective
    · intro hρ
      exact (hleft.rightInverse_of_injective hρ).surjective
  have hker : ρ.ker = Subgroup.normalClosure
      (⋃ i, γ i '' ((p i).ker : Set (FundamentalGroup (U i).1 ⟨wL, (U i).2⟩))) :=
    widePushoutPointFundamentalGroupCoproductRetraction_ker_eq_normalClosure
      a₀ C hpcC hpcX hnull
  change Function.Surjective q ↔ ∀ i, (p i).ker ≤ (γ i).ker
  rw [hsurj, ← ρ.ker_eq_bot_iff, hker, Subgroup.normalClosure_eq_bot_iff]
  constructor
  · intro h i x hx
    apply (γ i).mem_ker.mpr
    exact Set.mem_singleton_iff.mp
      (h (Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩))
  · intro h x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, y, hy, rfl⟩
    exact Set.mem_singleton_iff.mpr ((γ i).mem_ker.mp (h i hy))

/-- The equivalence from the coproduct of the original factor fundamental groups
to the ambient fundamental group when the chart-collapse defects vanish under
the chart inclusions. Its forward homomorphism is the factor-induced coproduct
map, and its inverse is the chart retraction to that coproduct. This is the
conditional original-factor consequence of May's point-wedge setting,
Chapter 2, §§6–8, not an unconditional free-product formula. -/
def widePushoutPointFundamentalGroupCoproductEquiv :
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
      let U : I → OpenNhds (X := WL) wL := widePushoutPointChartNhds aL C
      let p : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup (X₀ i) (a₀ i) := fun i ↦
        FundamentalGroup.mapOfEq
          (x := (⟨wL, (U i).2⟩ : (U i).1)) (y := a₀ i)
          ((((eL i).symm : C(XL i, X₀ i)).comp
            (widePushoutPointRetraction XL aL i).hom).comp
              (ContinuousMap.subtypeVal ((U i).1 : Set WL)))
          (by
            change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
            rw [widePushoutPointRetraction_head_apply]
            exact (eL i).symm_apply_apply (a₀ i))
      let γ : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup WL wL := fun i ↦
        ((FundamentalGroup.openNhdsCocone wL).ι.app (U i)).hom
      (∀ i, (p i).ker ≤ (γ i).ker) →
        Monoid.CoprodI (fun i ↦ FundamentalGroup (X₀ i) (a₀ i)) ≃*
          FundamentalGroup WL wL := by
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull U p γ hkill
  let q := widePushoutPointFundamentalGroupCoproductMap a₀
  let ρ := widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull
  exact q.toMulEquiv ρ
    (widePushoutPointFundamentalGroupCoproductRetraction_comp_coproductMap
      a₀ C hpcC hpcX hnull)
    (by
      have hq : Function.Surjective q :=
        (widePushoutPointFundamentalGroupCoproductMap_surjective_iff
          a₀ C hpcC hpcX hnull).2 hkill
      have hρq : Function.LeftInverse ρ q :=
        DFunLike.congr_fun
          (widePushoutPointFundamentalGroupCoproductRetraction_comp_coproductMap
            a₀ C hpcC hpcX hnull)
      exact MonoidHom.ext (hρq.rightInverse_of_surjective hq))

/-- The forward homomorphism of the original-factor equivalence is the
homomorphism induced by the original factor inclusions. -/
@[simp] theorem widePushoutPointFundamentalGroupCoproductEquiv_toMonoidHom :
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
      let U : I → OpenNhds (X := WL) wL := widePushoutPointChartNhds aL C
      let p : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup (X₀ i) (a₀ i) := fun i ↦
        FundamentalGroup.mapOfEq
          (x := (⟨wL, (U i).2⟩ : (U i).1)) (y := a₀ i)
          ((((eL i).symm : C(XL i, X₀ i)).comp
            (widePushoutPointRetraction XL aL i).hom).comp
              (ContinuousMap.subtypeVal ((U i).1 : Set WL)))
          (by
            change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
            rw [widePushoutPointRetraction_head_apply]
            exact (eL i).symm_apply_apply (a₀ i))
      let γ : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup WL wL := fun i ↦
        ((FundamentalGroup.openNhdsCocone wL).ι.app (U i)).hom
      ∀ (hkill : ∀ i, (p i).ker ≤ (γ i).ker),
        (widePushoutPointFundamentalGroupCoproductEquiv a₀ C hpcC hpcX hnull
          hkill : Monoid.CoprodI (fun i ↦ FundamentalGroup (X₀ i) (a₀ i)) →*
            FundamentalGroup WL wL) = widePushoutPointFundamentalGroupCoproductMap a₀ := by
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull U p γ hkill
  rfl

/-- The inverse homomorphism of the original-factor equivalence is the
homomorphism obtained from the chart retractions. -/
@[simp] theorem widePushoutPointFundamentalGroupCoproductEquiv_symm_toMonoidHom :
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
      let U : I → OpenNhds (X := WL) wL := widePushoutPointChartNhds aL C
      let p : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup (X₀ i) (a₀ i) := fun i ↦
        FundamentalGroup.mapOfEq
          (x := (⟨wL, (U i).2⟩ : (U i).1)) (y := a₀ i)
          ((((eL i).symm : C(XL i, X₀ i)).comp
            (widePushoutPointRetraction XL aL i).hom).comp
              (ContinuousMap.subtypeVal ((U i).1 : Set WL)))
          (by
            change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
            rw [widePushoutPointRetraction_head_apply]
            exact (eL i).symm_apply_apply (a₀ i))
      let γ : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup WL wL := fun i ↦
        ((FundamentalGroup.openNhdsCocone wL).ι.app (U i)).hom
      ∀ (hkill : ∀ i, (p i).ker ≤ (γ i).ker),
        ((widePushoutPointFundamentalGroupCoproductEquiv a₀ C hpcC hpcX hnull
          hkill).symm : FundamentalGroup WL wL →*
            Monoid.CoprodI (fun i ↦ FundamentalGroup (X₀ i) (a₀ i))) =
              widePushoutPointFundamentalGroupCoproductRetraction a₀ C hpcC hpcX hnull := by
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull U p γ hkill
  rfl

/-- On each coproduct factor, the original-factor equivalence is the
homomorphism induced by the original-domain inclusion into the point attachment. -/
theorem widePushoutPointFundamentalGroupCoproductEquiv_comp_of :
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
      let U : I → OpenNhds (X := WL) wL := widePushoutPointChartNhds aL C
      let p : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup (X₀ i) (a₀ i) := fun i ↦
        FundamentalGroup.mapOfEq
          (x := (⟨wL, (U i).2⟩ : (U i).1)) (y := a₀ i)
          ((((eL i).symm : C(XL i, X₀ i)).comp
            (widePushoutPointRetraction XL aL i).hom).comp
              (ContinuousMap.subtypeVal ((U i).1 : Set WL)))
          (by
            change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
            rw [widePushoutPointRetraction_head_apply]
            exact (eL i).symm_apply_apply (a₀ i))
      let γ : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup WL wL := fun i ↦
        ((FundamentalGroup.openNhdsCocone wL).ι.app (U i)).hom
      ∀ (hkill : ∀ i, (p i).ker ≤ (γ i).ker) (i : I),
        (widePushoutPointFundamentalGroupCoproductEquiv a₀ C hpcC hpcX hnull
          hkill).toMonoidHom.comp (Monoid.CoprodI.of (i := i)) =
            FundamentalGroup.mapOfEq (ιL i) (widePushout_point_ι_point aL i) := by
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull U p γ hkill i
  rw [MulEquiv.toMonoidHom_eq_coe,
    widePushoutPointFundamentalGroupCoproductEquiv_toMonoidHom]
  exact widePushoutPointFundamentalGroupCoproductMap_comp_of a₀ i

/-- The inverse original-factor equivalence takes the homomorphism induced by
each original-domain factor inclusion to the corresponding coproduct insertion. -/
theorem widePushoutPointFundamentalGroupCoproductEquiv_symm_comp_inclusion :
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
      let U : I → OpenNhds (X := WL) wL := widePushoutPointChartNhds aL C
      let p : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup (X₀ i) (a₀ i) := fun i ↦
        FundamentalGroup.mapOfEq
          (x := (⟨wL, (U i).2⟩ : (U i).1)) (y := a₀ i)
          ((((eL i).symm : C(XL i, X₀ i)).comp
            (widePushoutPointRetraction XL aL i).hom).comp
              (ContinuousMap.subtypeVal ((U i).1 : Set WL)))
          (by
            change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
            rw [widePushoutPointRetraction_head_apply]
            exact (eL i).symm_apply_apply (a₀ i))
      let γ : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup WL wL := fun i ↦
        ((FundamentalGroup.openNhdsCocone wL).ι.app (U i)).hom
      ∀ (hkill : ∀ i, (p i).ker ≤ (γ i).ker) (i : I),
        (widePushoutPointFundamentalGroupCoproductEquiv a₀ C hpcC hpcX hnull
          hkill).symm.toMonoidHom.comp
            (FundamentalGroup.mapOfEq (ιL i) (widePushout_point_ι_point aL i)) =
              Monoid.CoprodI.of
                (M := fun j ↦ FundamentalGroup (X₀ j) (a₀ j)) (i := i) := by
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull U p γ hkill i
  rw [MulEquiv.toMonoidHom_eq_coe,
    widePushoutPointFundamentalGroupCoproductEquiv_symm_toMonoidHom]
  exact widePushoutPointFundamentalGroupCoproductRetraction_comp_inclusion
    a₀ C hpcC hpcX hnull i

universe z

/-- When the chart-collapse defects are killed by the chart inclusions, any
homomorphism to an independently universed monoid with the prescribed
original-factor restrictions equals the extension obtained from the chart
retractions. Only original-domain inclusion restrictions are needed, including
for an empty index type. This is the original-factor universal-property
consequence of the conditional vanishing-defect criterion above, in May's
point-wedge setting, Chapter 2, §§6–8. -/
theorem eq_widePushoutPointFundamentalGroupExtend (H : Type z) [Monoid H]
    (φ : ∀ i, FundamentalGroup (X₀ i) (a₀ i) →* H) :
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
      let U : I → OpenNhds (X := WL) wL := widePushoutPointChartNhds aL C
      let p : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup (X₀ i) (a₀ i) := fun i ↦
        FundamentalGroup.mapOfEq
          (x := (⟨wL, (U i).2⟩ : (U i).1)) (y := a₀ i)
          ((((eL i).symm : C(XL i, X₀ i)).comp
            (widePushoutPointRetraction XL aL i).hom).comp
              (ContinuousMap.subtypeVal ((U i).1 : Set WL)))
          (by
            change (eL i).symm (widePushoutPointRetraction XL aL i wL) = a₀ i
            rw [widePushoutPointRetraction_head_apply]
            exact (eL i).symm_apply_apply (a₀ i))
      let γ : ∀ i, FundamentalGroup (U i).1 ⟨wL, (U i).2⟩ →*
          FundamentalGroup WL wL := fun i ↦
        ((FundamentalGroup.openNhdsCocone wL).ι.app (U i)).hom
      (∀ i, (p i).ker ≤ (γ i).ker) →
      ∀ (g : FundamentalGroup WL wL →* H),
        (∀ i, g.comp
          (FundamentalGroup.mapOfEq (ιL i) (widePushout_point_ι_point aL i)) = φ i) →
        g = widePushoutPointFundamentalGroupExtend a₀ H φ C hpcC hpcX hnull := by
  intro XL eL aL sL WL wL ιL C hpcC hpcX hnull U p γ hkill g hg
  have hq : Function.Surjective (widePushoutPointFundamentalGroupCoproductMap a₀) :=
    (widePushoutPointFundamentalGroupCoproductMap_surjective_iff
      a₀ C hpcC hpcX hnull).2 hkill
  apply (MonoidHom.cancel_right hq).mp
  rw [widePushoutPointFundamentalGroupExtend_comp_coproductMap
    a₀ H φ C hpcC hpcX hnull]
  apply Monoid.CoprodI.ext_hom
  intro i
  rw [MonoidHom.comp_assoc,
    widePushoutPointFundamentalGroupCoproductMap_comp_of a₀ i,
    Monoid.CoprodI.lift_comp_of]
  exact hg i

end TopCat
