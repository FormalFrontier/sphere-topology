/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Topology.SingularLifts

/-!
# Covering-space lift examples

The discrete projection from two points to one point has two distinct constant
lifts in every degree. The zeroth face of an edge omits its zeroth vertex;
a degeneracy raises dimension. Both operators have unique preimages for each
constant sheet. Identity maps and the covering with empty total space give
the one-lift and empty-lift boundaries.
-/

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

namespace SphereTopologyTest

private abbrev twoSheetTotal : TopCat := TopCat.of (Fin 2)
private abbrev pointBase : TopCat := TopCat.of PUnit

private def twoSheetProjection : twoSheetTotal ⟶ pointBase :=
  TopCat.ofHom (ContinuousMap.const _ PUnit.unit)

private theorem twoSheetProjection_covering : IsCoveringMap twoSheetProjection :=
  IsCoveringMap.of_discreteTopology _

private theorem twoSheetProjection_equifibered :
    NatTrans.Equifibered (TopCat.toSSet.map twoSheetProjection) :=
  twoSheetProjection_covering.toSSet_map_equifibered

private def pointSimplex (k : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj pointBase).obj k :=
  (pointBase.toSSetObjEquiv k).symm (ContinuousMap.const _ PUnit.unit)

private def sheetSimplex (k : SimplexCategoryᵒᵖ) (i : Fin 2) :
    (TopCat.toSSet.obj twoSheetTotal).obj k :=
  (twoSheetTotal.toSSetObjEquiv k).symm (ContinuousMap.const _ i)

private def sheetLift (k : SimplexCategoryᵒᵖ) (i : Fin 2) :
    {u : (TopCat.toSSet.obj twoSheetTotal).obj k //
      (TopCat.toSSet.map twoSheetProjection).app k u = pointSimplex k} :=
  ⟨sheetSimplex k i, by
    apply (pointBase.toSSetObjEquiv k).injective
    ext x⟩

private theorem sheetLift_value (k : SimplexCategoryᵒᵖ) (i : Fin 2)
    (x : StdSimplex ℝ (Fin (k.unop.len + 1))) :
    twoSheetTotal.toSSetObjEquiv k (sheetLift k i).val x = i := by
  simp [sheetLift, sheetSimplex]

private theorem two_constant_lifts_distinct (k : SimplexCategoryᵒᵖ) :
    sheetLift k 0 ≠ sheetLift k 1 := by
  intro h
  have hval : (sheetLift k 0).val = (sheetLift k 1).val := congrArg Subtype.val h
  have heval :
      twoSheetTotal.toSSetObjEquiv k (sheetLift k 0).val (.single 0) =
        twoSheetTotal.toSSetObjEquiv k (sheetLift k 1).val (.single 0) :=
    congrArg (fun u : (TopCat.toSSet.obj twoSheetTotal).obj k =>
      twoSheetTotal.toSSetObjEquiv k u (.single 0)) hval
  have h01 : (0 : Fin 2) = 1 := calc
    0 = twoSheetTotal.toSSetObjEquiv k (sheetLift k 0).val (.single 0) :=
      (sheetLift_value k 0 (.single 0)).symm
    _ = twoSheetTotal.toSSetObjEquiv k (sheetLift k 1).val (.single 0) := heval
    _ = 1 := sheetLift_value k 1 (.single 0)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

private def sheetPoint (k : SimplexCategoryᵒᵖ)
    (x : StdSimplex ℝ (Fin (k.unop.len + 1))) (i : Fin 2) :
    {y : twoSheetTotal //
      twoSheetProjection y = pointBase.toSSetObjEquiv k (pointSimplex k) x} :=
  ⟨i, by simp [twoSheetProjection, pointSimplex]⟩

private theorem inverse_evaluation_is_constant_sheet (k : SimplexCategoryᵒᵖ)
    (x : StdSimplex ℝ (Fin (k.unop.len + 1))) (i : Fin 2) :
    (twoSheetProjection_covering.singularLiftEquiv k (pointSimplex k) x).symm
      (sheetPoint k x i) = sheetLift k i := by
  apply (twoSheetProjection_covering.singularLiftEquiv k (pointSimplex k) x).injective
  apply Subtype.ext
  have hsheet :
      ((twoSheetProjection_covering.singularLiftEquiv k (pointSimplex k) x)
        (sheetLift k i)).val = i :=
    (IsCoveringMap.singularLiftEquiv_apply twoSheetProjection_covering
      k (pointSimplex k) x (sheetLift k i)).trans (sheetLift_value k i x)
  exact (congrArg Subtype.val
    ((twoSheetProjection_covering.singularLiftEquiv k (pointSimplex k) x).apply_symm_apply
      (sheetPoint k x i))).trans hsheet.symm

private theorem restrict_constant_sheet {k l : SimplexCategoryᵒᵖ}
    (α : k ⟶ l) (i : Fin 2) :
    (TopCat.singularLiftRestrict twoSheetProjection α (pointSimplex k)
      (sheetLift k i)).val = sheetSimplex l i := by
  apply (twoSheetTotal.toSSetObjEquiv l).injective
  apply ContinuousMap.ext
  intro x
  have hconst : twoSheetTotal.toSSetObjEquiv l (sheetSimplex l i) x = i :=
    congrArg
      (fun f : C(StdSimplex ℝ (Fin (l.unop.len + 1)), twoSheetTotal) => f x)
      ((twoSheetTotal.toSSetObjEquiv l).apply_symm_apply (ContinuousMap.const _ i))
  exact (congrArg
    (fun u : (TopCat.toSSet.obj twoSheetTotal).obj l => twoSheetTotal.toSSetObjEquiv l u x)
    (TopCat.singularLiftRestrict_val twoSheetProjection α (pointSimplex k)
      (sheetLift k i))).trans
    ((TopCat.toSSetObjEquiv_naturality_apply α.unop (sheetLift k i).val x).trans
      ((sheetLift_value k i (StdSimplex.map α.unop x)).trans hconst.symm))

private theorem unique_constant_sheet_preimage {k l : SimplexCategoryᵒᵖ}
    (α : k ⟶ l) (i : Fin 2) :
    ∃! u : {u : (TopCat.toSSet.obj twoSheetTotal).obj k //
        (TopCat.toSSet.map twoSheetProjection).app k u = pointSimplex k},
      (TopCat.singularLiftRestrict twoSheetProjection α (pointSimplex k) u).val =
        sheetSimplex l i := by
  refine ⟨sheetLift k i, restrict_constant_sheet α i, ?_⟩
  intro u hu
  apply (twoSheetProjection_covering.bijective_singularLiftRestrict α (pointSimplex k)).injective
  apply Subtype.ext
  exact hu.trans (restrict_constant_sheet α i).symm

private theorem face_zero_moves_vertex :
    StdSimplex.map (SimplexCategory.δ (0 : Fin 2)) (.single (0 : Fin 1)) =
      (.single (1 : Fin 2) : StdSimplex ℝ (Fin 2)) := by
  have hδ : (SimplexCategory.δ (0 : Fin 2)) (0 : Fin 1) = (1 : Fin 2) := rfl
  exact (StdSimplex.map_single (R := ℝ) (0 : Fin 1)
    (SimplexCategory.δ (0 : Fin 2))).trans
      (congrArg (StdSimplex.single (R := ℝ)) hδ)

private theorem face_zero_unique_sheet (i : Fin 2) :
    ∃! u : {u : (TopCat.toSSet.obj twoSheetTotal).obj (op ⦋1⦌) //
        (TopCat.toSSet.map twoSheetProjection).app (op ⦋1⦌) u = pointSimplex (op ⦋1⦌)},
      (TopCat.singularLiftRestrict twoSheetProjection
        (SimplexCategory.δ (0 : Fin 2)).op (pointSimplex (op ⦋1⦌)) u).val =
          sheetSimplex (op ⦋0⦌) i :=
  unique_constant_sheet_preimage (SimplexCategory.δ (0 : Fin 2)).op i

private theorem degeneracy_zero_unique_sheet (i : Fin 2) :
    ∃! u : {u : (TopCat.toSSet.obj twoSheetTotal).obj (op ⦋0⦌) //
        (TopCat.toSSet.map twoSheetProjection).app (op ⦋0⦌) u = pointSimplex (op ⦋0⦌)},
      (TopCat.singularLiftRestrict twoSheetProjection
        (SimplexCategory.σ (0 : Fin 1)).op (pointSimplex (op ⦋0⦌)) u).val =
          sheetSimplex (op ⦋1⦌) i :=
  unique_constant_sheet_preimage (SimplexCategory.σ (0 : Fin 1)).op i

private theorem twoSheet_lifts_finite (k : SimplexCategoryᵒᵖ) :
    Finite {u : (TopCat.toSSet.obj twoSheetTotal).obj k //
      (TopCat.toSSet.map twoSheetProjection).app k u = pointSimplex k} :=
  twoSheetProjection_covering.finite_singularLift k (pointSimplex k) (.single 0)

private theorem identity_lift_unique {X : TopCat} (k : SimplexCategoryᵒᵖ)
    (s : (TopCat.toSSet.obj X).obj k) :
    ∃! u : {u : (TopCat.toSSet.obj X).obj k //
      (TopCat.toSSet.map (𝟙 X)).app k u = s}, u.val = s := by
  refine ⟨⟨s, by simp⟩, rfl, ?_⟩
  intro u hu
  exact Subtype.ext hu

private abbrev emptyTotal : TopCat := TopCat.of Empty

private def emptyProjection : emptyTotal ⟶ pointBase :=
  TopCat.ofHom (ContinuousMap.const _ PUnit.unit)

private theorem emptyProjection_covering : IsCoveringMap emptyProjection :=
  IsCoveringMap.of_isEmpty _

private theorem empty_lift_fiber (k : SimplexCategoryᵒᵖ) :
    IsEmpty {u : (TopCat.toSSet.obj emptyTotal).obj k //
      (TopCat.toSSet.map emptyProjection).app k u = pointSimplex k} :=
  ⟨fun u => (emptyTotal.toSSetObjEquiv k u.val (.single 0)).elim⟩

end SphereTopologyTest
