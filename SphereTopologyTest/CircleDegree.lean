/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homotopy.CircleDegree

/-!
# Circle degree examples

The square map tests degree on a nonidentity, nonconstant continuous self-map.
Its coefficient is computed from the transported positive loop and the integer
calculator. Identity and a constant at minus one give boundary computations.
The degree API computes composition and signed powers, distinguishes free homotopy
classes and supplies a fixed point for the square map. Rotation by minus one is
freely homotopic to identity, but is not based at one and has no fixed points.
-/

noncomputable section

namespace SphereTopologyTest

private theorem transport_path_of_eq {x : Circle} (h : x = 1)
    (γ : FundamentalGroup Circle x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (Circle.path x 1) γ =
      FundamentalGroup.fromPath (γ.toPath.cast h.symm h.symm) := by
  subst x
  rw [Circle.path_self]
  change (Path.Homotopic.Quotient.refl (1 : Circle)).trans
      (γ.toPath.trans (Path.Homotopic.Quotient.refl (1 : Circle))) =
    γ.toPath.cast rfl rfl
  simp only [Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.cast_rfl_rfl]

private def mapSquare : C(Circle, Circle) :=
  (ContinuousMap.id Circle) ^ (2 : ℕ)

private theorem mapSquare_fixed_one : mapSquare 1 = 1 := by
  simp only [mapSquare, ContinuousMap.pow_apply, ContinuousMap.id_apply, one_pow]

private theorem mapSquare_loop :
    ((Circle.loop 1).map mapSquare.continuous).cast
        mapSquare_fixed_one.symm mapSquare_fixed_one.symm = Circle.loop 2 := by
  apply Path.ext
  funext t
  change (Circle.loop 1 t) ^ (2 : ℕ) = Circle.loop 2 t
  rw [Circle.loop_apply, Circle.loop_apply, ← Circle.exp_natCast_mul]
  congr 1
  norm_num
  ring

private theorem mapSquare_degree : Circle.degree mapSquare = 2 := by
  rw [Circle.degree_def, Circle.fundamentalGroupEquivInt_symm_apply,
    transport_path_of_eq mapSquare_fixed_one]
  change (Circle.fundamentalGroupEquivInt
    (FundamentalGroup.fromPath
      ⟦((Circle.loop 1).map mapSquare.continuous).cast
        mapSquare_fixed_one.symm mapSquare_fixed_one.symm⟧)).toAdd = 2
  rw [mapSquare_loop, Circle.fundamentalGroupEquivInt_loop]
  rfl

private theorem mapSquare_degree_ne_one : Circle.degree mapSquare ≠ 1 := by
  rw [mapSquare_degree]
  norm_num

private theorem mapSquare_ne_id : mapSquare ≠ ContinuousMap.id Circle := by
  intro h
  have he := congrArg (fun f : C(Circle, Circle) ↦ f (-1)) h
  have hneg : (1 : Circle) = -1 := by
    simpa only [mapSquare, ContinuousMap.pow_apply, ContinuousMap.mul_apply,
      ContinuousMap.id_apply, pow_two, neg_mul_neg, one_mul] using he
  exact Circle.neg_ne_self (1 : Circle) hneg.symm

private theorem mapSquare_ne_const (c : Circle) :
    mapSquare ≠ ContinuousMap.const Circle c := by
  intro h
  have hc : c = 1 := by
    simpa only [mapSquare, ContinuousMap.pow_apply, ContinuousMap.id_apply,
      one_pow, ContinuousMap.const_apply] using
      (congrArg (fun f : C(Circle, Circle) ↦ f 1) h).symm
  have ht : mapSquare (Circle.exp (Real.pi / 2)) = 1 := by
    simpa only [ContinuousMap.const_apply, hc] using
      congrArg (fun f : C(Circle, Circle) ↦ f (Circle.exp (Real.pi / 2))) h
  apply Circle.exp_pi_ne_one
  calc
    Circle.exp Real.pi = (Circle.exp (Real.pi / 2)) ^ (2 : ℕ) := by
      rw [← Circle.exp_natCast_mul]
      congr 1
      norm_num
      ring
    _ = 1 := ht

private theorem identity_degree : Circle.degree (ContinuousMap.id Circle) = 1 := by
  rw [Circle.degree_def, Circle.fundamentalGroupEquivInt_symm_apply,
    transport_path_of_eq (show ContinuousMap.id Circle 1 = 1 from rfl)]
  change (Circle.fundamentalGroupEquivInt
    (FundamentalGroup.fromPath ⟦(Circle.loop 1).map continuous_id⟧)).toAdd = 1
  rw [Path.map_id, Circle.fundamentalGroupEquivInt_loop]
  rfl

private def constantNegOne : C(Circle, Circle) :=
  ContinuousMap.const Circle (-1)

private theorem constantNegOne_not_based : constantNegOne 1 ≠ 1 :=
  Circle.neg_ne_self (1 : Circle)

private theorem constantNegOne_degree : Circle.degree constantNegOne = 0 := by
  have hm : FundamentalGroup.map constantNegOne 1
      (FundamentalGroup.fromPath ⟦Circle.loop 1⟧) =
        (1 : FundamentalGroup Circle (constantNegOne 1)) := by
    change Path.Homotopic.Quotient.mk ((Circle.loop 1).map constantNegOne.continuous) =
      Path.Homotopic.Quotient.mk (Path.refl (-1))
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    rfl
  rw [Circle.degree_def, Circle.fundamentalGroupEquivInt_symm_apply, hm]
  simp only [map_one]
  rfl

private def rotation : C(Circle, Circle) :=
  -(ContinuousMap.id Circle)

private theorem rotation_not_based : rotation 1 ≠ 1 :=
  Circle.neg_ne_self (1 : Circle)

private theorem rotation_no_fixedPoint : ¬ ∃ z : Circle, rotation z = z := by
  rintro ⟨z, hz⟩
  exact Circle.neg_ne_self z hz

private theorem mapSquare_coordinate (a : Path (mapSquare 1) 1) :
    Circle.fundamentalGroupEquivInt
        (FundamentalGroup.fundamentalGroupMulEquivOfPath a
          (FundamentalGroup.map mapSquare 1
            (Circle.fundamentalGroupEquivInt.symm (Multiplicative.ofAdd (-3))))) =
      Multiplicative.ofAdd (-6) := by
  norm_num only [Circle.fundamentalGroupEquivInt_map, mapSquare_degree]

private theorem mapSquare_comp_degree :
    Circle.degree (mapSquare.comp mapSquare) = 4 := by
  norm_num only [Circle.degree_comp, mapSquare_degree]

private theorem inversion_degree :
    Circle.degree ((ContinuousMap.id Circle) ^ (-1 : ℤ)) = -1 :=
  Circle.degree_zpow (-1)

private theorem constantNegOne_homotopic_zpow_zero :
    constantNegOne.Homotopic ((ContinuousMap.id Circle) ^ (0 : ℤ)) := by
  apply (Circle.homotopic_iff_degree_eq _ _).mpr
  exact (Circle.degree_const (-1)).trans (Circle.degree_zpow 0).symm

private theorem mapSquare_not_homotopic_id :
    ¬ mapSquare.Homotopic (ContinuousMap.id Circle) := by
  intro h
  apply mapSquare_degree_ne_one
  exact ((Circle.homotopic_iff_degree_eq _ _).mp h).trans Circle.degree_id

private theorem mapSquare_has_fixedPoint : ∃ z : Circle, mapSquare z = z :=
  Circle.exists_fixedPoint_of_degree_ne_one mapSquare mapSquare_degree_ne_one

private def rotationHomotopy : rotation.Homotopy (ContinuousMap.id Circle) where
  toFun q := Circle.path (-1) 1 q.1 * q.2
  continuous_toFun :=
    ((Circle.path (-1) 1).continuous.comp continuous_fst).mul continuous_snd
  map_zero_left z := by
    change Circle.path (-1) 1 0 * z = -z
    rw [(Circle.path (-1) 1).source, neg_mul, one_mul]
  map_one_left z := by
    change Circle.path (-1) 1 1 * z = z
    rw [(Circle.path (-1) 1).target, one_mul]

private theorem degree_one_fixedPoint_examples :
    Circle.degree (ContinuousMap.id Circle) = 1 ∧
      (∃ z : Circle, ContinuousMap.id Circle z = z) ∧
      Circle.degree rotation = 1 ∧ ¬ ∃ z : Circle, rotation z = z := by
  refine ⟨Circle.degree_id, ⟨1, rfl⟩, ?_, rotation_no_fixedPoint⟩
  exact (Circle.degree_eq_of_homotopic ⟨rotationHomotopy⟩).trans Circle.degree_id

end SphereTopologyTest
