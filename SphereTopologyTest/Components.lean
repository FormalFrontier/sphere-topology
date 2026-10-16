/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homology.Singular.Reduced
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Clients of the nonbasepoint-component presentation

The discrete three-point space based at `0` has two lifted-integer coefficient
summands, with inverse generators `[1] - [0]` and `[2] - [0]`. A separate ordinary
`H₀` coordinate detects a nonzero difference without using the component-kernel
universal property. Path-connected and zero-coefficient boundaries likewise use
only coproduct and point-class APIs. The two-point compatibility uses the
existing false-minus-true basis rather than computing it again.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped ZeroObject

noncomputable section

namespace SphereTopologyTest

private abbrev threePointSpace : TopCat := TopCat.of (Fin 3)

private def threePointComponentsEquiv : ZerothHomotopy threePointSpace ≃ Fin 3 where
  toFun := ZerothHomotopy.lift id
    (fun {_ _} p ↦ TopCat.path_endpoints_eq_of_totallyDisconnected p)
  invFun := ZerothHomotopy.mk
  left_inv c := by induction c using ZerothHomotopy.rec; rfl
  right_inv _ := rfl

@[simp]
private theorem threePointComponentsEquiv_mk (i : threePointSpace) :
    threePointComponentsEquiv (.mk i) = i :=
  threePointComponentsEquiv.apply_symm_apply i

private def threePointNonbaseEquiv :
    Fin 2 ≃ {c : ZerothHomotopy threePointSpace // c ≠ .mk (0 : Fin 3)} :=
  (finSuccAboveEquiv (0 : Fin 3)).trans
    (threePointComponentsEquiv.subtypeEquiv
      (p := fun c ↦ c ≠ .mk (0 : Fin 3)) (q := fun i ↦ i ≠ 0) (fun c ↦ by
      constructor
      · intro hc he
        apply hc
        exact threePointComponentsEquiv.injective he
      · intro hi hc
        apply hi
        rw [hc]
        rfl)).symm

/-- This comparison only combines two summands; it makes no infinite-biproduct
assumption and introduces no rank or freeness theory. -/
private def threePointTwoSummandIso :
    (∐ (fun _ : Fin 2 ↦ TopCat.singularHomologyIntegerCoefficients.{0})) ≅
      TopCat.singularHomologyIntegerCoefficients.{0} ⊞
        TopCat.singularHomologyIntegerCoefficients.{0} where
  hom := Sigma.desc (fun i ↦ if i = 0 then biprod.inl else biprod.inr)
  inv := biprod.desc
    (Sigma.ι (fun _ : Fin 2 ↦ TopCat.singularHomologyIntegerCoefficients.{0}) 0)
    (Sigma.ι (fun _ : Fin 2 ↦ TopCat.singularHomologyIntegerCoefficients.{0}) 1)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    fin_cases i <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> simp

@[reassoc]
private theorem threePointTwoSummandIso_inl_inv :
    biprod.inl ≫ threePointTwoSummandIso.inv =
      Sigma.ι (fun _ : Fin 2 ↦ TopCat.singularHomologyIntegerCoefficients.{0}) 0 := by
  simp [threePointTwoSummandIso]

@[reassoc]
private theorem threePointTwoSummandIso_inr_inv :
    biprod.inr ≫ threePointTwoSummandIso.inv =
      Sigma.ι (fun _ : Fin 2 ↦ TopCat.singularHomologyIntegerCoefficients.{0}) 1 := by
  simp [threePointTwoSummandIso]

/-- The component presentation has two coefficient summands on this discrete
space, not a single surviving summand as in the two-point computation. -/
private def threePointReducedIso :
    TopCat.reducedSingularHomology threePointSpace 0 ≅
      TopCat.singularHomologyIntegerCoefficients.{0} ⊞
        TopCat.singularHomologyIntegerCoefficients.{0} :=
  TopCat.reducedSingularHomologyZeroComponentsIso threePointSpace (0 : Fin 3) ≪≫
    (Sigma.reindex threePointNonbaseEquiv
      (fun _ ↦ TopCat.singularHomologyIntegerCoefficients.{0})).symm ≪≫
    threePointTwoSummandIso

@[reassoc]
private theorem threePointReducedIso_inl_inv :
    biprod.inl ≫ threePointReducedIso.inv =
      Sigma.ι (fun _ : {c : ZerothHomotopy threePointSpace // c ≠ .mk (0 : Fin 3)} ↦
        TopCat.singularHomologyIntegerCoefficients.{0}) (threePointNonbaseEquiv 0) ≫
        (TopCat.reducedSingularHomologyZeroComponentsIso threePointSpace (0 : Fin 3)).inv := by
  calc
    _ = Sigma.ι (fun _ : Fin 2 ↦ TopCat.singularHomologyIntegerCoefficients.{0}) 0 ≫
        (Sigma.reindex threePointNonbaseEquiv
          (fun _ ↦ TopCat.singularHomologyIntegerCoefficients.{0})).hom ≫
        (TopCat.reducedSingularHomologyZeroComponentsIso threePointSpace (0 : Fin 3)).inv := by
      simp only [threePointReducedIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
        threePointTwoSummandIso_inl_inv_assoc]
    _ = _ := Sigma.ι_reindex_hom_assoc threePointNonbaseEquiv
      (fun _ ↦ TopCat.singularHomologyIntegerCoefficients.{0}) (0 : Fin 2) _

@[reassoc]
private theorem threePointReducedIso_inr_inv :
    biprod.inr ≫ threePointReducedIso.inv =
      Sigma.ι (fun _ : {c : ZerothHomotopy threePointSpace // c ≠ .mk (0 : Fin 3)} ↦
        TopCat.singularHomologyIntegerCoefficients.{0}) (threePointNonbaseEquiv 1) ≫
        (TopCat.reducedSingularHomologyZeroComponentsIso threePointSpace (0 : Fin 3)).inv := by
  calc
    _ = Sigma.ι (fun _ : Fin 2 ↦ TopCat.singularHomologyIntegerCoefficients.{0}) 1 ≫
        (Sigma.reindex threePointNonbaseEquiv
          (fun _ ↦ TopCat.singularHomologyIntegerCoefficients.{0})).hom ≫
        (TopCat.reducedSingularHomologyZeroComponentsIso threePointSpace (0 : Fin 3)).inv := by
      simp only [threePointReducedIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
        threePointTwoSummandIso_inr_inv_assoc]
    _ = _ := Sigma.ι_reindex_hom_assoc threePointNonbaseEquiv
      (fun _ ↦ TopCat.singularHomologyIntegerCoefficients.{0}) (1 : Fin 2) _

private theorem threePointReducedIso_inl_inv_toOrdinary :
    biprod.inl ≫ threePointReducedIso.inv ≫
        TopCat.reducedSingularHomologyZeroToOrdinary threePointSpace =
      TopCat.singularHomologyZeroPoint threePointSpace (1 : Fin 3) -
        TopCat.singularHomologyZeroPoint threePointSpace (0 : Fin 3) := by
  exact (threePointReducedIso_inl_inv_assoc
    (TopCat.reducedSingularHomologyZeroToOrdinary threePointSpace)).trans
      (TopCat.ι_reducedSingularHomologyZeroComponentsIso_inv_toOrdinary_point
        threePointSpace (0 : Fin 3) (1 : Fin 3) (threePointNonbaseEquiv 0).property)

private theorem threePointReducedIso_inr_inv_toOrdinary :
    biprod.inr ≫ threePointReducedIso.inv ≫
        TopCat.reducedSingularHomologyZeroToOrdinary threePointSpace =
      TopCat.singularHomologyZeroPoint threePointSpace (2 : Fin 3) -
        TopCat.singularHomologyZeroPoint threePointSpace (0 : Fin 3) := by
  exact (threePointReducedIso_inr_inv_assoc
    (TopCat.reducedSingularHomologyZeroToOrdinary threePointSpace)).trans
      (TopCat.ι_reducedSingularHomologyZeroComponentsIso_inv_toOrdinary_point
        threePointSpace (0 : Fin 3) (2 : Fin 3) (threePointNonbaseEquiv 1).property)

/-- A coordinate on ordinary homology, independent of the new kernel witness. -/
private def threePointFirstCoordinate :
    (integralSingularHomologyFunctor 0).obj threePointSpace ⟶
      TopCat.singularHomologyIntegerCoefficients.{0} :=
  (threePointSpace.singularHomology₀Iso TopCat.singularHomologyIntegerCoefficients.{0}).hom ≫
    Sigma.desc (fun c ↦ if threePointComponentsEquiv c = 1 then 𝟙 _ else 0)

private theorem threePoint_first_difference_coordinate :
    (TopCat.singularHomologyZeroPoint threePointSpace (1 : Fin 3) -
        TopCat.singularHomologyZeroPoint threePointSpace (0 : Fin 3)) ≫
        threePointFirstCoordinate = 𝟙 TopCat.singularHomologyIntegerCoefficients.{0} := by
  simp [threePointFirstCoordinate, Preadditive.sub_comp,
    TopCat.singularHomologyZeroPoint_homology₀Iso_assoc]
  let φ : Fin 3 → (TopCat.singularHomologyIntegerCoefficients.{0} ⟶
      TopCat.singularHomologyIntegerCoefficients.{0}) :=
    fun i ↦ if i = 1 then 𝟙 _ else 0
  have h := congrArg₂
    (fun f g : TopCat.singularHomologyIntegerCoefficients.{0} ⟶
        TopCat.singularHomologyIntegerCoefficients.{0} ↦ f - g)
    (congrArg φ (threePointComponentsEquiv_mk (1 : threePointSpace)))
    (congrArg φ (threePointComponentsEquiv_mk (0 : threePointSpace)))
  exact h.trans (by simp [φ])

/-- The ordinary difference is nonzero without invoking the component-kernel
universal property or an isomorphism constructed from it. -/
private theorem threePoint_first_difference_ne_zero :
    TopCat.singularHomologyZeroPoint threePointSpace (1 : Fin 3) -
        TopCat.singularHomologyZeroPoint threePointSpace (0 : Fin 3) ≠ 0 := by
  intro h
  have hid : (𝟙 TopCat.singularHomologyIntegerCoefficients.{0}) =
      (0 : TopCat.singularHomologyIntegerCoefficients.{0} ⟶
        TopCat.singularHomologyIntegerCoefficients.{0}) := by
    rw [← threePoint_first_difference_coordinate, h, zero_comp]
  have hone : (1 : ℤ) = 0 :=
    congrArg (fun f : TopCat.singularHomologyIntegerCoefficients.{0} ⟶
      TopCat.singularHomologyIntegerCoefficients.{0} ↦ (f (ULift.up (1 : ℤ))).down) hid
  exact one_ne_zero hone

private theorem twoPoint_false_component_ne_true :
    (ZerothHomotopy.mk false : ZerothHomotopy TopCat.twoPointSpace) ≠ .mk true := by
  intro h
  have hf : TopCat.twoPointZerothHomotopyEquiv
      (ZerothHomotopy.mk false : ZerothHomotopy TopCat.twoPointSpace) = false :=
    TopCat.twoPointZerothHomotopyEquiv_mk false
  have ht : TopCat.twoPointZerothHomotopyEquiv
      (ZerothHomotopy.mk true : ZerothHomotopy TopCat.twoPointSpace) = true :=
    TopCat.twoPointZerothHomotopyEquiv_mk true
  have h' : false = true :=
    hf.symm.trans ((congrArg TopCat.twoPointZerothHomotopyEquiv h).trans ht)
  cases h'

/-- Basepoint `true` recovers the existing inverse basis, not its negative.
The codomain is compared through the existing nonnegative-to-kernel isomorphism. -/
private theorem twoPoint_component_inverse_compatibility :
    Sigma.ι (fun _ : {c : ZerothHomotopy TopCat.twoPointSpace // c ≠ .mk true} ↦
        TopCat.singularHomologyIntegerCoefficients.{0})
        ⟨.mk false, twoPoint_false_component_ne_true⟩ ≫
        (TopCat.reducedSingularHomologyZeroComponentsIso TopCat.twoPointSpace true).inv ≫
        (TopCat.reducedSingularHomologyZeroIso TopCat.twoPointSpace).hom =
      TopCat.reducedSingularHomologyZeroTwoPointIso.inv := by
  apply (cancel_mono (TopCat.reducedSingularHomologyZeroι TopCat.twoPointSpace)).1
  simp only [Category.assoc]
  change Sigma.ι _ ⟨.mk false, twoPoint_false_component_ne_true⟩ ≫
      (TopCat.reducedSingularHomologyZeroComponentsIso TopCat.twoPointSpace true).inv ≫
      TopCat.reducedSingularHomologyZeroToOrdinary TopCat.twoPointSpace =
    TopCat.twoPointReducedBasis ≫ TopCat.reducedSingularHomologyZeroι TopCat.twoPointSpace
  rw [TopCat.ι_reducedSingularHomologyZeroComponentsIso_inv_toOrdinary_point,
    TopCat.twoPointReducedBasis_ι]
  rfl

universe w v u

/-- A based path-connected space has no nonbasepoint path components. This is
about path components, not deletion of one point from the underlying space. -/
private theorem pathConnected_nonbase_index_empty (X : TopCat.{w})
    [PathConnectedSpace X] (x : X) :
    IsEmpty {c : ZerothHomotopy X // c ≠ .mk x} :=
  ⟨fun c ↦ c.property (Subsingleton.elim _ _)⟩

/-- The empty index gives a zero coproduct without using the new kernel witness. -/
private theorem pathConnected_component_coproduct_isZero
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    (X : TopCat.{w}) [PathConnectedSpace X] (R : C) (x : X) :
    IsZero (∐ (fun _ : {c : ZerothHomotopy X // c ≠ .mk x} ↦ R)) := by
  let := pathConnected_nonbase_index_empty X x
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro c
  exact isEmptyElim c

private theorem threePoint_zeroCoefficient_coproduct_isZero :
    IsZero (∐ (fun _ : {c : ZerothHomotopy threePointSpace // c ≠ .mk (0 : Fin 3)} ↦
      (0 : ModuleCat.{0} ℤ))) := by
  apply IsColimit.isZero_pt (coproductIsCoproduct _)
  apply Functor.isZero
  intro j
  exact isZero_zero (ModuleCat.{0} ℤ)

/-- Zero coefficients are allowed even for the disconnected three-point space;
the inclusion is then zero, independently of its kernel universal property. -/
private theorem threePoint_zeroCoefficient_inclusion_eq_zero :
    TopCat.singularHomologyZeroComponentInclusion threePointSpace
      (0 : ModuleCat.{0} ℤ) (0 : Fin 3) = 0 :=
  threePoint_zeroCoefficient_coproduct_isZero.eq_of_src _ _

end SphereTopologyTest
