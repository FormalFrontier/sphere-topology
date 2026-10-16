/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homology.Singular.Connectedness
import Mathlib.Analysis.Convex.PathConnected

/-!
# Clients of the zeroth augmentation criteria

The closed unit interval has distinct endpoints and satisfies both criteria
with integer coefficients. The empty and discrete two-point spaces exhibit the
nonemptiness and nonzero-coefficient boundaries. In particular, the integer
coefficient object has an element and is nonzero, while the zero-coefficient
augmentation of the two-point space is invertible despite disconnectedness.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped ZeroObject unitInterval

noncomputable section

namespace SphereTopologyTest

universe u

private theorem integerCoefficients_nonempty_and_not_isZero :
    Nonempty TopCat.singularHomologyIntegerCoefficients.{u} ∧
      ¬ IsZero TopCat.singularHomologyIntegerCoefficients.{u} := by
  refine ⟨⟨ULift.up (0 : ℤ)⟩, ?_⟩
  intro h
  have : Subsingleton TopCat.singularHomologyIntegerCoefficients.{u} :=
    ModuleCat.isZero_iff_subsingleton.mp h
  have h01 :
      (ULift.up (0 : ℤ) : TopCat.singularHomologyIntegerCoefficients.{u}) =
        ULift.up (1 : ℤ) :=
    @Subsingleton.elim TopCat.singularHomologyIntegerCoefficients.{u} this _ _
  exact zero_ne_one (congrArg ULift.down h01)

private theorem interval_criteria :
    (0 : I) ≠ 1 ∧
      IsIso ((TopCat.of I).singularHomology₀ε
        TopCat.singularHomologyIntegerCoefficients.{0}) ∧
      IsZero (TopCat.reducedSingularHomologyZero (TopCat.of I)) := by
  have hI : PathConnectedSpace I :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, unitInterval.zero_mem⟩)
  refine ⟨zero_ne_one, ?_, ?_⟩
  · exact (TopCat.isIso_singularHomology₀ε_iff_pathConnectedSpace
      (TopCat.of I) TopCat.singularHomologyIntegerCoefficients.{0}
      integerCoefficients_nonempty_and_not_isZero.{0}.2).mpr hI
  · exact (TopCat.isZero_reducedSingularHomologyZero_iff_pathConnectedSpace
      (TopCat.of I)).mpr hI

private theorem empty_not_pathConnected : ¬ PathConnectedSpace TopCat.emptySpace.{u} := by
  intro h
  obtain ⟨x⟩ := h.nonempty
  exact x.down.elim

private theorem empty_boundary :
    IsZero (TopCat.reducedSingularHomologyZero TopCat.emptySpace.{u}) ∧
      ¬ IsIso (TopCat.emptySpace.{u}.singularHomology₀ε
        TopCat.singularHomologyIntegerCoefficients.{u}) ∧
      ¬ PathConnectedSpace TopCat.emptySpace.{u} := by
  refine ⟨TopCat.isZero_reducedSingularHomologyZero_empty, ?_, empty_not_pathConnected⟩
  intro h
  let := h
  apply integerCoefficients_nonempty_and_not_isZero.{u}.2
  apply (IsZero.iff_id_eq_zero TopCat.singularHomologyIntegerCoefficients.{u}).mpr
  apply (cancel_epi (TopCat.emptySpace.{u}.singularHomology₀ε
    TopCat.singularHomologyIntegerCoefficients.{u})).1
  apply (cancel_epi (TopCat.emptySpace.{u}.singularHomology₀Iso
    TopCat.singularHomologyIntegerCoefficients.{u}).inv).1
  apply Sigma.hom_ext
  intro c
  induction c using ZerothHomotopy.rec with
  | mk x => exact x.down.elim

private theorem twoPoint_not_pathConnected : ¬ PathConnectedSpace TopCat.twoPointSpace := by
  intro h
  let : PathConnectedSpace TopCat.twoPointSpace := h
  have hcomponents :
      (ZerothHomotopy.mk false : ZerothHomotopy TopCat.twoPointSpace) =
        ZerothHomotopy.mk true := Subsingleton.elim _ _
  have hbool : (false : Bool) = true := by
    calc
      false = TopCat.twoPointZerothHomotopyEquiv
          (ZerothHomotopy.mk false : ZerothHomotopy TopCat.twoPointSpace) :=
        (TopCat.twoPointZerothHomotopyEquiv_mk false).symm
      _ = TopCat.twoPointZerothHomotopyEquiv
          (ZerothHomotopy.mk true : ZerothHomotopy TopCat.twoPointSpace) :=
        congrArg TopCat.twoPointZerothHomotopyEquiv hcomponents
      _ = true := TopCat.twoPointZerothHomotopyEquiv_mk true
  exact Bool.false_ne_true hbool

private theorem twoPoint_boundary :
    ¬ IsZero (TopCat.reducedSingularHomologyZero TopCat.twoPointSpace) ∧
      ¬ IsIso (TopCat.twoPointSpace.singularHomology₀ε
        TopCat.singularHomologyIntegerCoefficients.{0}) ∧
      ¬ PathConnectedSpace TopCat.twoPointSpace := by
  have hred : ¬ IsZero (TopCat.reducedSingularHomologyZero TopCat.twoPointSpace) := by
    intro h
    exact integerCoefficients_nonempty_and_not_isZero.{0}.2
      (h.of_iso TopCat.reducedSingularHomologyZeroTwoPointIso.symm)
  refine ⟨hred, ?_, twoPoint_not_pathConnected⟩
  intro h
  let := h
  exact hred (isZero_kernel_of_mono
    (TopCat.twoPointSpace.singularHomology₀ε TopCat.singularHomologyIntegerCoefficients.{0}))

private theorem twoPoint_zeroCoefficients_augmentation_isIso :
    IsIso (TopCat.twoPointSpace.singularHomology₀ε (0 : ModuleCat.{0, 0} ℤ)) := by
  have hcoprod : IsZero
      (∐ (fun _ : ZerothHomotopy TopCat.twoPointSpace ↦ (0 : ModuleCat.{0, 0} ℤ))) := by
    apply IsColimit.isZero_pt (coproductIsCoproduct _)
    apply Functor.isZero
    intro j
    exact isZero_zero _
  have hH₀ : IsZero
      (((singularHomologyFunctor (ModuleCat.{0, 0} ℤ) 0).obj
        (0 : ModuleCat.{0, 0} ℤ)).obj TopCat.twoPointSpace) :=
    hcoprod.of_iso
      (TopCat.twoPointSpace.singularHomology₀Iso (0 : ModuleCat.{0, 0} ℤ))
  exact hH₀.isIso (isZero_zero _) _

end SphereTopologyTest
