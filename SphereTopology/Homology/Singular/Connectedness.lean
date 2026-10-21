/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homology.Singular.Reduced

import Mathlib.Analysis.Convex.PathConnected

/-!
# Zeroth singular augmentation and path connectedness

The total augmentation `H₀(X; R) ⟶ R` detects path connectedness when the
coefficient object `R` is nonzero. The statement concerns this particular map,
not merely the existence of an abstract isomorphism `H₀(X; R) ≅ R`.

For integer coefficients, vanishing of reduced degree-zero homology detects
path connectedness provided the space is nonempty. Reduced degree zero here is
the kernel of the augmentation in the nonnegative theory: there is no degree
minus one term repairing the empty-space case. In particular, the empty space has
zero reduced `H₀`, even though its augmentation to a nonzero coefficient object
is not invertible.

These statements use Mathlib's component-coproduct description and augmentation
of singular `H₀`, formalized by Joël Riou, and the integral augmentation-kernel
interface of `SphereTopology.Homology.Singular.Reduced`.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 13, §2 and
  Chapter 15, §2, for the path-component description of reduced degree-zero
  integral homology. The convention here is the unbased nonnegative
  augmentation kernel; no comparison with based relative reduced homology or
  normalized chains is asserted.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

namespace TopCat

/-- A nonzero constant coproduct can fold isomorphically only over a singleton index. -/
private theorem nonempty_subsingleton_of_isIso_sigma_desc_id
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (ι : Type w) (R : C) [HasCoproduct (fun _ : ι ↦ R)]
    (hR : ¬ IsZero R) [IsIso (Sigma.desc (fun _ : ι ↦ 𝟙 R))] :
    Nonempty ι ∧ Subsingleton ι := by
  classical
  have hn : Nonempty ι := by
    by_contra hn
    apply hR
    apply (IsZero.iff_id_eq_zero R).mpr
    apply (cancel_epi (Sigma.desc (fun _ : ι ↦ 𝟙 R))).1
    apply Sigma.hom_ext
    intro i
    exact (hn ⟨i⟩).elim
  refine ⟨hn, ⟨?_⟩⟩
  intro i j
  by_contra hij
  have hι : Sigma.ι (fun _ : ι ↦ R) i = Sigma.ι (fun _ : ι ↦ R) j := by
    apply (cancel_mono (Sigma.desc (fun _ : ι ↦ 𝟙 R))).1
    simp
  have hid : 𝟙 R = (0 : R ⟶ R) := by
    simpa only [Sigma.ι_π_eq_id, Sigma.ι_π_of_ne _ (Ne.symm hij)] using
      congrArg (fun f ↦ f ≫ Sigma.π (fun _ : ι ↦ R) i) hι
  exact hR ((IsZero.iff_id_eq_zero R).mpr hid)

/-- With a nonzero coefficient object, the total zeroth singular augmentation
is invertible exactly when the space is path connected. Path connectedness
includes nonemptiness, which is a conclusion rather than an assumption here.
The nonzero hypothesis is essential: with zero coefficients, the augmentation
is invertible even for empty or disconnected spaces. -/
theorem isIso_singularHomology₀ε_iff_pathConnectedSpace
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Preadditive C] [CategoryWithHomology C]
    (X : TopCat.{w}) (R : C) (hR : ¬ IsZero R) :
    IsIso (X.singularHomology₀ε R) ↔ PathConnectedSpace X := by
  constructor
  · intro h
    have hcomp : IsIso ((X.singularHomology₀Iso R).hom ≫
        Sigma.desc (fun _ : ZerothHomotopy X ↦ 𝟙 R)) := by
      simpa only [singularHomology₀Iso_sigma_desc_id] using h
    have : IsIso (Sigma.desc (fun _ : ZerothHomotopy X ↦ 𝟙 R)) := by
      simpa only [isIso_comp_left_iff] using hcomp
    exact pathConnectedSpace_iff_zerothHomotopy.mpr
      (nonempty_subsingleton_of_isIso_sigma_desc_id (ZerothHomotopy X) R hR)
  · intro h
    let : PathConnectedSpace X := h
    infer_instance

/-- A nonempty space has zero reduced degree-zero integer singular homology
exactly when it is path connected. Nonemptiness is essential because reduced
`H₀` is the augmentation kernel, which also vanishes on the empty space under
the nonnegative convention; no degree minus one term is added. Compare May,
*A Concise Course in Algebraic Topology*, Chapter 13, §2 and Chapter 15, §2,
for the based reduced path-component calculation. -/
theorem isZero_reducedSingularHomologyZero_iff_pathConnectedSpace
    (X : TopCat.{w}) [Nonempty X] :
    IsZero (TopCat.reducedSingularHomologyZero X) ↔ PathConnectedSpace X := by
  constructor
  · intro h
    obtain ⟨x⟩ := ‹Nonempty X›
    let : Mono (X.singularHomology₀ε singularHomologyIntegerCoefficients) :=
      (Preadditive.mono_iff_isZero_kernel _).2 h
    let : IsSplitEpi (X.singularHomology₀ε singularHomologyIntegerCoefficients) :=
      IsSplitEpi.mk'
        { section_ := singularHomologyZeroPoint X x
          id := singularHomologyZeroPoint_augmentation X x }
    let : IsIso (X.singularHomology₀ε singularHomologyIntegerCoefficients) :=
      isIso_of_mono_of_isSplitEpi _
    have hR : ¬ IsZero (singularHomologyIntegerCoefficients.{w}) := by
      rw [ModuleCat.isZero_iff_subsingleton]
      exact not_subsingleton_iff_nontrivial.mpr inferInstance
    exact (isIso_singularHomology₀ε_iff_pathConnectedSpace
      X singularHomologyIntegerCoefficients hR).mp inferInstance
  · intro h
    let : PathConnectedSpace X := h
    exact isZero_reducedSingularHomologyZero_of_pathConnected X

end TopCat

end

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

end
