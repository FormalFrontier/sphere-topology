/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.CircleBouquet
public import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Data.Int.Cast.Lemmas
import SphereTopology.Homotopy.Sphere
import SphereTopology.Topology.WidePushout.FundamentalGroupKernel
import SphereTopology.Topology.WidePushout.OpenNeighborhood
import SphereTopology.Topology.WidePushout.PointLift
import SphereTopology.Topology.WidePushoutPointHomotopy

/-!
# Free generators for circle-bouquet fundamental groups

`CircleBouquet.generatorMap` identifies the free group on the circle labels with
`FundamentalGroup (CircleBouquet.space I) (CircleBouquet.basepoint I)`.
`CircleBouquet.generatorEquiv` retains this homomorphism, sending each free
generator to the included counterclockwise circle class. Its inverse records
that class as the corresponding free generator. No inversion is inserted.

`CircleBouquet.lift` gives the free-group universal property for group targets
whose universe is independent of both bouquet universes. Distinct included
positive generators do not commute. The index family may be arbitrary or empty;
the common point in the empty bouquet is retained.

The fundamental group uses endomorphism multiplication: `p * q = q.trans p`.
Thus the right loop is traversed first in a product. These concrete circle-bouquet
results do not assert a free-product computation from ordinary contractibility
for a general family of based spaces.

The proof uses a punctured-circle core and charts consisting of one whole circle
and that core. Relative puncture contractions kill the chart-collapse kernels,
so the original circle inclusions generate the fundamental group. Positively
normalized circle coordinates then identify this group with the free group.
The inverse of `generatorEquiv` is the inverse furnished by `MulEquiv.ofBijective`,
not an algorithm selecting geometric words from loops.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8, p. 19,
  for the circle-bouquet fundamental-group computation.
* The existing circle coordinates and positive-loop normalization in Fundamental
  Groupoids, and Mathlib's free-group and multiplicative-equivalence APIs.
* The project's point-relative sphere contractions, point-wide-pushout
  neighborhood, descent and original-inclusion fundamental-group APIs.
-/

@[expose] public section

noncomputable section

universe u v w w'

open CategoryTheory CategoryTheory.Limits

namespace CircleBouquetGeometryData

private abbrev X0 (I : Type v) : I → TopCat.{max u v} :=
  fun _ ↦ TopCat.of (ULift.{max u v} Circle)

private abbrev a0 (I : Type v) : ∀ i, X0.{u, v} I i := fun _ ↦ ULift.up (1 : Circle)

private abbrev XL (I : Type v) : I → TopCat.{max u v} :=
  fun i ↦ TopCat.uliftFunctor.{v, max u v}.obj (X0.{u, v} I i)

private abbrev eL (I : Type v) (i : I) : X0.{u, v} I i ≃ₜ XL.{u, v} I i :=
  (X0.{u, v} I i).uliftFunctorObjHomeo

private abbrev aL (I : Type v) : ∀ i, XL.{u, v} I i :=
  fun i ↦ eL.{u, v} I i (a0.{u, v} I i)

private abbrev sL (I : Type v) (i : I) :
    TopCat.of PUnit.{max u v + 1} ⟶ XL.{u, v} I i :=
  TopCat.const (aL.{u, v} I i)

private abbrev W (I : Type v) : TopCat.{max u v} :=
  widePushout (TopCat.of PUnit.{max u v + 1}) (XL.{u, v} I) (sL.{u, v} I)

private theorem W_raw (I : Type v) :
    W.{u, v} I =
      (widePushout (TopCat.of PUnit.{max u v + 1})
        (fun _ : I ↦ TopCat.of (ULift.{v} (ULift.{max u v} Circle)))
        (fun _ ↦ TopCat.const (ULift.up (ULift.up (1 : Circle)))) :
          TopCat.{max u v}) := rfl

-- The original-circle characteristic map of the lifted diagram.
private def originalCircleInclusion (I : Type v) (i : I) : C(Circle, W.{u, v} I) :=
  (WidePushout.ι (sL.{u, v} I) i).hom.comp
    ((eL.{u, v} I i : C(X0.{u, v} I i, XL.{u, v} I i)).comp
      ((Homeomorph.ulift.{max u v, 0} (X := Circle)).symm :
        C(Circle, ULift.{max u v} Circle)))

private theorem originalCircleInclusion_basepoint (I : Type v) (i : I) :
    originalCircleInclusion.{u, v} I i 1 =
      WidePushout.head (sL.{u, v} I) PUnit.unit :=
  TopCat.widePushout_point_ι_point (aL.{u, v} I) i

-- Both universe transports are existing homeomorphisms; no raw target ι is used.
private def comparisonFactor (I : Type v) (i : I) :
    C(XL.{u, v} I i, CircleBouquet.space.{u, v} I) :=
  (CircleBouquet.inclusion.{u, v} i).comp
    ((Homeomorph.ulift.{max u v, 0} (X := Circle) :
        C(ULift.{max u v} Circle, Circle)).comp
      ((eL.{u, v} I i).symm : C(XL.{u, v} I i, X0.{u, v} I i)))

private theorem comparisonFactor_basepoint (I : Type v) (i : I) :
    comparisonFactor.{u, v} I i (aL.{u, v} I i) =
      CircleBouquet.basepoint.{u, v} I := by
  change CircleBouquet.inclusion.{u, v} i
    (((eL.{u, v} I i).symm (eL.{u, v} I i (a0.{u, v} I i))).down) = _
  rw [Homeomorph.symm_apply_apply]
  exact CircleBouquet.inclusion_basepoint.{u, v} i

-- Forward descent to the bouquet through its original-circle API.
private def comparison (I : Type v) : C(W.{u, v} I, CircleBouquet.space.{u, v} I) :=
  TopCat.widePushoutDesc (sL.{u, v} I)
    (ContinuousMap.const _ (CircleBouquet.basepoint.{u, v} I))
    (comparisonFactor.{u, v} I)
    (fun i _ ↦ comparisonFactor_basepoint.{u, v} I i)

private theorem comparison_head (I : Type v) (q : PUnit.{max u v + 1}) :
    comparison.{u, v} I (WidePushout.head (sL.{u, v} I) q) =
      CircleBouquet.basepoint.{u, v} I :=
  TopCat.widePushoutDesc_head (sL.{u, v} I)
    (ContinuousMap.const _ (CircleBouquet.basepoint.{u, v} I))
    (comparisonFactor.{u, v} I)
    (fun i _ ↦ comparisonFactor_basepoint.{u, v} I i) q

private theorem comparison_ι (I : Type v) (i : I) (x : XL.{u, v} I i) :
    comparison.{u, v} I (WidePushout.ι (sL.{u, v} I) i x) =
      CircleBouquet.inclusion.{u, v} i x.down.down :=
  TopCat.widePushoutDesc_ι (sL.{u, v} I)
    (ContinuousMap.const _ (CircleBouquet.basepoint.{u, v} I))
    (comparisonFactor.{u, v} I)
    (fun i _ ↦ comparisonFactor_basepoint.{u, v} I i) i x

private theorem comparison_original_circle (I : Type v) (i : I) (z : Circle) :
    comparison.{u, v} I (originalCircleInclusion.{u, v} I i z) =
      CircleBouquet.inclusion.{u, v} i z :=
  comparison_ι.{u, v} I i (eL.{u, v} I i (ULift.up z))

-- Inverse descent prescribes the source head even when I is empty.
private def inverseComparison (I : Type v) :
    C(CircleBouquet.space.{u, v} I, W.{u, v} I) :=
  (CircleBouquet.desc.{u, v}
    (WidePushout.head (sL.{u, v} I) PUnit.unit)
    (originalCircleInclusion.{u, v} I)
    (originalCircleInclusion_basepoint.{u, v} I)).hom

private theorem inverseComparison_basepoint (I : Type v) :
    inverseComparison.{u, v} I (CircleBouquet.basepoint.{u, v} I) =
      WidePushout.head (sL.{u, v} I) PUnit.unit :=
  CircleBouquet.desc_basepoint.{u, v}
    (WidePushout.head (sL.{u, v} I) PUnit.unit)
    (originalCircleInclusion.{u, v} I)
    (originalCircleInclusion_basepoint.{u, v} I)

private theorem inverseComparison_inclusion (I : Type v) (i : I) (z : Circle) :
    inverseComparison.{u, v} I (CircleBouquet.inclusion.{u, v} i z) =
      originalCircleInclusion.{u, v} I i z :=
  congrArg (fun k : C(Circle, W.{u, v} I) ↦ k z)
    (CircleBouquet.inclusion_desc.{u, v}
      (WidePushout.head (sL.{u, v} I) PUnit.unit)
      (originalCircleInclusion.{u, v} I)
      (originalCircleInclusion_basepoint.{u, v} I) i)

private theorem inverseComparison_leftInverse (I : Type v) :
    Function.LeftInverse (inverseComparison.{u, v} I) (comparison.{u, v} I) := by
  have h : (fun x : W.{u, v} I ↦ inverseComparison.{u, v} I (comparison.{u, v} I x)) =
      (fun x : W.{u, v} I ↦ x) := by
    apply TopCat.widePushout_funext (sL.{u, v} I)
    · intro q
      cases q
      exact (congrArg (inverseComparison.{u, v} I)
        (comparison_head.{u, v} I PUnit.unit)).trans
          (inverseComparison_basepoint.{u, v} I)
    · intro i x
      have hx : originalCircleInclusion.{u, v} I i x.down.down =
          (WidePushout.ι (sL.{u, v} I) i x : W.{u, v} I) := by
        rcases x with ⟨⟨z⟩⟩
        rfl
      exact (congrArg (inverseComparison.{u, v} I)
        (comparison_ι.{u, v} I i x)).trans
          ((inverseComparison_inclusion.{u, v} I i x.down.down).trans hx)
  intro x
  exact congrFun h x

private theorem inverseComparison_rightInverse (I : Type v) :
    Function.RightInverse (inverseComparison.{u, v} I) (comparison.{u, v} I) := by
  have h : (fun y : CircleBouquet.space.{u, v} I ↦
      comparison.{u, v} I (inverseComparison.{u, v} I y)) =
      (fun y : CircleBouquet.space.{u, v} I ↦ y) := by
    apply CircleBouquet.funext.{u, v}
    · intro i z
      exact (congrArg (comparison.{u, v} I)
        (inverseComparison_inclusion.{u, v} I i z)).trans
          (comparison_original_circle.{u, v} I i z)
    · exact (congrArg (comparison.{u, v} I)
        (inverseComparison_basepoint.{u, v} I)).trans
          (comparison_head.{u, v} I PUnit.unit)
  intro y
  exact congrFun h y

-- Both maps, rather than a choice of an inverse from surjectivity, are specified.
private def comparisonHomeomorph (I : Type v) :
    W.{u, v} I ≃ₜ CircleBouquet.space.{u, v} I where
  toFun := comparison.{u, v} I
  invFun := inverseComparison.{u, v} I
  left_inv := inverseComparison_leftInverse.{u, v} I
  right_inv := inverseComparison_rightInverse.{u, v} I
  continuous_toFun := (comparison.{u, v} I).continuous
  continuous_invFun := (inverseComparison.{u, v} I).continuous

private theorem comparisonHomeomorph_apply (I : Type v) (x : W.{u, v} I) :
    comparisonHomeomorph.{u, v} I x = comparison.{u, v} I x := rfl

private theorem comparisonHomeomorph_symm_apply (I : Type v)
    (y : CircleBouquet.space.{u, v} I) :
    (comparisonHomeomorph.{u, v} I).symm y = inverseComparison.{u, v} I y := rfl

-- The head equation is independent of any i : I.
private theorem comparisonHomeomorph_head (I : Type v) (q : PUnit.{max u v + 1}) :
    comparisonHomeomorph.{u, v} I (WidePushout.head (sL.{u, v} I) q) =
      CircleBouquet.basepoint.{u, v} I :=
  comparison_head.{u, v} I q

private theorem comparisonHomeomorph_common_head (I : Type v) :
    (comparisonHomeomorph.{u, v} I : C(W.{u, v} I, CircleBouquet.space.{u, v} I)).comp
      (WidePushout.head (sL.{u, v} I)).hom =
        ContinuousMap.const _ (CircleBouquet.basepoint.{u, v} I) := by
  apply ContinuousMap.ext
  exact comparisonHomeomorph_head.{u, v} I

private theorem comparisonHomeomorph_original_factor (I : Type v) (i : I)
    (x : X0.{u, v} I i) :
    comparisonHomeomorph.{u, v} I
      (WidePushout.ι (sL.{u, v} I) i (eL.{u, v} I i x)) =
      CircleBouquet.inclusion.{u, v} i x.down :=
  comparison_ι.{u, v} I i (eL.{u, v} I i x)

private theorem comparisonHomeomorph_comp_originalFactorInclusion (I : Type v) (i : I) :
    (comparisonHomeomorph.{u, v} I : C(W.{u, v} I, CircleBouquet.space.{u, v} I)).comp
      ((WidePushout.ι (sL.{u, v} I) i).hom.comp
        (eL.{u, v} I i : C(X0.{u, v} I i, XL.{u, v} I i))) =
      (CircleBouquet.inclusion.{u, v} i).comp
        (Homeomorph.ulift.{max u v, 0} (X := Circle) :
          C(ULift.{max u v} Circle, Circle)) := by
  apply ContinuousMap.ext
  exact comparisonHomeomorph_original_factor.{u, v} I i

private theorem comparisonHomeomorph_original_circle (I : Type v) (i : I) (z : Circle) :
    comparisonHomeomorph.{u, v} I
      (WidePushout.ι (sL.{u, v} I) i (eL.{u, v} I i (ULift.up z))) =
      CircleBouquet.inclusion.{u, v} i z :=
  comparison_original_circle.{u, v} I i z

private theorem comparisonHomeomorph_comp_originalCircleInclusion (I : Type v) (i : I) :
    (comparisonHomeomorph.{u, v} I : C(W.{u, v} I, CircleBouquet.space.{u, v} I)).comp
      (originalCircleInclusion.{u, v} I i) = CircleBouquet.inclusion.{u, v} i := by
  apply ContinuousMap.ext
  exact comparisonHomeomorph_original_circle.{u, v} I i

private theorem comparisonHomeomorph_symm_basepoint (I : Type v) :
    (comparisonHomeomorph.{u, v} I).symm (CircleBouquet.basepoint.{u, v} I) =
      WidePushout.head (sL.{u, v} I) PUnit.unit :=
  inverseComparison_basepoint.{u, v} I

private theorem comparisonHomeomorph_symm_comp_inclusion (I : Type v) (i : I) :
    ((comparisonHomeomorph.{u, v} I).symm :
        C(CircleBouquet.space.{u, v} I, W.{u, v} I)).comp
      (CircleBouquet.inclusion.{u, v} i) = originalCircleInclusion.{u, v} I i := by
  apply ContinuousMap.ext
  exact inverseComparison_inclusion.{u, v} I i

-- The circle coordinate is induced by the inner-lift homeomorphism.
-- The algebraic target universe remains independent of the factor/index universes.
-- This is the up-map for the existing inner lift, not the additional outer lift XL.
private def circleUp (I : Type v) (i : I) : C(Circle, X0.{u, v} I i) :=
  ((Homeomorph.ulift.{max u v, 0} (X := Circle)).symm :
    C(Circle, ULift.{max u v} Circle))

private theorem circleUp_apply (I : Type v) (i : I) (z : Circle) :
    circleUp.{u, v} I i z = ULift.up z := rfl

private def circleLiftEquiv (I : Type v) (i : I) :
    FundamentalGroup Circle 1 ≃* FundamentalGroup (X0.{u, v} I i) (a0.{u, v} I i) :=
  let e : Circle ≃ₜ X0.{u, v} I i :=
    (Homeomorph.ulift.{max u v, 0} (X := Circle)).symm
  let E : CategoryTheory.Equivalence
      (FundamentalGroupoid Circle) (FundamentalGroupoid (X0.{u, v} I i)) :=
    FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv
  E.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk (1 : Circle))

private theorem circleLiftEquiv_apply (I : Type v) (i : I)
    (γ : FundamentalGroup Circle 1) :
    circleLiftEquiv.{u, v} I i γ =
      FundamentalGroup.mapOfEq (circleUp.{u, v} I i) rfl γ := by
  rw [FundamentalGroup.mapOfEq_rfl]
  rfl

private def circleCoordinate (I : Type v) (i : I) :
    FundamentalGroup (X0.{u, v} I i) (a0.{u, v} I i) ≃* Multiplicative ℤ :=
  (circleLiftEquiv.{u, v} I i).symm.trans Circle.fundamentalGroupEquivInt

private theorem circleCoordinate_map_circleUp (I : Type v) (i : I)
    (γ : FundamentalGroup Circle 1) :
    circleCoordinate.{u, v} I i
        (FundamentalGroup.mapOfEq (circleUp.{u, v} I i) rfl γ) =
      Circle.fundamentalGroupEquivInt γ := by
  change Circle.fundamentalGroupEquivInt
    ((circleLiftEquiv.{u, v} I i).symm
      (FundamentalGroup.mapOfEq (circleUp.{u, v} I i) rfl γ)) = _
  rw [← circleLiftEquiv_apply, MulEquiv.symm_apply_apply]

private def posX (I : Type v) (i : I) :
    FundamentalGroup (X0.{u, v} I i) (a0.{u, v} I i) :=
  FundamentalGroup.mapOfEq (circleUp.{u, v} I i) rfl
    (FundamentalGroup.fromPath ⟦Circle.loop 1⟧)

private theorem posX_eq_loop (I : Type v) (i : I) :
    posX.{u, v} I i = FundamentalGroup.fromPath
      ⟦(Circle.loop 1).map (circleUp.{u, v} I i).continuous⟧ := by
  rw [posX, FundamentalGroup.mapOfEq_apply]
  rfl

private theorem circleCoordinate_posX (I : Type v) (i : I) :
    circleCoordinate.{u, v} I i (posX.{u, v} I i) = Multiplicative.ofAdd (1 : ℤ) := by
  rw [posX, circleCoordinate_map_circleUp, Circle.fundamentalGroupEquivInt_loop]

private theorem circleCoordinate_symm_one (I : Type v) (i : I) :
    (circleCoordinate.{u, v} I i).symm (Multiplicative.ofAdd (1 : ℤ)) =
      posX.{u, v} I i :=
  (circleCoordinate.{u, v} I i).symm_apply_eq.mpr
    (circleCoordinate_posX.{u, v} I i).symm

private theorem cyclicHom_ext (I : Type v) (i : I) {M : Type w} [Monoid M]
    (f g : FundamentalGroup (X0.{u, v} I i) (a0.{u, v} I i) →* M)
    (hpos : f (posX.{u, v} I i) = g (posX.{u, v} I i)) : f = g := by
  have h : f.comp (circleCoordinate.{u, v} I i).symm.toMonoidHom =
      g.comp (circleCoordinate.{u, v} I i).symm.toMonoidHom := by
    apply MonoidHom.ext_mint
    change f ((circleCoordinate.{u, v} I i).symm (Multiplicative.ofAdd (1 : ℤ))) =
      g ((circleCoordinate.{u, v} I i).symm (Multiplicative.ofAdd (1 : ℤ)))
    rw [circleCoordinate_symm_one]
    exact hpos
  apply MonoidHom.ext
  intro γ
  have hγ := DFunLike.congr_fun h (circleCoordinate.{u, v} I i γ)
  change f ((circleCoordinate.{u, v} I i).symm (circleCoordinate.{u, v} I i γ)) =
    g ((circleCoordinate.{u, v} I i).symm (circleCoordinate.{u, v} I i γ)) at hγ
  simpa only [MulEquiv.symm_apply_apply] using hγ

private def factorToFreeGroup (I : Type v) (i : I) :
    FundamentalGroup (X0.{u, v} I i) (a0.{u, v} I i) →* FreeGroup I :=
  (zpowersHom (FreeGroup I) (FreeGroup.of i)).comp
    (circleCoordinate.{u, v} I i).toMonoidHom

private theorem factorToFreeGroup_apply (I : Type v) (i : I)
    (γ : FundamentalGroup (X0.{u, v} I i) (a0.{u, v} I i)) :
    factorToFreeGroup.{u, v} I i γ =
      FreeGroup.of i ^ (circleCoordinate.{u, v} I i γ).toAdd := rfl

private theorem factorToFreeGroup_posX (I : Type v) (i : I) :
    factorToFreeGroup.{u, v} I i (posX.{u, v} I i) = FreeGroup.of i := by
  change zpowersHom (FreeGroup I) (FreeGroup.of i)
    (circleCoordinate.{u, v} I i (posX.{u, v} I i)) = _
  rw [circleCoordinate_posX, zpowersHom_apply]
  exact zpow_one _

private abbrev w (I : Type v) : W.{u, v} I :=
  WidePushout.head (sL.{u, v} I) PUnit.unit

private def originalInclusion (I : Type v) (i : I) : C(X0.{u, v} I i, W.{u, v} I) :=
  (WidePushout.ι (sL.{u, v} I) i).hom.comp
    (eL.{u, v} I i : C(X0.{u, v} I i, XL.{u, v} I i))

private theorem originalInclusion_basepoint (I : Type v) (i : I) :
    originalInclusion.{u, v} I i (a0.{u, v} I i) = w.{u, v} I :=
  TopCat.widePushout_point_ι_point (aL.{u, v} I) i

private def originalGroupMap (I : Type v) (i : I) :
    FundamentalGroup (X0.{u, v} I i) (a0.{u, v} I i) →*
      FundamentalGroup (W.{u, v} I) (w.{u, v} I) :=
  FundamentalGroup.mapOfEq (originalInclusion.{u, v} I i)
    (originalInclusion_basepoint.{u, v} I i)

-- Restrict the comparison's groupoid equivalence to the source head, then transport
-- its image to the bouquet basepoint by the head equation; no index is chosen.
private def comparisonFundamentalGroup (I : Type v) :
    FundamentalGroup (W.{u, v} I) (w.{u, v} I) ≃*
      FundamentalGroup (CircleBouquet.space.{u, v} I) (CircleBouquet.basepoint.{u, v} I) :=
  let E : CategoryTheory.Equivalence
      (FundamentalGroupoid (W.{u, v} I))
      (FundamentalGroupoid (CircleBouquet.space.{u, v} I)) :=
    FundamentalGroupoidFunctor.equivOfHomotopyEquiv
      (comparisonHomeomorph.{u, v} I).toHomotopyEquiv
  let e₀ : FundamentalGroup (W.{u, v} I) (w.{u, v} I) ≃*
      FundamentalGroup (CircleBouquet.space.{u, v} I)
        (comparisonHomeomorph.{u, v} I (w.{u, v} I)) :=
    E.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk (w.{u, v} I))
  e₀.trans (CategoryTheory.eqToIso
    (C := FundamentalGroupoid (CircleBouquet.space.{u, v} I))
    (congrArg FundamentalGroupoid.mk
      (comparisonHomeomorph_head.{u, v} I PUnit.unit))).conj

private theorem comparisonFundamentalGroup_apply (I : Type v)
    (γ : FundamentalGroup (W.{u, v} I) (w.{u, v} I)) :
    comparisonFundamentalGroup.{u, v} I γ =
      FundamentalGroup.mapOfEq
        (comparisonHomeomorph.{u, v} I :
          C(W.{u, v} I, CircleBouquet.space.{u, v} I))
        (comparisonHomeomorph_head.{u, v} I PUnit.unit) γ := rfl

private theorem comparisonFundamentalGroup_toMonoidHom (I : Type v) :
    (comparisonFundamentalGroup.{u, v} I).toMonoidHom =
      FundamentalGroup.mapOfEq
        (comparisonHomeomorph.{u, v} I :
          C(W.{u, v} I, CircleBouquet.space.{u, v} I))
        (comparisonHomeomorph_head.{u, v} I PUnit.unit) := by
  apply MonoidHom.ext
  intro γ
  exact comparisonFundamentalGroup_apply.{u, v} I γ

-- Recover this characteristic equation from the public loop formula, without
-- unfolding the bouquet's positive generator, inclusion or basepoint.
private theorem positiveGenerator_eq_mapOfEq (I : Type v) (i : I) :
    CircleBouquet.positiveGenerator.{u, v} i =
      FundamentalGroup.mapOfEq (CircleBouquet.inclusion.{u, v} i)
        (CircleBouquet.inclusion_basepoint.{u, v} i)
        (FundamentalGroup.fromPath ⟦Circle.loop 1⟧) := by
  rw [CircleBouquet.positiveGenerator_eq_loop, FundamentalGroup.mapOfEq_apply]
  rfl

private theorem comparisonFundamentalGroup_originalGroupMap_posX (I : Type v) (i : I) :
    comparisonFundamentalGroup.{u, v} I
        (originalGroupMap.{u, v} I i (posX.{u, v} I i)) =
      CircleBouquet.positiveGenerator.{u, v} i := by
  let γ : FundamentalGroup Circle 1 := FundamentalGroup.fromPath ⟦Circle.loop 1⟧
  -- originalCircleInclusion is definitionally originalInclusion.comp circleUp.
  have hcircle :
      FundamentalGroup.mapOfEq (originalCircleInclusion.{u, v} I i)
        (originalCircleInclusion_basepoint.{u, v} I i) =
      (originalGroupMap.{u, v} I i).comp
        (FundamentalGroup.mapOfEq (circleUp.{u, v} I i) rfl) :=
    FundamentalGroup.mapOfEq_comp (originalInclusion.{u, v} I i)
      (circleUp.{u, v} I i) rfl (originalInclusion_basepoint.{u, v} I i)
  have hcomparison :
      (FundamentalGroup.mapOfEq
        (comparisonHomeomorph.{u, v} I :
          C(W.{u, v} I, CircleBouquet.space.{u, v} I))
        (comparisonHomeomorph_head.{u, v} I PUnit.unit)).comp
          (FundamentalGroup.mapOfEq (originalCircleInclusion.{u, v} I i)
            (originalCircleInclusion_basepoint.{u, v} I i)) =
      FundamentalGroup.mapOfEq (CircleBouquet.inclusion.{u, v} i)
        (CircleBouquet.inclusion_basepoint.{u, v} i) := by
    simpa only [comparisonHomeomorph_comp_originalCircleInclusion] using
      (FundamentalGroup.mapOfEq_comp
        (comparisonHomeomorph.{u, v} I :
          C(W.{u, v} I, CircleBouquet.space.{u, v} I))
        (originalCircleInclusion.{u, v} I i)
        (originalCircleInclusion_basepoint.{u, v} I i)
        (comparisonHomeomorph_head.{u, v} I PUnit.unit)).symm
  calc
    comparisonFundamentalGroup.{u, v} I
        (originalGroupMap.{u, v} I i (posX.{u, v} I i)) =
        FundamentalGroup.mapOfEq
          (comparisonHomeomorph.{u, v} I :
            C(W.{u, v} I, CircleBouquet.space.{u, v} I))
          (comparisonHomeomorph_head.{u, v} I PUnit.unit)
          (FundamentalGroup.mapOfEq (originalCircleInclusion.{u, v} I i)
            (originalCircleInclusion_basepoint.{u, v} I i) γ) := by
      rw [comparisonFundamentalGroup_apply, posX]
      exact congrArg
        (FundamentalGroup.mapOfEq
          (comparisonHomeomorph.{u, v} I :
            C(W.{u, v} I, CircleBouquet.space.{u, v} I))
          (comparisonHomeomorph_head.{u, v} I PUnit.unit))
        (DFunLike.congr_fun hcircle γ).symm
    _ = FundamentalGroup.mapOfEq (CircleBouquet.inclusion.{u, v} i)
        (CircleBouquet.inclusion_basepoint.{u, v} i) γ :=
      DFunLike.congr_fun hcomparison γ
    _ = CircleBouquet.positiveGenerator.{u, v} i :=
      (positiveGenerator_eq_mapOfEq.{u, v} I i).symm

-- This identifies the transported homomorphism on every word, not just generators.
private theorem comparisonFundamentalGroup_comp_lift (I : Type v) :
    (comparisonFundamentalGroup.{u, v} I).toMonoidHom.comp
        (FreeGroup.lift (fun i ↦ originalGroupMap.{u, v} I i (posX.{u, v} I i))) =
      CircleBouquet.generatorMap.{u, v} I := by
  apply FreeGroup.ext_hom
  intro i
  rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, CircleBouquet.generatorMap_of]
  exact comparisonFundamentalGroup_originalGroupMap_posX.{u, v} I i

private def coreOfSets (I : Type v) (A : ∀ i, Set (XL.{u, v} I i))
    (ha : ∀ i, aL.{u, v} I i ∈ A i) (ho : ∀ i, IsOpen (A i)) :
    TopologicalSpace.OpenNhds (X := W.{u, v} I) (w.{u, v} I) :=
  ⟨⟨TopCat.widePushoutPointNeighborhood (aL.{u, v} I) A,
      TopCat.isOpen_widePushoutPointNeighborhood (aL.{u, v} I) A ha ho⟩,
    TopCat.widePushoutPointNeighborhood_head_mem (aL.{u, v} I) A⟩

private def arc : Set Circle := ({(-1 : Circle)} : Set Circle)ᶜ
private def arcOne : arc := ⟨1, (Circle.neg_ne_self (1 : Circle)).symm⟩

private def coordinate (I : Type v) (i : I) : XL.{u, v} I i ≃ₜ Circle :=
  (eL.{u, v} I i).symm.trans (Homeomorph.ulift.{max u v, 0} (X := Circle))

private theorem coordinate_eL (I : Type v) (i : I) (x : X0.{u, v} I i) :
    coordinate.{u, v} I i (eL.{u, v} I i x) =
      Homeomorph.ulift.{max u v, 0} (X := Circle) x :=
  congrArg (Homeomorph.ulift.{max u v, 0} (X := Circle))
    ((eL.{u, v} I i).symm_apply_apply x)

private theorem coordinate_aL (I : Type v) (i : I) :
    coordinate.{u, v} I i (aL.{u, v} I i) = 1 :=
  coordinate_eL.{u, v} I i (a0.{u, v} I i)

private def factorArc (I : Type v) (i : I) : Set (XL.{u, v} I i) :=
  coordinate.{u, v} I i ⁻¹' arc

private theorem factorArc_mem (I : Type v) (i : I) :
    aL.{u, v} I i ∈ factorArc.{u, v} I i := by
  change coordinate.{u, v} I i (aL.{u, v} I i) ∈ arc
  rw [coordinate_aL]
  exact arcOne.property

private theorem arc_isOpen : IsOpen arc :=
  isClosed_singleton.isOpen_compl

private theorem factorArc_isOpen (I : Type v) (i : I) :
    IsOpen (factorArc.{u, v} I i) :=
  arc_isOpen.preimage (coordinate.{u, v} I i).continuous

private def factorArcHomeomorph (I : Type v) (i : I) :
    factorArc.{u, v} I i ≃ₜ arc :=
  (coordinate.{u, v} I i).subtype (fun _ ↦ Iff.rfl)

private theorem factorArcHomeomorph_basepoint (I : Type v) (i : I) :
    factorArcHomeomorph.{u, v} I i
      ⟨aL.{u, v} I i, factorArc_mem.{u, v} I i⟩ = arcOne := by
  apply Subtype.ext
  exact coordinate_aL.{u, v} I i

private theorem factorArcHomeomorph_symm_arcOne (I : Type v) (i : I) :
    (factorArcHomeomorph.{u, v} I i).symm arcOne =
      ⟨aL.{u, v} I i, factorArc_mem.{u, v} I i⟩ := by
  apply (factorArcHomeomorph.{u, v} I i).injective
  exact ((factorArcHomeomorph.{u, v} I i).apply_symm_apply arcOne).trans
    (factorArcHomeomorph_basepoint.{u, v} I i).symm

/-- Transport the supplied point-fixed arc contraction to a lifted factor arc. -/
private def factorContraction (I : Type v)
    (Karc : ContinuousMap.HomotopyRel (ContinuousMap.id arc)
      (ContinuousMap.const arc arcOne) {arcOne}) (i : I) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (factorArc.{u, v} I i))
      (ContinuousMap.const (factorArc.{u, v} I i)
        ⟨aL.{u, v} I i, factorArc_mem.{u, v} I i⟩)
      {⟨aL.{u, v} I i, factorArc_mem.{u, v} I i⟩} := by
  let e := factorArcHomeomorph.{u, v} I i
  let c : factorArc.{u, v} I i := ⟨aL.{u, v} I i, factorArc_mem.{u, v} I i⟩
  have he : e c = arcOne := factorArcHomeomorph_basepoint.{u, v} I i
  have he' : e.symm arcOne = c := factorArcHomeomorph_symm_arcOne.{u, v} I i
  refine {
    toFun := fun z ↦ e.symm (Karc (z.1, e z.2))
    continuous_toFun := e.symm.continuous.comp
      (Karc.continuous.comp
        (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · intro x
    exact (congrArg e.symm (Karc.apply_zero (e x))).trans (e.symm_apply_apply x)
  · intro x
    exact (congrArg e.symm (Karc.apply_one (e x))).trans he'
  · intro t x hx
    have hx' : x = c := Set.mem_singleton_iff.mp hx
    subst x
    change e.symm (Karc (t, e c)) = c
    rw [he]
    exact (congrArg e.symm
      (Karc.eq_fst t (x := arcOne) (by simp))).trans he'

private theorem factorContraction_apply (I : Type v)
    (Karc : ContinuousMap.HomotopyRel (ContinuousMap.id arc)
      (ContinuousMap.const arc arcOne) {arcOne}) (i : I)
    (t : unitInterval) (x : factorArc.{u, v} I i) :
    factorContraction.{u, v} I Karc i (t, x) =
      (factorArcHomeomorph.{u, v} I i).symm
        (Karc (t, factorArcHomeomorph.{u, v} I i x)) := rfl

private def core (I : Type v) :
    TopologicalSpace.OpenNhds (X := W.{u, v} I) (w.{u, v} I) :=
  coreOfSets.{u, v} I (factorArc.{u, v} I)
    (factorArc_mem.{u, v} I) (factorArc_isOpen.{u, v} I)

private theorem preimage_factorInclusion_core (I : Type v) (i : I) :
    WidePushout.ι (sL.{u, v} I) i ⁻¹' ((core.{u, v} I).1 : Set (W.{u, v} I)) =
      factorArc.{u, v} I i :=
  TopCat.preimage_widePushoutPointNeighborhood (aL.{u, v} I) (factorArc.{u, v} I)
    i (factorArc_mem.{u, v} I i)

private theorem factorArc_isPathConnected (I : Type v) (i : I) :
    IsPathConnected (factorArc.{u, v} I i) :=
  (coordinate.{u, v} I i).isPathConnected_preimage.mpr
    (Circle.isPathConnected_compl_singleton (-1 : Circle))

private theorem core_isPathConnected (I : Type v) :
    IsPathConnected ((core.{u, v} I).1 : Set (W.{u, v} I)) := by
  refine TopCat.isPathConnected_of_widePushout_point_preimage
    (X := XL.{u, v} I) (aL.{u, v} I)
    (C := ((core.{u, v} I).1 : Set (W.{u, v} I))) (core.{u, v} I).2 ?_
  intro i
  exact (preimage_factorInclusion_core.{u, v} I i).symm ▸
    factorArc_isPathConnected.{u, v} I i

private theorem X0_isPathConnected (I : Type v) (i : I) :
    IsPathConnected (Set.univ : Set (X0.{u, v} I i)) := by
  let : PathConnectedSpace (X0.{u, v} I i) :=
    (Homeomorph.ulift.{max u v, 0} (X := Circle)).symm.pathConnectedSpace
  exact isPathConnected_univ

/-- The inverse image is taken along the original-domain inclusion, not the
lifted inclusion with domain `XL I i`. -/
private theorem original_preimage_core (I : Type v) (i : I) :
    originalInclusion.{u, v} I i ⁻¹' ((core.{u, v} I).1 : Set (W.{u, v} I)) =
      Homeomorph.ulift.{max u v, 0} (X := Circle) ⁻¹' arc := by
  ext x
  change eL.{u, v} I i x ∈
      (WidePushout.ι (sL.{u, v} I) i ⁻¹'
        ((core.{u, v} I).1 : Set (W.{u, v} I))) ↔
    Homeomorph.ulift.{max u v, 0} (X := Circle) x ∈ arc
  rw [preimage_factorInclusion_core]
  change coordinate.{u, v} I i (eL.{u, v} I i x) ∈ arc ↔ _
  rw [coordinate_eL]

private def originalCoreHomeomorph (I : Type v) (i : I) :
    (originalInclusion.{u, v} I i ⁻¹'
      ((core.{u, v} I).1 : Set (W.{u, v} I))) ≃ₜ arc :=
  (Homeomorph.ulift.{max u v, 0} (X := Circle)).sets
    (original_preimage_core.{u, v} I i)

private theorem originalInclusion_mem_core (I : Type v) (i : I) :
    originalInclusion.{u, v} I i (a0.{u, v} I i) ∈
      ((core.{u, v} I).1 : Set (W.{u, v} I)) := by
  rw [originalInclusion_basepoint]
  exact (core.{u, v} I).2

private theorem originalCoreHomeomorph_basepoint (I : Type v) (i : I) :
    originalCoreHomeomorph.{u, v} I i
      ⟨a0.{u, v} I i, originalInclusion_mem_core.{u, v} I i⟩ = arcOne := by
  apply Subtype.ext
  rfl

private theorem arc_contractibleSpace : ContractibleSpace arc :=
  contractibleSpace_sphere_compl_singleton (E := ℂ) (-1 : Circle)

private theorem originalCore_contractibleSpace (I : Type v) (i : I) :
    ContractibleSpace (originalInclusion.{u, v} I i ⁻¹'
      ((core.{u, v} I).1 : Set (W.{u, v} I))) := by
  let : ContractibleSpace arc := arc_contractibleSpace
  exact (originalCoreHomeomorph.{u, v} I i).contractibleSpace

/-- The original-core-preimage inclusion has trivial fundamental-group image,
with exactly the subtype and basepoint required by the extension criterion. -/
private theorem originalCore_hnull (I : Type v) (i : I) :
    (FundamentalGroup.map
      (ContinuousMap.subtypeVal (originalInclusion.{u, v} I i ⁻¹'
        ((core.{u, v} I).1 : Set (W.{u, v} I))))
      ⟨a0.{u, v} I i, originalInclusion_mem_core.{u, v} I i⟩).range = ⊥ := by
  let : ContractibleSpace (originalInclusion.{u, v} I i ⁻¹'
      ((core.{u, v} I).1 : Set (W.{u, v} I))) :=
    originalCore_contractibleSpace.{u, v} I i
  apply MonoidHom.range_eq_bot_iff.mpr
  apply MonoidHom.ext
  intro g
  have hg : g = 1 := Subsingleton.elim _ _
  simp only [hg, map_one]

private def chartOfSets (I : Type v) (A : ∀ j, Set (XL.{u, v} I j))
    (ha : ∀ j, aL.{u, v} I j ∈ A j) (ho : ∀ j, IsOpen (A j)) (i : I) :
    TopologicalSpace.OpenNhds (X := W.{u, v} I) (w.{u, v} I) :=
  TopCat.widePushoutPointChartNhds (aL.{u, v} I) (coreOfSets I A ha ho) i

private def chartRetraction (I : Type v) (A : ∀ j, Set (XL.{u, v} I j))
    (ha : ∀ j, aL.{u, v} I j ∈ A j) (ho : ∀ j, IsOpen (A j)) (i : I) :
    C((chartOfSets I A ha ho i).1, X0.{u, v} I i) :=
  (((eL.{u, v} I i).symm : C(XL.{u, v} I i, X0.{u, v} I i)).comp
    (TopCat.widePushoutPointRetraction (XL.{u, v} I) (aL.{u, v} I) i).hom).comp
      (ContinuousMap.subtypeVal ((chartOfSets I A ha ho i).1 : Set (W.{u, v} I)))

private theorem chartRetraction_basepoint (I : Type v)
    (A : ∀ j, Set (XL.{u, v} I j)) (ha : ∀ j, aL.{u, v} I j ∈ A j)
    (ho : ∀ j, IsOpen (A j)) (i : I) :
    chartRetraction I A ha ho i ⟨w.{u, v} I, (chartOfSets I A ha ho i).2⟩ =
      a0.{u, v} I i := by
  change (eL I i).symm
    (TopCat.widePushoutPointRetraction (XL I) (aL I) i (w I)) = a0 I i
  have hhead :
      TopCat.widePushoutPointRetraction (XL I) (aL I) i (w I) = aL I i :=
    TopCat.widePushoutPointRetraction_head_apply (XL I) (aL I) i PUnit.unit
  exact (congrArg (eL I i).symm hhead).trans
    ((eL I i).symm_apply_apply (a0 I i))

private def chartFactorSet (I : Type v) (A : ∀ j, Set (XL.{u, v} I j))
    (i j : I) : Set (XL.{u, v} I j) := by
  classical
  exact if j = i then Set.univ else A j

private theorem chartFactorSet_mem (I : Type v) (A : ∀ j, Set (XL.{u, v} I j))
    (ha : ∀ j, aL.{u, v} I j ∈ A j) (i j : I) :
    aL.{u, v} I j ∈ chartFactorSet I A i j := by
  classical
  by_cases hji : j = i
  · simp [chartFactorSet, hji]
  · simpa only [chartFactorSet, ite_eq_right hji] using ha j

private theorem isOpen_chartFactorSet (I : Type v) (A : ∀ j, Set (XL.{u, v} I j))
    (ho : ∀ j, IsOpen (A j)) (i j : I) : IsOpen (chartFactorSet I A i j) := by
  classical
  by_cases hji : j = i
  · simpa only [chartFactorSet, ite_eq_left hji] using
      (isOpen_univ : IsOpen (Set.univ : Set (XL I j)))
  · simpa only [chartFactorSet, ite_eq_right hji] using ho j

private abbrev chartFactorPoint (I : Type v) (A : ∀ j, Set (XL.{u, v} I j))
    (ha : ∀ j, aL.{u, v} I j ∈ A j) (i j : I) : chartFactorSet I A i j :=
  ⟨aL I j, chartFactorSet_mem I A ha i j⟩

private abbrev chartAttach (I : Type v) (A : ∀ j, Set (XL.{u, v} I j))
    (ha : ∀ j, aL.{u, v} I j ∈ A j) (i j : I) :
    TopCat.of PUnit.{max u v + 1} ⟶ TopCat.of (chartFactorSet I A i j) :=
  TopCat.const (chartFactorPoint I A ha i j)

private abbrev chartModel (I : Type v) (A : ∀ j, Set (XL.{u, v} I j))
    (ha : ∀ j, aL.{u, v} I j ∈ A j) (i : I) : TopCat.{max u v} :=
  widePushout (TopCat.of PUnit.{max u v + 1})
    (fun j ↦ TopCat.of (chartFactorSet I A i j)) (chartAttach I A ha i)

private theorem chartNeighborhood_eq (I : Type v) (A : ∀ j, Set (XL.{u, v} I j))
    (ha : ∀ j, aL.{u, v} I j ∈ A j) (ho : ∀ j, IsOpen (A j)) (i : I) :
    TopCat.widePushoutPointNeighborhood (aL I) (chartFactorSet I A i) =
      ((chartOfSets I A ha ho i).1 : Set (W.{u, v} I)) := by
  classical
  ext z
  change z ∈ TopCat.widePushoutPointNeighborhood (aL I) (chartFactorSet I A i) ↔
    (∃ x : XL I i, WidePushout.ι (sL I) i x = z) ∨
      z ∈ TopCat.widePushoutPointNeighborhood (aL I) A
  simp only [TopCat.mem_widePushoutPointNeighborhood]
  constructor
  · rintro (hz | ⟨j, x, hx, hxz⟩)
    · exact Or.inr (Or.inl hz)
    · by_cases hji : j = i
      · subst j
        exact Or.inl ⟨x, hxz⟩
      · exact Or.inr (Or.inr ⟨j, x,
          by simpa only [chartFactorSet, ite_eq_right hji] using hx, hxz⟩)
  · rintro (⟨x, hxz⟩ | hz | ⟨j, x, hx, hxz⟩)
    · exact Or.inr ⟨i, x, by simp [chartFactorSet], hxz⟩
    · exact Or.inl hz
    · refine Or.inr ⟨j, x, ?_, hxz⟩
      by_cases hji : j = i
      · simp [chartFactorSet, hji]
      · simpa only [chartFactorSet, ite_eq_right hji] using hx

private def chartDomainHomeomorph (I : Type v) (A : ∀ j, Set (XL.{u, v} I j))
    (ha : ∀ j, aL.{u, v} I j ∈ A j) (ho : ∀ j, IsOpen (A j)) (i : I) :
    chartModel I A ha i ≃ₜ (chartOfSets I A ha ho i).1 :=
  (TopCat.widePushoutPointNeighborhoodHomeomorph (aL I) (chartFactorSet I A i)
    (chartFactorSet_mem I A ha i) (isOpen_chartFactorSet I A ho i)).trans
      (Homeomorph.setCongr (chartNeighborhood_eq I A ha ho i))

private theorem chartDomainHomeomorph_head (I : Type v)
    (A : ∀ j, Set (XL.{u, v} I j)) (ha : ∀ j, aL.{u, v} I j ∈ A j)
    (ho : ∀ j, IsOpen (A j)) (i : I) :
    chartDomainHomeomorph I A ha ho i
      (WidePushout.head (chartAttach I A ha i) PUnit.unit) =
        ⟨w.{u, v} I, (chartOfSets I A ha ho i).2⟩ := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (TopCat.widePushoutPointNeighborhoodHomeomorph_head (aL I) (chartFactorSet I A i)
      (chartFactorSet_mem I A ha i) (isOpen_chartFactorSet I A ho i) PUnit.unit)
  exact h

private theorem chartDomainHomeomorph_ι (I : Type v)
    (A : ∀ j, Set (XL.{u, v} I j)) (ha : ∀ j, aL.{u, v} I j ∈ A j)
    (ho : ∀ j, IsOpen (A j)) (i j : I) (x : chartFactorSet I A i j) :
    (chartDomainHomeomorph I A ha ho i
      (WidePushout.ι (chartAttach I A ha i) j x) : W.{u, v} I) =
        WidePushout.ι (sL I) j (x : XL I j) := by
  have h := congrArg Subtype.val
    (TopCat.widePushoutPointNeighborhoodHomeomorph_ι (aL I) (chartFactorSet I A i)
      (chartFactorSet_mem I A ha i) (isOpen_chartFactorSet I A ho i) j x)
  exact h

-- Mathlib's relative compContinuousMap is target postcomposition. This small
-- source-precomposition wrapper keeps the fixed-set field explicit.
private def homotopyRelPrecomp {D : Type*} {E : Type*} {F : Type*}
    [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace F]
    {f g : C(E, F)} {S : Set E} {T : Set D}
    (H : ContinuousMap.HomotopyRel f g S) (q : C(D, E)) (hq : Set.MapsTo q T S) :
    ContinuousMap.HomotopyRel (f.comp q) (g.comp q) T where
  toHomotopy := H.toHomotopy.compContinuousMap q
  prop' t x hx := H.eq_fst t (x := q x) (hq hx)

private def chartInclusionHomotopy (I : Type v)
    (A : ∀ j, Set (XL.{u, v} I j)) (ha : ∀ j, aL.{u, v} I j ∈ A j)
    (ho : ∀ j, IsOpen (A j))
    (K : ∀ j, ContinuousMap.HomotopyRel (ContinuousMap.id (A j))
      (ContinuousMap.const (A j) ⟨aL I j, ha j⟩) {⟨aL I j, ha j⟩}) (i : I) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.subtypeVal ((chartOfSets I A ha ho i).1 : Set (W.{u, v} I)))
      ((originalInclusion I i).comp (chartRetraction I A ha ho i))
      {(⟨w.{u, v} I, (chartOfSets I A ha ho i).2⟩ : (chartOfSets I A ha ho i).1)} := by
  classical
  let E := chartDomainHomeomorph I A ha ho i
  let f : C(chartModel I A ha i, W I) :=
    (ContinuousMap.subtypeVal ((chartOfSets I A ha ho i).1 : Set (W I))).comp
      (E : C(chartModel I A ha i, (chartOfSets I A ha ho i).1))
  let g : C(chartModel I A ha i, W I) :=
    ((originalInclusion I i).comp (chartRetraction I A ha ho i)).comp
      (E : C(chartModel I A ha i, (chartOfSets I A ha ho i).1))
  have hf (j : I) (x : chartFactorSet I A i j) :
      f (WidePushout.ι (chartAttach I A ha i) j x) =
        WidePushout.ι (sL I) j (x : XL I j) :=
    chartDomainHomeomorph_ι I A ha ho i j x
  have hg (j : I) (x : chartFactorSet I A i j) :
      g (WidePushout.ι (chartAttach I A ha i) j x) =
        WidePushout.ι (sL I) i
          (TopCat.widePushoutPointRetraction (XL I) (aL I) i
            (WidePushout.ι (sL I) j (x : XL I j))) := by
    change WidePushout.ι (sL I) i
      (eL I i ((eL I i).symm
        (TopCat.widePushoutPointRetraction (XL I) (aL I) i
          (E (WidePushout.ι (chartAttach I A ha i) j x) : W I)))) = _
    rw [Homeomorph.apply_symm_apply, chartDomainHomeomorph_ι]
  have hhead : f (WidePushout.head (chartAttach I A ha i) PUnit.unit) =
      g (WidePushout.head (chartAttach I A ha i) PUnit.unit) := by
    change (E (WidePushout.head (chartAttach I A ha i) PUnit.unit) : W I) =
      originalInclusion I i (chartRetraction I A ha ho i
        (E (WidePushout.head (chartAttach I A ha i) PUnit.unit)))
    rw [chartDomainHomeomorph_head, chartRetraction_basepoint,
      originalInclusion_basepoint]
  have Hfactor (j : I) : ContinuousMap.HomotopyRel
      (f.comp (WidePushout.ι (chartAttach I A ha i) j).hom)
      (g.comp (WidePushout.ι (chartAttach I A ha i) j).hom)
      {chartFactorPoint I A ha i j} := by
    by_cases hji : j = i
    · subst j
      refine (ContinuousMap.HomotopyRel.refl
        (f.comp (WidePushout.ι (chartAttach I A ha i) i).hom)
        {chartFactorPoint I A ha i i}).cast rfl ?_
      apply ContinuousMap.ext
      intro x
      change f (WidePushout.ι (chartAttach I A ha i) i x) =
        g (WidePushout.ι (chartAttach I A ha i) i x)
      have hret : TopCat.widePushoutPointRetraction (XL I) (aL I) i
          (WidePushout.ι (sL I) i (x : XL I i)) = (x : XL I i) :=
        TopCat.widePushoutPointRetraction_ι_apply (XL I) (aL I) i (x : XL I i)
      exact (hf i x).trans
        (((hg i x).trans
          (congrArg (fun y : XL I i ↦ WidePushout.ι (sL I) i y) hret)).symm)
    · have hmem (x : chartFactorSet I A i j) : (x : XL I j) ∈ A j := by
        have hx := x.property
        change (x : XL I j) ∈ (if j = i then Set.univ else A j) at hx
        simpa only [ite_eq_right hji] using hx
      let q : C(chartFactorSet I A i j, A j) :=
        ⟨fun x ↦ ⟨(x : XL I j), hmem x⟩,
          continuous_subtype_val.subtype_mk hmem⟩
      have hq : Set.MapsTo q {chartFactorPoint I A ha i j} {⟨aL I j, ha j⟩} := by
        intro x hx
        have hx : x = chartFactorPoint I A ha i j := Set.mem_singleton_iff.mp hx
        subst x
        apply Set.mem_singleton_iff.mpr
        apply Subtype.ext
        rfl
      let inc : C(A j, W I) :=
        (WidePushout.ι (sL I) j).hom.comp (ContinuousMap.subtypeVal (A j))
      refine ((homotopyRelPrecomp (K j) q hq).compContinuousMap inc).cast ?_ ?_
      · apply ContinuousMap.ext
        intro x
        change WidePushout.ι (sL I) j (x : XL I j) =
          f (WidePushout.ι (chartAttach I A ha i) j x)
        exact (hf j x).symm
      · apply ContinuousMap.ext
        intro x
        change WidePushout.ι (sL I) j (aL I j) =
          g (WidePushout.ι (chartAttach I A ha i) j x)
        have hret : TopCat.widePushoutPointRetraction (XL I) (aL I) i
            (WidePushout.ι (sL I) j (x : XL I j)) = aL I i :=
          TopCat.widePushoutPointRetraction_ι_of_ne_apply (XL I) (aL I) i j hji
            (x : XL I j)
        exact (TopCat.widePushout_point_ι_point (aL I) j).trans
          (((hg j x).trans
            (congrArg (fun y : XL I i ↦ WidePushout.ι (sL I) i y) hret)).trans
              (TopCat.widePushout_point_ι_point (aL I) i)).symm
  let H : ContinuousMap.HomotopyRel f g
      {WidePushout.head (chartAttach I A ha i) PUnit.unit} :=
    TopCat.widePushoutPointHomotopyRel
      (X := fun j ↦ TopCat.of (chartFactorSet I A i j))
      (chartFactorPoint I A ha i) (f := f) (g := g) hhead Hfactor
  have hE : Set.MapsTo
      (E.symm : C((chartOfSets I A ha ho i).1, chartModel I A ha i))
      {(⟨w I, (chartOfSets I A ha ho i).2⟩ : (chartOfSets I A ha ho i).1)}
      {WidePushout.head (chartAttach I A ha i) PUnit.unit} := by
    intro x hx
    have hx : x = (⟨w I, (chartOfSets I A ha ho i).2⟩ :
        (chartOfSets I A ha ho i).1) := Set.mem_singleton_iff.mp hx
    subst x
    apply Set.mem_singleton_iff.mpr
    have hEhead : E (WidePushout.head (chartAttach I A ha i) PUnit.unit) =
        (⟨w I, (chartOfSets I A ha ho i).2⟩ : (chartOfSets I A ha ho i).1) :=
      chartDomainHomeomorph_head I A ha ho i
    exact (congrArg E.symm hEhead).symm.trans
      (E.symm_apply_apply (WidePushout.head (chartAttach I A ha i) PUnit.unit))
  refine (homotopyRelPrecomp H
    (E.symm : C((chartOfSets I A ha ho i).1, chartModel I A ha i)) hE).cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    change (E (E.symm x) : W I) = (x : W I)
    rw [E.apply_symm_apply]
  · apply ContinuousMap.ext
    intro x
    change originalInclusion I i (chartRetraction I A ha ho i (E (E.symm x))) =
      originalInclusion I i (chartRetraction I A ha ho i x)
    rw [E.apply_symm_apply]

private theorem chartInclusionFundamentalGroup (I : Type v)
    (A : ∀ j, Set (XL.{u, v} I j)) (ha : ∀ j, aL.{u, v} I j ∈ A j)
    (ho : ∀ j, IsOpen (A j))
    (K : ∀ j, ContinuousMap.HomotopyRel (ContinuousMap.id (A j))
      (ContinuousMap.const (A j) ⟨aL I j, ha j⟩) {⟨aL I j, ha j⟩}) (i : I) :
    let U := chartOfSets I A ha ho i
    let p := FundamentalGroup.mapOfEq
      (x := (⟨w I, U.2⟩ : U.1)) (y := a0 I i) (chartRetraction I A ha ho i)
      (chartRetraction_basepoint I A ha ho i)
    ((FundamentalGroup.openNhdsCocone (w I)).ι.app U).hom =
      (FundamentalGroup.mapOfEq (originalInclusion I i)
        (originalInclusion_basepoint I i)).comp p := by
  intro U p
  let j : C(U.1, W I) := ContinuousMap.subtypeVal (U.1 : Set (W I))
  have hc : ((originalInclusion I i).comp (chartRetraction I A ha ho i))
      (⟨w I, U.2⟩ : U.1) = w I :=
    (congrArg (originalInclusion I i) (chartRetraction_basepoint I A ha ho i)).trans
      (originalInclusion_basepoint I i)
  calc
    _ = FundamentalGroup.mapOfEq (x := (⟨w I, U.2⟩ : U.1)) (y := w I) j rfl := by
      exact (FundamentalGroup.openNhdsCocone_ι_app_hom (w I) U).trans
        (FundamentalGroup.mapOfEq_rfl j (⟨w I, U.2⟩ : U.1)).symm
    _ = FundamentalGroup.mapOfEq
        ((originalInclusion I i).comp (chartRetraction I A ha ho i)) hc :=
      FundamentalGroup.mapOfEq_eq_of_homotopicRel
        ⟨chartInclusionHomotopy I A ha ho K i⟩ (by simp) rfl hc
    _ = _ := FundamentalGroup.mapOfEq_comp (originalInclusion I i)
      (chartRetraction I A ha ho i) (chartRetraction_basepoint I A ha ho i)
      (originalInclusion_basepoint I i)

private theorem chartKernel_le (I : Type v)
    (A : ∀ j, Set (XL.{u, v} I j)) (ha : ∀ j, aL.{u, v} I j ∈ A j)
    (ho : ∀ j, IsOpen (A j))
    (K : ∀ j, ContinuousMap.HomotopyRel (ContinuousMap.id (A j))
      (ContinuousMap.const (A j) ⟨aL I j, ha j⟩) {⟨aL I j, ha j⟩}) (i : I) :
    let U := chartOfSets I A ha ho i
    let p := FundamentalGroup.mapOfEq
      (x := (⟨w I, U.2⟩ : U.1)) (y := a0 I i) (chartRetraction I A ha ho i)
      (chartRetraction_basepoint I A ha ho i)
    p.ker ≤ (((FundamentalGroup.openNhdsCocone (w I)).ι.app U).hom).ker := by
  intro U p x hx
  change ((FundamentalGroup.openNhdsCocone (w I)).ι.app U).hom x = 1
  calc
    _ = FundamentalGroup.mapOfEq (originalInclusion I i)
        (originalInclusion_basepoint I i) (p x) :=
      DFunLike.congr_fun (chartInclusionFundamentalGroup I A ha ho K i) x
    _ = 1 := by rw [show p x = 1 from hx, map_one]

/-- The punctured-sphere contraction centered at the circle point one. -/
private def arcContraction : ContinuousMap.HomotopyRel
    (ContinuousMap.id arc) (ContinuousMap.const arc arcOne) {arcOne} := by
  let a : arc :=
    ⟨-((-1 : Circle) : Metric.sphere (0 : ℂ) 1),
      (ne_neg_of_mem_unit_sphere ℝ (-1 : Circle)).symm⟩
  have ha : a = arcOne := by
    apply Subtype.ext
    apply Subtype.ext
    change -(-(1 : ℂ)) = (1 : ℂ)
    exact neg_neg (1 : ℂ)
  rw [← ha]
  exact Metric.Sphere.complSingletonContraction (E := ℂ) (-1 : Circle)

private theorem freeGroupLift_bijective (I : Type v)
    (e : ∀ i, FundamentalGroup (X0.{u, v} I i) (a0.{u, v} I i) ≃* Multiplicative ℤ)
    (z : ∀ i, FundamentalGroup (X0.{u, v} I i) (a0.{u, v} I i))
    (he : ∀ i, e i (z i) = Multiplicative.ofAdd (1 : ℤ))
    (C : TopologicalSpace.OpenNhds (X := W.{u, v} I) (w.{u, v} I))
    (hpcC : IsPathConnected (C.1 : Set (W.{u, v} I)))
    (hpcX : ∀ i, IsPathConnected (Set.univ : Set (X0.{u, v} I i)))
    (hnull : ∀ i,
      (FundamentalGroup.map
        (ContinuousMap.subtypeVal
          (originalInclusion.{u, v} I i ⁻¹' (C.1 : Set (W.{u, v} I))))
        ⟨a0.{u, v} I i, by
          change originalInclusion.{u, v} I i (a0.{u, v} I i) ∈ C.1
          rw [originalInclusion_basepoint]
          exact C.2⟩).range = ⊥)
    (hq : Function.Surjective
      (TopCat.widePushoutPointFundamentalGroupCoproductMap (a0.{u, v} I))) :
    Function.Bijective
      (FreeGroup.lift (fun i ↦ originalGroupMap.{u, v} I i (z i))) := by
  let β : FreeGroup I →* FundamentalGroup (W.{u, v} I) (w.{u, v} I) :=
    FreeGroup.lift (fun i ↦ originalGroupMap.{u, v} I i (z i))
  let φ : ∀ i, FundamentalGroup (X0.{u, v} I i) (a0.{u, v} I i) →* FreeGroup I :=
    fun i ↦ (zpowersHom (FreeGroup I) (FreeGroup.of i)).comp (e i).toMonoidHom
  have hφ (i : I) : φ i (z i) = FreeGroup.of i := by
    change zpowersHom (FreeGroup I) (FreeGroup.of i) (e i (z i)) = _
    rw [he i, zpowersHom_apply]
    simp
  let ψ : FundamentalGroup (W.{u, v} I) (w.{u, v} I) →* FreeGroup I :=
    TopCat.widePushoutPointFundamentalGroupExtend (a0.{u, v} I)
      (FreeGroup I) φ C hpcC hpcX hnull
  have hψ (i : I) : ψ.comp (originalGroupMap.{u, v} I i) = φ i :=
    TopCat.widePushoutPointFundamentalGroupExtend_comp_inclusion
      (a0.{u, v} I) (FreeGroup I) φ C hpcC hpcX hnull i
  have hleft : ψ.comp β = MonoidHom.id (FreeGroup I) := by
    apply FreeGroup.ext_hom
    intro i
    change ψ (β (FreeGroup.of i)) = FreeGroup.of i
    rw [show β (FreeGroup.of i) = originalGroupMap.{u, v} I i (z i) from
      FreeGroup.lift_apply_of]
    exact (DFunLike.congr_fun (hψ i) (z i)).trans (hφ i)
  have hβφ (i : I) : β.comp (φ i) = originalGroupMap.{u, v} I i := by
    apply (MonoidHom.cancel_right (f := (e i).symm.toMonoidHom)
      (e i).symm.surjective).mp
    apply MonoidHom.ext_mint
    have hz : (e i).symm (Multiplicative.ofAdd (1 : ℤ)) = z i := by
      rw [← he i, MulEquiv.symm_apply_apply]
    change β (φ i ((e i).symm (Multiplicative.ofAdd (1 : ℤ)))) =
      originalGroupMap.{u, v} I i ((e i).symm (Multiplicative.ofAdd (1 : ℤ)))
    rw [hz, hφ]
    exact FreeGroup.lift_apply_of
  let τ := Monoid.CoprodI.lift φ
  have hfactor : β.comp τ =
      TopCat.widePushoutPointFundamentalGroupCoproductMap (a0.{u, v} I) := by
    apply Monoid.CoprodI.ext_hom
    intro i
    rw [MonoidHom.comp_assoc, Monoid.CoprodI.lift_comp_of]
    exact (hβφ i).trans
      (TopCat.widePushoutPointFundamentalGroupCoproductMap_comp_of (a0.{u, v} I) i).symm
  refine ⟨?_, ?_⟩
  · apply Function.LeftInverse.injective (f := β) (g := ψ)
    intro g
    exact DFunLike.congr_fun hleft g
  · intro g
    obtain ⟨a, ha⟩ := hq g
    refine ⟨τ a, ?_⟩
    exact (DFunLike.congr_fun hfactor a).trans ha

/-- The punctured-circle contractions kill the physical chart-collapse kernels. -/
private theorem coproductMap_surjective (I : Type v) :
    Function.Surjective
      (TopCat.widePushoutPointFundamentalGroupCoproductMap (a0.{u, v} I)) := by
  apply (TopCat.widePushoutPointFundamentalGroupCoproductMap_surjective_iff
    (a0.{u, v} I) (core.{u, v} I) (core_isPathConnected.{u, v} I)
    (X0_isPathConnected.{u, v} I) (originalCore_hnull.{u, v} I)).2
  intro i
  exact chartKernel_le.{u, v} I (factorArc.{u, v} I) (factorArc_mem.{u, v} I)
    (factorArc_isOpen.{u, v} I) (factorContraction.{u, v} I arcContraction) i

/-- The free-group lift uses the included positively normalized factor classes. -/
private theorem originalFreeGroupLift_bijective (I : Type v) :
    Function.Bijective
      (FreeGroup.lift (fun i ↦ originalGroupMap.{u, v} I i (posX.{u, v} I i))) :=
  freeGroupLift_bijective.{u, v} I (circleCoordinate.{u, v} I) (posX.{u, v} I)
    (circleCoordinate_posX.{u, v} I) (core.{u, v} I) (core_isPathConnected.{u, v} I)
    (X0_isPathConnected.{u, v} I) (originalCore_hnull.{u, v} I)
    (coproductMap_surjective.{u, v} I)

/-- The included positive circle classes freely generate the bouquet fundamental group. -/
private theorem generatorMap_bijective (I : Type v) :
    Function.Bijective (CircleBouquet.generatorMap.{u, v} I) := by
  have h : Function.Bijective
      ((comparisonFundamentalGroup.{u, v} I).toMonoidHom.comp
        (FreeGroup.lift (fun i ↦ originalGroupMap.{u, v} I i (posX.{u, v} I i)))) :=
    (comparisonFundamentalGroup.{u, v} I).bijective.comp
      (originalFreeGroupLift_bijective.{u, v} I)
  rw [comparisonFundamentalGroup_comp_lift] at h
  exact h

end CircleBouquetGeometryData

namespace CircleBouquet

/-- May's circle-bouquet computation (Chapter 2, §8): the included positive circle
classes freely generate the bouquet fundamental group. -/
theorem generatorMap_bijective (I : Type v) :
    Function.Bijective (generatorMap.{u, v} I) := by
  exact CircleBouquetGeometryData.generatorMap_bijective.{u, v} I

/-- The free group on the circle indices, identified with the bouquet fundamental
group by its included positive generators. -/
def generatorEquiv (I : Type v) :
    FreeGroup I ≃* FundamentalGroup (space.{u, v} I) (basepoint.{u, v} I) :=
  MulEquiv.ofBijective (generatorMap.{u, v} I) (generatorMap_bijective.{u, v} I)

/-- The equivalence's forward homomorphism is the prescribed generator map. -/
@[simp] theorem generatorEquiv_toMonoidHom (I : Type v) :
    (generatorEquiv.{u, v} I : FreeGroup I →*
      FundamentalGroup (space.{u, v} I) (basepoint.{u, v} I)) =
      generatorMap.{u, v} I := by
  ext x
  rfl

/-- Each free generator is the included counterclockwise circle class. -/
@[simp] theorem generatorEquiv_of {I : Type v} (i : I) :
    generatorEquiv.{u, v} I (FreeGroup.of i) = positiveGenerator.{u, v} i := by
  change generatorMap.{u, v} I (FreeGroup.of i) = positiveGenerator.{u, v} i
  exact generatorMap_of i

/-- The inverse equivalence sends each included positive class to its free generator. -/
@[simp] theorem generatorEquiv_symm_positiveGenerator {I : Type v} (i : I) :
    (generatorEquiv.{u, v} I).symm (positiveGenerator.{u, v} i) = FreeGroup.of i := by
  rw [← generatorEquiv_of.{u, v} i, MulEquiv.symm_apply_apply]

/-- Assigning arbitrary values to the included positive generators is equivalent
to specifying a homomorphism from the bouquet fundamental group to a group. -/
def lift {I : Type v} {G : Type w} [Group G] :
    (I → G) ≃ (FundamentalGroup (space.{u, v} I) (basepoint.{u, v} I) →* G) :=
  FreeGroup.lift.trans
    (MulEquiv.monoidHomCongrLeftEquiv (N := G) (generatorEquiv.{u, v} I))

/-- The lifted homomorphism is the free-group lift after the inverse equivalence. -/
theorem lift_eq_comp {I : Type v} {G : Type w} [Group G] (f : I → G) :
    lift.{u, v, w} f =
      (FreeGroup.lift f).comp (generatorEquiv.{u, v} I).symm.toMonoidHom := by
  rfl

/-- Restricting a homomorphism records its values on the positive generators. -/
@[simp] theorem lift_symm_apply {I : Type v} {G : Type w} [Group G]
    (φ : FundamentalGroup (space.{u, v} I) (basepoint.{u, v} I) →* G) (i : I) :
    (lift.{u, v, w} (I := I) (G := G)).symm φ i =
      φ (positiveGenerator.{u, v} i) := by
  change φ (generatorEquiv.{u, v} I (FreeGroup.of i)) = _
  rw [generatorEquiv_of]

/-- A lift has its assigned positive-generator values. -/
@[simp] theorem lift_positiveGenerator {I : Type v} {G : Type w} [Group G]
    (f : I → G) (i : I) :
    lift.{u, v, w} f (positiveGenerator.{u, v} i) = f i := by
  rw [lift_eq_comp]
  change FreeGroup.lift f ((generatorEquiv.{u, v} I).symm
    (positiveGenerator.{u, v} i)) = f i
  rw [generatorEquiv_symm_positiveGenerator, FreeGroup.lift_apply_of]

/-- Pulling back along the generator map gives the stock free-group lift. -/
@[simp] theorem lift_comp_generatorMap {I : Type v} {G : Type w} [Group G]
    (f : I → G) :
    (lift.{u, v, w} f).comp (generatorMap.{u, v} I) = FreeGroup.lift f := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply, generatorMap_of, lift_positiveGenerator,
    FreeGroup.lift_apply_of]

/-- Generator values uniquely determine a homomorphism to a group. -/
theorem lift_unique {I : Type v} {G : Type w} [Group G] (f : I → G)
    (φ : FundamentalGroup (space.{u, v} I) (basepoint.{u, v} I) →* G)
    (hφ : ∀ i, φ (positiveGenerator.{u, v} i) = f i) :
    φ = lift.{u, v, w} f := by
  apply (lift.{u, v, w} (I := I) (G := G)).symm.injective
  rw [Equiv.symm_apply_apply]
  funext i
  exact (lift_symm_apply φ i).trans (hφ i)

/-- The generator-value equivalence is natural under homomorphisms of target
groups, whose universes are independent of each other and of the bouquet. -/
theorem lift_natural {I : Type v} {G : Type w} {H : Type w'}
    [Group G] [Group H] (f : I → G) (k : G →* H) :
    k.comp (lift.{u, v, w} f) = lift.{u, v, w'} (k ∘ f) := by
  apply lift_unique
  intro i
  change k (lift.{u, v, w} f (positiveGenerator.{u, v} i)) = k (f i)
  rw [lift_positiveGenerator]

/-- Positive loops on distinct included circles do not commute. -/
theorem positiveGenerator_mul_ne_mul {I : Type v} {i j : I} (hij : i ≠ j) :
    positiveGenerator.{u, v} i * positiveGenerator.{u, v} j ≠
      positiveGenerator.{u, v} j * positiveGenerator.{u, v} i := by
  classical
  intro h
  have hfree : FreeGroup.of i * FreeGroup.of j = FreeGroup.of j * FreeGroup.of i := by
    apply (generatorEquiv.{u, v} I).injective
    simpa only [map_mul, generatorEquiv_of] using h
  -- These swaps send the two products at `none` to `some j` and `some i`.
  let ρ : FreeGroup I →* Equiv.Perm (Option I) :=
    FreeGroup.lift (fun k => Equiv.swap none (some k))
  have hρ := congrArg (fun g : FreeGroup I => ρ g none) hfree
  simp [ρ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hij, Ne.symm hij] at hρ

end CircleBouquet

end

end
