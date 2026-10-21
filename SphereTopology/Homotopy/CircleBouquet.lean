/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.Circle
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Bouquets of circles and their positive generators

`CircleBouquet.space I` is the categorical wide pushout of the maps from a point to
copies of the complex unit circle at one. The point is part of the diagram even
when `I` is empty. The index universe and the ambient universe are independent;
the colimit lives in their maximum. `Homeomorph.ulift` supplies the universe
transport, without changing the original circle or its topology.

`CircleBouquet.generatorMap` is the homomorphism from `FreeGroup I` to the
fundamental group of this space. It sends each free generator to the included
counterclockwise loop `Circle.loop 1`. The fundamental group uses Mathlib's
endomorphism multiplication: `p * q = q.trans p`, so the right loop is traversed
first. No inversion is inserted in the positive generators.

The descent and extensionality API is the universal property of the categorical wide
pushout. Retraction onto any one circle independently detects its positive loop
using `Circle.fundamentalGroupEquivInt` and its positive normalization.

## Implementation notes

The lifted-circle diagram is private. The public constructions are used through
`inclusion_basepoint`, `inclusion_desc`, `desc_basepoint` and `hom_ext`, rather than
by unfolding the chosen colimit or its universe transport.

Bijectivity of `generatorMap` and the resulting identification of the bouquet's
fundamental group with `FreeGroup I` are not proved here.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  p. 19, for the circle-bouquet setting; the fundamental-group calculation is
  not established in this module.
* Mathlib's wide pushouts, topological colimits, path homotopy quotients and
  free groups supply the constructions used here.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CircleBouquet

/-- The one-point head of a bouquet diagram. -/
private def point : TopCat.{u} := TopCat.of PUnit.{u + 1}

/-- A copy of the original circle in the ambient universe. -/
private def circle : TopCat.{u} := TopCat.of (ULift.{u} Circle)

/-- The attaching map selects one in every circle. -/
private def attach (I : Type v) (_i : I) : point.{max u v} ⟶ circle.{max u v} :=
  TopCat.const (ULift.up (1 : Circle))

/-- The bouquet, formed by the categorical wide pushout of the based circles. -/
def space (I : Type v) : TopCat.{max u v} :=
  widePushout point.{max u v} (fun _ : I ↦ circle.{max u v}) (attach.{u, v} I)

/-- The map from the one-point head of the diagram. -/
private def head (I : Type v) : point.{max u v} ⟶ space.{u, v} I :=
  WidePushout.head (attach.{u, v} I)

/-- The common point, present also for the empty family. -/
def basepoint (I : Type v) : space.{u, v} I :=
  head.{u, v} I PUnit.unit

/-- The colimit inclusion of a universe-lifted factor. -/
private def factorInclusion {I : Type v} (i : I) : circle.{max u v} ⟶ space.{u, v} I :=
  WidePushout.ι (attach.{u, v} I) i

/-- The inclusion whose domain is the original complex unit circle. -/
def inclusion {I : Type v} (i : I) : C(Circle, space.{u, v} I) :=
  (factorInclusion.{u, v} i).hom.comp
    ((Homeomorph.ulift.{max u v, 0} (X := Circle)).symm :
      C(Circle, ULift.{max u v} Circle))

/-- All circle inclusions take one to the common point. -/
@[simp] theorem inclusion_basepoint {I : Type v} (i : I) :
    inclusion.{u, v} i 1 = basepoint.{u, v} I := by
  exact congrArg (fun f : point.{max u v} ⟶ space.{u, v} I ↦ f PUnit.unit)
    (WidePushout.arrow_ι (attach.{u, v} I) i)

/-- Descend maps from the original circles that agree at one. This is
`WidePushout.desc`, with `Homeomorph.ulift` on each factor. -/
def desc {I : Type v} {Y : TopCat.{max u v}} (y : Y)
    (f : I → C(Circle, Y)) (hf : ∀ i, f i 1 = y) :
    space.{u, v} I ⟶ Y :=
  WidePushout.desc (arrows := attach.{u, v} I) (TopCat.const y)
    (fun i ↦ TopCat.ofHom ((f i).comp
      (Homeomorph.ulift.{max u v, 0} (X := Circle) :
        C(ULift.{max u v} Circle, Circle))))
    (by
      intro i
      apply TopCat.ext
      intro x
      change f i 1 = y
      exact hf i)

/-- The factor equation for descent. -/
private theorem factorInclusion_desc {I : Type v} {Y : TopCat.{max u v}} (y : Y)
    (f : I → C(Circle, Y)) (hf : ∀ i, f i 1 = y) (i : I) :
    factorInclusion.{u, v} i ≫ desc.{u, v} y f hf =
      TopCat.ofHom ((f i).comp
        (Homeomorph.ulift.{max u v, 0} (X := Circle) :
          C(ULift.{max u v} Circle, Circle))) :=
  WidePushout.ι_desc (attach.{u, v} I) _ _ _ i

/-- Descent restricts to the prescribed map on each original circle. -/
@[simp] theorem inclusion_desc {I : Type v} {Y : TopCat.{max u v}} (y : Y)
    (f : I → C(Circle, Y)) (hf : ∀ i, f i 1 = y) (i : I) :
    (desc.{u, v} y f hf).hom.comp (inclusion.{u, v} i) = f i := by
  apply ContinuousMap.ext
  intro z
  exact congrArg (fun k : circle.{max u v} ⟶ Y ↦ k (ULift.up z))
    (factorInclusion_desc.{u, v} y f hf i)

/-- Descent takes the head point to the prescribed point. -/
@[simp] theorem desc_basepoint {I : Type v} {Y : TopCat.{max u v}} (y : Y)
    (f : I → C(Circle, Y)) (hf : ∀ i, f i 1 = y) :
    desc.{u, v} y f hf (basepoint.{u, v} I) = y := by
  exact congrArg (fun k : point.{max u v} ⟶ Y ↦ k PUnit.unit)
    (WidePushout.head_desc (attach.{u, v} I) _ _ _)

/-- Maps out of the bouquet are determined by their circle restrictions and their
value at the common point. Keeping the latter condition also covers the empty family. -/
theorem hom_ext {I : Type v} {Y : TopCat.{max u v}}
    (f g : space.{u, v} I ⟶ Y)
    (hi : ∀ i, f.hom.comp (inclusion.{u, v} i) =
      g.hom.comp (inclusion.{u, v} i))
    (hb : f (basepoint.{u, v} I) = g (basepoint.{u, v} I)) : f = g := by
  apply WidePushout.hom_ext (attach.{u, v} I) f g
  · intro i
    apply TopCat.ext
    intro z
    exact congrArg (fun k : C(Circle, Y) ↦ k z.down) (hi i)
  · apply TopCat.ext
    intro x
    cases x
    exact hb

/-- The induced image of the positive loop `Circle.loop 1`. -/
def positiveGenerator {I : Type v} (i : I) :
    FundamentalGroup (space.{u, v} I) (basepoint.{u, v} I) :=
  FundamentalGroup.mapOfEq (inclusion.{u, v} i) (inclusion_basepoint.{u, v} i)
    (FundamentalGroup.fromPath ⟦Circle.loop 1⟧)

/-- The positive generator is the class of the included counterclockwise
loop, with endpoints transported by the inclusion's basepoint equation. -/
theorem positiveGenerator_eq_loop {I : Type v} (i : I) :
    positiveGenerator.{u, v} i = FundamentalGroup.fromPath
      ⟦((Circle.loop 1).map (inclusion.{u, v} i).continuous).cast
        (inclusion_basepoint.{u, v} i).symm (inclusion_basepoint.{u, v} i).symm⟧ := by
  rw [positiveGenerator, FundamentalGroup.mapOfEq_apply]
  rfl

/-- The canonical generator homomorphism into the fundamental group. -/
def generatorMap (I : Type v) :
    FreeGroup I →* FundamentalGroup (space.{u, v} I) (basepoint.{u, v} I) :=
  FreeGroup.lift (positiveGenerator.{u, v} (I := I))

/-- Every free generator maps to the prescribed positive loop class. -/
@[simp] theorem generatorMap_of {I : Type v} (i : I) :
    generatorMap.{u, v} I (FreeGroup.of i) = positiveGenerator.{u, v} i :=
  FreeGroup.lift_apply_of

/-- The factor maps for retraction onto one circle: identity on that circle and
constant at one on all other circles. -/
private def retractionFactor {I : Type v} (i j : I) :
    circle.{max u v} ⟶ circle.{max u v} := by
  classical
  exact if j = i then 𝟙 _ else TopCat.const (ULift.up (1 : Circle))

/-- The chosen factor is unchanged by its retraction map. -/
private theorem retractionFactor_self {I : Type v} (i : I) :
    retractionFactor.{u, v} i i = 𝟙 circle.{max u v} := by
  classical
  simp [retractionFactor]

/-- Other factors are sent to one. -/
private theorem retractionFactor_of_ne {I : Type v} (i j : I) (h : j ≠ i) :
    retractionFactor.{u, v} i j = TopCat.const (ULift.up (1 : Circle)) := by
  classical
  simp [retractionFactor, h]

/-- Retraction onto the universe-lifted circle, constructed by `WidePushout.desc`. -/
private def retractionLifted {I : Type v} (i : I) :
    space.{u, v} I ⟶ circle.{max u v} :=
  WidePushout.desc (arrows := attach.{u, v} I)
    (TopCat.const (ULift.up (1 : Circle))) (retractionFactor.{u, v} i)
    (by
      classical
      intro j
      apply TopCat.ext
      intro x
      by_cases h : j = i <;> simp [retractionFactor, h, attach]
      rfl)

/-- The descent equation for a retraction. -/
private theorem factorInclusion_retractionLifted {I : Type v} (i j : I) :
    factorInclusion.{u, v} j ≫ retractionLifted.{u, v} i =
      retractionFactor.{u, v} i j :=
  WidePushout.ι_desc (attach.{u, v} I) _ _ _ j

/-- Retraction to the original circle, using `Homeomorph.ulift`. -/
def retraction {I : Type v} (i : I) : C(space.{u, v} I, Circle) :=
  (Homeomorph.ulift.{max u v, 0} (X := Circle) :
    C(ULift.{max u v} Circle, Circle)).comp (retractionLifted.{u, v} i).hom

/-- Retraction composed with its circle inclusion is the identity. -/
@[simp] theorem retraction_inclusion {I : Type v} (i : I) :
    (retraction.{u, v} i).comp (inclusion.{u, v} i) = ContinuousMap.id Circle := by
  have h : factorInclusion.{u, v} i ≫ retractionLifted.{u, v} i =
      𝟙 circle.{max u v} := by
    rw [factorInclusion_retractionLifted, retractionFactor_self]
  apply ContinuousMap.ext
  intro z
  exact congrArg (fun k : circle.{max u v} ⟶ circle.{max u v} ↦
    (k (ULift.up z)).down) h

/-- Retraction is constant at one on each other circle. -/
theorem retraction_inclusion_of_ne {I : Type v} (i j : I) (hji : j ≠ i) :
    (retraction.{u, v} i).comp (inclusion.{u, v} j) = ContinuousMap.const Circle 1 := by
  have h : factorInclusion.{u, v} j ≫ retractionLifted.{u, v} i =
      TopCat.const (ULift.up (1 : Circle)) := by
    rw [factorInclusion_retractionLifted, retractionFactor_of_ne i j hji]
  apply ContinuousMap.ext
  intro z
  exact congrArg (fun k : circle.{max u v} ⟶ circle.{max u v} ↦
    (k (ULift.up z)).down) h

/-- Every retraction fixes the common point at one. -/
@[simp] theorem retraction_basepoint {I : Type v} (i : I) :
    retraction.{u, v} i (basepoint.{u, v} I) = 1 := by
  rw [← inclusion_basepoint.{u, v} i]
  exact congrArg (fun k : C(Circle, Circle) ↦ k 1) (retraction_inclusion.{u, v} i)

/-- Retraction sends the included positive loop class back to the original
positive circle class. This does not use any presentation of the bouquet group. -/
theorem retraction_positiveGenerator {I : Type v} (i : I) :
    FundamentalGroup.mapOfEq (retraction.{u, v} i) (retraction_basepoint.{u, v} i)
        (positiveGenerator.{u, v} i) =
      FundamentalGroup.fromPath ⟦Circle.loop 1⟧ := by
  rw [positiveGenerator_eq_loop, FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk (Circle.loop 1)
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  exact congrArg (fun k : C(Circle, Circle) ↦ k (Circle.loop 1 t))
    (retraction_inclusion.{u, v} i)

/-- Each included positive generator is nonidentity, independently of the free-group
calculation, since its retraction is the positively normalized circle generator. -/
theorem positiveGenerator_ne_one {I : Type v} (i : I) :
    positiveGenerator.{u, v} i ≠ 1 := by
  intro h
  have h' := congrArg
    (FundamentalGroup.mapOfEq (retraction.{u, v} i) (retraction_basepoint.{u, v} i)) h
  rw [retraction_positiveGenerator, map_one] at h'
  exact Circle.loop_one_ne_one h'

end CircleBouquet

end

end

/-!
# Circle-bouquet clients

The two-circle bouquet uses the positive loops in the original circle.
Retraction computes a positive generator's existing circle coordinate.
The empty-family boundary retains the common point.
-/

noncomputable section

open CategoryTheory

universe u

namespace SphereTopologyTest

/-- In the two-circle bouquet, the first positive free generator retracts to the
circle class with coordinate one. -/
private theorem two_circle_generator_coordinate :
    Circle.fundamentalGroupEquivInt
      (FundamentalGroup.mapOfEq (CircleBouquet.retraction.{u, 0} false)
        (CircleBouquet.retraction_basepoint.{u, 0} false)
        (CircleBouquet.generatorMap.{u, 0} Bool (FreeGroup.of false))) =
      Multiplicative.ofAdd (1 : ℤ) := by
  rw [CircleBouquet.generatorMap_of, CircleBouquet.retraction_positiveGenerator,
    Circle.fundamentalGroupEquivInt_loop]

/-- With no circles, the head still supplies exactly the one common point. -/
private theorem empty_bouquet_point (x : CircleBouquet.space.{u, 0} Empty) :
    x = CircleBouquet.basepoint.{u, 0} Empty := by
  have h : (𝟙 (CircleBouquet.space.{u, 0} Empty)) =
      TopCat.const (CircleBouquet.basepoint.{u, 0} Empty) := by
    apply CircleBouquet.hom_ext
    · intro i
      cases i
    · rfl
  exact congrArg (fun f : CircleBouquet.space.{u, 0} Empty ⟶
    CircleBouquet.space.{u, 0} Empty ↦ f x) h

end SphereTopologyTest

end
