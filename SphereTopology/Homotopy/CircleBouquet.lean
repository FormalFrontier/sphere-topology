/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.Circle
public import SphereTopology.Topology.WidePushoutHomotopy
public import SphereTopology.Topology.WidePushoutRetraction
public import SphereTopology.Topology.WidePushout.Subfamily
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Basic

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
using `Circle.fundamentalGroupEquivInt` and its positive normalization. The
retraction specializes `TopCat.widePushoutPointRetraction` on the already-lifted
circle diagram, as recorded by `retraction_eq_widePushoutPointRetraction`.
Subfamilies include and retract by the general point-wide-pushout maps; every
based loop factors through a finite subbouquet with both endpoints preserved.

## Implementation notes

The head and factor helpers are private; `space` exposes their categorical diagram.
The other public constructions are used through
`inclusion_basepoint`, `inclusion_desc`, `desc_basepoint` and `hom_ext`, rather than
by unfolding the chosen colimit or its universe transport. Likewise, `prodDesc`
and `homotopy` keep this diagram hidden; their common-point and original-circle
computation and uniqueness lemmas characterize the descended families.

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
@[expose] def space (I : Type v) : TopCat.{max u v} :=
  widePushout (TopCat.of PUnit.{max u v + 1})
    (fun _ : I ↦ TopCat.of (ULift.{max u v} Circle))
    (fun _ ↦ TopCat.const (ULift.up (1 : Circle)))

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

/-- Functions on a bouquet are determined by the common point and the
restrictions to the original circles, with no topology on the target. -/
theorem funext {I : Type v} {Y : Sort*} {f g : space.{u, v} I → Y}
    (hi : ∀ i z, f (inclusion.{u, v} i z) = g (inclusion.{u, v} i z))
    (hb : f (basepoint.{u, v} I) = g (basepoint.{u, v} I)) : f = g := by
  apply TopCat.widePushout_funext (attach.{u, v} I)
  · intro x
    cases x
    exact hb
  · intro i z
    exact hi i z.down

/-- Descend jointly continuous families on the original circles with a moving
common-point value. The parameter and target universes are independent. -/
def prodDesc {I : Type v} {P Y : Type*}
    [TopologicalSpace P] [TopologicalSpace Y] [LocallyCompactPair P Y]
    (g : C(P, Y)) (h : I → C(P × Circle, Y))
    (w : ∀ i t, h i (t, 1) = g t) : C(P × space.{u, v} I, Y) :=
  TopCat.widePushoutProdDesc (attach.{u, v} I) (g.comp ContinuousMap.fst)
    (fun i ↦ (h i).comp ((ContinuousMap.id P).prodMap
      (Homeomorph.ulift.{max u v, 0} (X := Circle) : C(ULift.{max u v} Circle, Circle))))
    (fun i t _ ↦ w i t)

/-- Circle-family descent has the prescribed moving value at the common point. -/
@[simp] theorem prodDesc_basepoint {I : Type v} {P Y : Type*}
    [TopologicalSpace P] [TopologicalSpace Y] [LocallyCompactPair P Y]
    (g : C(P, Y)) (h : I → C(P × Circle, Y))
    (w : ∀ i t, h i (t, 1) = g t) (t : P) :
    prodDesc.{u, v} g h w (t, basepoint.{u, v} I) = g t :=
  TopCat.widePushoutProdDesc_head (attach.{u, v} I) (g.comp ContinuousMap.fst)
    (fun i ↦ (h i).comp ((ContinuousMap.id P).prodMap
      (Homeomorph.ulift.{max u v, 0} (X := Circle) : C(ULift.{max u v} Circle, Circle))))
    (fun i t _ ↦ w i t) t PUnit.unit

/-- Circle-family descent restricts to each prescribed original-circle family. -/
@[simp] theorem prodDesc_inclusion {I : Type v} {P Y : Type*}
    [TopologicalSpace P] [TopologicalSpace Y] [LocallyCompactPair P Y]
    (g : C(P, Y)) (h : I → C(P × Circle, Y))
    (w : ∀ i t, h i (t, 1) = g t) (i : I) (t : P) (z : Circle) :
    prodDesc.{u, v} g h w (t, inclusion.{u, v} i z) = h i (t, z) :=
  TopCat.widePushoutProdDesc_ι (attach.{u, v} I) (g.comp ContinuousMap.fst)
    (fun i ↦ (h i).comp ((ContinuousMap.id P).prodMap
      (Homeomorph.ulift.{max u v, 0} (X := Circle) : C(ULift.{max u v} Circle, Circle))))
    (fun i t _ ↦ w i t) i t (ULift.up z)

/-- The moving common-point and circle equations uniquely determine descent. -/
theorem prodDesc_unique {I : Type v} {P Y : Type*}
    [TopologicalSpace P] [TopologicalSpace Y] [LocallyCompactPair P Y]
    (g : C(P, Y)) (h : I → C(P × Circle, Y))
    (w : ∀ i t, h i (t, 1) = g t) (a : C(P × space.{u, v} I, Y))
    (hi : ∀ i t z, a (t, inclusion.{u, v} i z) = h i (t, z))
    (hb : ∀ t, a (t, basepoint.{u, v} I) = g t) : a = prodDesc.{u, v} g h w := by
  apply ContinuousMap.ext
  rintro ⟨t, x⟩
  exact congrFun (CircleBouquet.funext
    (f := fun x ↦ a (t, x)) (g := fun x ↦ prodDesc.{u, v} g h w (t, x))
    (fun i z ↦ (hi i t z).trans (prodDesc_inclusion g h w i t z).symm)
    ((hb t).trans (prodDesc_basepoint g h w t).symm)) x

section Homotopy

variable {I : Type v} {Y : Type*} [TopologicalSpace Y]
  {a₀ a₁ : C(space.{u, v} I, Y)}
  (g : ContinuousMap.Homotopy
    (ContinuousMap.const PUnit.{1} (a₀ (basepoint.{u, v} I)))
    (ContinuousMap.const PUnit.{1} (a₁ (basepoint.{u, v} I))))
  (h : ∀ i, ContinuousMap.Homotopy (a₀.comp (inclusion.{u, v} i))
    (a₁.comp (inclusion.{u, v} i)))
  (w : ∀ i t, h i (t, 1) = g (t, PUnit.unit))

/-- Transport a common-point path to the universe-lifted head. -/
private def homotopyHead : ContinuousMap.Homotopy
    (a₀.comp (head.{u, v} I).hom) (a₁.comp (head.{u, v} I).hom) where
  toContinuousMap := g.toContinuousMap.comp
    ((ContinuousMap.id unitInterval).prodMap (ContinuousMap.const _ PUnit.unit))
  map_zero_left := by
    intro b
    cases b
    exact g.map_zero_left PUnit.unit
  map_one_left := by
    intro b
    cases b
    exact g.map_one_left PUnit.unit

/-- Transport a circle homotopy to its universe-lifted factor. -/
private def homotopyFactor (i : I) : ContinuousMap.Homotopy
    (a₀.comp (factorInclusion.{u, v} i).hom)
    (a₁.comp (factorInclusion.{u, v} i).hom) where
  toContinuousMap := (h i).toContinuousMap.comp
    ((ContinuousMap.id unitInterval).prodMap
      (Homeomorph.ulift.{max u v, 0} (X := Circle) : C(ULift.{max u v} Circle, Circle)))
  map_zero_left := fun z ↦ (h i).map_zero_left z.down
  map_one_left := fun z ↦ (h i).map_one_left z.down

/-- Glue homotopies on the original circles, with a prescribed common-point
path and agreement at one throughout time. The common point may move. -/
def homotopy : ContinuousMap.Homotopy a₀ a₁ :=
  TopCat.widePushoutHomotopy (attach.{u, v} I) (homotopyHead g) (homotopyFactor h)
    (fun i t _ ↦ w i t)

/-- The glued bouquet homotopy has its prescribed common-point path. -/
@[simp] theorem homotopy_basepoint (t : unitInterval) :
    homotopy.{u, v} g h w (t, basepoint.{u, v} I) = g (t, PUnit.unit) :=
  TopCat.widePushoutHomotopy_head (attach.{u, v} I) (homotopyHead g) (homotopyFactor h)
    (fun i t _ ↦ w i t) t PUnit.unit

/-- The glued bouquet homotopy restricts to every original-circle homotopy. -/
@[simp] theorem homotopy_inclusion (i : I) (t : unitInterval) (z : Circle) :
    homotopy.{u, v} g h w (t, inclusion.{u, v} i z) = h i (t, z) :=
  TopCat.widePushoutHomotopy_ι (attach.{u, v} I) (homotopyHead g) (homotopyFactor h)
    (fun i t _ ↦ w i t) i t (ULift.up z)

/-- The common-point and original-circle equations uniquely characterize the
bouquet homotopy at every time. -/
theorem homotopy_unique (H : ContinuousMap.Homotopy a₀ a₁)
    (hi : ∀ i t z, H (t, inclusion.{u, v} i z) = h i (t, z))
    (hb : ∀ t, H (t, basepoint.{u, v} I) = g (t, PUnit.unit)) :
    H = homotopy.{u, v} g h w := by
  apply ContinuousMap.Homotopy.ext
  rintro ⟨t, x⟩
  exact congrFun (CircleBouquet.funext
    (f := fun x ↦ H (t, x)) (g := fun x ↦ homotopy.{u, v} g h w (t, x))
    (fun i z ↦ (hi i t z).trans (homotopy_inclusion g h w i t z).symm)
    ((hb t).trans (homotopy_basepoint g h w t).symm)) x

end Homotopy

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

/-- Retraction to the original circle, using the point-wide-pushout retraction
and `Homeomorph.ulift`. -/
@[expose] def retraction {I : Type v} (i : I) : C(space.{u, v} I, Circle) :=
  (Homeomorph.ulift.{max u v, 0} (X := Circle) :
    C(ULift.{max u v} Circle, Circle)).comp
      (TopCat.widePushoutPointRetraction.{u, v}
        (fun _ : I ↦ TopCat.of (ULift.{max u v} Circle))
        (fun _ ↦ ULift.up (1 : Circle)) i).hom

/-- The bouquet retraction is the general point-wide-pushout retraction on the
already-lifted circle diagram, followed by the homeomorphism to the original circle. -/
theorem retraction_eq_widePushoutPointRetraction {I : Type v} (i : I) :
    retraction.{u, v} i =
      (Homeomorph.ulift.{max u v, 0} (X := Circle) :
        C(ULift.{max u v} Circle, Circle)).comp
        (TopCat.widePushoutPointRetraction.{u, v}
          (fun _ : I ↦ TopCat.of (ULift.{max u v} Circle))
          (fun _ ↦ ULift.up (1 : Circle)) i).hom := rfl

/-- Retraction composed with its circle inclusion is the identity. -/
@[simp] theorem retraction_inclusion {I : Type v} (i : I) :
    (retraction.{u, v} i).comp (inclusion.{u, v} i) = ContinuousMap.id Circle := by
  have h := TopCat.widePushoutPointRetraction_ι.{u, v} (fun _ : I ↦ circle.{max u v})
    (fun _ ↦ ULift.up (1 : Circle)) i
  apply ContinuousMap.ext
  intro z
  exact congrArg (fun k : circle.{max u v} ⟶ circle.{max u v} ↦
    (k (ULift.up z)).down) h

/-- Retraction is constant at one on each other circle. -/
theorem retraction_inclusion_of_ne {I : Type v} (i j : I) (hji : j ≠ i) :
    (retraction.{u, v} i).comp (inclusion.{u, v} j) = ContinuousMap.const Circle 1 := by
  have h := TopCat.widePushoutPointRetraction_ι_of_ne.{u, v} (fun _ : I ↦ circle.{max u v})
    (fun _ ↦ ULift.up (1 : Circle)) i j hji
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

/-- The canonical inclusion of a subfamily of circles into the bouquet. -/
def subfamilyInclusion {I : Type v} (S : Set I) :
    C(space.{u, v} S, space.{u, v} I) :=
  TopCat.widePushoutPointSubfamilyInclusion.{u, v}
    (X := fun _ : I ↦ circle.{max u v}) (fun _ ↦ ULift.up (1 : Circle)) S

/-- Retraction onto a subfamily of circles, collapsing omitted circles to the
common point. -/
def subfamilyRetraction {I : Type v} (S : Set I) :
    C(space.{u, v} I, space.{u, v} S) :=
  TopCat.widePushoutPointSubfamilyRetraction.{u, v}
    (X := fun _ : I ↦ circle.{max u v}) (fun _ ↦ ULift.up (1 : Circle)) S

/-- Subfamily inclusion preserves the common point. -/
@[simp] theorem subfamilyInclusion_basepoint {I : Type v} (S : Set I) :
    subfamilyInclusion.{u, v} S (basepoint.{u, v} S) = basepoint.{u, v} I :=
  TopCat.widePushoutPointSubfamilyInclusion_head.{u, v}
    (X := fun _ : I ↦ circle.{max u v}) (fun _ ↦ ULift.up (1 : Circle)) S PUnit.unit

/-- Subfamily retraction preserves the common point. -/
@[simp] theorem subfamilyRetraction_basepoint {I : Type v} (S : Set I) :
    subfamilyRetraction.{u, v} S (basepoint.{u, v} I) = basepoint.{u, v} S :=
  TopCat.widePushoutPointSubfamilyRetraction_head.{u, v}
    (X := fun _ : I ↦ circle.{max u v}) (fun _ ↦ ULift.up (1 : Circle)) S PUnit.unit

/-- Subfamily inclusion agrees with every original-circle inclusion. -/
@[simp] theorem subfamilyInclusion_inclusion {I : Type v} (S : Set I) (i : S) :
    (subfamilyInclusion.{u, v} S).comp (inclusion.{u, v} i) = inclusion.{u, v} i.1 := by
  apply ContinuousMap.ext
  intro z
  exact TopCat.widePushoutPointSubfamilyInclusion_ι.{u, v}
    (X := fun _ : I ↦ circle.{max u v}) (fun _ ↦ ULift.up (1 : Circle)) S i (ULift.up z)

/-- Retraction retains the original circle belonging to the subfamily. -/
@[simp] theorem subfamilyRetraction_inclusion_of_mem {I : Type v}
    (S : Set I) (i : I) (hi : i ∈ S) :
    (subfamilyRetraction.{u, v} S).comp (inclusion.{u, v} i) =
      inclusion.{u, v} (⟨i, hi⟩ : S) := by
  apply ContinuousMap.ext
  intro z
  exact TopCat.widePushoutPointSubfamilyRetraction_ι_of_mem.{u, v}
    (X := fun _ : I ↦ circle.{max u v}) (fun _ ↦ ULift.up (1 : Circle)) S i hi (ULift.up z)

/-- Retraction collapses every omitted original circle to the common point. -/
theorem subfamilyRetraction_inclusion_of_not_mem {I : Type v}
    (S : Set I) (i : I) (hi : i ∉ S) :
    (subfamilyRetraction.{u, v} S).comp (inclusion.{u, v} i) =
      ContinuousMap.const Circle (basepoint.{u, v} S) := by
  apply ContinuousMap.ext
  intro z
  exact TopCat.widePushoutPointSubfamilyRetraction_ι_of_not_mem.{u, v}
    (X := fun _ : I ↦ circle.{max u v}) (fun _ ↦ ULift.up (1 : Circle)) S i hi (ULift.up z)

/-- Retraction to a subbouquet is a left inverse to its inclusion. -/
@[simp] theorem subfamilyRetraction_comp_subfamilyInclusion {I : Type v} (S : Set I) :
    (subfamilyRetraction.{u, v} S).comp (subfamilyInclusion.{u, v} S) =
      ContinuousMap.id (space.{u, v} S) :=
  TopCat.widePushoutPointSubfamilyRetraction_comp_inclusion.{u, v}
    (X := fun _ : I ↦ circle.{max u v}) (fun _ ↦ ULift.up (1 : Circle)) S

/-- Every based loop in the bouquet factors through a finite subbouquet, with
both endpoints at its common point. In particular this applies to the included
positive original-circle loops, whose classes are detected by
`positiveGenerator_ne_one`; no free-group calculation is required. -/
theorem exists_finite_subfamily_loop {I : Type v}
    (γ : Path (basepoint.{u, v} I) (basepoint.{u, v} I)) :
    ∃ S : Set I, S.Finite ∧
      ∃ δ : Path (basepoint.{u, v} S) (basepoint.{u, v} S),
        ∀ t, subfamilyInclusion.{u, v} S (δ t) = γ t := by
  let a : ∀ _ : I, circle.{max u v} := fun _ ↦ ULift.up (1 : Circle)
  let S := TopCat.widePushoutPointSupport (X := fun _ : I ↦ circle.{max u v})
    a (Set.range γ)
  let : T1Space circle.{max u v} := by
    change T1Space (ULift.{max u v} Circle)
    exact (Homeomorph.ulift.{max u v, 0} (X := Circle)).symm.t1Space
  have hS : S.Finite := TopCat.finite_widePushoutPointSupport
    (X := fun _ : I ↦ circle.{max u v}) a (isCompact_range γ.continuous)
  have hfactor := (TopCat.widePushoutPointSubfamily_factorization_iff
    (X := fun _ : I ↦ circle.{max u v}) a S γ.toContinuousMap).2 Set.Subset.rfl
  let δ : Path (basepoint.{u, v} S) (basepoint.{u, v} S) :=
    (γ.map (subfamilyRetraction.{u, v} S).continuous).cast
      (subfamilyRetraction_basepoint.{u, v} S).symm
      (subfamilyRetraction_basepoint.{u, v} S).symm
  refine ⟨S, hS, δ, ?_⟩
  intro t
  exact congrArg (fun k : C(Set.Icc (0 : ℝ) 1, space.{u, v} I) ↦ k t) hfactor

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

/-- The countable bouquet's included positive circle loop factors through a
finite subbouquet, without replacing it by a constant loop. -/
private theorem countable_positive_loop_subfamily :
    ∃ S : Set ℕ, S.Finite ∧
      ∃ δ : Path (CircleBouquet.basepoint.{u, 0} S) (CircleBouquet.basepoint.{u, 0} S),
        ∀ t, CircleBouquet.subfamilyInclusion.{u, 0} S (δ t) =
          CircleBouquet.inclusion.{u, 0} (0 : ℕ) (Circle.loop 1 t) := by
  let γ := ((Circle.loop 1).map (CircleBouquet.inclusion.{u, 0} (0 : ℕ)).continuous).cast
    (CircleBouquet.inclusion_basepoint.{u, 0} (0 : ℕ)).symm
    (CircleBouquet.inclusion_basepoint.{u, 0} (0 : ℕ)).symm
  exact CircleBouquet.exists_finite_subfamily_loop.{u, 0} γ

end SphereTopologyTest

end
