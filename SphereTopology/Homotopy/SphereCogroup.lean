/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.HomotopyGroup.SphereCoordinateReflection
public import SphereTopology.Homotopy.HomotopyGroup.SpherePinchFold
public import FundamentalGroupoids.Topology.Category.TopCat.Based.Cartesian
public import FundamentalGroupoids.Topology.Category.TopCat.Based.FiniteWedge
public import FundamentalGroupoids.Topology.Category.TopCat.Based.ULift
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The metric sphere as a cogroup up to based homotopy

The positive-dimensional metric sphere, with its last-axis north pole, gives a
stock `CategoryTheory.Grp` in the ordinary opposite of the based-homotopy category.
The multiplication is opposite to the class of `Metric.Sphere.pinch`, followed by
the universe-lift comparison and the ordered comparison from `Fin 2` to
`WalkingPair`. The unit is opposite to collapse to a point followed by the head
of the empty wedge. The inverse is opposite to physical reflection in the first
ambient coordinate hyperplane.

The sphere dimension is `n + 1`; in particular `n = 0` includes the circle.
`ULift` changes only the ambient universe. The original sphere, pole, first-coordinate
zero equator, cube collapse and factor order are retained. The cartesian structure
is the existing named structure, enabled only locally in this module. No
commutativity in dimension one or identification with a homotopy group is asserted.

## Implementation notes

The construction uses the original north-relative retraction, coassociativity and
coordinate-reflection homotopies. Ordered wedge comparisons identify these
geometric operations with the chosen products in the ordinary opposite category.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 9, §1,
  for spheres and based homotopy groups.
* Mathlib supplies ordinary opposites and the stock `MonObj`, `GrpObj` and `Grp`.
* Fundamental Groupoids supplies the based-homotopy quotient, strict ordered
  finite-wedge comparisons, universe lifting and the named cartesian structure.
* The sphere pinch, cube normalization, relative cogroup laws and coordinate
  reflection are those of this library's sphere and sphere-pinch modules.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped unitInterval Topology

namespace Metric.Sphere

variable (n : ℕ)

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1
local notation "a" => EuclideanSpace.northPoint (n + 1)
local notation "D₀" => (fun _ : Fin 2 ↦ TopCat.of S)
local notation "α" =>
  (fun j : Fin 2 ↦ (TopCat.const a : TopCat.of (PUnit : Type) ⟶ D₀ j))
local notation "W₂" => (widePushout (TopCat.of (PUnit : Type)) D₀ α : TopCat)
local notation "b₂" => WidePushout.head α PUnit.unit

/-- The original metric sphere with lifted universe and lifted last-axis north pole. -/
def basedSpace : BasedTopCat.{u} :=
  BasedTopCat.of (ULift.{u} S) (ULift.up a)

/-- The underlying space is the universe lift of the specified metric sphere. -/
theorem basedSpace_right :
    (basedSpace.{u} n).right = TopCat.of (ULift.{u} S) := rfl

/-- The selected point is the lifted last-axis north pole. -/
theorem basedSpace_point :
    BasedTopCat.point (basedSpace.{u} n) = ULift.up a := rfl

/-- The carrier in the ordinary opposite based-homotopy category. -/
def cogroupCarrier : BasedTopCat.HomotopyCategory.{u}ᵒᵖ :=
  op ((BasedTopCat.homotopyQuotient.{u}).obj (BasedTopCat.of (ULift.{u} S) (ULift.up a)))

/-- The carrier is the opposite of the quotient image of the lifted original sphere. -/
theorem cogroupCarrier_eq :
    cogroupCarrier.{u} n =
      op ((BasedTopCat.homotopyQuotient.{u}).obj (BasedTopCat.of (ULift.{u} S) (ULift.up a))) := rfl

/-- The universe lift of the original `Fin 2` pinch, before wedge comparisons. -/
def pinchBased : basedSpace.{u} n ⟶ BasedTopCat.of (ULift.{u} W₂) (ULift.up b₂) :=
  BasedTopCat.ofHom (x := ULift.up a) (y := ULift.up b₂)
    (⟨fun z : ULift.{u} S ↦ ULift.up (pinch n z.down),
      continuous_uliftUp.comp ((pinch n).continuous.comp continuous_uliftDown)⟩ :
      C(ULift.{u} S, ULift.{u} W₂))
    (congrArg (ULift.up : W₂ → ULift.{u} W₂) (pinch_northPoint n))

/-- The lifted pinch evaluates by the original pinch, without a change of operation. -/
theorem pinchBased_apply (s : S) :
    (pinchBased.{u} n).right.hom (ULift.up s) = ULift.up (pinch n s) := rfl

/-- The lifted pinch sends the lifted original pole to the lifted original head. -/
theorem pinchBased_northPoint :
    (pinchBased.{u} n).right.hom (ULift.up a) = ULift.up b₂ :=
  congrArg ULift.up (pinch_northPoint n)

/-- Compare the lifted original two-factor wedge with the ordered binary wedge. -/
def pinchWedgeIso :
    BasedTopCat.of (ULift.{u} W₂) (ULift.up b₂) ≅
      BasedTopCat.basedWedge (pairFunction (basedSpace.{u} n) (basedSpace.{u} n)) :=
  BasedTopCat.basedWedgeULiftIso.{0, u, 0} D₀ (fun _ ↦ a) ≪≫
    BasedTopCat.basedWedgeFinTwoIso (fun _ : Fin 2 ↦ basedSpace.{u} n)

/-- The comparison preserves the lifted original head. -/
theorem pinchWedgeIso_hom_head :
    (pinchWedgeIso.{u} n).hom.right.hom (ULift.up b₂) =
      BasedTopCat.point (BasedTopCat.basedWedge
        (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))) :=
  BasedTopCat.map_point (pinchWedgeIso.{u} n).hom

/-- Original factor `0` becomes the left binary factor. -/
theorem pinchWedgeIso_hom_ι_zero (s : S) :
    (pinchWedgeIso.{u} n).hom.right.hom (ULift.up (WidePushout.ι α 0 s)) =
      (BasedTopCat.basedWedgeι (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
        WalkingPair.left).right.hom (ULift.up s) := by
  change (BasedTopCat.basedWedgeFinTwoIso
      (fun _ : Fin 2 ↦ basedSpace.{u} n)).hom.right.hom
      ((BasedTopCat.basedWedgeULiftIso.{0, u, 0} D₀ (fun _ ↦ a)).hom.right.hom
        (ULift.up (WidePushout.ι α 0 s))) = _
  exact (congrArg
    (fun z : (BasedTopCat.basedWedge (fun _ : Fin 2 ↦ basedSpace.{u} n)).right ↦
      (BasedTopCat.basedWedgeFinTwoIso
        (fun _ : Fin 2 ↦ basedSpace.{u} n)).hom.right.hom z)
    (BasedTopCat.basedWedgeULiftIso_hom_ι.{0, u, 0} D₀ (fun _ ↦ a) 0 s)).trans
      (congrArg
        (fun f : basedSpace.{u} n ⟶ BasedTopCat.basedWedge
            (pairFunction (basedSpace.{u} n) (basedSpace.{u} n)) ↦
          f.right.hom (ULift.up s))
        (BasedTopCat.basedWedgeFinTwoIso_ι_zero_hom
          (fun _ : Fin 2 ↦ basedSpace.{u} n)))

/-- Original factor `1` becomes the right binary factor. -/
theorem pinchWedgeIso_hom_ι_one (s : S) :
    (pinchWedgeIso.{u} n).hom.right.hom (ULift.up (WidePushout.ι α 1 s)) =
      (BasedTopCat.basedWedgeι (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
        WalkingPair.right).right.hom (ULift.up s) := by
  change (BasedTopCat.basedWedgeFinTwoIso
      (fun _ : Fin 2 ↦ basedSpace.{u} n)).hom.right.hom
      ((BasedTopCat.basedWedgeULiftIso.{0, u, 0} D₀ (fun _ ↦ a)).hom.right.hom
        (ULift.up (WidePushout.ι α 1 s))) = _
  exact (congrArg
    (fun z : (BasedTopCat.basedWedge (fun _ : Fin 2 ↦ basedSpace.{u} n)).right ↦
      (BasedTopCat.basedWedgeFinTwoIso
        (fun _ : Fin 2 ↦ basedSpace.{u} n)).hom.right.hom z)
    (BasedTopCat.basedWedgeULiftIso_hom_ι.{0, u, 0} D₀ (fun _ ↦ a) 1 s)).trans
      (congrArg
        (fun f : basedSpace.{u} n ⟶ BasedTopCat.basedWedge
            (pairFunction (basedSpace.{u} n) (basedSpace.{u} n)) ↦
          f.right.hom (ULift.up s))
        (BasedTopCat.basedWedgeFinTwoIso_ι_one_hom
          (fun _ : Fin 2 ↦ basedSpace.{u} n)))

/-- The inverse comparison retains the original head. -/
theorem pinchWedgeIso_inv_point :
    (pinchWedgeIso.{u} n).inv.right.hom (BasedTopCat.point (BasedTopCat.basedWedge
      (pairFunction (basedSpace.{u} n) (basedSpace.{u} n)))) = ULift.up b₂ :=
  BasedTopCat.map_point (pinchWedgeIso.{u} n).inv

/-- The original pinch followed by the universe and ordered-wedge comparisons. -/
def pinchToWedge : basedSpace.{u} n ⟶
    BasedTopCat.basedWedge (pairFunction (basedSpace.{u} n) (basedSpace.{u} n)) :=
  pinchBased n ≫ (pinchWedgeIso n).hom

/-- The continuous map of the comultiplication uses the original pinch. -/
theorem pinchToWedge_apply (s : S) :
    (pinchToWedge.{u} n).right.hom (ULift.up s) =
      (pinchWedgeIso.{u} n).hom.right.hom (ULift.up (pinch n s)) := rfl

/-- The common point is preserved by the comultiplication. -/
theorem pinchToWedge_northPoint :
    (pinchToWedge.{u} n).right.hom (ULift.up a) =
      BasedTopCat.point (BasedTopCat.basedWedge
        (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))) :=
  BasedTopCat.map_point (pinchToWedge.{u} n)

/-- Postcomposing the compared pinch folds the two based factor restrictions,
with the left factor first, on the original metric sphere. -/
theorem pinchToWedge_comp_apply (Y : BasedTopCat.{u})
    (f : BasedTopCat.basedWedge
      (pairFunction (basedSpace.{u} n) (basedSpace.{u} n)) ⟶ Y) (s : S) :
    (pinchToWedge.{u} n ≫ f).right.hom (ULift.up s) =
      (pinchFold n (BasedTopCat.point Y)
        (⟨(BasedTopCat.basedWedgeι
            (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
            WalkingPair.left ≫ f).right.hom.comp
              (⟨ULift.up, continuous_uliftUp⟩ : C(S, ULift.{u} S)),
          BasedTopCat.map_point (BasedTopCat.basedWedgeι
            (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
            WalkingPair.left ≫ f)⟩,
         ⟨(BasedTopCat.basedWedgeι
            (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
            WalkingPair.right ≫ f).right.hom.comp
              (⟨ULift.up, continuous_uliftUp⟩ : C(S, ULift.{u} S)),
          BasedTopCat.map_point (BasedTopCat.basedWedgeι
            (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
            WalkingPair.right ≫ f)⟩)).val s := by
  let F : {F : C(S, Y.right) // F a = BasedTopCat.point Y} :=
    ⟨(BasedTopCat.basedWedgeι
        (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
        WalkingPair.left ≫ f).right.hom.comp
          (⟨ULift.up, continuous_uliftUp⟩ : C(S, ULift.{u} S)),
      BasedTopCat.map_point (BasedTopCat.basedWedgeι
        (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
        WalkingPair.left ≫ f)⟩
  let G : {F : C(S, Y.right) // F a = BasedTopCat.point Y} :=
    ⟨(BasedTopCat.basedWedgeι
        (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
        WalkingPair.right ≫ f).right.hom.comp
          (⟨ULift.up, continuous_uliftUp⟩ : C(S, ULift.{u} S)),
      BasedTopCat.map_point (BasedTopCat.basedWedgeι
        (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
        WalkingPair.right ≫ f)⟩
  have hd :
      f.right.hom.comp ((pinchWedgeIso.{u} n).hom.right.hom.comp
        (⟨ULift.up, continuous_uliftUp⟩ : C(W₂, ULift.{u} W₂))) =
      TopCat.widePushoutDesc α
        (ContinuousMap.const (TopCat.of (PUnit : Type)) (BasedTopCat.point Y))
        (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
        (fun j _ ↦ Subtype.property (ite (j = 0) F G)) := by
    apply TopCat.widePushoutDesc_unique
    · intro p
      cases p
      change f.right.hom ((pinchWedgeIso.{u} n).hom.right.hom
        (ULift.up b₂)) = BasedTopCat.point Y
      rw [pinchWedgeIso_hom_head]
      exact BasedTopCat.map_point f
    · intro j t
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · change f.right.hom ((pinchWedgeIso.{u} n).hom.right.hom
          (ULift.up (WidePushout.ι α 0 t))) = F.val t
        rw [pinchWedgeIso_hom_ι_zero]
        rfl
      · refine Fin.cases ?_ (fun k : Fin 0 ↦ Fin.elim0 k) j
        change f.right.hom ((pinchWedgeIso.{u} n).hom.right.hom
          (ULift.up (WidePushout.ι α 1 t))) = G.val t
        rw [pinchWedgeIso_hom_ι_one]
        rfl
  exact congrArg (fun d : C(W₂, Y.right) ↦ d (pinch n s)) hd

local notation "Q₀" =>
  (Subtype.mk (Cube.collapseToSphere (n + 1))
    (fun t ht ↦ Iff.mpr (Cube.collapseToSphere_eq_northPoint_iff (n + 1) t) ht) :
      GenLoop (Fin (n + 1)) S a)

/-- The cube normalization is the original coordinate-zero concatenation, with
factor `0` traversed before factor `1`. -/
theorem pinchToWedge_comp_collapseToSphere :
    ((pinchToWedge.{u} n).right.hom.comp
      (⟨ULift.up, continuous_uliftUp⟩ : C(S, ULift.{u} S))).comp
        (Cube.collapseToSphere (n + 1)) =
      Subtype.val (GenLoop.transAt (0 : Fin (n + 1))
        (GenLoop.map
          (BasedTopCat.basedWedgeι (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
            WalkingPair.left).right.hom
          (BasedTopCat.map_point
            (BasedTopCat.basedWedgeι (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
              WalkingPair.left))
          (GenLoop.map (⟨ULift.up, continuous_uliftUp⟩ : C(S, ULift.{u} S)) rfl Q₀))
        (GenLoop.map
          (BasedTopCat.basedWedgeι (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
            WalkingPair.right).right.hom
          (BasedTopCat.map_point
            (BasedTopCat.basedWedgeι (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))
              WalkingPair.right))
          (GenLoop.map (⟨ULift.up, continuous_uliftUp⟩ : C(S, ULift.{u} S)) rfl Q₀))) := by
  let f : C(W₂, (BasedTopCat.basedWedge
      (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))).right) :=
    (pinchWedgeIso.{u} n).hom.right.hom.comp
      (⟨ULift.up, continuous_uliftUp⟩ : C(W₂, ULift.{u} W₂))
  have hf : f b₂ = BasedTopCat.point (BasedTopCat.basedWedge
      (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))) :=
    pinchWedgeIso_hom_head n
  change f.comp ((pinch n).comp (Cube.collapseToSphere (n + 1))) = _
  rw [pinch_comp_collapseToSphere]
  change Subtype.val (GenLoop.map f hf
    (GenLoop.transAt (0 : Fin (n + 1))
      (GenLoop.map (WidePushout.ι α 0).hom
        (TopCat.widePushout_point_ι_point (X := D₀) (fun _ ↦ a) 0) Q₀)
      (GenLoop.map (WidePushout.ι α 1).hom
        (TopCat.widePushout_point_ι_point (X := D₀) (fun _ ↦ a) 1) Q₀))) = _
  rw [GenLoop.map_transAt]
  apply congrArg Subtype.val
  apply congrArg₂ (GenLoop.transAt (0 : Fin (n + 1)))
  · apply GenLoop.ext
    intro t
    exact pinchWedgeIso_hom_ι_zero n (Cube.collapseToSphere (n + 1) t)
  · apply GenLoop.ext
    intro t
    exact pinchWedgeIso_hom_ι_one n (Cube.collapseToSphere (n + 1) t)

/-- The first-coordinate-zero equator collapses to the common wedge point. -/
theorem pinchToWedge_of_firstCoordinate_eq_zero (s : S)
    (hs : (s : EuclideanSpace ℝ (Fin ((n + 1) + 1)))
      (0 : Fin (n + 1)).castSucc = 0) :
    (pinchToWedge.{u} n).right.hom (ULift.up s) =
      BasedTopCat.point (BasedTopCat.basedWedge
        (pairFunction (basedSpace.{u} n) (basedSpace.{u} n))) := by
  have hp : pinch n s = b₂ :=
    (pinch_eq_head_iff n s).mpr (by simpa only [Fin.castSucc_zero] using hs)
  rw [pinchToWedge_apply, hp]
  exact pinchWedgeIso_hom_head n

/-- Physical reflection in the first ambient coordinate hyperplane, as a based map. -/
def coordinateReflectionBased : basedSpace.{u} n ⟶ basedSpace.{u} n :=
  BasedTopCat.ofHom (x := ULift.up a) (y := ULift.up a)
    (⟨fun z : ULift.{u} S ↦ ULift.up (coordinateReflection n (0 : Fin (n + 1)) z.down),
      continuous_uliftUp.comp
        ((coordinateReflection n (0 : Fin (n + 1))).continuous.comp continuous_uliftDown)⟩ :
      C(ULift.{u} S, ULift.{u} S))
    (congrArg (ULift.up : S → ULift.{u} S)
      (coordinateReflection_northPoint n (0 : Fin (n + 1))))

/-- The based reflection is the lift of the physical coordinate reflection. -/
theorem coordinateReflectionBased_apply (s : S) :
    (coordinateReflectionBased.{u} n).right.hom (ULift.up s) =
      ULift.up (coordinateReflection n (0 : Fin (n + 1)) s) := rfl

/-- The first coordinate changes sign; the other coordinates, including the last,
are unchanged by the coinverse. -/
theorem coordinateReflectionBased_apply_coordinate (s : S)
    (j : Fin ((n + 1) + 1)) :
    (((coordinateReflectionBased.{u} n).right.hom (ULift.up s)).down :
        EuclideanSpace ℝ (Fin ((n + 1) + 1))) j =
      if j = (0 : Fin (n + 1)).castSucc then -(s : EuclideanSpace ℝ _) j
      else (s : EuclideanSpace ℝ _) j :=
  coordinateReflection_apply n (0 : Fin (n + 1)) s j

/-- Physical reflection fixes the first-coordinate-zero equator pointwise. -/
theorem coordinateReflectionBased_of_firstCoordinate_eq_zero (s : S)
    (hs : (s : EuclideanSpace ℝ (Fin ((n + 1) + 1)))
      (0 : Fin (n + 1)).castSucc = 0) :
    (coordinateReflectionBased.{u} n).right.hom (ULift.up s) = ULift.up s := by
  rw [coordinateReflectionBased_apply]
  apply congrArg ULift.up
  apply Subtype.ext
  apply PiLp.ext
  intro j
  rw [coordinateReflection_apply]
  split_ifs with hj
  · subst j
    rw [hs, neg_zero]
  · rfl

/-- The lifted physical reflection fixes the specified pole. -/
theorem coordinateReflectionBased_northPoint :
    (coordinateReflectionBased.{u} n).right.hom (ULift.up a) = ULift.up a :=
  BasedTopCat.map_point (coordinateReflectionBased.{u} n)

/-- Collapse the lifted original sphere to the designated one-point based space. -/
def collapseBased : basedSpace.{u} n ⟶ Under.mk (𝟙 (TopCat.of PUnit.{u + 1})) :=
  Under.homMk (TopCat.const PUnit.unit) (by
    apply TopCat.ext
    intro t
    cases t
    rfl)

/-- Collapse has the constant value in the designated one-point space. -/
theorem collapseBased_apply (s : ULift.{u} S) :
    (collapseBased.{u} n).right.hom s = PUnit.unit := rfl

/-- Collapse followed by the canonical map from the designated point to the
chosen empty wedge. -/
def counitBased : basedSpace.{u} n ⟶
    BasedTopCat.basedWedge (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u})) :=
  collapseBased n ≫ Under.mkIdInitial.to
    (BasedTopCat.basedWedge (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u})))

/-- The counit is collapse followed by the head of the empty point-wide-pushout. -/
theorem counitBased_apply (s : ULift.{u} S) :
    (counitBased.{u} n).right.hom s =
      BasedTopCat.point
        (BasedTopCat.basedWedge (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u}))) := by
  let E := BasedTopCat.basedWedge
    (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u}))
  change (Under.mkIdInitial.to E).right.hom PUnit.unit = BasedTopCat.point E
  exact congrArg (fun f : TopCat.of PUnit.{u + 1} ⟶ E.right ↦ f.hom PUnit.unit)
    (Under.mkIdInitial_to_right E)

attribute [local instance] BasedTopCat.homotopyOppositeCartesianMonoidalCategory

/-- Multiplication in the ordinary opposite is the class of the original pinch,
with the specified universe and ordered-wedge comparisons. -/
def cogroupMul : cogroupCarrier.{u} n ⊗ cogroupCarrier.{u} n ⟶ cogroupCarrier.{u} n :=
  ((BasedTopCat.homotopyQuotient.{u}).map (pinchToWedge n)).op

/-- The unit in the ordinary opposite is the class of the original collapse,
followed by the canonical point-to-empty-wedge map. -/
def cogroupOne : 𝟙_ (BasedTopCat.HomotopyCategory.{u}ᵒᵖ) ⟶ cogroupCarrier.{u} n :=
  ((BasedTopCat.homotopyQuotient.{u}).map (counitBased n)).op

/-- Inversion in the ordinary opposite is the class of physical first-coordinate reflection. -/
def cogroupInv : cogroupCarrier.{u} n ⟶ cogroupCarrier.{u} n :=
  ((BasedTopCat.homotopyQuotient.{u}).map (coordinateReflectionBased n)).op

/-- Unopposite multiplication is the quotient image of the pointed pinch. -/
theorem cogroupMul_unop_eq_map :
    (cogroupMul.{u} n).unop =
      (BasedTopCat.homotopyQuotient.{u}).map (pinchToWedge n) := rfl

/-- Unopposite multiplication is the class of the lifted original pinch followed
by the existing lifted-wedge and ordered `Fin 2` comparisons. -/
theorem cogroupMul_unop :
    (cogroupMul.{u} n).unop =
      (BasedTopCat.homotopyQuotient.{u}).map (pinchBased n) ≫
        (BasedTopCat.homotopyQuotient.{u}).map
          (BasedTopCat.basedWedgeULiftIso.{0, u, 0} D₀ (fun _ ↦ a)).hom ≫
        (BasedTopCat.homotopyQuotient.{u}).map
          (BasedTopCat.basedWedgeFinTwoIso (fun _ : Fin 2 ↦ basedSpace.{u} n)).hom := by
  let Q := BasedTopCat.homotopyQuotient.{u}
  let e := BasedTopCat.basedWedgeULiftIso.{0, u, 0} D₀ (fun _ ↦ a)
  let e' := BasedTopCat.basedWedgeFinTwoIso (fun _ : Fin 2 ↦ basedSpace.{u} n)
  change Q.map (pinchBased n ≫ e.hom ≫ e'.hom) =
    Q.map (pinchBased n) ≫ Q.map e.hom ≫ Q.map e'.hom
  exact (Q.map_comp (pinchBased n) (e.hom ≫ e'.hom)).trans
    (congrArg (fun f ↦ Q.map (pinchBased n) ≫ f) (Q.map_comp e.hom e'.hom))

/-- Unopposite unit is collapse followed by the existing canonical point comparison. -/
theorem cogroupOne_unop :
    (cogroupOne.{u} n).unop =
      (BasedTopCat.homotopyQuotient.{u}).map (collapseBased n) ≫
        (BasedTopCat.homotopyQuotient.{u}).map (Under.mkIdInitial.to
          (BasedTopCat.basedWedge (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u})))) := by
  change (BasedTopCat.homotopyQuotient.{u}).map (counitBased n) = _
  exact (BasedTopCat.homotopyQuotient.{u}).map_comp (collapseBased n)
    (Under.mkIdInitial.to (BasedTopCat.basedWedge
      (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u}))))

/-- Unopposite inversion is the class of the lifted physical reflection. -/
theorem cogroupInv_unop :
    (cogroupInv.{u} n).unop =
      (BasedTopCat.homotopyQuotient.{u}).map (coordinateReflectionBased n) := rfl

local notation "T₀" => (fun _ : Fin 3 ↦ TopCat.of S)
local notation "β" =>
  (fun j : Fin 3 ↦ (TopCat.const a : TopCat.of (PUnit : Type) ⟶ T₀ j))
local notation "W₃" => (widePushout (TopCat.of (PUnit : Type)) T₀ β : TopCat)
local notation "b₃" => WidePushout.head β PUnit.unit
local notation "I₃" =>
  (fun j : Fin 3 ↦
    (Subtype.mk (TopCat.Hom.hom (WidePushout.ι β j))
      (TopCat.widePushout_point_ι_point (X := T₀) (fun _ ↦ a) j) :
      {F : C(S, W₃) // F a = b₃}))
local notation "L₃" => pinchFold n b₃ (pinchFold n b₃ (I₃ 0, I₃ 1), I₃ 2)
local notation "R₃" => pinchFold n b₃ (I₃ 0, pinchFold n b₃ (I₃ 1, I₃ 2))

/-- The chosen associator has the ordinary-opposite orientation and retains the
three original ordered factors. -/
theorem cogroup_associator_unop_comp_finThreeLeft :
    (α_ (cogroupCarrier.{u} n) (cogroupCarrier.{u} n) (cogroupCarrier.{u} n)).hom.unop ≫
        (BasedTopCat.homotopyQuotient.{u}).map
          (BasedTopCat.basedWedgeFinThreeLeftIso (fun _ : Fin 3 ↦ basedSpace.{u} n)).hom =
      (BasedTopCat.homotopyQuotient.{u}).map
        (BasedTopCat.basedWedgeFinThreeRightIso (fun _ : Fin 3 ↦ basedSpace.{u} n)).hom := by
  exact BasedTopCat.homotopyOpposite_associator_unop_comp_finThreeLeft
    (fun _ : Fin 3 ↦ basedSpace.{u} n)

/-- Flattening the left multiplication composite agrees with the lifted original
left iterated pinch into the original ordered three-factor point-wide-pushout. -/
theorem cogroupMul_left_unop_comp_finThreeLeft :
    ((cogroupMul.{u} n ▷ cogroupCarrier.{u} n) ≫ cogroupMul n).unop ≫
        (BasedTopCat.homotopyQuotient.{u}).map
          (BasedTopCat.basedWedgeFinThreeLeftIso (fun _ : Fin 3 ↦ basedSpace.{u} n)).hom =
      (BasedTopCat.homotopyQuotient.{u}).map
        (BasedTopCat.ofHom (x := ULift.up a) (y := ULift.up b₃)
          (⟨fun z : ULift.{u} S ↦ ULift.up (Subtype.val L₃ z.down),
            continuous_uliftUp.comp ((Subtype.val L₃).continuous.comp continuous_uliftDown)⟩ :
            C(ULift.{u} S, ULift.{u} W₃))
          (congrArg (ULift.up : W₃ → ULift.{u} W₃) (Subtype.property L₃))) ≫
        (BasedTopCat.homotopyQuotient.{u}).map
          (BasedTopCat.basedWedgeULiftIso.{0, u, 0} T₀ (fun _ ↦ a)).hom := by
  let Q := BasedTopCat.homotopyQuotient.{u}
  let X := basedSpace.{u} n
  let P := pairFunction X X
  let V := BasedTopCat.basedWedge P
  let N := BasedTopCat.basedWedge (pairFunction V X)
  let D := fun _ : Fin 3 ↦ X
  let W := BasedTopCat.basedWedge D
  let e := BasedTopCat.basedWedgeFinThreeLeftIso D
  let e₃ := BasedTopCat.basedWedgeULiftIso.{0, u, 0} T₀ (fun _ ↦ a)
  let i₀ : X ⟶ V := BasedTopCat.basedWedgeι P WalkingPair.left
  let i₁ : X ⟶ V := BasedTopCat.basedWedgeι P WalkingPair.right
  let o₀ : V ⟶ N := BasedTopCat.basedWedgeι (pairFunction V X) WalkingPair.left
  let o₁ : X ⟶ N := BasedTopCat.basedWedgeι (pairFunction V X) WalkingPair.right
  let t := BasedTopCat.basedWedgeι D
  let l : V ⟶ N := BasedTopCat.basedWedgeDesc P (fun j ↦ match j with
    | WalkingPair.left => pinchToWedge n ≫ o₀
    | WalkingPair.right => o₁)
  have hl₀ : i₀ ≫ l = pinchToWedge n ≫ o₀ :=
    BasedTopCat.basedWedgeι_desc P _ WalkingPair.left
  have hl₁ : i₁ ≫ l = o₁ :=
    BasedTopCat.basedWedgeι_desc P _ WalkingPair.right
  -- Transport the two cartesian projection equations as typed equalities, then unop them.
  have hw : (cogroupMul.{u} n ▷ cogroupCarrier.{u} n).unop = Q.map l := by
    apply BasedTopCat.basedWedgeHomotopy_hom_ext P
    intro j
    cases j with
    | left =>
        change Q.map i₀ ≫ (cogroupMul.{u} n ▷ cogroupCarrier.{u} n).unop =
          Q.map i₀ ≫ Q.map l
        calc
          _ = Q.map (pinchToWedge n) ≫ Q.map o₀ := by
            have hproj :
                (cogroupMul.{u} n ▷ cogroupCarrier.{u} n) ≫ (Q.map i₀).op =
                  (Q.map o₀).op ≫ cogroupMul n :=
              (congrArg
                (fun f : op (Q.obj V) ⟶ op (Q.obj X) ↦
                  (cogroupMul.{u} n ▷ cogroupCarrier.{u} n) ≫ f)
                (BasedTopCat.homotopyOpposite_fst
                  (cogroupCarrier.{u} n) (cogroupCarrier.{u} n))).symm.trans
                ((CartesianMonoidalCategory.whiskerRight_fst
                  (cogroupMul.{u} n) (cogroupCarrier.{u} n)).trans
                  (congrArg
                    (fun f : op (Q.obj N) ⟶ op (Q.obj V) ↦ f ≫ cogroupMul n)
                    (BasedTopCat.homotopyOpposite_fst
                      (cogroupCarrier.{u} n ⊗ cogroupCarrier.{u} n)
                      (cogroupCarrier.{u} n))))
            exact (unop_comp
              (f := cogroupMul.{u} n ▷ cogroupCarrier.{u} n)
              (g := (Q.map i₀).op)).symm.trans
                ((congrArg (fun f : op (Q.obj N) ⟶ op (Q.obj X) ↦ f.unop)
                  hproj).trans
                  ((unop_comp (f := (Q.map o₀).op) (g := cogroupMul.{u} n)).trans
                    (congrArg (fun f : Q.obj X ⟶ Q.obj V ↦ f ≫ Q.map o₀)
                      (cogroupMul_unop_eq_map.{u} n))))
          _ = _ := by
            simpa only [Functor.map_comp] using (congrArg Q.map hl₀).symm
    | right =>
        change Q.map i₁ ≫ (cogroupMul.{u} n ▷ cogroupCarrier.{u} n).unop =
          Q.map i₁ ≫ Q.map l
        calc
          _ = Q.map o₁ := by
            have hproj :
                (cogroupMul.{u} n ▷ cogroupCarrier.{u} n) ≫ (Q.map i₁).op =
                  (Q.map o₁).op :=
              (congrArg
                (fun f : op (Q.obj V) ⟶ op (Q.obj X) ↦
                  (cogroupMul.{u} n ▷ cogroupCarrier.{u} n) ≫ f)
                (BasedTopCat.homotopyOpposite_snd
                  (cogroupCarrier.{u} n) (cogroupCarrier.{u} n))).symm.trans
                ((CartesianMonoidalCategory.whiskerRight_snd
                  (cogroupMul.{u} n) (cogroupCarrier.{u} n)).trans
                  (BasedTopCat.homotopyOpposite_snd
                    (cogroupCarrier.{u} n ⊗ cogroupCarrier.{u} n)
                    (cogroupCarrier.{u} n)))
            exact (unop_comp
              (f := cogroupMul.{u} n ▷ cogroupCarrier.{u} n)
              (g := (Q.map i₁).op)).symm.trans
                (congrArg (fun f : op (Q.obj N) ⟶ op (Q.obj X) ↦ f.unop) hproj)
          _ = _ := by
            simpa only [Functor.map_comp] using (congrArg Q.map hl₁).symm
  let d : V ⟶ W := BasedTopCat.basedWedgeDesc P (fun j ↦ match j with
    | WalkingPair.left => t 0
    | WalkingPair.right => t 1)
  have hd₀ : i₀ ≫ d = t 0 := BasedTopCat.basedWedgeι_desc P _ WalkingPair.left
  have hd₁ : i₁ ≫ d = t 1 := BasedTopCat.basedWedgeι_desc P _ WalkingPair.right
  have ho₀ : o₀ ≫ e.hom = d := by
    apply BasedTopCat.basedWedge_hom_ext P
    intro j
    cases j with
    | left =>
        rw [← Category.assoc]
        exact (BasedTopCat.basedWedgeFinThreeLeftIso_ι_zero_hom D).trans hd₀.symm
    | right =>
        rw [← Category.assoc]
        exact (BasedTopCat.basedWedgeFinThreeLeftIso_ι_one_hom D).trans hd₁.symm
  have ho₁ : o₁ ≫ e.hom = t 2 :=
    BasedTopCat.basedWedgeFinThreeLeftIso_ι_two_hom D
  have hflat₀ : i₀ ≫ l ≫ e.hom = pinchToWedge n ≫ d := by
    rw [← Category.assoc, hl₀, Category.assoc, ho₀]
  have hflat₁ : i₁ ≫ l ≫ e.hom = t 2 := by
    rw [← Category.assoc, hl₁, ho₁]
  let H : C(W₃, W.right) := e₃.hom.right.hom.comp
    (⟨ULift.up, continuous_uliftUp⟩ : C(W₃, ULift.{u} W₃))
  have hH : H b₃ = BasedTopCat.point W := BasedTopCat.map_point e₃.hom
  let r : (X ⟶ W) → {F : C(S, W.right) // F a = BasedTopCat.point W} :=
    fun g ↦ ⟨g.right.hom.comp
      (⟨ULift.up, continuous_uliftUp⟩ : C(S, ULift.{u} S)), BasedTopCat.map_point g⟩
  let p : {F : C(S, W₃) // F a = b₃} →
      {F : C(S, W.right) // F a = BasedTopCat.point W} :=
    fun F ↦ ⟨H.comp F.val, (congrArg H F.property).trans hH⟩
  have ht (j : Fin 3) : r (t j) = p (I₃ j) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    exact (BasedTopCat.basedWedgeULiftIso_hom_ι.{0, u, 0}
      T₀ (fun _ ↦ a) j s).symm
  have hp (F G : {F : C(S, W₃) // F a = b₃}) :
      pinchFold n (BasedTopCat.point W) (p F, p G) =
        p (pinchFold n b₃ (F, G)) := by
    apply Subtype.ext
    simpa only [p, coe_pinchFold, apply_ite] using
      (pinch_postcomp n b₃ F G H hH).symm
  have hinner : r (pinchToWedge n ≫ d) = p (pinchFold n b₃ (I₃ 0, I₃ 1)) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    change (pinchToWedge n ≫ d).right.hom (ULift.up s) = _
    rw [pinchToWedge_comp_apply]
    change (pinchFold n (BasedTopCat.point W) (r (i₀ ≫ d), r (i₁ ≫ d))).val s = _
    rw [hd₀, hd₁, ht 0, ht 1, hp]
  have houter : r (pinchToWedge n ≫ l ≫ e.hom) = p L₃ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    change (pinchToWedge n ≫ (l ≫ e.hom)).right.hom (ULift.up s) = _
    rw [pinchToWedge_comp_apply]
    change (pinchFold n (BasedTopCat.point W)
      (r (i₀ ≫ l ≫ e.hom), r (i₁ ≫ l ≫ e.hom))).val s = _
    rw [hflat₀, hflat₁, hinner, ht 2, hp]
  let k : X ⟶ BasedTopCat.of (ULift.{u} W₃) (ULift.up b₃) :=
    BasedTopCat.ofHom
      (⟨fun z : ULift.{u} S ↦ ULift.up (Subtype.val L₃ z.down),
        continuous_uliftUp.comp ((Subtype.val L₃).continuous.comp continuous_uliftDown)⟩ :
        C(ULift.{u} S, ULift.{u} W₃))
      (congrArg (ULift.up : W₃ → ULift.{u} W₃) (Subtype.property L₃))
  have hstrict : pinchToWedge n ≫ l ≫ e.hom = k ≫ e₃.hom := by
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    rintro ⟨s⟩
    exact congrArg (fun F : {F : C(S, W.right) // F a = BasedTopCat.point W} ↦
      F.val s) houter
  rw [unop_comp, hw]
  change (Q.map (pinchToWedge n) ≫ Q.map l) ≫ Q.map e.hom =
    Q.map k ≫ Q.map e₃.hom
  have hmap : Q.map (pinchToWedge n ≫ l ≫ e.hom) =
      Q.map (pinchToWedge n) ≫ Q.map l ≫ Q.map e.hom :=
    (Q.map_comp (pinchToWedge n) (l ≫ e.hom)).trans
      (congrArg (fun f : Q.obj V ⟶ Q.obj W ↦ Q.map (pinchToWedge n) ≫ f)
        (Q.map_comp l e.hom))
  exact (Category.assoc _ _ _).trans
    (hmap.symm.trans ((congrArg (fun f : X ⟶ W ↦ Q.map f) hstrict).trans
      (Q.map_comp k e₃.hom)))

/-- Flattening the right multiplication composite agrees with the lifted original
right iterated pinch into the same ordered three-factor point-wide-pushout. -/
theorem cogroupMul_right_unop_comp_finThreeRight :
    ((cogroupCarrier.{u} n ◁ cogroupMul.{u} n) ≫ cogroupMul n).unop ≫
        (BasedTopCat.homotopyQuotient.{u}).map
          (BasedTopCat.basedWedgeFinThreeRightIso (fun _ : Fin 3 ↦ basedSpace.{u} n)).hom =
      (BasedTopCat.homotopyQuotient.{u}).map
        (BasedTopCat.ofHom (x := ULift.up a) (y := ULift.up b₃)
          (⟨fun z : ULift.{u} S ↦ ULift.up (Subtype.val R₃ z.down),
            continuous_uliftUp.comp ((Subtype.val R₃).continuous.comp continuous_uliftDown)⟩ :
            C(ULift.{u} S, ULift.{u} W₃))
          (congrArg (ULift.up : W₃ → ULift.{u} W₃) (Subtype.property R₃))) ≫
        (BasedTopCat.homotopyQuotient.{u}).map
          (BasedTopCat.basedWedgeULiftIso.{0, u, 0} T₀ (fun _ ↦ a)).hom := by
  let Q := BasedTopCat.homotopyQuotient.{u}
  let X := basedSpace.{u} n
  let P := pairFunction X X
  let V := BasedTopCat.basedWedge P
  let N := BasedTopCat.basedWedge (pairFunction X V)
  let D := fun _ : Fin 3 ↦ X
  let W := BasedTopCat.basedWedge D
  let e := BasedTopCat.basedWedgeFinThreeRightIso D
  let e₃ := BasedTopCat.basedWedgeULiftIso.{0, u, 0} T₀ (fun _ ↦ a)
  let i₀ : X ⟶ V := BasedTopCat.basedWedgeι P WalkingPair.left
  let i₁ : X ⟶ V := BasedTopCat.basedWedgeι P WalkingPair.right
  let o₀ : X ⟶ N := BasedTopCat.basedWedgeι (pairFunction X V) WalkingPair.left
  let o₁ : V ⟶ N := BasedTopCat.basedWedgeι (pairFunction X V) WalkingPair.right
  let t := BasedTopCat.basedWedgeι D
  let l : V ⟶ N := BasedTopCat.basedWedgeDesc P (fun j ↦ match j with
    | WalkingPair.left => o₀
    | WalkingPair.right => pinchToWedge n ≫ o₁)
  have hl₀ : i₀ ≫ l = o₀ :=
    BasedTopCat.basedWedgeι_desc P _ WalkingPair.left
  have hl₁ : i₁ ≫ l = pinchToWedge n ≫ o₁ :=
    BasedTopCat.basedWedgeι_desc P _ WalkingPair.right
  -- Transport the two cartesian projection equations as typed equalities, then unop them.
  have hw : (cogroupCarrier.{u} n ◁ cogroupMul.{u} n).unop = Q.map l := by
    apply BasedTopCat.basedWedgeHomotopy_hom_ext P
    intro j
    cases j with
    | left =>
        change Q.map i₀ ≫ (cogroupCarrier.{u} n ◁ cogroupMul.{u} n).unop =
          Q.map i₀ ≫ Q.map l
        calc
          _ = Q.map o₀ := by
            have hproj :
                (cogroupCarrier.{u} n ◁ cogroupMul.{u} n) ≫ (Q.map i₀).op =
                  (Q.map o₀).op :=
              (congrArg
                (fun f : op (Q.obj V) ⟶ op (Q.obj X) ↦
                  (cogroupCarrier.{u} n ◁ cogroupMul.{u} n) ≫ f)
                (BasedTopCat.homotopyOpposite_fst
                  (cogroupCarrier.{u} n) (cogroupCarrier.{u} n))).symm.trans
                ((CartesianMonoidalCategory.whiskerLeft_fst
                  (cogroupCarrier.{u} n) (cogroupMul.{u} n)).trans
                  (BasedTopCat.homotopyOpposite_fst
                    (cogroupCarrier.{u} n)
                    (cogroupCarrier.{u} n ⊗ cogroupCarrier.{u} n)))
            exact (unop_comp
              (f := cogroupCarrier.{u} n ◁ cogroupMul.{u} n)
              (g := (Q.map i₀).op)).symm.trans
                (congrArg (fun f : op (Q.obj N) ⟶ op (Q.obj X) ↦ f.unop) hproj)
          _ = _ := by
            simpa only [Functor.map_comp] using (congrArg Q.map hl₀).symm
    | right =>
        change Q.map i₁ ≫ (cogroupCarrier.{u} n ◁ cogroupMul.{u} n).unop =
          Q.map i₁ ≫ Q.map l
        calc
          _ = Q.map (pinchToWedge n) ≫ Q.map o₁ := by
            have hproj :
                (cogroupCarrier.{u} n ◁ cogroupMul.{u} n) ≫ (Q.map i₁).op =
                  (Q.map o₁).op ≫ cogroupMul n :=
              (congrArg
                (fun f : op (Q.obj V) ⟶ op (Q.obj X) ↦
                  (cogroupCarrier.{u} n ◁ cogroupMul.{u} n) ≫ f)
                (BasedTopCat.homotopyOpposite_snd
                  (cogroupCarrier.{u} n) (cogroupCarrier.{u} n))).symm.trans
                ((CartesianMonoidalCategory.whiskerLeft_snd
                  (cogroupCarrier.{u} n) (cogroupMul.{u} n)).trans
                  (congrArg
                    (fun f : op (Q.obj N) ⟶ op (Q.obj V) ↦ f ≫ cogroupMul n)
                    (BasedTopCat.homotopyOpposite_snd
                      (cogroupCarrier.{u} n)
                      (cogroupCarrier.{u} n ⊗ cogroupCarrier.{u} n))))
            exact (unop_comp
              (f := cogroupCarrier.{u} n ◁ cogroupMul.{u} n)
              (g := (Q.map i₁).op)).symm.trans
                ((congrArg (fun f : op (Q.obj N) ⟶ op (Q.obj X) ↦ f.unop)
                  hproj).trans
                  ((unop_comp (f := (Q.map o₁).op) (g := cogroupMul.{u} n)).trans
                    (congrArg (fun f : Q.obj X ⟶ Q.obj V ↦ f ≫ Q.map o₁)
                      (cogroupMul_unop_eq_map.{u} n))))
          _ = _ := by
            simpa only [Functor.map_comp] using (congrArg Q.map hl₁).symm
  let d : V ⟶ W := BasedTopCat.basedWedgeDesc P (fun j ↦ match j with
    | WalkingPair.left => t 1
    | WalkingPair.right => t 2)
  have hd₀ : i₀ ≫ d = t 1 := BasedTopCat.basedWedgeι_desc P _ WalkingPair.left
  have hd₁ : i₁ ≫ d = t 2 := BasedTopCat.basedWedgeι_desc P _ WalkingPair.right
  have ho₀ : o₀ ≫ e.hom = t 0 :=
    BasedTopCat.basedWedgeFinThreeRightIso_ι_zero_hom D
  have ho₁ : o₁ ≫ e.hom = d := by
    apply BasedTopCat.basedWedge_hom_ext P
    intro j
    cases j with
    | left =>
        rw [← Category.assoc]
        exact (BasedTopCat.basedWedgeFinThreeRightIso_ι_one_hom D).trans hd₀.symm
    | right =>
        rw [← Category.assoc]
        exact (BasedTopCat.basedWedgeFinThreeRightIso_ι_two_hom D).trans hd₁.symm
  have hflat₀ : i₀ ≫ l ≫ e.hom = t 0 := by
    rw [← Category.assoc, hl₀, ho₀]
  have hflat₁ : i₁ ≫ l ≫ e.hom = pinchToWedge n ≫ d := by
    rw [← Category.assoc, hl₁, Category.assoc, ho₁]
  let H : C(W₃, W.right) := e₃.hom.right.hom.comp
    (⟨ULift.up, continuous_uliftUp⟩ : C(W₃, ULift.{u} W₃))
  have hH : H b₃ = BasedTopCat.point W := BasedTopCat.map_point e₃.hom
  let r : (X ⟶ W) → {F : C(S, W.right) // F a = BasedTopCat.point W} :=
    fun g ↦ ⟨g.right.hom.comp
      (⟨ULift.up, continuous_uliftUp⟩ : C(S, ULift.{u} S)), BasedTopCat.map_point g⟩
  let p : {F : C(S, W₃) // F a = b₃} →
      {F : C(S, W.right) // F a = BasedTopCat.point W} :=
    fun F ↦ ⟨H.comp F.val, (congrArg H F.property).trans hH⟩
  have ht (j : Fin 3) : r (t j) = p (I₃ j) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    exact (BasedTopCat.basedWedgeULiftIso_hom_ι.{0, u, 0}
      T₀ (fun _ ↦ a) j s).symm
  have hp (F G : {F : C(S, W₃) // F a = b₃}) :
      pinchFold n (BasedTopCat.point W) (p F, p G) =
        p (pinchFold n b₃ (F, G)) := by
    apply Subtype.ext
    simpa only [p, coe_pinchFold, apply_ite] using
      (pinch_postcomp n b₃ F G H hH).symm
  have hinner : r (pinchToWedge n ≫ d) = p (pinchFold n b₃ (I₃ 1, I₃ 2)) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    change (pinchToWedge n ≫ d).right.hom (ULift.up s) = _
    rw [pinchToWedge_comp_apply]
    change (pinchFold n (BasedTopCat.point W) (r (i₀ ≫ d), r (i₁ ≫ d))).val s = _
    rw [hd₀, hd₁, ht 1, ht 2, hp]
  have houter : r (pinchToWedge n ≫ l ≫ e.hom) = p R₃ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    change (pinchToWedge n ≫ (l ≫ e.hom)).right.hom (ULift.up s) = _
    rw [pinchToWedge_comp_apply]
    change (pinchFold n (BasedTopCat.point W)
      (r (i₀ ≫ l ≫ e.hom), r (i₁ ≫ l ≫ e.hom))).val s = _
    rw [hflat₀, hflat₁, ht 0, hinner, hp]
  let k : X ⟶ BasedTopCat.of (ULift.{u} W₃) (ULift.up b₃) :=
    BasedTopCat.ofHom
      (⟨fun z : ULift.{u} S ↦ ULift.up (Subtype.val R₃ z.down),
        continuous_uliftUp.comp ((Subtype.val R₃).continuous.comp continuous_uliftDown)⟩ :
        C(ULift.{u} S, ULift.{u} W₃))
      (congrArg (ULift.up : W₃ → ULift.{u} W₃) (Subtype.property R₃))
  have hstrict : pinchToWedge n ≫ l ≫ e.hom = k ≫ e₃.hom := by
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    rintro ⟨s⟩
    exact congrArg (fun F : {F : C(S, W.right) // F a = BasedTopCat.point W} ↦
      F.val s) houter
  rw [unop_comp, hw]
  change (Q.map (pinchToWedge n) ≫ Q.map l) ≫ Q.map e.hom =
    Q.map k ≫ Q.map e₃.hom
  have hmap : Q.map (pinchToWedge n ≫ l ≫ e.hom) =
      Q.map (pinchToWedge n) ≫ Q.map l ≫ Q.map e.hom :=
    (Q.map_comp (pinchToWedge n) (l ≫ e.hom)).trans
      (congrArg (fun f : Q.obj V ⟶ Q.obj W ↦ Q.map (pinchToWedge n) ≫ f)
        (Q.map_comp l e.hom))
  exact (Category.assoc _ _ _).trans
    (hmap.symm.trans ((congrArg (fun f : X ⟶ W ↦ Q.map f) hstrict).trans
      (Q.map_comp k e₃.hom)))

private theorem cogroup_lift_mul_eq_of_homotopicRel
    (f g h : basedSpace.{u} n ⟶ basedSpace.{u} n)
    (r : C(W₂, S)) (k : C(S, S)) (hr : r b₂ = a)
    (hf : ∀ s : S, f.right.hom (ULift.up s) =
      ULift.up (r (WidePushout.ι α 0 s)))
    (hg : ∀ s : S, g.right.hom (ULift.up s) =
      ULift.up (r (WidePushout.ι α 1 s)))
    (hh : ∀ s : S, h.right.hom (ULift.up s) = ULift.up (k s))
    (H : (r.comp (pinch n)).HomotopicRel k ({a} : Set S)) :
    CartesianMonoidalCategory.lift
        ((BasedTopCat.homotopyQuotient.{u}).map f).op
        ((BasedTopCat.homotopyQuotient.{u}).map g).op ≫ cogroupMul n =
      ((BasedTopCat.homotopyQuotient.{u}).map h).op := by
  let D := pairFunction (basedSpace.{u} n) (basedSpace.{u} n)
  let r' : BasedTopCat.of (ULift.{u} W₂) (ULift.up b₂) ⟶ basedSpace.{u} n :=
    BasedTopCat.ofHom
      (⟨fun z : ULift.{u} W₂ ↦ ULift.up (r z.down),
        continuous_uliftUp.comp (r.continuous.comp continuous_uliftDown)⟩ :
        C(ULift.{u} W₂, ULift.{u} S))
      (congrArg (ULift.up : S → ULift.{u} S) hr)
  let p : BasedTopCat.basedWedge D ⟶ basedSpace.{u} n :=
    (pinchWedgeIso n).inv ≫ r'
  have hc (z : ULift.{u} W₂) :
      (pinchWedgeIso.{u} n).inv.right.hom
          ((pinchWedgeIso.{u} n).hom.right.hom z) = z :=
    congrArg (fun q : BasedTopCat.of (ULift.{u} W₂) (ULift.up b₂) ⟶
        BasedTopCat.of (ULift.{u} W₂) (ULift.up b₂) ↦ q.right.hom z)
      (pinchWedgeIso.{u} n).hom_inv_id
  have hl : BasedTopCat.basedWedgeι D WalkingPair.left ≫ p = f := by
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    rintro ⟨s⟩
    change r'.right.hom ((pinchWedgeIso.{u} n).inv.right.hom
        ((BasedTopCat.basedWedgeι D WalkingPair.left).right.hom (ULift.up s))) =
      f.right.hom (ULift.up s)
    rw [← pinchWedgeIso_hom_ι_zero, hc]
    exact (hf s).symm
  have hr' : BasedTopCat.basedWedgeι D WalkingPair.right ≫ p = g := by
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    rintro ⟨s⟩
    change r'.right.hom ((pinchWedgeIso.{u} n).inv.right.hom
        ((BasedTopCat.basedWedgeι D WalkingPair.right).right.hom (ULift.up s))) =
      g.right.hom (ULift.up s)
    rw [← pinchWedgeIso_hom_ι_one, hc]
    exact (hg s).symm
  have hp : CartesianMonoidalCategory.lift
        ((BasedTopCat.homotopyQuotient.{u}).map f).op
        ((BasedTopCat.homotopyQuotient.{u}).map g).op =
      ((BasedTopCat.homotopyQuotient.{u}).map p).op := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [CartesianMonoidalCategory.lift_fst, BasedTopCat.homotopyOpposite_fst]
      change ((BasedTopCat.homotopyQuotient.{u}).map f).op =
        ((BasedTopCat.homotopyQuotient.{u}).map p).op ≫
          ((BasedTopCat.homotopyQuotient.{u}).map
            (BasedTopCat.basedWedgeι D WalkingPair.left)).op
      exact (congrArg (fun q : basedSpace.{u} n ⟶ basedSpace.{u} n ↦
        ((BasedTopCat.homotopyQuotient.{u}).map q).op) hl).symm.trans
          ((congrArg Quiver.Hom.op
            ((BasedTopCat.homotopyQuotient.{u}).map_comp
              (BasedTopCat.basedWedgeι D WalkingPair.left) p)).trans op_comp)
    · rw [CartesianMonoidalCategory.lift_snd, BasedTopCat.homotopyOpposite_snd]
      change ((BasedTopCat.homotopyQuotient.{u}).map g).op =
        ((BasedTopCat.homotopyQuotient.{u}).map p).op ≫
          ((BasedTopCat.homotopyQuotient.{u}).map
            (BasedTopCat.basedWedgeι D WalkingPair.right)).op
      exact (congrArg (fun q : basedSpace.{u} n ⟶ basedSpace.{u} n ↦
        ((BasedTopCat.homotopyQuotient.{u}).map q).op) hr').symm.trans
          ((congrArg Quiver.Hom.op
            ((BasedTopCat.homotopyQuotient.{u}).map_comp
              (BasedTopCat.basedWedgeι D WalkingPair.right) p)).trans op_comp)
  have hcomp : pinchToWedge.{u} n ≫ p = pinchBased n ≫ r' := by
    simp only [pinchToWedge, p, Category.assoc, Iso.hom_inv_id_assoc]
  let up : C(S, ULift.{u} S) := ⟨ULift.up, continuous_uliftUp⟩
  let down : C(ULift.{u} S, S) := ⟨ULift.down, continuous_uliftDown⟩
  have hh' : h.right.hom = (up.comp k).comp down := by
    apply ContinuousMap.ext
    intro z
    exact hh z.down
  rw [hp]
  apply Quiver.Hom.unop_inj
  change (BasedTopCat.homotopyQuotient.{u}).map (pinchToWedge n) ≫
      (BasedTopCat.homotopyQuotient.{u}).map p =
    (BasedTopCat.homotopyQuotient.{u}).map h
  rw [← Functor.map_comp, hcomp]
  apply (BasedTopCat.homotopyQuotient_map_eq_iff _ _).2
  change ContinuousMap.HomotopicRel
    ((up.comp (r.comp (pinch n))).comp down) h.right.hom ({ULift.up a} : Set (ULift.{u} S))
  rw [hh']
  exact (H.comp_continuousMap up).precomp_continuousMap down (by
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact Set.mem_singleton_iff.mpr rfl)

private theorem cogroup_toUnit_one_eq :
    CartesianMonoidalCategory.toUnit (cogroupCarrier.{u} n) ≫ cogroupOne n =
      ((BasedTopCat.homotopyQuotient.{u}).map
        (BasedTopCat.ofHom (x := ULift.up a) (y := ULift.up a)
          (ContinuousMap.const (ULift.{u} S) (ULift.up a)) rfl)).op := by
  let E : PEmpty.{1} → BasedTopCat.{u} := fun j ↦ isEmptyElim j
  let e : BasedTopCat.basedWedge E ⟶ basedSpace.{u} n :=
    BasedTopCat.basedWedgeDesc E (fun j ↦ isEmptyElim j)
  have he : CartesianMonoidalCategory.toUnit (cogroupCarrier.{u} n) =
      ((BasedTopCat.homotopyQuotient.{u}).map e).op :=
    CartesianMonoidalCategory.toUnit_unique _ _
  rw [he]
  apply Quiver.Hom.unop_inj
  change (BasedTopCat.homotopyQuotient.{u}).map (counitBased n) ≫
      (BasedTopCat.homotopyQuotient.{u}).map e = _
  rw [← Functor.map_comp]
  apply congrArg (fun f : basedSpace.{u} n ⟶ basedSpace.{u} n ↦
    (BasedTopCat.homotopyQuotient.{u}).map f)
  apply Under.UnderMorphism.ext
  apply TopCat.ext
  rintro ⟨s⟩
  exact (congrArg (fun t : (BasedTopCat.basedWedge E).right ↦ e.right.hom t)
    (counitBased_apply.{u} n (ULift.up s))).trans (BasedTopCat.map_point e)

/-- The left unit law for the specified maps, in the stock `MonObj` form. -/
theorem cogroup_one_mul :
    cogroupOne.{u} n ▷ cogroupCarrier.{u} n ≫ cogroupMul n =
      (λ_ (cogroupCarrier.{u} n)).hom := by
  let c : basedSpace.{u} n ⟶ basedSpace.{u} n :=
    BasedTopCat.ofHom (ContinuousMap.const (ULift.{u} S) (ULift.up a)) rfl
  apply (cancel_epi (λ_ (cogroupCarrier.{u} n)).inv).1
  rw [← Category.assoc, Iso.inv_hom_id]
  have hlift : (λ_ (cogroupCarrier.{u} n)).inv ≫
      (cogroupOne n ▷ cogroupCarrier n) =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.toUnit (cogroupCarrier n) ≫ cogroupOne n)
        (𝟙 (cogroupCarrier n)) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [hlift, cogroup_toUnit_one_eq]
  have hq : CartesianMonoidalCategory.lift
      ((BasedTopCat.homotopyQuotient.{u}).map c).op
      ((BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} n))).op ≫ cogroupMul n =
      ((BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} n))).op := by
    apply cogroup_lift_mul_eq_of_homotopicRel n c (𝟙 _) (𝟙 _)
      (TopCat.widePushoutPointRetraction D₀ (fun _ ↦ a) 1).hom (ContinuousMap.id S)
      (TopCat.widePushoutPointRetraction_head_apply D₀ (fun _ ↦ a) 1 PUnit.unit)
    · intro s
      exact (congrArg (ULift.up : S → ULift.{u} S)
        (TopCat.widePushoutPointRetraction_ι_of_ne_apply D₀ (fun _ ↦ a)
          1 0 (by decide) s)).symm
    · intro s
      exact (congrArg (ULift.up : S → ULift.{u} S)
        (TopCat.widePushoutPointRetraction_ι_apply D₀ (fun _ ↦ a) 1 s)).symm
    · intro s
      rfl
    · exact pinch_retraction_homotopicRel n 1
  have hid : ((BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} n))).op =
      𝟙 (cogroupCarrier.{u} n) :=
    (congrArg Quiver.Hom.op
      ((BasedTopCat.homotopyQuotient.{u}).map_id (basedSpace.{u} n))).trans op_id
  rw [hid] at hq
  exact hq

/-- The right unit law for the specified maps, in the stock `MonObj` form. -/
theorem cogroup_mul_one :
    cogroupCarrier.{u} n ◁ cogroupOne.{u} n ≫ cogroupMul n =
      (ρ_ (cogroupCarrier.{u} n)).hom := by
  let c : basedSpace.{u} n ⟶ basedSpace.{u} n :=
    BasedTopCat.ofHom (ContinuousMap.const (ULift.{u} S) (ULift.up a)) rfl
  apply (cancel_epi (ρ_ (cogroupCarrier.{u} n)).inv).1
  rw [← Category.assoc, Iso.inv_hom_id]
  have hlift : (ρ_ (cogroupCarrier.{u} n)).inv ≫
      (cogroupCarrier n ◁ cogroupOne n) =
      CartesianMonoidalCategory.lift (𝟙 (cogroupCarrier n))
        (CartesianMonoidalCategory.toUnit (cogroupCarrier n) ≫ cogroupOne n) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [hlift, cogroup_toUnit_one_eq]
  have hq : CartesianMonoidalCategory.lift
      ((BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} n))).op
      ((BasedTopCat.homotopyQuotient.{u}).map c).op ≫ cogroupMul n =
      ((BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} n))).op := by
    apply cogroup_lift_mul_eq_of_homotopicRel n (𝟙 _) c (𝟙 _)
      (TopCat.widePushoutPointRetraction D₀ (fun _ ↦ a) 0).hom (ContinuousMap.id S)
      (TopCat.widePushoutPointRetraction_head_apply D₀ (fun _ ↦ a) 0 PUnit.unit)
    · intro s
      exact (congrArg (ULift.up : S → ULift.{u} S)
        (TopCat.widePushoutPointRetraction_ι_apply D₀ (fun _ ↦ a) 0 s)).symm
    · intro s
      exact (congrArg (ULift.up : S → ULift.{u} S)
        (TopCat.widePushoutPointRetraction_ι_of_ne_apply D₀ (fun _ ↦ a)
          0 1 (by decide) s)).symm
    · intro s
      rfl
    · exact pinch_retraction_homotopicRel n 0
  have hid : ((BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} n))).op =
      𝟙 (cogroupCarrier.{u} n) :=
    (congrArg Quiver.Hom.op
      ((BasedTopCat.homotopyQuotient.{u}).map_id (basedSpace.{u} n))).trans op_id
  rw [hid] at hq
  exact hq

/-- Associativity for the specified pinch class, in the stock `MonObj` form. -/
theorem cogroup_mul_assoc :
    (cogroupMul.{u} n ▷ cogroupCarrier.{u} n) ≫ cogroupMul n =
      (α_ (cogroupCarrier.{u} n) (cogroupCarrier.{u} n) (cogroupCarrier.{u} n)).hom ≫
        (cogroupCarrier.{u} n ◁ cogroupMul n) ≫ cogroupMul n := by
  let Q := BasedTopCat.homotopyQuotient.{u}
  let e := BasedTopCat.basedWedgeFinThreeLeftIso (fun _ : Fin 3 ↦ basedSpace.{u} n)
  let e' := BasedTopCat.basedWedgeFinThreeRightIso (fun _ : Fin 3 ↦ basedSpace.{u} n)
  let e₃ := BasedTopCat.basedWedgeULiftIso.{0, u, 0} T₀ (fun _ ↦ a)
  let kₗ : basedSpace.{u} n ⟶ BasedTopCat.of (ULift.{u} W₃) (ULift.up b₃) :=
    BasedTopCat.ofHom
      (⟨fun z : ULift.{u} S ↦ ULift.up (Subtype.val L₃ z.down),
        continuous_uliftUp.comp ((Subtype.val L₃).continuous.comp continuous_uliftDown)⟩ :
        C(ULift.{u} S, ULift.{u} W₃))
      (congrArg (ULift.up : W₃ → ULift.{u} W₃) (Subtype.property L₃))
  let kᵣ : basedSpace.{u} n ⟶ BasedTopCat.of (ULift.{u} W₃) (ULift.up b₃) :=
    BasedTopCat.ofHom
      (⟨fun z : ULift.{u} S ↦ ULift.up (Subtype.val R₃ z.down),
        continuous_uliftUp.comp ((Subtype.val R₃).continuous.comp continuous_uliftDown)⟩ :
        C(ULift.{u} S, ULift.{u} W₃))
      (congrArg (ULift.up : W₃ → ULift.{u} W₃) (Subtype.property R₃))
  -- Lift the existing original three-inclusion, north-relative coassociativity.
  have hLR : Q.map kₗ = Q.map kᵣ := by
    apply (BasedTopCat.homotopyQuotient_map_eq_iff kₗ kᵣ).2
    exact ContinuousMap.HomotopicRel.precomp_continuousMap
      ((pinch_homotopicRel_coassoc n).comp_continuousMap
        (⟨ULift.up, continuous_uliftUp⟩ : C(W₃, ULift.{u} W₃)))
      (⟨ULift.down, continuous_uliftDown⟩ : C(ULift.{u} S, S))
      (by
        intro z hz
        have hz' : z = ULift.up a := Set.mem_singleton_iff.mp hz
        subst z
        exact Set.mem_singleton_iff.mpr rfl)
  have hα :
      (α_ (cogroupCarrier.{u} n) (cogroupCarrier.{u} n) (cogroupCarrier.{u} n)).hom.unop ≫
          Q.map e.hom = Q.map e'.hom :=
    cogroup_associator_unop_comp_finThreeLeft n
  have hleft :
      ((cogroupMul.{u} n ▷ cogroupCarrier.{u} n) ≫ cogroupMul n).unop ≫ Q.map e.hom =
        Q.map kₗ ≫ Q.map e₃.hom :=
    cogroupMul_left_unop_comp_finThreeLeft n
  have hright :
      ((cogroupCarrier.{u} n ◁ cogroupMul.{u} n) ≫ cogroupMul n).unop ≫ Q.map e'.hom =
        Q.map kᵣ ≫ Q.map e₃.hom :=
    cogroupMul_right_unop_comp_finThreeRight n
  have hflat :
      ((cogroupMul.{u} n ▷ cogroupCarrier.{u} n) ≫ cogroupMul n).unop ≫ Q.map e.hom =
        ((cogroupCarrier.{u} n ◁ cogroupMul.{u} n) ≫ cogroupMul n).unop ≫ Q.map e'.hom :=
    hleft.trans ((congrArg
      (fun f : Q.obj (basedSpace.{u} n) ⟶
          Q.obj (BasedTopCat.of (ULift.{u} W₃) (ULift.up b₃)) ↦
        f ≫ Q.map e₃.hom) hLR).trans hright.symm)
  -- The comparison is a strict isomorphism, hence its mapped opposite is epi.
  apply (cancel_epi ((Q.map e.hom).op)).1
  apply Quiver.Hom.unop_inj
  change ((cogroupMul.{u} n ▷ cogroupCarrier.{u} n) ≫ cogroupMul n).unop ≫ Q.map e.hom =
    (((cogroupCarrier.{u} n ◁ cogroupMul.{u} n) ≫ cogroupMul n).unop ≫
      (α_ (cogroupCarrier.{u} n) (cogroupCarrier.{u} n) (cogroupCarrier.{u} n)).hom.unop) ≫
        Q.map e.hom
  exact hflat.trans
    ((congrArg
      (fun f : unop (cogroupCarrier.{u} n ⊗
          (cogroupCarrier.{u} n ⊗ cogroupCarrier.{u} n)) ⟶
            Q.obj (BasedTopCat.basedWedge (fun _ : Fin 3 ↦ basedSpace.{u} n)) ↦
        ((cogroupCarrier.{u} n ◁ cogroupMul.{u} n) ≫ cogroupMul n).unop ≫ f)
      hα).symm.trans
        (Category.assoc
          ((cogroupCarrier.{u} n ◁ cogroupMul.{u} n) ≫ cogroupMul n).unop
          (α_ (cogroupCarrier.{u} n) (cogroupCarrier.{u} n) (cogroupCarrier.{u} n)).hom.unop
          (Q.map e.hom)).symm)

/-- The left inverse law for physical reflection, in the stock `GrpObj` form. -/
theorem cogroup_left_inv :
    CartesianMonoidalCategory.lift (cogroupInv.{u} n) (𝟙 (cogroupCarrier.{u} n)) ≫ cogroupMul n =
      CartesianMonoidalCategory.toUnit (cogroupCarrier.{u} n) ≫ cogroupOne n := by
  let c : basedSpace.{u} n ⟶ basedSpace.{u} n :=
    BasedTopCat.ofHom (ContinuousMap.const (ULift.{u} S) (ULift.up a)) rfl
  rw [cogroup_toUnit_one_eq]
  have hq : CartesianMonoidalCategory.lift
      ((BasedTopCat.homotopyQuotient.{u}).map (coordinateReflectionBased n)).op
      ((BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} n))).op ≫ cogroupMul n =
      ((BasedTopCat.homotopyQuotient.{u}).map c).op := by
    let F : {F : C(S, S) // F a = a} :=
      ⟨coordinateReflection n (0 : Fin (n + 1)),
        coordinateReflection_northPoint n (0 : Fin (n + 1))⟩
    let G : {F : C(S, S) // F a = a} := ⟨ContinuousMap.id S, rfl⟩
    let r := TopCat.widePushoutDesc α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G))
    apply cogroup_lift_mul_eq_of_homotopicRel n (coordinateReflectionBased n) (𝟙 _) c
      r (ContinuousMap.const S a) (TopCat.widePushoutDesc_head α _ _ _ PUnit.unit)
    · intro s
      exact (coordinateReflectionBased_apply.{u} n s).trans
        (congrArg (ULift.up : S → ULift.{u} S)
          (TopCat.widePushoutDesc_ι α
            (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
            (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
            (fun j _ ↦ Subtype.property (ite (j = 0) F G)) 0 s)).symm
    · intro s
      exact (congrArg (ULift.up : S → ULift.{u} S)
        (TopCat.widePushoutDesc_ι α
          (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
          (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
          (fun j _ ↦ Subtype.property (ite (j = 0) F G)) 1 s)).symm
    · intro s
      rfl
    · exact pinch_coordinateReflection_id_homotopicRel n (0 : Fin (n + 1))
  have hid : ((BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} n))).op =
      𝟙 (cogroupCarrier.{u} n) :=
    (congrArg Quiver.Hom.op
      ((BasedTopCat.homotopyQuotient.{u}).map_id (basedSpace.{u} n))).trans op_id
  rw [hid] at hq
  exact hq

/-- The right inverse law for physical reflection, in the stock `GrpObj` form. -/
theorem cogroup_right_inv :
    CartesianMonoidalCategory.lift (𝟙 (cogroupCarrier.{u} n)) (cogroupInv.{u} n) ≫ cogroupMul n =
      CartesianMonoidalCategory.toUnit (cogroupCarrier.{u} n) ≫ cogroupOne n := by
  let c : basedSpace.{u} n ⟶ basedSpace.{u} n :=
    BasedTopCat.ofHom (ContinuousMap.const (ULift.{u} S) (ULift.up a)) rfl
  rw [cogroup_toUnit_one_eq]
  have hq : CartesianMonoidalCategory.lift
      ((BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} n))).op
      ((BasedTopCat.homotopyQuotient.{u}).map (coordinateReflectionBased n)).op ≫ cogroupMul n =
      ((BasedTopCat.homotopyQuotient.{u}).map c).op := by
    let F : {F : C(S, S) // F a = a} := ⟨ContinuousMap.id S, rfl⟩
    let G : {F : C(S, S) // F a = a} :=
      ⟨coordinateReflection n (0 : Fin (n + 1)),
        coordinateReflection_northPoint n (0 : Fin (n + 1))⟩
    let r := TopCat.widePushoutDesc α
      (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
      (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
      (fun j _ ↦ Subtype.property (ite (j = 0) F G))
    apply cogroup_lift_mul_eq_of_homotopicRel n (𝟙 _) (coordinateReflectionBased n) c
      r (ContinuousMap.const S a) (TopCat.widePushoutDesc_head α _ _ _ PUnit.unit)
    · intro s
      exact (congrArg (ULift.up : S → ULift.{u} S)
        (TopCat.widePushoutDesc_ι α
          (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
          (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
          (fun j _ ↦ Subtype.property (ite (j = 0) F G)) 0 s)).symm
    · intro s
      exact (coordinateReflectionBased_apply.{u} n s).trans
        (congrArg (ULift.up : S → ULift.{u} S)
          (TopCat.widePushoutDesc_ι α
            (ContinuousMap.const (TopCat.of (PUnit : Type)) a)
            (fun j : Fin 2 ↦ Subtype.val (ite (j = 0) F G))
            (fun j _ ↦ Subtype.property (ite (j = 0) F G)) 1 s)).symm
    · intro s
      rfl
    · exact pinch_id_coordinateReflection_homotopicRel n (0 : Fin (n + 1))
  have hid : ((BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} n))).op =
      𝟙 (cogroupCarrier.{u} n) :=
    (congrArg Quiver.Hom.op
      ((BasedTopCat.homotopyQuotient.{u}).map_id (basedSpace.{u} n))).trans op_id
  rw [hid] at hq
  exact hq

/-- The stock monoid-object data of the sphere in the ordinary opposite category.
This is named data, not a global instance. -/
@[instance_reducible]
def cogroupMonObj : MonObj (cogroupCarrier.{u} n) where
  one := cogroupOne n
  mul := cogroupMul n
  one_mul := cogroup_one_mul n
  mul_one := cogroup_mul_one n
  mul_assoc := cogroup_mul_assoc n

/-- The stock group-object data with physical reflection as inverse.
This is named data, not a global instance. -/
@[instance_reducible]
def cogroupGrpObj : GrpObj (cogroupCarrier.{u} n) where
  toMonObj := cogroupMonObj n
  inv := cogroupInv n
  left_inv := cogroup_left_inv n
  right_inv := cogroup_right_inv n

/-- The sphere cogroup, bundled as a stock group object in the ordinary opposite
based-homotopy category. -/
def cogroup : Grp (BasedTopCat.HomotopyCategory.{u}ᵒᵖ) where
  X := cogroupCarrier.{u} n
  grp := cogroupGrpObj n

/-- The bundled carrier is precisely the opposite quotient image of the lifted sphere. -/
theorem cogroup_X :
    (cogroup.{u} n).X =
      op ((BasedTopCat.homotopyQuotient.{u}).obj
        (BasedTopCat.of (ULift.{u} S) (ULift.up a))) := rfl

/-- The stock multiplication field is the specified original pinch class. -/
theorem cogroupGrpObj_mul :
    (cogroupGrpObj.{u} n).toMonObj.mul = cogroupMul n := rfl

/-- The stock unit field is the specified collapse class. -/
theorem cogroupGrpObj_one :
    (cogroupGrpObj.{u} n).toMonObj.one = cogroupOne n := rfl

/-- The stock inverse field is the specified physical reflection class. -/
theorem cogroupGrpObj_inv : (cogroupGrpObj.{u} n).inv = cogroupInv n := rfl

end Metric.Sphere
