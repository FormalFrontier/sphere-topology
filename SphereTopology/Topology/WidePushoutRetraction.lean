/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# Retractions onto factors of a point-wide-pushout

For an arbitrary family of spaces with chosen points, each factor of the
categorical wide pushout over a point has a canonical continuous retraction.
`TopCat.widePushoutPointRetraction` fixes the selected factor, sends every other
factor to the selected point, and sends the head to that point. Consequently,
each factor inclusion is an embedding, without separation or finiteness assumptions.
The head remains part of the diagram when the index is empty.

The index and space universes are independent: the diagram lies in their maximum.
For original spaces `X₀ : I → TopCat.{u}`, import
`Mathlib.Topology.Category.TopCat.ULift` and use `F := TopCat.uliftFunctor.{v,u}`
and `e j := (X₀ j).uliftFunctorObjHomeo`. Apply the construction to
`X j := F.obj (X₀ j)` and `x j := e j (x₀ j)`. Writing `a j := TopCat.const (x j)`,
the original-space inclusion and retraction are the explicit continuous maps
`(WidePushout.ι a j).hom.comp (e j : C(X₀ j, X j))` and
`((e i).symm : C(X i, X₀ i)).comp (widePushoutPointRetraction X x i).hom`.
Their composite is the identity for the selected factor and constant at `x₀ i`
for every other factor; the head has value `x₀ i`. Each original-space inclusion
is an embedding by composition with the homeomorphism. No equality of universes
or user-supplied smallness witness is needed.

## Implementation notes

The dependent factor maps use equality transport internally. The construction
uses only categorical descent, independently of any quotient presentation.
It generalizes the factor-selection construction of
`SphereTopology.Homotopy.CircleBouquet`, whose retraction now uses this map.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  p. 19, for the point-wedge setting.
* Mathlib's wide pushouts and topological colimits supply the descent construction;
  its `Function.LeftInverse.isEmbedding` supplies the embedding consequence.
* `SphereTopology.Homotopy.CircleBouquet` supplies the original circle-factor
  retraction approach and a nontrivial application.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace TopCat

variable {I : Type v} (X : I → TopCat.{max u v}) (x : ∀ j, X j)

section

variable {X}

/-- The chosen point of each factor is the common head point. -/
@[simp] theorem widePushout_point_ι_point (a : ∀ i, X i) (i : I) :
    WidePushout.ι (B := TopCat.of PUnit.{max u v + 1})
      (fun j ↦ TopCat.const (a j)) i (a i) =
        WidePushout.head (fun j ↦ TopCat.const (a j)) PUnit.unit :=
  congrArg (fun k : TopCat.of PUnit.{max u v + 1} ⟶
      widePushout (TopCat.of PUnit.{max u v + 1}) X (fun j ↦ TopCat.const (a j)) ↦
    k PUnit.unit) (WidePushout.arrow_ι (fun j ↦ TopCat.const (a j)) i)

end

/-- Retract a wide pushout of chosen-point spaces onto its selected factor. -/
def widePushoutPointRetraction (i : I) :
    widePushout (TopCat.of PUnit.{max u v + 1}) X
      (fun j ↦ TopCat.const (x j)) ⟶ X i := by
  classical
  exact WidePushout.desc (TopCat.const (x i))
    (fun j ↦ if h : j = i then eqToHom (congrArg X h) else TopCat.const (x i)) (by
      intro j
      by_cases h : j = i
      · subst j
        simp
      · apply TopCat.ext
        intro b
        simp [h]
        rfl)

/-- The head is sent to the selected point. -/
@[simp] theorem widePushoutPointRetraction_head (i : I) :
    WidePushout.head (fun j ↦ TopCat.const (x j)) ≫
      widePushoutPointRetraction X x i = TopCat.const (x i) :=
  WidePushout.head_desc _ _ _ _

/-- Retraction composed with the selected factor inclusion is the identity. -/
@[simp] theorem widePushoutPointRetraction_ι (i : I) :
    WidePushout.ι (fun j ↦ TopCat.const (x j)) i ≫
      widePushoutPointRetraction X x i = 𝟙 (X i) := by
  classical
  unfold widePushoutPointRetraction
  rw [WidePushout.ι_desc]
  simp

/-- Retraction is constant at the selected point on every other factor. -/
theorem widePushoutPointRetraction_ι_of_ne (i j : I) (hji : j ≠ i) :
    WidePushout.ι (fun j ↦ TopCat.const (x j)) j ≫
      widePushoutPointRetraction X x i = TopCat.const (x i) := by
  classical
  unfold widePushoutPointRetraction
  rw [WidePushout.ι_desc]
  simp [hji]

/-- Pointwise computation on the head. -/
@[simp] theorem widePushoutPointRetraction_head_apply (i : I)
    (b : PUnit.{max u v + 1}) :
    widePushoutPointRetraction X x i
      (WidePushout.head (fun j ↦ TopCat.const (x j)) b) = x i :=
  congrArg (fun k : TopCat.of PUnit.{max u v + 1} ⟶ X i ↦ k b)
    (widePushoutPointRetraction_head X x i)

/-- Pointwise computation on the retained factor. -/
@[simp] theorem widePushoutPointRetraction_ι_apply (i : I) (t : X i) :
    widePushoutPointRetraction X x i
      (WidePushout.ι (fun j ↦ TopCat.const (x j)) i t) = t :=
  congrArg (fun k : X i ⟶ X i ↦ k t) (widePushoutPointRetraction_ι X x i)

/-- Pointwise computation on an omitted factor. -/
theorem widePushoutPointRetraction_ι_of_ne_apply (i j : I) (hji : j ≠ i) (t : X j) :
    widePushoutPointRetraction X x i
      (WidePushout.ι (fun k ↦ TopCat.const (x k)) j t) = x i :=
  congrArg (fun k : X j ⟶ X i ↦ k t) (widePushoutPointRetraction_ι_of_ne X x i j hji)

/-- Every factor of a point-wide-pushout embeds, since it has a continuous left inverse. -/
theorem isEmbedding_widePushout_point_ι (i : I) :
    Topology.IsEmbedding (WidePushout.ι (B := TopCat.of PUnit.{max u v + 1})
      (fun j ↦ TopCat.const (x j)) i) := by
  have h : Function.LeftInverse (widePushoutPointRetraction X x i)
      (WidePushout.ι (fun j ↦ TopCat.const (x j)) i) := by
    intro t
    exact congrArg (fun k : X i ⟶ X i ↦ k t) (widePushoutPointRetraction_ι X x i)
  exact h.isEmbedding (widePushoutPointRetraction X x i).hom.continuous
    (WidePushout.ι (fun j ↦ TopCat.const (x j)) i).hom.continuous

end TopCat
