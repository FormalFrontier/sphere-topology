/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.Chart

/-!
# Retractions of subsets in point-attached wide pushouts

A subset containing the common point inherits a continuous retraction onto its
inverse image in each factor. The section is the restriction of the categorical
factor inclusion. Consequently, the subset is path connected if and only if all
its factor inverse images are path connected.

No openness or connectedness assumption on the whole factors is needed. The index
and space universes are independent, and the empty family retains its common point.

## References

* The factor retractions are those of `TopCat.widePushoutPointRetraction`.
* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  motivates the point-attached setting. The arbitrary-subset retraction criterion
  is not a statement from that text.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u v

namespace TopCat

variable {I : Type v} {X : I → TopCat.{max u v}} (a : ∀ i, X i)

local notation "P" => TopCat.of PUnit
local notation "f" => (fun i ↦ (TopCat.const (a i) : P ⟶ X i))
local notation "W" => (widePushout P X f : TopCat)

/-- A factor retraction sends a subset containing the common point into its
inverse image under the corresponding factor inclusion. -/
theorem mapsTo_widePushoutPointRetraction_preimage {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) (i : I) :
    MapsTo (widePushoutPointRetraction X a i) C (WidePushout.ι f i ⁻¹' C) := by
  classical
  intro z hz
  change WidePushout.ι f i (widePushoutPointRetraction X a i z) ∈ C
  rcases subset_head_union_widePushoutPointSupport a C hz with hzhead | hzfactor
  · have hz' : z = WidePushout.head f PUnit.unit := mem_singleton_iff.mp hzhead
    subst z
    rw [widePushoutPointRetraction_head_apply X a i PUnit.unit,
      widePushout_point_ι_point a i]
    exact hC
  · rcases mem_iUnion.mp hzfactor with ⟨j, hj⟩
    rcases mem_iUnion.mp hj with ⟨_, x, rfl⟩
    by_cases hji : j = i
    · subst j
      simpa only [widePushoutPointRetraction_ι_apply] using hz
    · rw [widePushoutPointRetraction_ι_of_ne_apply X a i j hji,
        widePushout_point_ι_point a i]
      exact hC

/-- The image of a subset containing the common point under a factor retraction
is precisely its inverse image in that factor. -/
theorem image_widePushoutPointRetraction {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) (i : I) :
    widePushoutPointRetraction X a i '' C = WidePushout.ι f i ⁻¹' C := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact mapsTo_widePushoutPointRetraction_preimage a hC i hz
  · intro x hx
    exact ⟨WidePushout.ι f i x, hx, widePushoutPointRetraction_ι_apply X a i x⟩

/-- The restriction of a factor retraction to a subset containing the common point,
with codomain restricted to the corresponding factor inverse image. -/
def widePushoutPointSubsetRetraction {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) (i : I) :
    C(C, WidePushout.ι f i ⁻¹' C) where
  toFun z := ⟨widePushoutPointRetraction X a i z,
    mapsTo_widePushoutPointRetraction_preimage a hC i z.property⟩
  continuous_toFun :=
    ((widePushoutPointRetraction X a i).hom.continuous.comp continuous_subtype_val).subtype_mk _

/-- The restricted retraction has the same underlying values as the factor retraction. -/
@[simp] theorem coe_widePushoutPointSubsetRetraction_apply {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) (i : I) (z : C) :
    (widePushoutPointSubsetRetraction a hC i z : X i) =
      widePushoutPointRetraction X a i z := rfl

/-- The restricted factor inclusion is a section of the subset retraction. -/
@[simp] theorem widePushoutPointSubsetRetraction_restrictPreimage_apply {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) (i : I)
    (x : WidePushout.ι f i ⁻¹' C) :
    widePushoutPointSubsetRetraction a hC i
      (C.restrictPreimage (WidePushout.ι f i) x) = x := by
  apply Subtype.ext
  exact widePushoutPointRetraction_ι_apply X a i x

/-- The subset retraction is a continuous left inverse to the restricted factor inclusion. -/
theorem leftInverse_widePushoutPointSubsetRetraction {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) (i : I) :
    Function.LeftInverse (widePushoutPointSubsetRetraction a hC i)
      ((WidePushout.ι f i).hom.restrictPreimage C) :=
  widePushoutPointSubsetRetraction_restrictPreimage_apply a hC i

/-- Composing the restricted inclusion with the subset retraction is the identity. -/
@[simp] theorem widePushoutPointSubsetRetraction_comp_restrictPreimage {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) (i : I) :
    (widePushoutPointSubsetRetraction a hC i).comp
      ((WidePushout.ι f i).hom.restrictPreimage C) = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  exact widePushoutPointSubsetRetraction_restrictPreimage_apply a hC i

/-- A subset containing the common point is path connected exactly when all its
factor inverse images are path connected. -/
theorem isPathConnected_widePushout_point_preimage_iff {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) :
    IsPathConnected C ↔ ∀ i, IsPathConnected (WidePushout.ι f i ⁻¹' C) := by
  constructor
  · intro h i
    rw [← image_widePushoutPointRetraction a hC i]
    exact h.image (widePushoutPointRetraction X a i).hom.continuous
  · exact isPathConnected_of_widePushout_point_preimage a hC

end TopCat
