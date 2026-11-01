/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Limits.WidePushout.PointMap
public import SphereTopology.Topology.WidePushoutRetraction

/-!
# Descent of maps between point-attached families

These lemmas use the existing `TopCat.widePushoutDesc`, with a constant head
map and the prescribed factor maps. There is no additional space or bundled
family morphism. Point-family compatibility, evaluation, uniqueness,
identity and composition are supplied by the public Fundamental Groupoids
point-map API.

Identity, composition and the range formula need only point preservation.
The final-topology test is Mathlib's colimit test, including the head object
when the index type is empty.

## References

The categorical and point-collision API is due to Formal Frontier Agents and
Mathlib's colimit/quotient constructions (including Joël Riou's pushouts).
Mathlib's map API is due to Johannes Hölzl, Mario Carneiro and Patrick Massot.
Tiller and Loupe's public mathematical discussion supplied image/preimage and
empty-head observations. The existing provider notices remain authoritative.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u v w z

namespace TopCat

variable {I : Type v}

/-- The final topology of a wide pushout tests both its head and every factor. -/
theorem isOpen_widePushout_iff {B : TopCat.{max u v}}
    {X : I → TopCat.{max u v}} (s : ∀ i, B ⟶ X i)
    (V : Set (widePushout B X s : TopCat.{max u v})) :
    IsOpen V ↔ IsOpen (WidePushout.head s ⁻¹' V) ∧
      ∀ i, IsOpen (WidePushout.ι s i ⁻¹' V) := by
  refine (isOpen_iff_of_isColimit
    (colimit.cocone (WidePushoutShape.wideSpan B X s))
    (colimit.isColimit _) V).trans ?_
  constructor
  · intro h
    exact ⟨h none, fun i ↦ h (some i)⟩
  · rintro ⟨hB, hX⟩ (_ | i)
    · exact hB
    · exact hX i

variable {X : I → TopCat.{max u v}} {Y : I → TopCat.{max w v}}
  (a : ∀ i, X i) (b : ∀ i, Y i)

set_option quotPrecheck false in
local notation "PX" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "PY" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "α" => (fun i ↦ (TopCat.const (a i) : PX ⟶ X i))
set_option quotPrecheck false in
local notation "β" => (fun i ↦ (TopCat.const (b i) : PY ⟶ Y i))
set_option quotPrecheck false in
local notation "WX" => (widePushout PX X α : TopCat)
set_option quotPrecheck false in
local notation "WY" => (widePushout PY Y β : TopCat)
set_option quotPrecheck false in
local notation "hx" => WidePushout.head α PUnit.unit
set_option quotPrecheck false in
local notation "hy" => WidePushout.head β PUnit.unit

variable (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (a i) = b i)

set_option quotPrecheck false in
local notation "F" => widePushoutDesc α (ContinuousMap.const PX hy)
  (fun i ↦ (WidePushout.ι β i).hom.comp (f i))
  (widePushoutDesc_point_condition a b f hf)

/-- The image is the head together with the factor images, without embedding
assumptions. The head term is retained even when the index type is empty. -/
theorem range_widePushoutDesc_point :
    range F = {hy} ∪ ⋃ i, WidePushout.ι β i '' range (f i) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨_ | i, t, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan PX X α) q
    · left
      exact mem_singleton_iff.2 (widePushoutDesc_point_head a b f hf t)
    · right
      refine mem_iUnion.2 ⟨i, ?_⟩
      exact ⟨f i t, ⟨t, rfl⟩, (widePushoutDesc_point_ι a b f hf i t).symm⟩
  · rintro (hmem | hmem)
    · obtain rfl := mem_singleton_iff.1 hmem
      exact ⟨hx, widePushoutDesc_point_head a b f hf PUnit.unit⟩
    · rcases mem_iUnion.1 hmem with ⟨i, t, ⟨x, rfl⟩, rfl⟩
      exact ⟨WidePushout.ι α i x, widePushoutDesc_point_ι a b f hf i x⟩

end TopCat
