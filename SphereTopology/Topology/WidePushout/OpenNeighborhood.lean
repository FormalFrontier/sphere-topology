/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.OpenEmbedding
public import Mathlib.Topology.Constructions

/-!
# Open neighborhoods in a point-attached wide pushout

Open factor neighborhoods of the attaching points give an open neighborhood of
the common head. Its factor preimages are exactly the chosen neighborhoods.
The wide pushout of their subtype inclusions is identified with this ordinary
open subtype by Mathlib's embedding-to-range homeomorphism.

All spaces and maps are the existing categorical wide pushouts and descents.
The head is retained explicitly, including for an empty index type.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe v w

namespace TopCat

variable {I : Type v} {Y : I → TopCat.{max w v}}
  (b : ∀ i, Y i) (U : ∀ i, Set (Y i))

set_option quotPrecheck false in
local notation "P" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "β" => (fun i ↦ (TopCat.const (b i) : P ⟶ Y i))
set_option quotPrecheck false in
local notation "WY" => (widePushout P Y β : TopCat)
set_option quotPrecheck false in
local notation "hy" => WidePushout.head β PUnit.unit

/-- The head together with the images of the chosen factor subsets. -/
def widePushoutPointNeighborhood : Set WY :=
  {hy} ∪ ⋃ i, WidePushout.ι β i '' U i

/-- Membership in the union describing a point-wide-pushout neighborhood. -/
@[simp]
theorem mem_widePushoutPointNeighborhood (y : WY) :
    y ∈ widePushoutPointNeighborhood b U ↔
      y = hy ∨ ∃ i, ∃ x ∈ U i, WidePushout.ι β i x = y := by
  simp only [widePushoutPointNeighborhood, mem_union, mem_singleton_iff,
    mem_iUnion, mem_image]

/-- The neighborhood construction always retains the head. -/
theorem widePushoutPointNeighborhood_head_mem :
    hy ∈ widePushoutPointNeighborhood b U :=
  Or.inl rfl

variable (hb : ∀ i, b i ∈ U i)

set_option quotPrecheck false in
local notation "XU" => (fun i ↦ TopCat.of (U i))
set_option quotPrecheck false in
local notation "aU" => (fun i ↦ (⟨b i, hb i⟩ : U i))
set_option quotPrecheck false in
local notation "ιU" => (fun i ↦ (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, Y i)))
set_option quotPrecheck false in
local notation "α" => (fun i ↦ (TopCat.const (aU i) : P ⟶ XU i))
set_option quotPrecheck false in
local notation "WU" => (widePushout P XU α : TopCat)
set_option quotPrecheck false in
local notation "F" => widePushoutDesc α (ContinuousMap.const P hy)
  (fun i ↦ (WidePushout.ι β i).hom.comp (ιU i))
  (widePushoutDesc_point_condition (X := XU) (Y := Y) aU b ιU (fun _ ↦ rfl))

/-- Subtype inclusions have precisely the prescribed neighborhood union as range.
This equality needs the basepoint memberships, but does not need openness. -/
theorem range_widePushoutDesc_point_subtype :
    range F = widePushoutPointNeighborhood b U := by
  rw [range_widePushoutDesc_point (X := XU) (Y := Y) aU b ιU (fun _ ↦ rfl)]
  change {hy} ∪ ⋃ i, WidePushout.ι β i '' range (ιU i) =
    {hy} ∪ ⋃ i, WidePushout.ι β i '' U i
  ext y
  constructor
  · rintro (hh | h)
    · exact Or.inl hh
    · rcases mem_iUnion.1 h with ⟨i, z, ⟨x, rfl⟩, rfl⟩
      exact Or.inr (mem_iUnion.2 ⟨i, (x : Y i), x.property, rfl⟩)
  · rintro (hh | h)
    · exact Or.inl hh
    · rcases mem_iUnion.1 h with ⟨i, z, hz, rfl⟩
      exact Or.inr (mem_iUnion.2 ⟨i, z, ⟨⟨z, hz⟩, rfl⟩, rfl⟩)

variable (hU : ∀ i, IsOpen (U i))

/-- Each factor sees exactly its prescribed subset if that subset contains its
attaching point. No openness is required, and the other subsets are arbitrary. -/
@[simp]
theorem preimage_widePushoutPointNeighborhood (i : I) (hi : b i ∈ U i) :
    WidePushout.ι β i ⁻¹' widePushoutPointNeighborhood b U = U i := by
  ext y
  constructor
  · intro h
    by_cases hyb : y = b i
    · rw [hyb]
      exact hi
    · rcases (mem_widePushoutPointNeighborhood b U _).1 h with hh | ⟨k, z, hz, he⟩
      · exact (hyb ((widePushout_point_ι_eq_head_iff b i y).1 hh)).elim
      · have hik : i = k := congrArg Sigma.fst
          ((widePushout_point_ι_eq_ι_iff_of_ne b hyb).1 he.symm)
        subst k
        have hzy : z = y := (isEmbedding_widePushout_point_ι Y b i).injective he
        exact hzy ▸ hz
  · intro hyU
    exact (mem_widePushoutPointNeighborhood b U _).2 (Or.inr ⟨i, y, hyU, rfl⟩)

include hb hU

/-- The neighborhood union is open in the existing target wide pushout. -/
theorem isOpen_widePushoutPointNeighborhood :
    IsOpen (widePushoutPointNeighborhood b U) := by
  rw [← range_widePushoutDesc_point_subtype b U hb]
  exact (isOpenEmbedding_widePushoutDesc_point (X := XU) (Y := Y) aU b ιU (fun _ ↦ rfl)
    (fun i ↦ (hU i).isOpenEmbedding_subtypeVal)).2

/-- The source wide pushout is homeomorphic to the ordinary open neighborhood
subtype, using the existing embedding-to-range homeomorphism. -/
def widePushoutPointNeighborhoodHomeomorph :
    WU ≃ₜ widePushoutPointNeighborhood b U :=
  (isOpenEmbedding_widePushoutDesc_point (X := XU) (Y := Y) aU b ιU (fun _ ↦ rfl)
    (fun i ↦ (hU i).isOpenEmbedding_subtypeVal)).1.toHomeomorph |>.trans
      (Homeomorph.setCongr (range_widePushoutDesc_point_subtype b U hb))

/-- The homeomorphism has the canonical descent as its underlying function. -/
@[simp]
theorem widePushoutPointNeighborhoodHomeomorph_coe (q : WU) :
    ((widePushoutPointNeighborhoodHomeomorph b U hb hU q :
      widePushoutPointNeighborhood b U) : WY) = F q :=
  rfl

/-- The head maps to the head of the ordinary neighborhood subtype. -/
@[simp]
theorem widePushoutPointNeighborhoodHomeomorph_head (q : PUnit.{max w v + 1}) :
    widePushoutPointNeighborhoodHomeomorph b U hb hU (WidePushout.head α q) =
      ⟨hy, widePushoutPointNeighborhood_head_mem b U⟩ := by
  apply Subtype.ext
  exact (widePushoutPointNeighborhoodHomeomorph_coe b U hb hU
    (WidePushout.head α q)).trans
      (widePushoutDesc_point_head (X := XU) (Y := Y) aU b ιU (fun _ ↦ rfl) q)

/-- On each subtype factor the homeomorphism is the original factor inclusion. -/
@[simp]
theorem widePushoutPointNeighborhoodHomeomorph_ι (i : I) (x : U i) :
    widePushoutPointNeighborhoodHomeomorph b U hb hU (WidePushout.ι α i x) =
      ⟨WidePushout.ι β i (x : Y i),
        (mem_widePushoutPointNeighborhood b U _).2
          (Or.inr ⟨i, (x : Y i), x.property, rfl⟩)⟩ := by
  apply Subtype.ext
  exact (widePushoutPointNeighborhoodHomeomorph_coe b U hb hU
    (WidePushout.ι α i x)).trans
      (widePushoutDesc_point_ι (X := XU) (Y := Y) aU b ιU (fun _ ↦ rfl) i x)

/-- Ambient-set preimages through the homeomorphism are canonical-descent
preimages, with the neighborhood carrying the ordinary subtype topology. -/
theorem preimage_widePushoutPointNeighborhoodHomeomorph (S : Set WY) :
    widePushoutPointNeighborhoodHomeomorph b U hb hU ⁻¹' (Subtype.val ⁻¹' S) =
      F ⁻¹' S := by
  ext q
  change ((widePushoutPointNeighborhoodHomeomorph b U hb hU q :
    widePushoutPointNeighborhood b U) : WY) ∈ S ↔ F q ∈ S
  rw [widePushoutPointNeighborhoodHomeomorph_coe b U hb hU q]

end TopCat
