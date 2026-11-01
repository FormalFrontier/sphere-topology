/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.PointMap
public import SphereTopology.Topology.WidePushout.Compactness

/-!
# Closed maps between point-wide-pushouts

A given function between categorical wide pushouts of chosen-point spaces is
closed, under finite label fibers, closed component maps, point reflection,
and the head and factor equations, exactly when the chosen singleton in every
omitted target factor is closed. The component maps and the given function
are plain functions, without continuity assumptions. Source and target label
types and ambient universes are independent.

In a retained target factor, the preimage of an image is the union of the
component images over its label fiber. This union already contains the chosen
point whenever the source set contains the head; no closed-singleton assumption
is needed in retained factors. An omitted factor sees only the chosen point,
and only when the source set contains the head. The one-point heads remain
present for empty label types.

## References

The constructions, descent and collision API are supplied by
`SphereTopology.Topology.WidePushout.PointMap` and
`SphereTopology.Topology.WidePushout.Compactness`, using Mathlib's categorical
wide pushouts and topological colimits. This generalizes the same-index
closed-map argument in `SphereTopology.Topology.WidePushout.OpenEmbedding`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

universe u v u' w

namespace TopCat

section PointMap

variable {I : Type v} {J : Type w}
  {X : I → TopCat.{max u v}} {Y : J → TopCat.{max u' w}}
  (a : ∀ i, X i) (b : ∀ j, Y j) (σ : I → J)
  (g : ∀ i, X i → Y (σ i))

local notation "PX" => TopCat.of PUnit
local notation "PY" => TopCat.of PUnit
local notation "α" => (fun i ↦ (TopCat.const (a i) : PX ⟶ X i))
local notation "β" => (fun j ↦ (TopCat.const (b j) : PY ⟶ Y j))
local notation "WX" => (widePushout PX X α : TopCat)
local notation "WY" => (widePushout PY Y β : TopCat)
local notation "hx" => WidePushout.head α PUnit.unit
local notation "hy" => WidePushout.head β PUnit.unit

variable
  (G :
    ↑(widePushout (TopCat.of PUnit.{max u v + 1}) X
      (fun i ↦ TopCat.const (a i)) : TopCat.{max u v}) →
    ↑(widePushout (TopCat.of PUnit.{max u' w + 1}) Y
      (fun j ↦ TopCat.const (b j)) : TopCat.{max u' w}))
  (hhead : G (WidePushout.head
    (fun i ↦ (TopCat.const (a i) :
      TopCat.of PUnit.{max u v + 1} ⟶ X i)) PUnit.unit) =
    WidePushout.head
      (fun j ↦ (TopCat.const (b j) :
        TopCat.of PUnit.{max u' w + 1} ⟶ Y j)) PUnit.unit)
  (hlegs : ∀ i x,
    G (WidePushout.ι
      (fun k ↦ (TopCat.const (a k) :
        TopCat.of PUnit.{max u v + 1} ⟶ X k)) i x) =
      WidePushout.ι
        (fun j ↦ (TopCat.const (b j) :
          TopCat.of PUnit.{max u' w + 1} ⟶ Y j)) (σ i) (g i x))

include hhead hlegs

/-- The head and factor equations force preservation of every chosen point. -/
theorem widePushout_point_map_point (i : I) : g i (a i) = b (σ i) := by
  apply widePushout_point_ι_injective b (σ i)
  calc
    WidePushout.ι β (σ i) (g i (a i)) = G (WidePushout.ι α i (a i)) :=
      (hlegs i (a i)).symm
    _ = hy := by rw [widePushout_point_ι_point a i, hhead]
    _ = WidePushout.ι β (σ i) (b (σ i)) :=
      (widePushout_point_ι_point b (σ i)).symm

/-- Point reflection in the factors makes the given function reflect the head. -/
theorem widePushout_point_map_eq_head_iff
    (hreflection : ∀ i x, g i x = b (σ i) → x = a i) (q : WX) :
    G q = hy ↔ q = hx := by
  constructor
  · intro he
    obtain ⟨_ | i, t, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan PX X α) q
    · cases t
      rfl
    · change G (WidePushout.ι α i t) = hy at he
      have ht : t = a i := hreflection i t
        ((widePushout_point_ι_eq_head_iff b (σ i) (g i t)).1
          ((hlegs i t).symm.trans he))
      change WidePushout.ι α i t = hx
      rw [ht, widePushout_point_ι_point a i]
  · rintro rfl
    exact hhead

/-- An image contains the target head exactly when its source set contains the
source head, for a point-reflecting function with the head and factor equations. -/
theorem mem_image_widePushout_point_head_of_legs
    (hreflection : ∀ i x, g i x = b (σ i) → x = a i) (S : Set WX) :
    hy ∈ G '' S ↔ hx ∈ S := by
  constructor
  · rintro ⟨q, hq, he⟩
    exact (widePushout_point_map_eq_head_iff a b σ g G hhead hlegs
      hreflection q).1 he ▸ hq
  · intro hh
    exact ⟨hx, hh, hhead⟩

/-- A retained factor sees the component images over its label fiber. The
chosen point needs no separate singleton term. Equality of labels transports
component values into the target factor. -/
theorem preimage_image_widePushout_point_of_mem_range
    (hreflection : ∀ i x, g i x = b (σ i) → x = a i)
    (S : Set WX) (j : J) (hj : j ∈ range σ) :
    WidePushout.ι β j ⁻¹' (G '' S) =
      ⋃ i : σ ⁻¹' ({j} : Set J),
        (fun x : X i.1 ↦ (show σ i.1 = j from i.2) ▸ g i.1 x) ''
          (WidePushout.ι α i.1 ⁻¹' S) := by
  ext y
  constructor
  · intro hyS
    by_cases hyb : y = b j
    · have hh : hx ∈ S :=
        (mem_image_widePushout_point_head_of_legs a b σ g G hhead hlegs
          hreflection S).1 (by
            simpa only [mem_preimage, hyb, widePushout_point_ι_point b j] using hyS)
      obtain ⟨i, rfl⟩ := hj
      refine mem_iUnion.2 ⟨⟨i, rfl⟩, a i, ?_, ?_⟩
      · change WidePushout.ι α i (a i) ∈ S
        rw [widePushout_point_ι_point a i]
        exact hh
      · change g i (a i) = y
        exact (widePushout_point_map_point a b σ g G hhead hlegs i).trans hyb.symm
    · rcases hyS with ⟨q, hq, he⟩
      obtain ⟨_ | i, t, rfl⟩ :=
        Concrete.colimit_exists_rep (WidePushoutShape.wideSpan PX X α) q
      · cases t
        change G hx = WidePushout.ι β j y at he
        exact (hyb ((widePushout_point_ι_eq_head_iff b j y).1
          (he.symm.trans hhead))).elim
      · change WidePushout.ι α i t ∈ S at hq
        change G (WidePushout.ι α i t) = WidePushout.ι β j y at he
        have he' : WidePushout.ι β j y = WidePushout.ι β (σ i) (g i t) :=
          he.symm.trans (hlegs i t)
        have hji : j = σ i := congrArg Sigma.fst
          ((widePushout_point_ι_eq_ι_iff_of_ne b hyb).1 he')
        refine mem_iUnion.2 ⟨⟨i, hji.symm⟩, t, hq, ?_⟩
        subst j
        exact widePushout_point_ι_injective b (σ i) he'.symm
  · intro hyS
    rcases mem_iUnion.1 hyS with ⟨⟨i, hi⟩, x, hxS, hxy⟩
    change σ i = j at hi
    subst j
    change g i x = y at hxy
    exact ⟨WidePushout.ι α i x, hxS,
      (hlegs i x).trans (congrArg (WidePushout.ι β (σ i)) hxy)⟩

/-- In an omitted target factor the full range consists exactly of the chosen
point. This needs neither point reflection nor a finiteness assumption. -/
theorem preimage_range_widePushout_point_of_not_mem_range
    (j : J) (hj : j ∉ range σ) :
    WidePushout.ι β j ⁻¹' range G = {b j} := by
  ext y
  change (∃ q, G q = WidePushout.ι β j y) ↔ y = b j
  constructor
  · rintro ⟨q, he⟩
    by_contra hyb
    obtain ⟨_ | i, t, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan PX X α) q
    · cases t
      change G hx = WidePushout.ι β j y at he
      exact hyb ((widePushout_point_ι_eq_head_iff b j y).1
        (he.symm.trans hhead))
    · change G (WidePushout.ι α i t) = WidePushout.ι β j y at he
      have he' : WidePushout.ι β j y = WidePushout.ι β (σ i) (g i t) :=
        he.symm.trans (hlegs i t)
      have hji : j = σ i := congrArg Sigma.fst
        ((widePushout_point_ι_eq_ι_iff_of_ne b hyb).1 he')
      exact hj ⟨i, hji.symm⟩
  · rintro rfl
    exact ⟨hx, hhead.trans (widePushout_point_ι_point b j).symm⟩

open scoped Classical in
/-- An omitted factor sees the chosen singleton if the source head is in the
set, and sees the empty set otherwise. -/
theorem preimage_image_widePushout_point_of_not_mem_range
    (hreflection : ∀ i x, g i x = b (σ i) → x = a i)
    (S : Set WX) (j : J) (hj : j ∉ range σ) :
    WidePushout.ι β j ⁻¹' (G '' S) = if hx ∈ S then {b j} else ∅ := by
  classical
  have hbase {y : Y j} (hyS : y ∈ WidePushout.ι β j ⁻¹' (G '' S)) : y = b j := by
    have hr : y ∈ WidePushout.ι β j ⁻¹' range G := by
      rcases hyS with ⟨q, _, he⟩
      exact ⟨q, he⟩
    rw [preimage_range_widePushout_point_of_not_mem_range a b σ g G hhead hlegs
      j hj] at hr
    exact hr
  ext y
  by_cases hh : hx ∈ S
  · rw [ite_eq_left hh]
    constructor
    · exact hbase
    · intro hyb
      obtain rfl := mem_singleton_iff.1 hyb
      exact ⟨hx, hh, hhead.trans (widePushout_point_ι_point b j).symm⟩
  · rw [ite_eq_right hh]
    constructor
    · intro hyS
      have hyb := hbase hyS
      have hhy : hy ∈ G '' S := by
        simpa only [mem_preimage, hyb, widePushout_point_ι_point b j] using hyS
      exact (hh ((mem_image_widePushout_point_head_of_legs a b σ g G hhead hlegs
        hreflection S).1 hhy)).elim
    · exact fun hyS ↦ hyS.elim

end PointMap

/-- Finite label fibers, closed component maps, point reflection, and the head
and factor equations make a given function between point-wide-pushouts closed
exactly when every omitted target factor has a closed chosen singleton. No
continuity or separation assumption is imposed on retained factors. -/
theorem isClosedMap_iff_of_widePushout_point_legs
    {I : Type v} {J : Type w}
    (X : I → TopCat.{max u v}) (Y : J → TopCat.{max u' w})
    (a : ∀ i, X i) (b : ∀ j, Y j) (σ : I → J)
    (g : ∀ i, X i → Y (σ i))
    (G :
      ↑(widePushout (TopCat.of PUnit.{max u v + 1}) X
        (fun i ↦ TopCat.const (a i)) : TopCat.{max u v}) →
      ↑(widePushout (TopCat.of PUnit.{max u' w + 1}) Y
        (fun j ↦ TopCat.const (b j)) : TopCat.{max u' w}))
    (hfinite : ∀ j : J, Set.Finite (σ ⁻¹' ({j} : Set J)))
    (hclosed : ∀ i, IsClosedMap (g i))
    (hreflection : ∀ i x, g i x = b (σ i) → x = a i)
    (hhead : G (WidePushout.head
      (fun i ↦ (TopCat.const (a i) :
        TopCat.of PUnit.{max u v + 1} ⟶ X i)) PUnit.unit) =
      WidePushout.head
        (fun j ↦ (TopCat.const (b j) :
          TopCat.of PUnit.{max u' w + 1} ⟶ Y j)) PUnit.unit)
    (hlegs : ∀ i x,
      G (WidePushout.ι
        (fun k ↦ (TopCat.const (a k) :
          TopCat.of PUnit.{max u v + 1} ⟶ X k)) i x) =
        WidePushout.ι
          (fun j ↦ (TopCat.const (b j) :
            TopCat.of PUnit.{max u' w + 1} ⟶ Y j)) (σ i) (g i x)) :
    IsClosedMap G ↔ ∀ j, j ∉ Set.range σ → IsClosed ({b j} : Set (Y j)) := by
  classical
  let α : ∀ i, TopCat.of PUnit.{max u v + 1} ⟶ X i := fun i ↦ TopCat.const (a i)
  let β : ∀ j, TopCat.of PUnit.{max u' w + 1} ⟶ Y j := fun j ↦ TopCat.const (b j)
  constructor
  · intro hG j hj
    have hr : IsClosed (range G) := by
      simpa only [image_univ] using hG _ isClosed_univ
    have hp := hr.preimage (WidePushout.ι β j).hom.continuous
    rwa [preimage_range_widePushout_point_of_not_mem_range a b σ g G hhead hlegs
      j hj] at hp
  · intro homitted S hS
    apply (isClosed_widePushout_point_iff b (G '' S)).2
    intro j
    by_cases hj : j ∈ range σ
    · rw [preimage_image_widePushout_point_of_mem_range a b σ g G hhead hlegs
        hreflection S j hj]
      let : Finite (σ ⁻¹' ({j} : Set J)) := (hfinite j).to_subtype
      apply isClosed_iUnion_of_finite
      rintro ⟨i, hi⟩
      change σ i = j at hi
      subst j
      exact hclosed i _ (hS.preimage (WidePushout.ι α i).hom.continuous)
    · rw [preimage_image_widePushout_point_of_not_mem_range a b σ g G hhead hlegs
        hreflection S j hj]
      split_ifs
      · exact homitted j hj
      · exact isClosed_empty

end TopCat
