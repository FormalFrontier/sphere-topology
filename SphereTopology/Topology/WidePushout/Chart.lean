/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.Compactness
public import Mathlib.Topology.Connected.PathConnected

/-!
# Charts in point-attached wide pushouts

For an arbitrary subset `C` of a point-attached categorical wide pushout,
`TopCat.widePushoutPointChart a C i` adjoins the whole `i`th factor to `C`.
If `C` contains the common point, distinct charts intersect exactly in `C`,
and the family consisting of `C` and all the charts covers the pushout, including
when the index type is empty.

For `C` containing the common point, path connectedness of its factor inverse
images implies path connectedness of `C` itself. A chart is path connected if,
in addition, its own factor is path connected; no condition on the other whole
factors is needed. If `C` is open
and contains the common point, each chart is open. No separation assumption
is used, and the index and space universes are independent.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  motivates the point-attached setting. The arbitrary-subset formulation here
  is not a literal translation of a statement in that text.
* Mathlib supplies the path-connected image and union API and the quotient,
  disjoint-sum and dependent-sum openness criteria.
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

/-- The chart obtained by adjoining one whole factor to a subset of the pushout. -/
def widePushoutPointChart (C : Set W) (i : I) : Set W :=
  range (WidePushout.ι f i) ∪ C

/-- Membership is either a representative in the chosen factor or membership in `C`. -/
theorem mem_widePushoutPointChart (C : Set W) (i : I) (x : W) :
    x ∈ widePushoutPointChart a C i ↔
      (∃ y : X i, WidePushout.ι f i y = x) ∨ x ∈ C := Iff.rfl

/-- Every point of the chosen factor belongs to its chart. -/
@[simp] theorem ι_mem_widePushoutPointChart (C : Set W) (i : I) (x : X i) :
    WidePushout.ι f i x ∈ widePushoutPointChart a C i :=
  Or.inl (mem_range_self x)

/-- The common subset lies in every chart. -/
theorem subset_widePushoutPointChart (C : Set W) (i : I) :
    C ⊆ widePushoutPointChart a C i := subset_union_right

/-- Every existing chart contains the common point, whether or not `C` does. -/
@[simp] theorem head_mem_widePushoutPointChart (C : Set W) (i : I) :
    WidePushout.head f PUnit.unit ∈ widePushoutPointChart a C i := by
  rw [← widePushout_point_ι_point a i]
  exact ι_mem_widePushoutPointChart a C i (a i)

/-- The whole chosen factor is the inverse image of its chart. -/
@[simp] theorem preimage_ι_widePushoutPointChart (C : Set W) (i : I) :
    WidePushout.ι f i ⁻¹' widePushoutPointChart a C i = univ :=
  eq_univ_of_forall (ι_mem_widePushoutPointChart a C i)

/-- On a different factor a chart has exactly the inverse image of `C`,
provided `C` contains the common point. -/
theorem preimage_ι_widePushoutPointChart_of_ne {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) {i k : I} (hki : k ≠ i) :
    WidePushout.ι f k ⁻¹' widePushoutPointChart a C i = WidePushout.ι f k ⁻¹' C := by
  classical
  ext x
  change (WidePushout.ι f k x ∈ range (WidePushout.ι f i) ∨
    WidePushout.ι f k x ∈ C) ↔ WidePushout.ι f k x ∈ C
  constructor
  · rintro (⟨y, hy⟩ | hxC)
    · by_cases hx : x = a k
      · subst x
        rw [widePushout_point_ι_point a k]
        exact hC
      · have hki' : k = i := congrArg Sigma.fst
          ((widePushout_point_ι_eq_ι_iff_of_ne a hx).1 hy.symm)
        exact (hki hki').elim
    · exact hxC
  · exact Or.inr

/-- Distinct charts intersect exactly in the common subset. -/
theorem widePushoutPointChart_inter_of_ne {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) {i k : I} (hik : i ≠ k) :
    widePushoutPointChart a C i ∩ widePushoutPointChart a C k = C := by
  apply Subset.antisymm
  · rintro z ⟨hz, hzk⟩
    rcases hz with ⟨x, rfl⟩ | hzC
    · have hx : x ∈ WidePushout.ι f i ⁻¹' widePushoutPointChart a C k := hzk
      rw [preimage_ι_widePushoutPointChart_of_ne a hC hik] at hx
      exact hx
    · exact hzC
  · intro z hz
    exact ⟨subset_widePushoutPointChart a C i hz, subset_widePushoutPointChart a C k hz⟩

/-- Intersecting a chart with the common subset recovers that subset. -/
@[simp] theorem widePushoutPointChart_inter (C : Set W) (i : I) :
    widePushoutPointChart a C i ∩ C = C :=
  inter_eq_right.mpr (subset_widePushoutPointChart a C i)

/-- Intersecting the common subset with a chart recovers that subset. -/
@[simp] theorem inter_widePushoutPointChart (C : Set W) (i : I) :
    C ∩ widePushoutPointChart a C i = C :=
  inter_eq_left.mpr (subset_widePushoutPointChart a C i)

/-- The common subset and the charts cover the pushout, even for an empty index type. -/
theorem iUnion_widePushoutPointChart {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) :
    (⋃ o : Option I, o.elim C (widePushoutPointChart a C)) = univ := by
  apply eq_univ_of_forall
  intro z
  rcases subset_head_union_widePushoutPointSupport a (univ : Set W) (mem_univ z) with
    hz | hz
  · exact mem_iUnion.mpr ⟨none, (mem_singleton_iff.mp hz).symm ▸ hC⟩
  · rcases mem_iUnion.mp hz with ⟨i, hi⟩
    rcases mem_iUnion.mp hi with ⟨_, x, rfl⟩
    exact mem_iUnion.mpr ⟨some i, ι_mem_widePushoutPointChart a C i x⟩

/-- A subset containing the common point is path connected if all its factor
inverse images are path connected. No condition on the whole factors is required. -/
theorem isPathConnected_of_widePushout_point_preimage {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C)
    (h : ∀ i, IsPathConnected (WidePushout.ι f i ⁻¹' C)) : IsPathConnected C := by
  refine ⟨WidePushout.head f PUnit.unit, hC, ?_⟩
  intro y hy
  rcases subset_head_union_widePushoutPointSupport a C hy with hyhead | hyfactor
  · have he : y = WidePushout.head f PUnit.unit := mem_singleton_iff.mp hyhead
    subst y
    exact JoinedIn.refl hC
  · rcases mem_iUnion.mp hyfactor with ⟨i, hi⟩
    rcases mem_iUnion.mp hi with ⟨_, x, hx⟩
    have himage := (h i).image (WidePushout.ι f i).hom.continuous
    have hhead : WidePushout.head f PUnit.unit ∈
        WidePushout.ι f i '' (WidePushout.ι f i ⁻¹' C) :=
      ⟨a i, by
        change WidePushout.ι f i (a i) ∈ C
        rw [widePushout_point_ι_point a i]
        exact hC, widePushout_point_ι_point a i⟩
    have hyimage : y ∈ WidePushout.ι f i '' (WidePushout.ι f i ⁻¹' C) :=
      ⟨x, by simpa only [mem_preimage, hx] using hy, hx⟩
    exact (himage.joinedIn _ hhead _ hyimage).mono (image_preimage_subset _ _)

/-- A chart is path connected when the common subset and its own whole factor
are path connected and meet at the common point. Other factors are unrestricted. -/
theorem isPathConnected_widePushoutPointChart {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) (h : IsPathConnected C) (i : I)
    (hi : IsPathConnected (univ : Set (X i))) :
    IsPathConnected (widePushoutPointChart a C i) := by
  have hrange : IsPathConnected (range (WidePushout.ι f i)) := by
    simpa only [image_univ] using hi.image (WidePushout.ι f i).hom.continuous
  exact hrange.union h ⟨WidePushout.head f PUnit.unit,
    ⟨a i, widePushout_point_ι_point a i⟩, hC⟩

/-- Factorwise path connectedness of the common subset, together with path
connectedness of one whole factor, gives path connectedness of that chart. -/
theorem isPathConnected_widePushoutPointChart_of_preimage {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C)
    (h : ∀ k, IsPathConnected (WidePushout.ι f k ⁻¹' C)) (i : I)
    (hi : IsPathConnected (univ : Set (X i))) :
    IsPathConnected (widePushoutPointChart a C i) :=
  isPathConnected_widePushoutPointChart a hC
    (isPathConnected_of_widePushout_point_preimage a hC h) i hi

/-- A chart is open if the common subset is open and contains the common point.
This uses the quotient comparison for the existing categorical wide pushout. -/
theorem isOpen_widePushoutPointChart {C : Set W}
    (hC : WidePushout.head f PUnit.unit ∈ C) (h : IsOpen C) (i : I) :
    IsOpen (widePushoutPointChart a C i) := by
  classical
  rw [← (widePushoutHomeomorph f).isOpen_preimage]
  apply isQuotientMap_quot_mk.isOpen_preimage.mp
  apply isOpen_sum_iff.mpr
  change IsOpen ((WidePushout.head f) ⁻¹' widePushoutPointChart a C i) ∧
    IsOpen ((fun p : Σ k, X k ↦ WidePushout.ι f p.1 p.2) ⁻¹'
      widePushoutPointChart a C i)
  constructor
  · have hh : (WidePushout.head f) ⁻¹' widePushoutPointChart a C i = univ := by
      apply eq_univ_of_forall
      intro b
      cases b
      exact head_mem_widePushoutPointChart a C i
    rw [hh]
    exact isOpen_univ
  · rw [isOpen_sigma_iff]
    intro k
    change IsOpen (WidePushout.ι f k ⁻¹' widePushoutPointChart a C i)
    by_cases hki : k = i
    · subst k
      rw [preimage_ι_widePushoutPointChart]
      exact isOpen_univ
    · rw [preimage_ι_widePushoutPointChart_of_ne a hC hki]
      exact h.preimage (WidePushout.ι f k).hom.continuous

end TopCat
