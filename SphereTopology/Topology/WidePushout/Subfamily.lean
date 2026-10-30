/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.Compactness

/-!
# Subfamilies of point-attached wide pushouts

An arbitrary subfamily of chosen-point spaces includes into their categorical
wide pushout. The inclusion has a continuous retraction which collapses omitted
factors to the common point. Its range is precisely the common point together
with the ranges of the retained factors. No separation or finiteness hypothesis
is needed for these maps or their characteristic factorization property.

If the factors are T₁, a map from a compact space factors through a finite
subfamily, using the finite support of its image. The domain universe is
independent of the diagram universe. These are retractions, not deformation
retractions, and the empty subfamily still contains the head.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  p. 19, supplies the point-wedge setting, not these subfamily or arbitrary-T₁
  compact-domain results.
* Mathlib's wide pushouts and topological colimits, together with
  `TopCat.widePushoutDesc`, supply the constructions. The existing support and
  compactness interface supplies the finite-subfamily consequence.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u v z

namespace TopCat

variable {I : Type v} {X : I → TopCat.{max u v}} (a : ∀ i, X i) (S : Set I)

local notation "P" => TopCat.of PUnit
local notation "f" => (fun i ↦ (TopCat.const (a i) : P ⟶ X i))
local notation "W" => (widePushout P X f : TopCat)
local notation "fS" => (fun i : S ↦
  (TopCat.const (a (Subtype.val i)) : P ⟶ X (Subtype.val i)))
local notation "WS" => (widePushout P (fun i : S ↦ X (Subtype.val i)) fS : TopCat)

/-- Include the wide pushout of a subfamily into the full point-wide-pushout. -/
def widePushoutPointSubfamilyInclusion : C(WS, W) :=
  widePushoutDesc fS (WidePushout.head f).hom
    (fun i ↦ (WidePushout.ι f i.1).hom) (by
      intro i b
      exact congrArg (fun k : P ⟶ W ↦ k b) (WidePushout.arrow_ι f i.1))

/-- Retraction to a subfamily, collapsing every omitted factor to the head. -/
def widePushoutPointSubfamilyRetraction : C(W, WS) := by
  classical
  exact widePushoutDesc f (WidePushout.head fS).hom
    (fun i ↦ if hi : i ∈ S then (WidePushout.ι fS ⟨i, hi⟩).hom
      else ContinuousMap.const (X i) (WidePushout.head fS PUnit.unit)) (by
      intro i b
      by_cases hi : i ∈ S
      · simp only [dite_eq_left hi]
        exact congrArg (fun k : P ⟶ WS ↦ k b) (WidePushout.arrow_ι fS ⟨i, hi⟩)
      · simp only [dite_eq_right hi, ContinuousMap.const_apply])

/-- The subfamily inclusion preserves the head. -/
@[simp] theorem widePushoutPointSubfamilyInclusion_head (b : P) :
    widePushoutPointSubfamilyInclusion a S (WidePushout.head fS b) =
      WidePushout.head f b := by
  unfold widePushoutPointSubfamilyInclusion
  exact widePushoutDesc_head fS _ _ _ b

/-- The subfamily inclusion preserves every retained factor. -/
@[simp] theorem widePushoutPointSubfamilyInclusion_ι (i : S) (x : X i.1) :
    widePushoutPointSubfamilyInclusion a S (WidePushout.ι fS i x) =
      WidePushout.ι f i.1 x := by
  simp [widePushoutPointSubfamilyInclusion]

/-- The subfamily retraction preserves the head. -/
@[simp] theorem widePushoutPointSubfamilyRetraction_head (b : P) :
    widePushoutPointSubfamilyRetraction a S (WidePushout.head f b) =
      WidePushout.head fS b := by
  unfold widePushoutPointSubfamilyRetraction
  exact widePushoutDesc_head f _ _ _ b

/-- A retained factor is unchanged by the subfamily retraction. -/
@[simp] theorem widePushoutPointSubfamilyRetraction_ι_of_mem
    (i : I) (hi : i ∈ S) (x : X i) :
    widePushoutPointSubfamilyRetraction a S (WidePushout.ι f i x) =
      WidePushout.ι fS ⟨i, hi⟩ x := by
  classical
  simp [widePushoutPointSubfamilyRetraction, hi]

/-- An omitted factor is sent to the subfamily's common point. -/
theorem widePushoutPointSubfamilyRetraction_ι_of_not_mem
    (i : I) (hi : i ∉ S) (x : X i) :
    widePushoutPointSubfamilyRetraction a S (WidePushout.ι f i x) =
      WidePushout.head fS PUnit.unit := by
  classical
  simp [widePushoutPointSubfamilyRetraction, hi]

/-- The head and retained-factor equations characterize the inclusion. -/
theorem widePushoutPointSubfamilyInclusion_unique (k : C(WS, W))
    (hB : ∀ b, k (WidePushout.head fS b) = WidePushout.head f b)
    (hX : ∀ i x, k (WidePushout.ι fS i x) = WidePushout.ι f i.1 x) :
    k = widePushoutPointSubfamilyInclusion a S := by
  apply DFunLike.coe_injective
  apply widePushout_funext fS
  · intro b
    rw [widePushoutPointSubfamilyInclusion_head a S]
    exact hB b
  · intro i x
    simpa only [widePushoutPointSubfamilyInclusion_ι] using hX i x

/-- The head and all-factor equations characterize the retraction. -/
theorem widePushoutPointSubfamilyRetraction_unique (k : C(W, WS))
    (hB : ∀ b, k (WidePushout.head f b) = WidePushout.head fS b)
    (hS : ∀ i (hi : i ∈ S) x, k (WidePushout.ι f i x) = WidePushout.ι fS ⟨i, hi⟩ x)
    (hN : ∀ i, i ∉ S → ∀ x, k (WidePushout.ι f i x) =
      WidePushout.head fS PUnit.unit) :
    k = widePushoutPointSubfamilyRetraction a S := by
  apply DFunLike.coe_injective
  apply widePushout_funext f
  · intro b
    rw [widePushoutPointSubfamilyRetraction_head a S]
    exact hB b
  · intro i x
    by_cases hi : i ∈ S
    · simpa only [widePushoutPointSubfamilyRetraction_ι_of_mem a S i hi] using hS i hi x
    · simpa only [widePushoutPointSubfamilyRetraction_ι_of_not_mem a S i hi] using hN i hi x

/-- The subfamily retraction is a left inverse to the inclusion. -/
@[simp] theorem widePushoutPointSubfamilyRetraction_comp_inclusion :
    (widePushoutPointSubfamilyRetraction a S).comp
      (widePushoutPointSubfamilyInclusion a S) = ContinuousMap.id WS := by
  apply DFunLike.coe_injective
  apply widePushout_funext fS
  · intro b
    simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply,
      widePushoutPointSubfamilyInclusion_head a S,
      widePushoutPointSubfamilyRetraction_head a S]
  · intro i x
    simp [i.property]

/-- The inclusion has the prescribed continuous left inverse on points. -/
theorem leftInverse_widePushoutPointSubfamilyRetraction :
    Function.LeftInverse (widePushoutPointSubfamilyRetraction a S)
      (widePushoutPointSubfamilyInclusion a S) := by
  intro x
  exact congrArg (fun k : C(WS, WS) ↦ k x)
    (widePushoutPointSubfamilyRetraction_comp_inclusion a S)

/-- Any subfamily embeds in the full point-wide-pushout. -/
theorem isEmbedding_widePushoutPointSubfamilyInclusion :
    Topology.IsEmbedding (widePushoutPointSubfamilyInclusion a S) :=
  (leftInverse_widePushoutPointSubfamilyRetraction a S).isEmbedding
    (widePushoutPointSubfamilyRetraction a S).continuous
    (widePushoutPointSubfamilyInclusion a S).continuous

/-- The exact range includes the common point, even for an empty subfamily. -/
theorem range_widePushoutPointSubfamilyInclusion :
    range (widePushoutPointSubfamilyInclusion a S) =
      {WidePushout.head f PUnit.unit} ∪ ⋃ i ∈ S, range (WidePushout.ι f i) := by
  ext w
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨_ | i, x, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan P (fun i : S ↦ X i.1) fS) y
    · left
      change widePushoutPointSubfamilyInclusion a S (WidePushout.head fS x) =
        WidePushout.head f PUnit.unit
      rw [widePushoutPointSubfamilyInclusion_head]
      exact congrArg (WidePushout.head f) (Subsingleton.elim _ _)
    · right
      refine mem_iUnion.2 ⟨i.1, mem_iUnion.2 ⟨i.property, ?_⟩⟩
      exact ⟨x, by simp⟩
  · rintro (hB | hX)
    · obtain rfl := mem_singleton_iff.1 hB
      exact ⟨WidePushout.head fS PUnit.unit,
        widePushoutPointSubfamilyInclusion_head a S PUnit.unit⟩
    · rcases mem_iUnion.1 hX with ⟨i, hfactor⟩
      rcases mem_iUnion.1 hfactor with ⟨hmem, hrange⟩
      rcases hrange with ⟨x, rfl⟩
      exact ⟨WidePushout.ι fS ⟨i, hmem⟩ x,
        widePushoutPointSubfamilyInclusion_ι a S ⟨i, hmem⟩ x⟩

/-- A map is recovered by subfamily retraction and inclusion exactly when its
support lies in that subfamily. No separation or compactness is assumed. -/
theorem widePushoutPointSubfamily_factorization_iff
    {A : Type z} [TopologicalSpace A] (q : C(A, W)) :
    (widePushoutPointSubfamilyInclusion a S).comp
      ((widePushoutPointSubfamilyRetraction a S).comp q) = q ↔
        widePushoutPointSupport a (range q) ⊆ S := by
  rw [widePushoutPointSupport_subset_iff,
    ← range_widePushoutPointSubfamilyInclusion a S]
  constructor
  · intro h w hw
    obtain ⟨x, rfl⟩ := hw
    exact ⟨widePushoutPointSubfamilyRetraction a S (q x),
      congrArg (fun k : C(A, W) ↦ k x) h⟩
  · intro h
    apply ContinuousMap.ext
    intro x
    obtain ⟨y, hy⟩ := h (mem_range_self x)
    change widePushoutPointSubfamilyInclusion a S
      (widePushoutPointSubfamilyRetraction a S (q x)) = q x
    rw [← hy, leftInverse_widePushoutPointSubfamilyRetraction a S y]

/-- A continuous factor through the inclusion is necessarily the retraction
composite. This gives uniqueness without compactness or separation hypotheses. -/
theorem widePushoutPointSubfamily_factor_unique
    {A : Type z} [TopologicalSpace A] (q : C(A, W)) (k : C(A, WS))
    (hk : (widePushoutPointSubfamilyInclusion a S).comp k = q) :
    k = (widePushoutPointSubfamilyRetraction a S).comp q := by
  apply ContinuousMap.ext
  intro x
  have h : widePushoutPointSubfamilyRetraction a S
      (widePushoutPointSubfamilyInclusion a S (k x)) =
        widePushoutPointSubfamilyRetraction a S (q x) :=
    congrArg (fun m : C(A, W) ↦ widePushoutPointSubfamilyRetraction a S (m x)) hk
  exact (leftInverse_widePushoutPointSubfamilyRetraction a S (k x)).symm.trans h

/-- For nested subfamilies, retracting an included point to the larger stage
and then including it again leaves the original inclusion unchanged. This
triangle uses the existing maps as transition maps, without another diagram. -/
theorem widePushoutPointSubfamilyInclusion_comp_retraction_inclusion
    {T : Set I} (hST : S ⊆ T) :
    (widePushoutPointSubfamilyInclusion a T).comp
      ((widePushoutPointSubfamilyRetraction a T).comp
        (widePushoutPointSubfamilyInclusion a S)) =
      widePushoutPointSubfamilyInclusion a S := by
  apply DFunLike.coe_injective
  apply widePushout_funext fS
  · intro b
    simp only [ContinuousMap.comp_apply,
      widePushoutPointSubfamilyInclusion_head a S,
      widePushoutPointSubfamilyRetraction_head a T,
      widePushoutPointSubfamilyInclusion_head a T]
  · intro i x
    simp only [ContinuousMap.comp_apply,
      widePushoutPointSubfamilyInclusion_ι,
      widePushoutPointSubfamilyRetraction_ι_of_mem a T i.1 (hST i.property)]

/-- Every compact-domain map into a point-wide-pushout of T₁ factors factors
through a finite subfamily. Factors and the pushout need not be compact. -/
theorem exists_finite_widePushout_point_subfamily_factor
    [∀ i, T1Space (X i)] {A : Type z} [TopologicalSpace A] [CompactSpace A]
    (q : C(A, W)) :
    ∃ S : Set I, S.Finite ∧ ∃ qS : C(A,
      (widePushout P (fun i : S ↦ X i.1)
        (fun i ↦ TopCat.const (a i.1)) : TopCat)),
      (widePushoutPointSubfamilyInclusion a S).comp qS = q := by
  let S := widePushoutPointSupport a (range q)
  refine ⟨S, finite_widePushoutPointSupport a (isCompact_range q.continuous),
    (widePushoutPointSubfamilyRetraction a S).comp q, ?_⟩
  exact (widePushoutPointSubfamily_factorization_iff a S q).2 Subset.rfl

/-- Retraction to a retained factor commutes with subfamily retraction.
In particular, a singleton subfamily recovers the selected-factor retraction. -/
theorem widePushoutPointSubfamilyRetraction_factor (i : S) :
    (widePushoutPointRetraction (fun j : S ↦ X j.1) (fun j ↦ a j.1) i).hom.comp
      (widePushoutPointSubfamilyRetraction a S) =
        (widePushoutPointRetraction X a i.1).hom := by
  rcases i with ⟨i, hi⟩
  apply DFunLike.coe_injective
  apply widePushout_funext f
  · intro b
    simp only [ContinuousMap.comp_apply,
      widePushoutPointSubfamilyRetraction_head a S,
      widePushoutPointRetraction_head_apply (fun j : S ↦ X j.1)
        (fun j ↦ a j.1) ⟨i, hi⟩ b,
      widePushoutPointRetraction_head_apply X a i b]
  · intro j x
    by_cases hj : j ∈ S
    · by_cases hji : j = i
      · subst j
        simp [hi]
      · have hsub : (⟨j, hj⟩ : S) ≠ ⟨i, hi⟩ :=
          fun h ↦ hji (congrArg Subtype.val h)
        simp only [ContinuousMap.comp_apply,
          widePushoutPointSubfamilyRetraction_ι_of_mem a S j hj,
          widePushoutPointRetraction_ι_of_ne_apply _ _ _ _ hsub,
          widePushoutPointRetraction_ι_of_ne_apply _ _ _ _ hji]
    · have hji : j ≠ i := by
        rintro rfl
        exact hj hi
      simp only [ContinuousMap.comp_apply,
        widePushoutPointSubfamilyRetraction_ι_of_not_mem a S j hj,
        widePushoutPointRetraction_head_apply (fun k : S ↦ X k.1)
          (fun k ↦ a k.1) ⟨i, hi⟩ PUnit.unit,
        widePushoutPointRetraction_ι_of_ne_apply X a i j hji x]

end TopCat
