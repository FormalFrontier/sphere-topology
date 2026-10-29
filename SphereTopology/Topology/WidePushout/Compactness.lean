/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact subsets of point-attached wide pushouts

`TopCat.widePushoutPointSupport` records the factors met away from their chosen
points by a subset of the existing categorical wide pushout. Its covering
characterization includes the common head point, even for an empty index type.
If every factor is T₁, every compact subset has finite support. Consequently a
continuous map from any compact domain meets only finitely many factors away
from that point. Neither the factors nor the pushout need be Hausdorff or compact.

The index and space universes are independent. For smaller original factors,
`TopCat.exists_finite_widePushout_point_range_ulift` transports them once with
`TopCat.uliftFunctor` and states the covering using their original domains.

## Implementation notes

Nonpoint fibers are detected by descent of a singleton predicate on Mathlib's
existing quotient, not by an injectivity assumption on the attaching leg.
One nonpoint is chosen per supported index. Every subcollection of these points
is closed by the final topology and the T₁ property of the factors. Their set is
therefore a closed, discrete subset of the given compact set, hence finite.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  p. 19, motivates the point-wedge setting, not the stronger arbitrary-T₁ theorem.
* Mathlib's `CategoryTheory.Limits.Types.Pushout`, by Joël Riou, supplies the
  quotient used by the existing comparison. Mathlib's topological colimits,
  compactness and discrete-subset APIs supply the topological criteria.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u v z

namespace TopCat

variable {I : Type v} {X : I → TopCat.{max u v}} (a : ∀ i, X i)

local notation "P" => TopCat.of PUnit
local notation "f" => (fun i ↦ (TopCat.const (a i) : P ⟶ X i))
local notation "W" => (widePushout P X f : TopCat)

/-- The factors met by a set away from their chosen points. This is support in
an existing point-wide-pushout, not a finiteness or separation condition. -/
def widePushoutPointSupport (K : Set W) : Set I :=
  {i | ∃ x : X i, x ≠ a i ∧ WidePushout.ι f i x ∈ K}

/-- Characteristic membership in the support. -/
@[simp] theorem mem_widePushoutPointSupport (K : Set W) (i : I) :
    i ∈ widePushoutPointSupport a K ↔
      ∃ x : X i, x ≠ a i ∧ WidePushout.ι f i x ∈ K := Iff.rfl

/-- The chosen point of each factor is the common head point. -/
@[simp] theorem widePushout_point_ι_point (i : I) :
    WidePushout.ι f i (a i) = WidePushout.head f PUnit.unit :=
  congrArg (fun k : P ⟶ W ↦ k PUnit.unit) (WidePushout.arrow_ι f i)

private theorem pointQuotient_nonpoint_fiber (i : I) (x : X i) (hx : x ≠ a i)
    (s : P ⊕ Σ j, X j)
    (h : (Quot.mk _ (Sum.inr ⟨i, x⟩) : Types.Pushout
      (↾Prod.snd : (I × P) ⟶ (P : Type (max u v)))
      (↾fun q : I × P ↦ (⟨q.1, a q.1⟩ : Σ j, X j))) = Quot.mk _ s) :
    s = Sum.inr ⟨i, x⟩ := by
  let p : Types.Pushout
      (↾Prod.snd : (I × P) ⟶ (P : Type (max u v)))
      (↾fun q : I × P ↦ (⟨q.1, a q.1⟩ : Σ j, X j)) → Prop :=
    Quot.lift (fun t ↦ t = Sum.inr ⟨i, x⟩) (by
      rintro _ _ ⟨⟨j, b⟩⟩
      apply propext
      constructor
      · intro he
        cases he
      · intro he
        have hs : (⟨j, a j⟩ : Σ k, X k) = ⟨i, x⟩ := Sum.inr.inj he
        have hj : j = i := congrArg Sigma.fst hs
        subst j
        have ha : a i = x := by simpa using hs
        exact (hx ha.symm).elim)
  change p (Quot.mk _ s)
  rw [← h]

/-- A factor point maps to the head exactly when it is the chosen point.
No separation assumption is needed. -/
@[simp] theorem widePushout_point_ι_eq_head_iff (i : I) (x : X i) :
    WidePushout.ι f i x = WidePushout.head f PUnit.unit ↔ x = a i := by
  constructor
  · intro h
    by_contra hx
    have hq := congrArg (widePushoutHomeomorph (B := P) (X := X) f).symm h
    rw [widePushoutHomeomorph_symm_ι (B := P) (X := X) f i x,
      widePushoutHomeomorph_symm_head (B := P) (X := X) f PUnit.unit] at hq
    have he := pointQuotient_nonpoint_fiber a i x hx (Sum.inl PUnit.unit) hq
    cases he
  · rintro rfl
    exact widePushout_point_ι_point a i

/-- A nonpoint factor representative can equal another representative only
when their dependent index-and-point pairs agree. -/
theorem widePushout_point_ι_eq_ι_iff_of_ne {i j : I} {x : X i} {y : X j}
    (hx : x ≠ a i) :
    WidePushout.ι f i x = WidePushout.ι f j y ↔
      (⟨i, x⟩ : Σ k, X k) = ⟨j, y⟩ := by
  constructor
  · intro h
    have hq := congrArg (widePushoutHomeomorph (B := P) (X := X) f).symm h
    rw [widePushoutHomeomorph_symm_ι (B := P) (X := X) f i x,
      widePushoutHomeomorph_symm_ι (B := P) (X := X) f j y] at hq
    exact (Sum.inr.inj (pointQuotient_nonpoint_fiber a i x hx (Sum.inr ⟨j, y⟩) hq)).symm
  · intro h
    cases h
    rfl

private theorem point_ι_injective (i : I) : Function.Injective (WidePushout.ι f i) := by
  intro x y h
  by_cases hx : x = a i
  · subst x
    exact ((widePushout_point_ι_eq_head_iff a i y).1
      (h.symm.trans (widePushout_point_ι_point a i))).symm
  · have hs := (widePushout_point_ι_eq_ι_iff_of_ne a hx).1 h
    simpa using hs

/-- Support is monotone with respect to inclusion of sets. -/
theorem widePushoutPointSupport_mono {K L : Set W} (h : K ⊆ L) :
    widePushoutPointSupport a K ⊆ widePushoutPointSupport a L := by
  rintro i ⟨x, hx, hK⟩
  exact ⟨x, hx, h hK⟩

/-- The empty set meets no factors. -/
@[simp] theorem widePushoutPointSupport_empty :
    widePushoutPointSupport a ∅ = ∅ := by
  ext i
  simp

/-- The common point contributes no support, including for an empty family. -/
@[simp] theorem widePushoutPointSupport_head :
    widePushoutPointSupport a {WidePushout.head f PUnit.unit} = ∅ := by
  ext i
  simp only [mem_widePushoutPointSupport, mem_singleton_iff, mem_empty_iff_false, iff_false]
  rintro ⟨x, hx, h⟩
  exact hx ((widePushout_point_ι_eq_head_iff a i x).1 h)

/-- Support turns binary unions into unions. -/
@[simp] theorem widePushoutPointSupport_union (K L : Set W) :
    widePushoutPointSupport a (K ∪ L) =
      widePushoutPointSupport a K ∪ widePushoutPointSupport a L := by
  ext i
  simp only [mem_widePushoutPointSupport, mem_union]
  constructor
  · rintro ⟨x, hx, h | h⟩
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · exact ⟨x, hx, Or.inl h⟩
    · exact ⟨x, hx, Or.inr h⟩

/-- A set has support in `S` exactly when it is covered by the common point
and the ranges of the factors in `S`. Neither separation nor compactness is needed. -/
theorem widePushoutPointSupport_subset_iff (K : Set W) (S : Set I) :
    widePushoutPointSupport a K ⊆ S ↔
      K ⊆ {WidePushout.head f PUnit.unit} ∪ ⋃ i ∈ S, range (WidePushout.ι f i) := by
  constructor
  · intro h w hw
    obtain ⟨_ | i, x, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan P X f) w
    · left
      exact congrArg (WidePushout.head f) (Subsingleton.elim (α := PUnit) x PUnit.unit)
    · by_cases hx : x = a i
      · left
        simpa [hx] using widePushout_point_ι_point a i
      · right
        exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨h ⟨x, hx, hw⟩, mem_range_self x⟩⟩
  · intro h i ⟨x, hx, hw⟩
    rcases h hw with hhead | hfactor
    · exact (hx ((widePushout_point_ι_eq_head_iff a i x).1 hhead)).elim
    · rcases mem_iUnion.1 hfactor with ⟨j, hj⟩
      rcases mem_iUnion.1 hj with ⟨hj, y, hy⟩
      have hij : i = j := congrArg Sigma.fst
        ((widePushout_point_ι_eq_ι_iff_of_ne a hx).1 hy.symm)
      exact hij.symm ▸ hj

/-- The ranges of exactly the supported factors, together with the common point,
always cover the set. -/
theorem subset_head_union_widePushoutPointSupport (K : Set W) :
    K ⊆ {WidePushout.head f PUnit.unit} ∪
      ⋃ i ∈ widePushoutPointSupport a K, range (WidePushout.ι f i) :=
  (widePushoutPointSupport_subset_iff a K _).1 Subset.rfl

/-- An entire nontrivial factor has exactly its own singleton as support. -/
theorem widePushoutPointSupport_range_ι (i : I) (hi : ∃ x : X i, x ≠ a i) :
    widePushoutPointSupport a (range (WidePushout.ι f i)) = {i} := by
  apply Subset.antisymm
  · apply (widePushoutPointSupport_subset_iff a _ _).2
    intro w hw
    exact Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨mem_singleton i, hw⟩⟩)
  · intro j hj
    obtain rfl := mem_singleton_iff.1 hj
    obtain ⟨x, hx⟩ := hi
    exact ⟨x, hx, mem_range_self x⟩

/-- In a point-wide-pushout of T₁ spaces, a compact set meets only finitely
many factors away from the common point. No Hausdorff hypothesis is required. -/
theorem finite_widePushoutPointSupport [∀ i, T1Space (X i)] {K : Set W}
    (hK : IsCompact K) : (widePushoutPointSupport a K).Finite := by
  classical
  let J := widePushoutPointSupport a K
  choose x hx hmem using fun i : J ↦ i.property
  let c : J → W := fun i ↦ WidePushout.ι f i (x i)
  have hc_ne (i : J) : c i ≠ WidePushout.head f PUnit.unit := by
    exact fun h ↦ hx i ((widePushout_point_ι_eq_head_iff a i (x i)).1 h)
  have hc_index {i : J} {j : I} {y : X j}
      (h : c i = WidePushout.ι f j y) : (i : I) = j :=
    congrArg Sigma.fst ((widePushout_point_ι_eq_ι_iff_of_ne a (hx i)).1 h)
  have hc_inj : Function.Injective c := by
    intro i j h
    exact Subtype.ext (hc_index h)
  have hclosed (S : Set J) : IsClosed (c '' S) := by
    apply (isClosed_iff_of_isColimit
      (colimit.cocone (WidePushoutShape.wideSpan P X f)) (colimit.isColimit _) _).2
    rintro (_ | j)
    · change IsClosed (WidePushout.head f ⁻¹' (c '' S))
      have he : WidePushout.head f ⁻¹' (c '' S) = ∅ := by
        apply eq_empty_iff_forall_notMem.2
        rintro b ⟨i, _, hi⟩
        exact hc_ne i (hi.trans (congrArg (WidePushout.head f)
          (Subsingleton.elim b PUnit.unit)))
      rw [he]
      exact isClosed_empty
    · change IsClosed (WidePushout.ι f j ⁻¹' (c '' S))
      apply Set.Finite.isClosed
      apply Set.Subsingleton.finite
      rintro y ⟨i, _, hi⟩ y' ⟨i', _, hi'⟩
      have hii' : i = i' := Subtype.ext ((hc_index hi).trans (hc_index hi').symm)
      subst i'
      exact point_ι_injective a j (hi.symm.trans hi')
  have hDclosed : IsClosed (range c) := by simpa only [image_univ] using hclosed univ
  have hDcompact : IsCompact (range c) :=
    hK.of_isClosed_subset hDclosed (by rintro _ ⟨i, rfl⟩; exact hmem i)
  have hDdiscrete : IsDiscrete (range c) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.2
    intro S hS
    refine ⟨S, ?_, inter_eq_left.mpr hS⟩
    have he : c '' (c ⁻¹' S) = S := by
      ext w
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hw
        obtain ⟨i, rfl⟩ := hS hw
        exact ⟨i, hw, rfl⟩
    rw [← he]
    exact hclosed _
  have hDfinite := hDcompact.finite hDdiscrete
  let : Finite (range c) := hDfinite.to_subtype
  have : Finite J := Finite.of_injective
    (fun i ↦ (⟨c i, mem_range_self i⟩ : range c))
    (fun _ _ h ↦ hc_inj (congrArg Subtype.val h))
  exact finite_coe_iff.mp this

/-- A compact set is covered by the common point and finitely many factor ranges. -/
theorem exists_finite_widePushout_point_cover [∀ i, T1Space (X i)] {K : Set W}
    (hK : IsCompact K) :
    ∃ S : Set I, S.Finite ∧
      K ⊆ {WidePushout.head f PUnit.unit} ∪ ⋃ i ∈ S, range (WidePushout.ι f i) :=
  ⟨_, finite_widePushoutPointSupport a hK, subset_head_union_widePushoutPointSupport a K⟩

/-- A continuous image of a compact set, from a domain in any universe, has
finite support. In particular this applies to the image of a path. -/
theorem finite_widePushoutPointSupport_image [∀ i, T1Space (X i)]
    {A : Type z} [TopologicalSpace A] {C : Set A} (hC : IsCompact C)
    {g : A → W} (hg : Continuous g) :
    (widePushoutPointSupport a (g '' C)).Finite :=
  finite_widePushoutPointSupport a (hC.image hg)

/-- Every continuous map from a compact domain has its range in the common
point and finitely many factors. The domain universe is independent. -/
theorem exists_finite_widePushout_point_range [∀ i, T1Space (X i)]
    {A : Type z} [TopologicalSpace A] [CompactSpace A] (g : C(A, W)) :
    ∃ S : Set I, S.Finite ∧
      range g ⊆ {WidePushout.head f PUnit.unit} ∪ ⋃ i ∈ S, range (WidePushout.ι f i) :=
  exists_finite_widePushout_point_cover a (isCompact_range g.continuous)

/-- For factors in an independent smaller universe, transport the factors once
by the stock ULift functor. Any compact-domain map into that same wide pushout
is covered by the head and finitely many canonical maps from the original factors. -/
theorem exists_finite_widePushout_point_range_ulift
    {X₀ : I → TopCat.{u}} (a₀ : ∀ i, X₀ i) [∀ i, T1Space (X₀ i)]
    {A : Type z} [TopologicalSpace A] [CompactSpace A]
    (g : C(A, (widePushout P (fun i ↦ uliftFunctor.{v, u}.obj (X₀ i))
      (fun i ↦ TopCat.const ((X₀ i).uliftFunctorObjHomeo (a₀ i))) : TopCat.{max u v}))) :
    ∃ S : Set I, S.Finite ∧ range g ⊆
      {WidePushout.head (fun i ↦ TopCat.const ((X₀ i).uliftFunctorObjHomeo (a₀ i)))
        PUnit.unit} ∪ ⋃ i ∈ S,
          range (fun x : X₀ i ↦ WidePushout.ι
            (fun j ↦ TopCat.const ((X₀ j).uliftFunctorObjHomeo (a₀ j))) i
              ((X₀ i).uliftFunctorObjHomeo x)) := by
  let a' : ∀ i, uliftFunctor.{v, u}.obj (X₀ i) :=
    fun i ↦ (X₀ i).uliftFunctorObjHomeo (a₀ i)
  let : ∀ i, T1Space (uliftFunctor.{v, u}.obj (X₀ i)) :=
    fun i ↦ (X₀ i).uliftFunctorObjHomeo.t1Space
  obtain ⟨S, hS, hcover⟩ := exists_finite_widePushout_point_range a' g
  refine ⟨S, hS, ?_⟩
  intro w hw
  rcases hcover hw with hhead | hfactor
  · exact Or.inl hhead
  · right
    rcases mem_iUnion.1 hfactor with ⟨i, hi⟩
    rcases mem_iUnion.1 hi with ⟨hSi, y, rfl⟩
    exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hSi,
      (X₀ i).uliftFunctorObjHomeo.symm y, by simp [a']⟩⟩

end TopCat
