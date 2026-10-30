/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.Subfamily
public import Mathlib.Topology.Homotopy.Path

/-!
# Compact homotopies in point-attached wide pushouts

The existing subfamily retraction postcomposes a relative homotopy using
`ContinuousMap.HomotopyRel.compContinuousMap`. Inclusion recovers that prescribed
homotopy at every pair of parameters exactly when its image support lies in the
subfamily. The endpoint casts recover the homotopy as an object, and a factor
with those endpoints is unique. The relative equations are Mathlib's
`ContinuousMap.HomotopyRel.eq_fst` and `ContinuousMap.HomotopyRel.eq_snd` applied
to the same composite.

For T₁ factors, compact image gives a finite stage containing any prescribed
finite set of indices. In particular, this holds for any compact domain, in an
independent universe. No separation hypothesis is imposed on the domain, and
neither the factors nor the wide pushout need be compact.

In contrast, reflection of the existence of a relative homotopy at a fixed
subfamily uses only the continuous left inverse. It needs neither T₁ nor
compactness and does not assert strict recovery of a supplied ambient homotopy.
The common head is retained even for the empty family.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  p. 19, for the point-wedge setting, not the arbitrary-T₁ compact-image or
  arbitrary-relative-subset conclusions here.
* Mathlib's homotopy formalization by Shing Tak Lam supplies relative homotopies,
  postcomposition, endpoint casts, extensionality and path homotopies.
* The project's support, compactness and subfamily formalizations supply the
  finite-support theorem and the inclusion-retraction factorization interface.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u v z

namespace TopCat

variable {I : Type v} {X : I → TopCat.{max u v}} (a : ∀ i, X i) (S : Set I)

section Relative

variable {A : Type z} [TopologicalSpace A] {B : Set A}

/-- The canonical retracted relative homotopy recovers the prescribed homotopy
at every pair of parameters exactly when its whole image is supported in the
subfamily. No compactness or separation is needed. -/
theorem widePushoutPointSubfamily_homotopyRel_factorization_iff
    {f₀ f₁ : C(A, (widePushout (TopCat.of PUnit.{max u v + 1}) X
      (fun i ↦ (TopCat.const (a i) :
        TopCat.of PUnit.{max u v + 1} ⟶ X i)) : TopCat.{max u v}))}
    (H : f₀.HomotopyRel f₁ B) :
    (∀ t x, widePushoutPointSubfamilyInclusion a S
      ((H.compContinuousMap (widePushoutPointSubfamilyRetraction a S)) (t, x)) =
        H (t, x)) ↔ widePushoutPointSupport a (range H) ⊆ S := by
  have he : (∀ t x, widePushoutPointSubfamilyInclusion a S
      ((H.compContinuousMap (widePushoutPointSubfamilyRetraction a S)) (t, x)) =
        H (t, x)) ↔
      (widePushoutPointSubfamilyInclusion a S).comp
        ((widePushoutPointSubfamilyRetraction a S).comp H.toContinuousMap) =
          H.toContinuousMap := by
    constructor
    · intro h
      apply ContinuousMap.ext
      rintro ⟨t, x⟩
      exact h t x
    · intro h t x
      exact DFunLike.congr_fun h (t, x)
  exact he.trans (widePushoutPointSubfamily_factorization_iff a S H.toContinuousMap)

/-- Strict recovery of a relative homotopy also recovers its initial map. -/
theorem widePushoutPointSubfamily_homotopyRel_start
    {f₀ f₁ : C(A, (widePushout (TopCat.of PUnit.{max u v + 1}) X
      (fun i ↦ (TopCat.const (a i) :
        TopCat.of PUnit.{max u v + 1} ⟶ X i)) : TopCat.{max u v}))}
    (H : f₀.HomotopyRel f₁ B)
    (h : widePushoutPointSupport a (range H) ⊆ S) :
    (widePushoutPointSubfamilyInclusion a S).comp
      ((widePushoutPointSubfamilyRetraction a S).comp f₀) = f₀ := by
  ext x
  simpa only [ContinuousMap.HomotopyWith.apply_zero, ContinuousMap.comp_apply] using
    (widePushoutPointSubfamily_homotopyRel_factorization_iff a S H).2 h 0 x

/-- Strict recovery of a relative homotopy also recovers its terminal map. -/
theorem widePushoutPointSubfamily_homotopyRel_end
    {f₀ f₁ : C(A, (widePushout (TopCat.of PUnit.{max u v + 1}) X
      (fun i ↦ (TopCat.const (a i) :
        TopCat.of PUnit.{max u v + 1} ⟶ X i)) : TopCat.{max u v}))}
    (H : f₀.HomotopyRel f₁ B)
    (h : widePushoutPointSupport a (range H) ⊆ S) :
    (widePushoutPointSubfamilyInclusion a S).comp
      ((widePushoutPointSubfamilyRetraction a S).comp f₁) = f₁ := by
  ext x
  simpa only [ContinuousMap.HomotopyWith.apply_one, ContinuousMap.comp_apply] using
    (widePushoutPointSubfamily_homotopyRel_factorization_iff a S H).2 h 1 x

/-- Postcomposition by inclusion, followed by the endpoint casts, recovers the
relative homotopy itself, not only its homotopy class. -/
theorem widePushoutPointSubfamily_homotopyRel_cast
    {f₀ f₁ : C(A, (widePushout (TopCat.of PUnit.{max u v + 1}) X
      (fun i ↦ (TopCat.const (a i) :
        TopCat.of PUnit.{max u v + 1} ⟶ X i)) : TopCat.{max u v}))}
    (H : f₀.HomotopyRel f₁ B)
    (h : widePushoutPointSupport a (range H) ⊆ S) :
    (((H.compContinuousMap (widePushoutPointSubfamilyRetraction a S)).compContinuousMap
      (widePushoutPointSubfamilyInclusion a S)).cast
      (widePushoutPointSubfamily_homotopyRel_start a S H h)
      (widePushoutPointSubfamily_homotopyRel_end a S H h)) = H := by
  apply ContinuousMap.HomotopyWith.ext
  rintro ⟨t, x⟩
  exact (widePushoutPointSubfamily_homotopyRel_factorization_iff a S H).2 h t x

/-- A strict factor with the canonical retracted endpoints is the canonical
retracted homotopy. This is the existing continuous-factor uniqueness applied
to the whole parameter product. -/
theorem widePushoutPointSubfamily_homotopyRel_unique
    {f₀ f₁ : C(A, (widePushout (TopCat.of PUnit.{max u v + 1}) X
      (fun i ↦ (TopCat.const (a i) :
        TopCat.of PUnit.{max u v + 1} ⟶ X i)) : TopCat.{max u v}))}
    (H : f₀.HomotopyRel f₁ B)
    (K : ((widePushoutPointSubfamilyRetraction a S).comp f₀).HomotopyRel
      ((widePushoutPointSubfamilyRetraction a S).comp f₁) B)
    (hK : ∀ t x, widePushoutPointSubfamilyInclusion a S (K (t, x)) = H (t, x)) :
    K = H.compContinuousMap (widePushoutPointSubfamilyRetraction a S) := by
  have he := widePushoutPointSubfamily_factor_unique a S H.toContinuousMap
    K.toContinuousMap (by
      apply ContinuousMap.ext
      rintro ⟨t, x⟩
      exact hK t x)
  apply ContinuousMap.HomotopyWith.ext
  intro x
  exact DFunLike.congr_fun he x

/-- A compact-image relative homotopy in a point-wide-pushout of T₁ spaces
strictly factors through a finite stage containing any prescribed finite set.
The witness is Mathlib's retraction composite, retaining its endpoint and
relative equations. -/
theorem exists_finite_widePushout_point_subfamily_homotopyRel
    {f₀ f₁ : C(A, (widePushout (TopCat.of PUnit.{max u v + 1}) X
      (fun i ↦ (TopCat.const (a i) :
        TopCat.of PUnit.{max u v + 1} ⟶ X i)) : TopCat.{max u v}))}
    (H : f₀.HomotopyRel f₁ B)
    [∀ i, T1Space (X i)] (hH : IsCompact (range H))
    (F : Set I) (hF : F.Finite) :
    ∃ S : Set I, S.Finite ∧ F ⊆ S ∧
      ∀ t x, widePushoutPointSubfamilyInclusion a S
        ((H.compContinuousMap (widePushoutPointSubfamilyRetraction a S)) (t, x)) =
          H (t, x) := by
  refine ⟨F ∪ widePushoutPointSupport a (range H),
    hF.union (finite_widePushoutPointSupport a hH), subset_union_left, ?_⟩
  exact (widePushoutPointSubfamily_homotopyRel_factorization_iff a _ H).2
    subset_union_right

/-- A compact domain gives the compact-image hypothesis for strict finite-stage
factorization of any relative homotopy. The relative subset is arbitrary. -/
theorem exists_finite_widePushout_point_subfamily_homotopyRel_of_compactSpace
    {f₀ f₁ : C(A, (widePushout (TopCat.of PUnit.{max u v + 1}) X
      (fun i ↦ (TopCat.const (a i) :
        TopCat.of PUnit.{max u v + 1} ⟶ X i)) : TopCat.{max u v}))}
    (H : f₀.HomotopyRel f₁ B)
    [∀ i, T1Space (X i)] [CompactSpace A] (F : Set I) (hF : F.Finite) :
    ∃ S : Set I, S.Finite ∧ F ⊆ S ∧
      ∀ t x, widePushoutPointSubfamilyInclusion a S
        ((H.compContinuousMap (widePushoutPointSubfamilyRetraction a S)) (t, x)) =
          H (t, x) :=
  exists_finite_widePushout_point_subfamily_homotopyRel a H
    (isCompact_range H.continuous) F hF

end Relative

/-- Inclusion of any fixed subfamily reflects the existence of relative
homotopies. The continuous left inverse suffices, with no compactness or
separation assumptions and no claim of recovering a prescribed homotopy. -/
theorem widePushoutPointSubfamily_homotopicRel_iff
    {A : Type z} [TopologicalSpace A]
    (p₀ p₁ : C(A, (widePushout (TopCat.of PUnit.{max u v + 1})
      (fun i : S ↦ X (Subtype.val i)) (fun i : S ↦
        (TopCat.const (a (Subtype.val i)) :
          TopCat.of PUnit.{max u v + 1} ⟶ X (Subtype.val i))) : TopCat.{max u v})))
    (B : Set A) :
    ((widePushoutPointSubfamilyInclusion a S).comp p₀).HomotopicRel
      ((widePushoutPointSubfamilyInclusion a S).comp p₁) B ↔ p₀.HomotopicRel p₁ B := by
  constructor
  · rintro ⟨H⟩
    refine ⟨(H.compContinuousMap (widePushoutPointSubfamilyRetraction a S)).cast ?_ ?_⟩
    · ext x
      exact leftInverse_widePushoutPointSubfamilyRetraction a S (p₀ x)
    · ext x
      exact leftInverse_widePushoutPointSubfamilyRetraction a S (p₁ x)
  · intro h
    exact h.comp_continuousMap (widePushoutPointSubfamilyInclusion a S)

/-- The fixed-subfamily reflection theorem for paths, with the mapped
endpoints retained. In particular it applies to based loops without T₁ or
compactness hypotheses. -/
theorem widePushoutPointSubfamily_path_homotopic_iff
    {x y : (widePushout (TopCat.of PUnit.{max u v + 1})
      (fun i : S ↦ X (Subtype.val i)) (fun i : S ↦
        (TopCat.const (a (Subtype.val i)) :
          TopCat.of PUnit.{max u v + 1} ⟶ X (Subtype.val i))) : TopCat.{max u v})}
    (p q : Path x y) :
    (p.map (widePushoutPointSubfamilyInclusion a S).continuous).Homotopic
      (q.map (widePushoutPointSubfamilyInclusion a S).continuous) ↔ p.Homotopic q :=
  widePushoutPointSubfamily_homotopicRel_iff a S p.toContinuousMap q.toContinuousMap {0, 1}

end TopCat
