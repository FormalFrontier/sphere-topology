/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushoutRetraction
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Separation axioms for point-wide-pushouts

The canonical chosen-factor retractions jointly distinguish all points of a
categorical wide pushout over a point, without separation or finiteness
assumptions. This includes an empty index family: the head is retained and is
the only point. The coordinate map into the dependent product is continuous
and injective; no embedding or inducing assertion about that map is made.

Consequently the wide pushout is T₀, T₁ or T₂ exactly when all its factors are.
Factorwise inheritance is registered as instances; reflection uses the existing
factor embeddings and is exposed by the forward directions of the iff lemmas,
not by reverse instances. Index and space universes remain independent through
the maximum-universe diagram and the original-space transport described in
`SphereTopology.Topology.WidePushoutRetraction`.

## Implementation notes

Stock concrete-colimit representatives reduce point equality to the head and
factor cases. Only the existing retraction equations and attaching relation
are used; the proof is independent of any quotient comparison.

## References

* The project's `SphereTopology.Topology.WidePushoutRetraction` supplies the
  selected-factor maps, their equations and the factor embeddings.
* Mathlib's concrete colimits supply representatives. Its dependent-product
  topology, separation instances and continuous-injective transfer theorems
  supply inheritance; its embedding transfer theorems supply reflection.
* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  p. 19, supplies the point-wedge setting, not these arbitrary-family results.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace TopCat

variable {I : Type v} (X : I → TopCat.{max u v}) (x : ∀ j, X j)

local notation "P" => TopCat.of PUnit
local notation "f" => (fun j ↦ (TopCat.const (x j) : P ⟶ X j))
local notation "W" => (widePushout P X f : TopCat)

/-- The chosen-factor retractions jointly distinguish points, even for an empty
index family. No separation assumption on the factors is needed. -/
theorem widePushoutPointRetraction_jointly_injective :
    Function.Injective (fun p : W ↦ fun i ↦ widePushoutPointRetraction X x i p) := by
  intro p q h
  obtain ⟨_ | i, p, rfl⟩ :=
    Concrete.colimit_exists_rep (WidePushoutShape.wideSpan P X f) p
  · change PUnit.{max u v + 1} at p
    obtain ⟨_ | j, q, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan P X f) q
    · change PUnit.{max u v + 1} at q
      exact congrArg (WidePushout.head f) (Subsingleton.elim p q)
    · have hq : x j = q := by
        have hj := congrFun h j
        change widePushoutPointRetraction X x j (WidePushout.head f p) =
          widePushoutPointRetraction X x j (WidePushout.ι f j q) at hj
        exact (widePushoutPointRetraction_head_apply X x j p).symm.trans
          (hj.trans (widePushoutPointRetraction_ι_apply X x j q))
      change WidePushout.head f p = WidePushout.ι f j q
      rw [← hq, widePushout_point_ι_point]
  · obtain ⟨_ | j, q, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan P X f) q
    · change PUnit.{max u v + 1} at q
      have hp : p = x i := by
        have hi := congrFun h i
        change widePushoutPointRetraction X x i (WidePushout.ι f i p) =
          widePushoutPointRetraction X x i (WidePushout.head f q) at hi
        exact (widePushoutPointRetraction_ι_apply X x i p).symm.trans
          (hi.trans (widePushoutPointRetraction_head_apply X x i q))
      change WidePushout.ι f i p = WidePushout.head f q
      rw [hp, widePushout_point_ι_point]
    · by_cases hij : i = j
      · subst j
        have hpq : p = q := by
          simpa only [widePushoutPointRetraction_ι_apply] using congrFun h i
        exact congrArg (WidePushout.ι f i) hpq
      · have hp : p = x i := by
          have hi := congrFun h i
          change widePushoutPointRetraction X x i (WidePushout.ι f i p) =
            widePushoutPointRetraction X x i (WidePushout.ι f j q) at hi
          simpa only [widePushoutPointRetraction_ι_apply,
            widePushoutPointRetraction_ι_of_ne_apply X x i j (Ne.symm hij)] using hi
        have hq : x j = q := by
          have hj := congrFun h j
          change widePushoutPointRetraction X x j (WidePushout.ι f i p) =
            widePushoutPointRetraction X x j (WidePushout.ι f j q) at hj
          simpa only [widePushoutPointRetraction_ι_apply,
            widePushoutPointRetraction_ι_of_ne_apply X x j i hij] using hj
        change WidePushout.ι f i p = WidePushout.ι f j q
        rw [hp, ← hq, widePushout_point_ι_point, widePushout_point_ι_point]

/-- A point-wide-pushout of T₀ factors is T₀, including the empty family. -/
instance t0Space_widePushoutPoint [∀ i, T0Space (X i)] : T0Space W :=
  t0Space_of_injective_of_continuous (widePushoutPointRetraction_jointly_injective X x)
    (continuous_pi fun i ↦ (widePushoutPointRetraction X x i).hom.continuous)

/-- A point-wide-pushout of T₁ factors is T₁, including the empty family. -/
instance t1Space_widePushoutPoint [∀ i, T1Space (X i)] : T1Space W :=
  t1Space_of_injective_of_continuous (widePushoutPointRetraction_jointly_injective X x)
    (continuous_pi fun i ↦ (widePushoutPointRetraction X x i).hom.continuous)

/-- A point-wide-pushout of Hausdorff factors is Hausdorff, including the empty family. -/
instance t2Space_widePushoutPoint [∀ i, T2Space (X i)] : T2Space W :=
  T2Space.of_injective_continuous (widePushoutPointRetraction_jointly_injective X x)
    (continuous_pi fun i ↦ (widePushoutPointRetraction X x i).hom.continuous)

/-- A point-wide-pushout is T₀ exactly when each factor is T₀. -/
theorem t0Space_widePushoutPoint_iff : T0Space W ↔ ∀ i, T0Space (X i) := by
  constructor
  · intro h i
    let := h
    exact (isEmbedding_widePushout_point_ι X x i).t0Space
  · intro h
    let := h
    infer_instance

/-- A point-wide-pushout is T₁ exactly when each factor is T₁. -/
theorem t1Space_widePushoutPoint_iff : T1Space W ↔ ∀ i, T1Space (X i) := by
  constructor
  · intro h i
    let := h
    exact (isEmbedding_widePushout_point_ι X x i).t1Space
  · intro h
    let := h
    infer_instance

/-- A point-wide-pushout is Hausdorff exactly when each factor is Hausdorff. -/
theorem t2Space_widePushoutPoint_iff : T2Space W ↔ ∀ i, T2Space (X i) := by
  constructor
  · intro h i
    let := h
    exact (isEmbedding_widePushout_point_ι X x i).t2Space
  · intro h
    let := h
    infer_instance

end TopCat
