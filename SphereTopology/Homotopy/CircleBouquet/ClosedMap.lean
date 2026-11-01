/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.CircleBouquet
public import SphereTopology.Topology.WidePushout.ClosedMap
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Perfect

/-!
# Closed maps between circle bouquets

`CircleBouquet.isClosedMap_relabel_iff` characterizes closedness of the original
`CircleBouquet.relabel` by finiteness of every label fiber. Empty and infinite
label types are included, with independent source and target ambient and label
universes. The bouquet retains its categorical weak topology and its common
point, also when the label family is empty.

For necessity, an infinite fiber supplies distinct source labels. Choose
nonidentity circle points tending to one and place one on each of those source
circles. Their set is closed by the original-circle closed-set test: each circle
preimage has at most one point. Its relabeled image is not closed, since its
preimage on the common target circle omits one but contains the convergent
sequence. Only continuity of the target circle inclusion is needed.

## References

* `SphereTopology.Homotopy.CircleBouquet` supplies the categorical bouquet,
  original-circle inclusions, retractions and relabeling.
* `SphereTopology.Topology.WidePushout.ClosedMap` supplies the finite-fiber
  closed-map criterion specialized by the sufficient direction.
* Mathlib supplies the complex circle, its connectedness, the nonisolation
  theorem for connected nontrivial T₁ spaces and sequential selection for
  countably generated filters.
-/

@[expose] public section

open Filter
open scoped Topology

universe u v u' w

namespace CircleBouquet

/-- A closed circle-bouquet relabeling has finite label fibers. An infinite
fiber would send a closed set with one point on each of distinct source circles
to a set accumulating at, but omitting, the common point. -/
theorem finite_fibers_of_isClosedMap_relabel {I : Type v} {J : Type w}
    (σ : I → J) (hclosed : IsClosedMap (relabel.{u, v, u', w} σ)) :
    ∀ j : J, Set.Finite (σ ⁻¹' ({j} : Set J)) := by
  classical
  intro j
  by_contra hj
  let e : ℕ ↪ (σ ⁻¹' ({j} : Set J)) := Set.Infinite.natEmbedding _ hj
  let i : ℕ → I := fun n ↦ (e n).1
  have hi : Function.Injective i := by
    intro m n h
    exact e.injective (Subtype.ext h)
  have hσ (n : ℕ) : σ (i n) = j := (e n).property
  let : Nontrivial Circle := ⟨⟨-1, 1, Circle.neg_ne_self 1⟩⟩
  have hfreq : ∃ᶠ z : Circle in 𝓝 (1 : Circle), z ≠ 1 := by
    apply Filter.frequently_iff_neBot.2
    change Filter.NeBot (𝓝[≠] (1 : Circle))
    infer_instance
  obtain ⟨z, hzlim, hz⟩ := Filter.exists_seq_forall_of_frequently hfreq
  let c : ℕ → space.{u, v} I := fun n ↦ inclusion.{u, v} (i n) (z n)
  let A : Set (space.{u, v} I) := Set.range c
  have hA : IsClosed A := by
    simpa only [Set.image_univ] using
      (show IsClosed ((fun n ↦ inclusion.{u, v} (i n) (z n)) '' Set.univ) from
        isClosed_image_inclusion_of_injective i hi z hz Set.univ)
  let B : Set Circle :=
    inclusion.{u', w} j ⁻¹' (relabel.{u, v, u', w} σ '' A)
  have hB : IsClosed B :=
    (hclosed A hA).preimage (inclusion.{u', w} j).continuous
  have hzB (n : ℕ) : z n ∈ B := by
    refine ⟨c n, ⟨n, rfl⟩, ?_⟩
    change relabel.{u, v, u', w} σ (inclusion.{u, v} (i n) (z n)) =
      inclusion.{u', w} j (z n)
    rw [relabel_inclusion_apply, hσ n]
  have h1B : (1 : Circle) ∈ B :=
    hB.mem_of_tendsto hzlim (Filter.Eventually.of_forall hzB)
  obtain ⟨x, ⟨n, rfl⟩, hn⟩ := h1B
  have hp : inclusion.{u', w} j (z n) = inclusion.{u', w} j 1 := by
    simpa only [c, relabel_inclusion_apply, hσ] using hn
  exact hz n (inclusion_injective.{u', w} j hp)

/-- The original circle-bouquet relabeling is a closed map exactly when every
fiber of its label function is finite. This includes empty and infinite label
types and independent source and target ambient and label universes. -/
theorem isClosedMap_relabel_iff {I : Type v} {J : Type w} (σ : I → J) :
    IsClosedMap (CircleBouquet.relabel.{u, v, u', w} σ) ↔
      ∀ j : J, Set.Finite (σ ⁻¹' ({j} : Set J)) :=
  ⟨finite_fibers_of_isClosedMap_relabel.{u, v, u', w} σ,
    isClosedMap_relabel_of_finite_fibers.{u, v, u', w} σ⟩

end CircleBouquet
