/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Topology.WidePushout.OpenNeighborhood
import SphereTopology.Topology.WidePushout.PointLift

/-!
# A proper two-factor open neighborhood

Both target factors are discrete three-point spaces. Each source omits the
third point but retains a non-basepoint. The canonical descent is an open
embedding, misses a specified target point and retains a specified non-head.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopCat Set

namespace SphereTopologyTest.WidePushoutOpenEmbedding

local instance : TopologicalSpace (Fin 3) := ⊥
local instance : DiscreteTopology (Fin 3) := ⟨rfl⟩

private abbrev family : Bool → TopCat := fun _ ↦ TopCat.of (Fin 3)
private abbrev point : ∀ i, family i := fun _ ↦ 0
private abbrev neighborhood : ∀ i, Set (family i) := fun _ ↦ {0, 1}

private theorem point_mem_neighborhood (i : Bool) : point i ∈ neighborhood i :=
  Or.inl rfl

private theorem one_mem_neighborhood (i : Bool) : (1 : family i) ∈ neighborhood i :=
  Or.inr rfl

private theorem two_not_mem_neighborhood (i : Bool) :
    (2 : family i) ∉ neighborhood i := by
  change (2 : Fin 3) ∉ ({0, 1} : Set (Fin 3))
  decide

private theorem open_neighborhood (i : Bool) : IsOpen (neighborhood i) :=
  isOpen_discrete _

private abbrev inclusion (i : Bool) : C(neighborhood i, family i) :=
  ⟨Subtype.val, continuous_subtype_val⟩

set_option quotPrecheck false in
local notation "P" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "XU" => (fun i ↦ TopCat.of (neighborhood i))
set_option quotPrecheck false in
local notation "aU" => (fun i ↦ (⟨point i, point_mem_neighborhood i⟩ : neighborhood i))
set_option quotPrecheck false in
local notation "α" => (fun i ↦ (TopCat.const (aU i) : P ⟶ XU i))
set_option quotPrecheck false in
local notation "β" => (fun i ↦ (TopCat.const (point i) : P ⟶ family i))
set_option quotPrecheck false in
local notation "hy" => WidePushout.head β PUnit.unit
set_option quotPrecheck false in
local notation "F" => widePushoutDesc α (ContinuousMap.const P hy)
  (fun i ↦ (WidePushout.ι β i).hom.comp (inclusion i))
  (widePushoutDesc_point_condition (X := XU) (Y := family)
    aU point inclusion (fun _ ↦ rfl))

private theorem proper_open_neighborhood :
    (∀ i, range (inclusion i) ≠ univ) ∧
    Topology.IsOpenEmbedding F ∧
    WidePushout.ι β false (2 : family false) ∉ range F ∧
    F (WidePushout.ι α true ⟨1, one_mem_neighborhood true⟩) =
      WidePushout.ι β true (1 : family true) ∧
    F (WidePushout.ι α true ⟨1, one_mem_neighborhood true⟩) ≠ hy := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i he
    have h2 : (2 : family i) ∈ range (inclusion i) :=
      he.symm ▸ mem_univ (2 : family i)
    rcases h2 with ⟨q, hq⟩
    apply two_not_mem_neighborhood i
    rw [← hq]
    exact q.property
  · exact isOpenEmbedding_widePushoutDesc_point (X := XU) (Y := family)
      aU point inclusion (fun _ ↦ rfl)
      (fun i ↦ (open_neighborhood i).isOpenEmbedding_subtypeVal)
  · rw [range_widePushoutDesc_point_subtype (Y := family)
      point neighborhood point_mem_neighborhood]
    change (2 : family false) ∉ WidePushout.ι β false ⁻¹'
      widePushoutPointNeighborhood point neighborhood
    rw [preimage_widePushoutPointNeighborhood (Y := family) point neighborhood
      false (point_mem_neighborhood false)]
    exact two_not_mem_neighborhood false
  · exact widePushoutDesc_point_ι (X := XU) (Y := family)
      aU point inclusion (fun _ ↦ rfl)
      true ⟨1, one_mem_neighborhood true⟩
  · intro he
    have he' : WidePushout.ι β true (1 : family true) = hy :=
      (widePushoutDesc_point_ι (X := XU) (Y := family)
        aU point inclusion (fun _ ↦ rfl) true ⟨1, one_mem_neighborhood true⟩).symm.trans he
    have h10 : (1 : Fin 3) = 0 := (widePushout_point_ι_eq_head_iff point true 1).1 he'
    exact (by decide : (1 : Fin 3) ≠ 0) h10

end SphereTopologyTest.WidePushoutOpenEmbedding
