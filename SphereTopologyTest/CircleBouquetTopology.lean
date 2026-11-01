/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homotopy.CircleBouquet.Topology
import SphereTopology.Homotopy.CircleBouquet.ClosedMap

/-!
# Folding two circles onto one

The fold is a closed quotient map but not a closed embedding.
-/

private theorem fold_isQuotientMap_and_isClosedMap_and_not_isClosedEmbedding :
    Topology.IsQuotientMap
        (CircleBouquet.relabel.{0, 0, 0, 0} (fun _ : Bool ↦ ())) ∧
      IsClosedMap (CircleBouquet.relabel.{0, 0, 0, 0} (fun _ : Bool ↦ ())) ∧
      ¬ Topology.IsClosedEmbedding
        (CircleBouquet.relabel.{0, 0, 0, 0} (fun _ : Bool ↦ ())) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (CircleBouquet.isQuotientMap_relabel_iff _).2
      (fun _ ↦ ⟨false, Subsingleton.elim _ _⟩)
  · exact (CircleBouquet.isClosedMap_relabel_iff _).2 (fun _ ↦ Set.toFinite _)
  · intro h
    have hinj := (CircleBouquet.isClosedEmbedding_relabel_iff _).1 h
    have hbad : false = true := hinj rfl
    cases hbad
