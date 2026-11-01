/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homotopy.CircleBouquet.Topology

/-!
# Folding two circles onto one

The fold is a quotient map but not a closed embedding.
-/

private theorem fold_isQuotientMap_and_not_isClosedEmbedding :
    Topology.IsQuotientMap
        (CircleBouquet.relabel.{0, 0, 0, 0} (fun _ : Bool ↦ ())) ∧
      ¬ Topology.IsClosedEmbedding
        (CircleBouquet.relabel.{0, 0, 0, 0} (fun _ : Bool ↦ ())) := by
  constructor
  · exact (CircleBouquet.isQuotientMap_relabel_iff _).2
      (fun _ ↦ ⟨false, Subsingleton.elim _ _⟩)
  · intro h
    have hinj := (CircleBouquet.isClosedEmbedding_relabel_iff _).1 h
    have hbad : false = true := hinj rfl
    cases hbad
