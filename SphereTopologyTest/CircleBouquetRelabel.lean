/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import SphereTopology.Homotopy.CircleBouquet
import SphereTopology.Homotopy.CircleBouquet.FundamentalGroup

/-!
# Folding a two-circle bouquet onto a single circle

The relabeling `Bool → Unit` induces a surjective but noninjective homomorphism
of fundamental groups. This checks the relabeling criteria on the whole groups,
not only on the positive generators. Each included positive class is nonidentity
by `CircleBouquet.positiveGenerator_ne_one`.
-/

namespace SphereTopologyTest.CircleBouquetRelabel

private theorem fold_surjective_not_injective :
    Function.Surjective
        (FundamentalGroup.mapOfEq
          (CircleBouquet.relabel.{0, 0, 0, 0} (fun _ : Bool ↦ Unit.unit))
          (CircleBouquet.relabel_basepoint.{0, 0, 0, 0} (fun _ : Bool ↦ Unit.unit))) ∧
      ¬ Function.Injective
        (FundamentalGroup.mapOfEq
          (CircleBouquet.relabel.{0, 0, 0, 0} (fun _ : Bool ↦ Unit.unit))
          (CircleBouquet.relabel_basepoint.{0, 0, 0, 0} (fun _ : Bool ↦ Unit.unit))) := by
  constructor
  · apply (CircleBouquet.mapOfEq_relabel_surjective_iff (fun _ : Bool ↦ Unit.unit)).2
    intro j
    cases j
    exact ⟨false, rfl⟩
  · intro h
    have hlabels : Function.Injective (fun _ : Bool ↦ Unit.unit) :=
      (CircleBouquet.mapOfEq_relabel_injective_iff (fun _ : Bool ↦ Unit.unit)).1 h
    exact Bool.false_ne_true (hlabels rfl)

end SphereTopologyTest.CircleBouquetRelabel
