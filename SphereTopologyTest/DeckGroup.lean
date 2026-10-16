/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Topology.DeckGroup

import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Separation.Connected

/-!
# Deck transformations of the circle covering and a disconnected covering

Translation by one is a nonidentity deck transformation of the covering
`ℝ → AddCircle (1 : ℝ)`. Its value at zero is one, in the same fiber as zero.
The total space of this covering is preconnected.

For the discrete covering `Fin 3 → Unit`, transposing zero and one gives a
nonidentity deck transformation fixing two. Thus a fixed point does not force
a deck transformation to be the identity when the total space is disconnected.

## References

The constructions use Mathlib's `deck`, `Homeomorph.addRight`,
`Equiv.toHomeomorphOfDiscrete`, and `AddCircle.isCoveringMap_coe`.
-/

@[expose] public section

namespace SphereTopologyTest

private def realCircleProjection : ℝ → AddCircle (1 : ℝ) := (↑)

private theorem realCircleProjection_covering : IsCoveringMap realCircleProjection :=
  AddCircle.isCoveringMap_coe (1 : ℝ)

private theorem real_preconnected : PreconnectedSpace ℝ := inferInstance

/-- Translation by one, as a deck transformation of the circle covering. -/
private def realCircleTranslation : deck realCircleProjection :=
  ⟨Homeomorph.addRight (1 : ℝ), by
    funext x
    exact AddCircle.coe_add_period (1 : ℝ) x⟩

private theorem realCircleTranslation_smul (x : ℝ) :
    realCircleTranslation • x = x + 1 := rfl

private theorem realCircleTranslation_zero : realCircleTranslation • (0 : ℝ) = 1 := by
  rw [realCircleTranslation_smul, zero_add]

private theorem realCircleTranslation_ne_one : realCircleTranslation ≠ 1 := by
  intro h
  have hzero := realCircleTranslation_zero
  rw [h, one_smul] at hzero
  exact zero_ne_one hzero

private theorem realCircleTranslation_projection (x : ℝ) :
    realCircleProjection (realCircleTranslation • x) = realCircleProjection x :=
  deck.proj_smul realCircleTranslation x

/-- The origin in the point fiber of the circle covering over zero. -/
private def realCircleFiberOrigin : realCircleProjection ⁻¹' {0} :=
  ⟨0, AddCircle.coe_zero (1 : ℝ)⟩

/-- The translate of the origin, in the same point fiber. -/
private def realCircleFiberTranslatedOrigin : realCircleProjection ⁻¹' {0} :=
  ⟨realCircleTranslation • (0 : ℝ),
    (realCircleTranslation_projection 0).trans realCircleFiberOrigin.property⟩

private theorem realCircleFiberTranslatedOrigin_val :
    realCircleFiberTranslatedOrigin.val = 1 :=
  realCircleTranslation_zero

private theorem realCircleFiberTranslatedOrigin_ne_origin :
    realCircleFiberTranslatedOrigin ≠ realCircleFiberOrigin := by
  intro h
  have hval := congrArg Subtype.val h
  rw [realCircleFiberTranslatedOrigin_val] at hval
  exact one_ne_zero hval

private def threeSheetProjection (_ : Fin 3) : Unit := ()

private theorem threeSheetProjection_covering : IsCoveringMap threeSheetProjection :=
  IsCoveringMap.of_discreteTopology _

/-- The transposition of the first two sheets of the three-sheet covering. -/
private def threeSheetTransposition : deck threeSheetProjection :=
  ⟨(Equiv.swap (0 : Fin 3) 1).toHomeomorphOfDiscrete, by funext x; rfl⟩

private theorem threeSheetTransposition_fixes_two :
    threeSheetTransposition • (2 : Fin 3) = 2 := by
  change Equiv.swap (0 : Fin 3) 1 2 = 2
  decide

private theorem threeSheetTransposition_moves_zero :
    threeSheetTransposition • (0 : Fin 3) = 1 := by
  change Equiv.swap (0 : Fin 3) 1 0 = 1
  decide

private theorem threeSheetTransposition_ne_one : threeSheetTransposition ≠ 1 := by
  intro h
  have hzero := threeSheetTransposition_moves_zero
  rw [h, one_smul] at hzero
  exact (by decide : (0 : Fin 3) ≠ 1) hzero

private theorem threeSheet_not_preconnected : ¬ PreconnectedSpace (Fin 3) := by
  intro h
  let := h
  have hsub := PreconnectedSpace.trivial_of_discrete (X := Fin 3)
  exact (by decide : (0 : Fin 3) ≠ 1) (hsub.elim 0 1)

/-- The fiber action sends the origin to its translated point. -/
private theorem realCircleTranslation_smul_fiberOrigin :
    realCircleTranslation • realCircleFiberOrigin = realCircleFiberTranslatedOrigin := by
  apply Subtype.ext
  exact (deck.coe_fiber_smul realCircleTranslation realCircleFiberOrigin).trans rfl

/-- Evaluation at zero records the nonidentity translation at the point with value one. -/
private theorem realCircleTranslation_eval_origin :
    (deck.evalEmbedding realCircleProjection_covering.isSeparatedMap
      realCircleProjection_covering.isLocalHomeomorph.isLocallyInjective (0 : ℝ)
      realCircleTranslation : ℝ) = 1 := by
  simpa only [deck.coe_evalEmbedding_apply] using realCircleTranslation_zero

/-- A nonidentity translation of the circle covering has no fixed point. -/
private theorem realCircleTranslation_no_fixed_point (x : ℝ) :
    realCircleTranslation • x ≠ x := by
  intro hx
  exact realCircleTranslation_ne_one
    (deck.eq_one_of_smul_eq realCircleProjection_covering.isSeparatedMap
      realCircleProjection_covering.isLocalHomeomorph.isLocallyInjective hx)

/-- A deck transformation of the circle covering fixing the origin is the identity. -/
private theorem realCircleDeck_eq_one_of_fixed_origin (g : deck realCircleProjection)
    (hg : g • (0 : ℝ) = 0) : g = 1 :=
  realCircleProjection_covering.eq_one_of_deck_smul_eq hg

end SphereTopologyTest
