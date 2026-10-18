/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Homotopy.CircleBouquet

/-!
# Circle-bouquet clients

The two-circle bouquet uses the positive loops in the original circle.
Retraction computes a positive generator's existing circle coordinate.
The empty-family boundary retains the common point.
-/

noncomputable section

open CategoryTheory

universe u

namespace SphereTopologyTest

/-- In the two-circle bouquet, the first positive free generator retracts to the
circle class with coordinate one. -/
private theorem two_circle_generator_coordinate :
    Circle.fundamentalGroupEquivInt
      (FundamentalGroup.mapOfEq (CircleBouquet.retraction.{u, 0} false)
        (CircleBouquet.retraction_basepoint.{u, 0} false)
        (CircleBouquet.generatorMap.{u, 0} Bool (FreeGroup.of false))) =
      Multiplicative.ofAdd (1 : ℤ) := by
  rw [CircleBouquet.generatorMap_of, CircleBouquet.retraction_positiveGenerator,
    Circle.fundamentalGroupEquivInt_loop]

/-- With no circles, the head still supplies exactly the one common point. -/
private theorem empty_bouquet_point (x : CircleBouquet.space.{u, 0} Empty) :
    x = CircleBouquet.basepoint.{u, 0} Empty := by
  have h : (𝟙 (CircleBouquet.space.{u, 0} Empty)) =
      TopCat.const (CircleBouquet.basepoint.{u, 0} Empty) := by
    apply CircleBouquet.hom_ext
    · intro i
      cases i
    · rfl
  exact congrArg (fun f : CircleBouquet.space.{u, 0} Empty ⟶
    CircleBouquet.space.{u, 0} Empty ↦ f x) h

end SphereTopologyTest
