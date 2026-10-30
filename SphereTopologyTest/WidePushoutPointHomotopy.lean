/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology
import Mathlib.Tactic.FunProp

/-!
# A countable family of intervals with endpoint-zero contractions

The relative contraction is `(s,t) ↦ (1-s)*t`. The same data give both a
contraction of the wide pushout and a homotopy equivalence to the wide pushout
of a countable family of points. Each interval inclusion still separates
zero and one.
-/

open CategoryTheory CategoryTheory.Limits

namespace SphereTopologyTest.WidePushoutPointHomotopy

private def intervalZeroContraction :
    ContinuousMap.HomotopyRel (ContinuousMap.id unitInterval)
      (ContinuousMap.const unitInterval (0 : unitInterval)) {0} where
  toFun p := unitInterval.symm p.1 * p.2
  continuous_toFun := by fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' s t ht := by
    have ht : t = 0 := Set.mem_singleton_iff.mp ht
    subst t
    simp

private def pointInverseHomotopy :
    ContinuousMap.HomotopyRel
      ((ContinuousMap.const unitInterval PUnit.unit).comp
        (ContinuousMap.const PUnit (0 : unitInterval)))
      (ContinuousMap.id PUnit) {PUnit.unit} where
  toFun _ := PUnit.unit
  continuous_toFun := continuous_const
  map_zero_left _ := rfl
  map_one_left _ := Subsingleton.elim _ _
  prop' _ _ _ := rfl

set_option quotPrecheck false in
local notation "intervals" => (fun _ : ℕ ↦ TopCat.of unitInterval)
set_option quotPrecheck false in
local notation "zeros" => (fun _ : ℕ ↦ (0 : unitInterval))
set_option quotPrecheck false in
local notation "points" => (fun _ : ℕ ↦ TopCat.of PUnit.{1})
set_option quotPrecheck false in
local notation "units" => (fun _ : ℕ ↦ PUnit.unit)

example : ContractibleSpace
    (widePushout (TopCat.of PUnit.{1}) intervals (fun _ ↦ TopCat.const (0 : unitInterval)) :
      TopCat) :=
  TopCat.contractibleSpace_widePushout_point_of_contractions
    (J := ℕ) (X := intervals) zeros
    (fun _ ↦ intervalZeroContraction)

private noncomputable def intervalFamilyEquivalence : ContinuousMap.HomotopyEquiv
    (widePushout (TopCat.of PUnit.{1}) intervals (fun _ ↦ TopCat.const (0 : unitInterval)) :
      TopCat)
    (widePushout (TopCat.of PUnit.{1}) points (fun _ ↦ TopCat.const PUnit.unit) : TopCat) :=
  TopCat.widePushoutPointHomotopyEquiv
    (J := ℕ) (X := intervals) (Y := points) zeros units
    (fun _ ↦ ContinuousMap.const unitInterval PUnit.unit) (fun _ ↦ rfl)
    (fun _ ↦ ContinuousMap.const PUnit (0 : unitInterval))
    (fun _ ↦ intervalZeroContraction.symm) (fun _ ↦ pointInverseHomotopy)

example (j : ℕ) :
    WidePushout.ι (fun _ : ℕ ↦ (TopCat.const (0 : unitInterval) :
      TopCat.of PUnit.{1} ⟶ TopCat.of unitInterval)) j (0 : unitInterval) ≠
    WidePushout.ι (fun _ : ℕ ↦ (TopCat.const (0 : unitInterval) :
      TopCat.of PUnit.{1} ⟶ TopCat.of unitInterval)) j (1 : unitInterval) := by
  apply (TopCat.isEmbedding_widePushout_point_ι intervals zeros j).injective.ne
  intro h
  have h' : (0 : ℝ) = 1 := congrArg (fun t : unitInterval ↦ (t : ℝ)) h
  exact zero_ne_one h'

end SphereTopologyTest.WidePushoutPointHomotopy
