/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Topology.WidePushout.SubsetRetraction
import Mathlib.Analysis.Complex.Circle

/-!
# Support and factor preimages in an infinite family of circles

An entire circle factor is a compact subset with nonempty singleton support;
the common point has empty support. A path-connected subset containing that
point has path-connected factor preimages and continuous retractions onto them.
The examples use the stock complex circle and the public support and retraction
APIs, without any alternative circle or wedge model.
-/

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

private abbrev circles : ℕ → TopCat := fun _ ↦ TopCat.of Circle
private abbrev points : ∀ i, circles i := fun _ ↦ (1 : Circle)
private abbrev arrows := fun i ↦
  (TopCat.const (points i) : TopCat.of PUnit ⟶ circles i)

private theorem whole_circle_compact (i : ℕ) :
    IsCompact (range (WidePushout.ι arrows i)) :=
  isCompact_range (WidePushout.ι arrows i).hom.continuous

private theorem whole_circle_support (i : ℕ) :
    TopCat.widePushoutPointSupport points (range (WidePushout.ι arrows i)) = {i} :=
  TopCat.widePushoutPointSupport_range_ι points i ⟨-1, Circle.neg_ne_self 1⟩

private theorem common_point_support :
    TopCat.widePushoutPointSupport points {WidePushout.head arrows PUnit.unit} = ∅ :=
  TopCat.widePushoutPointSupport_head points

private theorem whole_circle_finite_support (i : ℕ) :
    (TopCat.widePushoutPointSupport points (range (WidePushout.ι arrows i))).Finite :=
  TopCat.finite_widePushoutPointSupport points (whole_circle_compact i)

private abbrev emptyArrows := fun _ : Empty ↦
  (TopCat.const PUnit.unit : TopCat.of PUnit ⟶ TopCat.of PUnit)

private theorem empty_family_needs_head :
    ¬ ({WidePushout.head emptyArrows PUnit.unit} :
      Set (widePushout (TopCat.of PUnit) (fun _ : Empty ↦ TopCat.of PUnit)
        emptyArrows : TopCat)) ⊆ ⋃ i : Empty, range (WidePushout.ι emptyArrows i) := by
  intro h
  have he := h (mem_singleton (WidePushout.head emptyArrows PUnit.unit))
  simp at he

private theorem path_connected_factor_preimage
    {C : Set (widePushout (TopCat.of PUnit) circles arrows : TopCat)}
    (hC : WidePushout.head arrows PUnit.unit ∈ C) (h : IsPathConnected C) (i : ℕ) :
    IsPathConnected (WidePushout.ι arrows i ⁻¹' C) ∧
      Function.LeftInverse (TopCat.widePushoutPointSubsetRetraction points hC i)
        ((WidePushout.ι arrows i).hom.restrictPreimage C) :=
  ⟨(TopCat.isPathConnected_widePushout_point_preimage_iff points hC).mp h i,
    TopCat.leftInverse_widePushoutPointSubsetRetraction points hC i⟩
