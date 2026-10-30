/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SphereTopology.Topology.WidePushout.FundamentalGroup

/-!
# A client of point-chart fundamental-group descent

Postcomposing compatible chart data with a homomorphism commutes with descent.
This client derives path connectedness of the open core from its factor inverse
images and uses only the characteristic equations and extensionality API.
-/

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace TopCat

universe u v z z'

variable {I : Type v} {X : I → TopCat.{max u v}} (a : ∀ i, X i)

local notation "P" => TopCat.of PUnit
local notation "f" => (fun i ↦ (TopCat.const (a i) : P ⟶ X i))
local notation "W" => (widePushout P X f : TopCat)
local notation "w" => WidePushout.head f PUnit.unit

private theorem descent_postcomp (C : OpenNhds (X := W) w)
    (hpre : ∀ i, IsPathConnected (WidePushout.ι f i ⁻¹' (C.1 : Set W)))
    (hpcX : ∀ i, IsPathConnected (univ : Set (X i)))
    {G : Type z} [Group G] {H : Type z'} [Group H]
    (hC : FundamentalGroup C.1 ⟨w, C.2⟩ →* G)
    (hU : ∀ i, FundamentalGroup (widePushoutPointChartNhds a C i).1
      ⟨w, (widePushoutPointChartNhds a C i).2⟩ →* G)
    (hcomp : ∀ i, (hU i).comp
      (((FundamentalGroup.openNhdsFunctor w).map
        (homOfLE (le_widePushoutPointChartNhds a C i))).hom) = hC)
    (q : G →* H) :
    let hpcC := isPathConnected_of_widePushout_point_preimage a C.2 hpre
    widePushoutPointChartFundamentalGroupDesc a C hpcC hpcX H
      (q.comp hC) (fun i => q.comp (hU i))
      (fun i => (MonoidHom.comp_assoc _ (hU i) q).trans
        (congrArg (fun k => q.comp k) (hcomp i))) =
        q.comp (widePushoutPointChartFundamentalGroupDesc a C hpcC hpcX G hC hU hcomp) := by
  let hpcC := isPathConnected_of_widePushout_point_preimage a C.2 hpre
  exact (eq_widePushoutPointChartFundamentalGroupDesc a C hpcC hpcX H
    (q.comp hC) (fun i => q.comp (hU i))
    (fun i => (MonoidHom.comp_assoc _ (hU i) q).trans
      (congrArg (fun k => q.comp k) (hcomp i)))
    (q.comp (widePushoutPointChartFundamentalGroupDesc a C hpcC hpcX G hC hU hcomp))
    ((MonoidHom.comp_assoc _ _ q).trans
      (congrArg (fun k => q.comp k)
        (widePushoutPointChartFundamentalGroupDesc_comp_core a C hpcC hpcX G hC hU hcomp)))
    (fun i => (MonoidHom.comp_assoc _ _ q).trans
      (congrArg (fun k => q.comp k)
        (widePushoutPointChartFundamentalGroupDesc_comp_chart a C hpcC hpcX G hC hU hcomp i)))).symm
