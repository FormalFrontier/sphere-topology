/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

import all SphereTopology.Homology.Singular.Circle
import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

/-!
# CircleModuleAxioms regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open Lean Elab Command

/-- Diagnose currently loaded names attributed to the standard-circle module.
This does not certify full stored-occurrence coverage. -/
local elab "#assert_circle_module_axioms" : command =>
    Command.runTermElabM fun _ => do
  let env ← getEnv
  let target := `SphereTopology.Homology.Singular.Circle
  let mut found : Bool := false
  let mut checked : Nat := 0
  for h : i in *...env.header.moduleNames.size do
    if env.header.moduleNames[i] = target then
      found := true
      let data := env.header.moduleData[i]!
      for h' : j in *...data.constNames.size do
        let name := data.constNames[j]
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax = ``propext || ax = ``Classical.choice ||
              ax = ``Quot.sound do
            throwError "{name} depends on disallowed axiom {ax}"
        checked := checked + 1
  unless found do
    throwError "circle module metadata was not found"
  if checked == 0 then
    throwError "empty imported-name diagnostic inventory"
  logInfo m!"Audited {checked} circle module declarations"

#assert_circle_module_axioms

#print axioms SphereTopology.circlePunctured_join
#print axioms SphereTopology.circleEastPuncturedHomeomorph
#print axioms SphereTopology.circleWestPuncturedHomeomorph
#print axioms SphereTopology.circlePunctureIntersectionComponent_eq_false_iff
#print axioms SphereTopology.circlePunctureIntersectionComponent_eq_true_iff
#print axioms SphereTopology.circlePunctureIntersectionRadialHomotopy
#print axioms SphereTopology.circlePunctureIntersectionHomotopyEquiv
#print axioms SphereTopology.circlePunctureIntersectionHomotopyEquivULift
#print axioms SphereTopology.circleEastPunctured_contractibleSpace
#print axioms SphereTopology.circleWestPunctured_contractibleSpace
#print axioms SphereTopology.isZero_reducedSingularHomology_circleEastPunctured
#print axioms SphereTopology.isZero_reducedSingularHomology_circleWestPunctured
#print axioms SphereTopology.reducedSingularHomologyOneSphereOneIntegerIso
#print axioms SphereTopology.reducedSingularHomologyOneSphereOneIntegerIso_hom
#print axioms SphereTopology.reducedSingularHomologyOneSphereOneIntegerIsoReversed
#print axioms SphereTopology.circleReducedMayerVietoris_swap_eq_neg
