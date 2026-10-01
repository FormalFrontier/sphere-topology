/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

import all SphereTopology.Homology.Singular.Sphere
import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

/-!
# SphereModuleAxioms regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open Lean Elab Command

/-- Diagnose currently loaded names attributed to the standard-two-sphere module.
This does not certify full stored-occurrence coverage. -/
local elab "#assert_sphere_module_axioms" : command =>
    Command.runTermElabM fun _ => do
  let env ← getEnv
  let target := `SphereTopology.Homology.Singular.Sphere
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
    throwError "sphere module metadata was not found"
  if checked == 0 then
    throwError "empty imported-name diagnostic inventory"
  logInfo m!"Audited {checked} sphere module declarations"

#assert_sphere_module_axioms

#print axioms SphereTopology.sphere2Punctured_join
#print axioms SphereTopology.sphere2NorthPuncturedHomeomorph
#print axioms SphereTopology.sphere2SouthPuncturedHomeomorph
#print axioms SphereTopology.sphere2PunctureIntersectionLinearVector_ne_zero
#print axioms SphereTopology.sphere2PunctureIntersectionRadialVector_norm
#print axioms SphereTopology.sphere2PunctureIntersectionRadialPoint_fixed
#print axioms SphereTopology.sphere2PunctureIntersectionToEquator_inclusion
#print axioms SphereTopology.sphere2PunctureIntersectionRadialHomotopy
#print axioms SphereTopology.sphere2PunctureIntersectionEquatorHomotopyEquiv
#print axioms SphereTopology.sphere2PunctureIntersectionEquatorHomotopyEquivULift
#print axioms SphereTopology.sphere2EquatorHomeomorphSphere1
#print axioms SphereTopology.sphere2PunctureIntersectionSphere1HomotopyEquiv
#print axioms SphereTopology.sphere2NorthPunctured_contractibleSpace
#print axioms SphereTopology.sphere2SouthPunctured_contractibleSpace
#print axioms SphereTopology.isZero_reducedSingularHomology_sphere2NorthPunctured
#print axioms SphereTopology.isZero_reducedSingularHomology_sphere2SouthPunctured
#print axioms SphereTopology.sphere2MayerVietorisδOne_isIso
#print axioms SphereTopology.sphere2ReducedMayerVietorisIso
#print axioms SphereTopology.sphere2ReducedMayerVietorisIso_hom
#print axioms SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso
#print axioms SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso_hom
#print axioms SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso_hom_explicit
