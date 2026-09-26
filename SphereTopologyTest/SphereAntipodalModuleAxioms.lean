/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker A, Prism. See README.md for internal reuse.
module

import all SphereTopology.Homology.Singular.SphereAntipodal
import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

/-!
# SphereAntipodalModuleAxioms regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open Lean Elab Command

/-- Diagnose currently loaded names attributed to the antipodal-action module.
This does not certify full stored-occurrence coverage. -/
local elab "#assert_sphere_antipodal_module_axioms" : command =>
    Command.runTermElabM fun _ => do
  let env ← getEnv
  let target := `SphereTopology.Homology.Singular.SphereAntipodal
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
    throwError "sphere antipodal module metadata was not found"
  if checked == 0 then
    throwError "empty imported-name diagnostic inventory"
  logInfo m!"Audited {checked} sphere antipodal module declarations"

#assert_sphere_antipodal_module_axioms

#print axioms SphereTopology.sphere2Antipodal
#print axioms SphereTopology.sphere2Antipodal_mapsTo_north_south
#print axioms SphereTopology.sphere2Antipodal_mapsTo_south_north
#print axioms SphereTopology.sphere2PunctureIntersectionAntipodalInduced_eq
#print axioms SphereTopology.sphere2EquatorHalfTurnVector_norm
#print axioms SphereTopology.sphere2EquatorHalfTurnHomotopy
#print axioms SphereTopology.sphere2PunctureIntersectionRadialPoint_antipodal
#print axioms SphereTopology.sphere2PunctureIntersectionAntipodal_homotopic_id
#print axioms SphereTopology.sphere2PunctureIntersectionAntipodal_homology_eq_id
#print axioms SphereTopology.sphere2MayerVietorisδOne_reversed_isIso
#print axioms SphereTopology.integralSingularHomologyMap_sphere2Antipodal_two
#print axioms SphereTopology.reducedSingularHomologyMap_sphere2Antipodal_two
#print axioms SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso_antipodal
#print axioms SphereTopology.sphere2_id_not_homotopic_antipodal
