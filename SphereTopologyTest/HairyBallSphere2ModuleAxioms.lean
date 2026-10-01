/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

import all SphereTopology.Homotopy.HairyBallSphere2
import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

/-!
# HairyBallSphere2ModuleAxioms regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open Lean Elab Command

/-- Diagnose currently loaded names attributed to the two-sphere hairy-ball module.
This does not certify full stored-occurrence coverage. -/
local elab "#assert_hairy_ball_sphere2_module_axioms" : command =>
    Command.runTermElabM fun _ => do
  let env ← getEnv
  let target := `SphereTopology.Homotopy.HairyBallSphere2
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
    throwError "hairy-ball sphere2 module metadata was not found"
  if checked == 0 then
    throwError "empty imported-name diagnostic inventory"
  logInfo m!"Audited {checked} hairy-ball sphere2 module declarations"

#assert_hairy_ball_sphere2_module_axioms

#print axioms SphereTopology.sphere2_exists_zero_of_orthogonal_field
