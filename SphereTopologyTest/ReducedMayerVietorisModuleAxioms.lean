/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker A, Prism. See README.md for internal reuse.
module

import all SphereTopology.Homology.Singular.ReducedMayerVietoris
import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

/-!
# ReducedMayerVietorisModuleAxioms regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open Lean Elab Command

/-- Diagnose currently loaded names attributed to the reduced Mayer--Vietoris module.
This does not certify full stored-occurrence coverage. -/
local elab "#assert_reduced_mayer_vietoris_module_axioms" : command =>
    Command.runTermElabM fun _ => do
  let env ← getEnv
  let target := `SphereTopology.Homology.Singular.ReducedMayerVietoris
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
    throwError "reduced Mayer--Vietoris module metadata was not found"
  if checked == 0 then
    throwError "empty imported-name diagnostic inventory"
  logInfo m!"Audited {checked} reduced Mayer--Vietoris module declarations"

#assert_reduced_mayer_vietoris_module_axioms

#print axioms AlgebraicTopology.twoOpenReducedMayerVietorisδZero
#print axioms AlgebraicTopology.twoOpenReducedMayerVietorisδZero_ordinary
#print axioms AlgebraicTopology.twoOpenReducedMayerVietoris_exact_intersectionZero
#print axioms AlgebraicTopology.twoOpenReducedMayerVietorisδZero_naturality
#print axioms AlgebraicTopology.twoOpenReducedMayerVietorisδZero_swap_eq_neg
#print axioms AlgebraicTopology.twoOpenReducedMayerVietorisδZero_isIso_of_acyclic_opens
#print axioms AlgebraicTopology.twoOpenReducedMayerVietorisIsoOfAcyclicOpens
