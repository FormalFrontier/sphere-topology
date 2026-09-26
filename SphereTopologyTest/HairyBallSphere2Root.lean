/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker B, Prism. See README.md for internal reuse.
module

import SphereTopology

/-!
# HairyBallSphere2Root regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open scoped RealInnerProductSpace

namespace SphereTopologyTest

open SphereTopology

private theorem case001 (V : C(sphere2, E3))
    (hV_orth : ∀ p, inner ℝ p.1 (V p) = 0) :
    ∃ p, V p = 0 :=
  sphere2_exists_zero_of_orthogonal_field V hV_orth

end SphereTopologyTest
