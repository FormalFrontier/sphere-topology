/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker A, Prism. See README.md for internal reuse.
module

import SphereTopology

/-!
# SphereAntipodalRoot regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open CategoryTheory

noncomputable section

namespace SphereTopologyTest

open SphereTopology

private theorem case001 : TopCat.reducedSingularHomologyMap sphere2Antipodal 2 = -𝟙 _ :=
  reducedSingularHomologyMap_sphere2Antipodal_two

private theorem case002 : reducedSingularHomologyTwoSphereTwoIntegerIso.inv ≫
      TopCat.reducedSingularHomologyMap sphere2Antipodal 2 ≫
      reducedSingularHomologyTwoSphereTwoIntegerIso.hom =
    -𝟙 (ModuleCat.of ℤ ℤ) :=
  reducedSingularHomologyTwoSphereTwoIntegerIso_antipodal

private theorem case003 : ¬ ContinuousMap.Homotopic (ContinuousMap.id sphere2)
    sphere2Antipodal.hom :=
  sphere2_id_not_homotopic_antipodal

end SphereTopologyTest
