/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker A, Formalization Worker B, Prism.
-- See README.md for internal reuse.
module

import all SphereTopology.Homology.Singular.Reduced

/-!
# ReducedAxioms regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

#print axioms SSet.homologyZeroPoint
#print axioms SSet.homologyZeroPoint_homology₀Iso
#print axioms SSet.homologyZeroPoint_naturality
#print axioms AlgebraicTopology.integralSingularHomologyFunctor_map
#print axioms TopCat.singularHomologyZeroAugmentation_naturality
#print axioms TopCat.reducedSingularHomologyZeroMap_comp
#print axioms TopCat.reducedSingularHomologyMap_isoOfNeZero
#print axioms TopCat.reducedSingularHomologyMap_eq_of_homotopy
#print axioms TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
#print axioms TopCat.reducedSingularHomologyZeroInclusion
#print axioms TopCat.reducedSingularHomologyZeroInclusion_naturality
#print axioms TopCat.reducedSingularHomologyZeroToOrdinary
#print axioms TopCat.reducedSingularHomologyZeroToOrdinary_naturality
#print axioms TopCat.isZero_reducedSingularHomologyZero_of_contractible
#print axioms TopCat.isZero_reducedSingularHomologyZero_empty
#print axioms TopCat.isZero_reducedSingularHomology_onePoint
#print axioms TopCat.isZero_reducedSingularHomology_of_contractible
#print axioms TopCat.reducedSingularHomologyZeroTwoPointIntegerIso
#print axioms TopCat.twoPointReducedBasis_swap
#print axioms TopCat.reducedSingularHomologyZeroTwoPointIntegerIso_swap
