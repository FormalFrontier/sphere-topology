/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker A, Formalization Worker B, Prism.
-- See README.md for internal reuse.
module

import all SphereTopology
import all SphereTopology.Homology.Singular.MayerVietoris

/-!
# Axioms regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open Lean

#print axioms SphereTopology.sphere2_exists_zero_of_orthogonal_field

/- Diagnose the currently loaded module-attributed names, separately from the
explicit list below. This is not a raw stored-occurrence census. -/
run_cmd do
  let env ← getEnv
  let moduleName := `SphereTopology.Homology.Singular.MayerVietoris
  let some moduleIdx := env.getModuleIdx? moduleName
    | throwError "module not found in environment: {moduleName}"
  let declarations := env.checked.get.constants.fold
    (fun names name _ ↦
      if env.getModuleIdxFor? name == some moduleIdx then names.push name else names)
    (#[] : Array Name)
  if declarations.isEmpty then
    throwError "empty module-attributed diagnostic inventory"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut failures : Array (Name × Array Name) := #[]
  for name in declarations do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax ↦ !allowed.contains ax
    unless unexpected.isEmpty do
      failures := failures.push (name, unexpected)
  unless failures.isEmpty do
    throwError "unexpected axioms in {moduleName}: {failures}"
  logInfo m!"module-attributed axiom audit: {moduleName}: \
    {declarations.size} declarations; allowed only {allowed}"

#print axioms ContinuousMap.normalizeOfNoZero
#print axioms ContinuousMap.norm_normalizeOfNoZero
#print axioms Metric.Sphere.antipodal
#print axioms Metric.Sphere.homotopyAntipodalOfUnitOrthogonal
#print axioms Metric.Sphere.homotopyAntipodalOfNowhereZeroOrthogonal

#print axioms Convexity.StdSimplex.affineSubdivision_boundary
#print axioms Convexity.StdSimplex.affineHomotopy_boundary
#print axioms Convexity.StdSimplex.subdivideSimplex_support_verticesIn
#print axioms Convexity.StdSimplex.homotopySimplex_support_verticesIn
#print axioms Convexity.StdSimplex.affineSubdivision_iterate_support_vertexDiameter_le
#print axioms Convexity.StdSimplex.exists_affineSubdivision_iterate_cover_small

#print axioms AlgebraicTopology.singularSubdivision_degree_zero
#print axioms AlgebraicTopology.singularSubdivision_naturality
#print axioms AlgebraicTopology.mem_support_singularSubdivision
#print axioms AlgebraicTopology.singularSubdivision_boundary
#print axioms AlgebraicTopology.singularSubdivisionIterate_boundary
#print axioms AlgebraicTopology.exists_singularSubdivisionIterate_chain_cover_small
#print axioms AlgebraicTopology.singularHomotopy_naturality
#print axioms AlgebraicTopology.mem_support_singularHomotopy
#print axioms AlgebraicTopology.singularHomotopy_boundary
#print axioms AlgebraicTopology.singularHomotopyIterate_degree_zero
#print axioms AlgebraicTopology.singularHomotopyIterate_boundary
#print axioms AlgebraicTopology.isCoverSmall_of_mem_singularHomotopyIterate

#print axioms TopCat.mem_smallSingularSet_iff
#print axioms TopCat.smallSingularSet_mono
#print axioms TopCat.smallSingularSetMap_comp_inclusion
#print axioms AlgebraicTopology.isCoverSmall_zero
#print axioms AlgebraicTopology.smallSingularChainMapOfRefinement_comp_inclusion
#print axioms AlgebraicTopology.smallSingularChainMap_comp_inclusion
#print axioms AlgebraicTopology.quasiIso_smallSingularChainInclusion

#print axioms TopCat.openSingularSet
#print axioms TopCat.mem_openSingularSet_iff
#print axioms TopCat.openSingularSetMap
#print axioms TopCat.openSingularSetMap_comp_inclusion
#print axioms TopCat.openSingularSetMap_comp_inclusion_assoc
#print axioms TopCat.openSingularSetInfMap
#print axioms TopCat.openSingularSetSupMap
#print axioms TopCat.openSingularSetInfMap_comp_left
#print axioms TopCat.openSingularSetInfMap_comp_left_assoc
#print axioms TopCat.openSingularSetInfMap_comp_right
#print axioms TopCat.openSingularSetInfMap_comp_right_assoc
#print axioms TopCat.openSingularSetMap_comp_supLeft
#print axioms TopCat.openSingularSetMap_comp_supLeft_assoc
#print axioms TopCat.openSingularSetMap_comp_supRight
#print axioms TopCat.openSingularSetMap_comp_supRight_assoc
#print axioms TopCat.openSingularSetIso
#print axioms TopCat.twoOpenCover
#print axioms TopCat.isOpenCover_twoOpenCover
#print axioms TopCat.openSingularSet_inf
#print axioms TopCat.openSingularSet_sup
#print axioms TopCat.openMap
#print axioms TopCat.openMap_comp_inclusion
#print axioms TopCat.openMap_comp_inclusion_assoc
#print axioms TopCat.mapsTo_twoOpenCover

#print axioms AlgebraicTopology.openSingularChainIso
#print axioms AlgebraicTopology.isPushout_chainComplexMap
#print axioms AlgebraicTopology.mono_chainComplexMap_subcomplex
#print axioms AlgebraicTopology.subcomplex_inter_union_isPushout
#print axioms AlgebraicTopology.subcomplexUnionShortComplex
#print axioms AlgebraicTopology.subcomplexUnionShortExact
#print axioms AlgebraicTopology.subcomplexInfSwapChainIso
#print axioms AlgebraicTopology.subcomplexSupSwapChainIso
#print axioms AlgebraicTopology.subcomplexUnionSwapIso
#print axioms AlgebraicTopology.subcomplexUnionδ
#print axioms AlgebraicTopology.subcomplexUnion_exact₁
#print axioms AlgebraicTopology.subcomplexUnion_exact₂
#print axioms AlgebraicTopology.subcomplexUnion_exact₃
#print axioms AlgebraicTopology.subcomplexUnionδ_swap
#print axioms AlgebraicTopology.integralSingularChains
#print axioms AlgebraicTopology.integralSingularChainMap
#print axioms AlgebraicTopology.twoOpenIntersectionToLeft
#print axioms AlgebraicTopology.twoOpenIntersectionToRight
#print axioms AlgebraicTopology.twoOpenIntersectionToLeft_comp
#print axioms AlgebraicTopology.twoOpenIntersectionToLeft_comp_assoc
#print axioms AlgebraicTopology.twoOpenIntersectionToRight_comp
#print axioms AlgebraicTopology.twoOpenIntersectionToRight_comp_assoc
#print axioms AlgebraicTopology.twoOpenDifferenceChainMap
#print axioms AlgebraicTopology.twoOpenSumChainMap
#print axioms AlgebraicTopology.twoOpenDifference_comp_sum
#print axioms AlgebraicTopology.twoOpenDifference_comp_sum_assoc
#print axioms AlgebraicTopology.twoOpenIntersectionMap
#print axioms AlgebraicTopology.twoOpenBiprodChainMap
#print axioms AlgebraicTopology.twoOpenSmallChainMap
#print axioms AlgebraicTopology.twoOpenAmbientShortComplex
#print axioms AlgebraicTopology.twoOpenAmbientShortComplexMap
#print axioms AlgebraicTopology.twoOpenIntersectionChainIso
#print axioms AlgebraicTopology.twoOpenBiprodChainIso
#print axioms AlgebraicTopology.twoOpenUnionChainIso
#print axioms AlgebraicTopology.twoOpenSmallShortComplex
#print axioms AlgebraicTopology.twoOpenSmallToAmbientIso
#print axioms AlgebraicTopology.twoOpenSmallShortExact
#print axioms AlgebraicTopology.twoOpenSmallShortComplexSwapIso
#print axioms AlgebraicTopology.twoOpenIntersectionSwapChainIso
#print axioms AlgebraicTopology.twoOpenCoverSwapChainIso
#print axioms AlgebraicTopology.twoOpenCoverSwapChainIso_comp_inclusion
#print axioms AlgebraicTopology.twoOpenCoverSwapChainIso_comp_inclusion_assoc
#print axioms AlgebraicTopology.twoOpenSmallShortComplexMap
#print axioms AlgebraicTopology.twoOpenSmallShortComplexMap_comp_inclusion
#print axioms AlgebraicTopology.twoOpenSmallShortComplexMap_comp_inclusion_assoc
#print axioms AlgebraicTopology.integralSingularHomology
#print axioms AlgebraicTopology.smallSingularHomologyIso
#print axioms AlgebraicTopology.twoOpenSpaceHomologyIso
#print axioms AlgebraicTopology.twoOpenMiddleHomologyIso
#print axioms AlgebraicTopology.twoOpenMayerVietorisδ
#print axioms AlgebraicTopology.twoOpenMayerVietorisSwapSpaceMap
#print axioms AlgebraicTopology.twoOpenMayerVietorisSwapSpaceMap_eq_id
#print axioms AlgebraicTopology.twoOpenMayerVietorisδ_swap
#print axioms AlgebraicTopology.twoOpenMayerVietorisδ_swap_eq_neg
#print axioms AlgebraicTopology.twoOpenMayerVietorisToSpace
#print axioms AlgebraicTopology.twoOpenMayerVietorisFromIntersection
#print axioms AlgebraicTopology.twoOpenMayerVietorisFromBiprod
#print axioms AlgebraicTopology.twoOpenMayerVietorisδ_comp
#print axioms AlgebraicTopology.twoOpenMayerVietorisδ_comp_assoc
#print axioms AlgebraicTopology.twoOpenMayerVietoris_comp_toSpace
#print axioms AlgebraicTopology.twoOpenMayerVietoris_comp_toSpace_assoc
#print axioms AlgebraicTopology.twoOpenMayerVietoris_toSpace_comp_δ
#print axioms AlgebraicTopology.twoOpenMayerVietoris_toSpace_comp_δ_assoc
#print axioms AlgebraicTopology.twoOpenMayerVietorisIntersectionMap
#print axioms AlgebraicTopology.twoOpenMayerVietorisSpaceMap
#print axioms AlgebraicTopology.twoOpenMayerVietorisSpaceMap_eq
#print axioms AlgebraicTopology.twoOpenMayerVietorisδ_naturality
#print axioms AlgebraicTopology.twoOpenMayerVietorisδ_naturality_induced
#print axioms AlgebraicTopology.twoOpenMayerVietoris_exact_intersection
#print axioms AlgebraicTopology.twoOpenMayerVietoris_exact_middle
#print axioms AlgebraicTopology.twoOpenMayerVietoris_exact_space
#print axioms AlgebraicTopology.twoOpenMayerVietoris_exact_at_intersection
#print axioms AlgebraicTopology.twoOpenMayerVietoris_exact_at_biprod
#print axioms AlgebraicTopology.twoOpenMayerVietoris_exact_at_space
#print axioms AlgebraicTopology.twoOpenSmallShortComplex_f_eq_difference
#print axioms AlgebraicTopology.twoOpenIntersectionHomologyIso
#print axioms AlgebraicTopology.integralSingularChainMap_twoOpenIntersectionMap
#print axioms AlgebraicTopology.twoOpenMayerVietorisIntersectionMap_eq
#print axioms AlgebraicTopology.twoOpenIntersectionSwapMap
#print axioms AlgebraicTopology.integralSingularChainMap_twoOpenIntersectionSwapMap
#print axioms AlgebraicTopology.twoOpenIntersectionSwapMap_comp
#print axioms AlgebraicTopology.integralSingularHomologyMap_eq_neg_id_of_twoOpen_swap
#print axioms AlgebraicTopology.twoOpenMayerVietorisδ_isIso_of_isZero_outer
