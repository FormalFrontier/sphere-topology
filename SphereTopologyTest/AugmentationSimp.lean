/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism. New bounded simp compatibility clients; see issue 14.
module

import SphereTopology.Homology.Singular.Subdivision

/-!
# Degree-zero subdivision augmentation simplification clients

Ordinary imports test default, restricted and explicitly named simplification,
including the zero-dimensional ambient simplex and signed chain operations.
These private clients do not claim compatibility with every possible simp set.
-/

open Convexity.StdSimplex

namespace SphereTopologyAugmentationClient

private theorem ordinary {m : ℕ} (a : AffineSimplex m 0) :
    affineAugmentation m (subdivideSimplex 0 a) = 1 := by
  simp

private theorem restricted {m : ℕ} (a : AffineSimplex m 0) :
    affineAugmentation m (subdivideSimplex 0 a) = 1 := by
  simp [-subdivideSimplex_zero, -affineAugmentation_single]

private theorem namedOnly {m : ℕ} (a : AffineSimplex m 0) :
    affineAugmentation m (subdivideSimplex 0 a) = 1 := by
  simp only [affineAugmentation_subdivide_zero]

private theorem namedRewrite {m : ℕ} (a : AffineSimplex m 0) :
    affineAugmentation m (subdivideSimplex 0 a) = 1 := by
  rw [affineAugmentation_subdivide_zero]

private theorem ambientZero (a : AffineSimplex 0 0) :
    affineAugmentation 0 (subdivideSimplex 0 a) = 1 := by
  simp [-subdivideSimplex_zero, -affineAugmentation_single]

private theorem signedSum {m : ℕ} (a b : AffineSimplex m 0) (z : ℤ) :
    affineAugmentation m (z • subdivideSimplex 0 a - subdivideSimplex 0 b) = z - 1 := by
  simp [-subdivideSimplex_zero, -affineAugmentation_single]

private theorem wholeChain {m : ℕ} (c : AffineChain m 0) :
    affineAugmentation m (affineSubdivision m 0 c) = affineAugmentation m c := by
  exact affineAugmentation_affineSubdivision_zero c

private theorem repeatedSubdivision {m : ℕ} (a : AffineSimplex m 0) :
    affineAugmentation m (affineSubdivision m 0 (subdivideSimplex 0 a)) = 1 := by
  rw [affineAugmentation_affineSubdivision_zero]
  simp [-subdivideSimplex_zero, -affineAugmentation_single]

private theorem boundaryZero {m : ℕ} (a : AffineSimplex m 1) :
    affineAugmentation m (affineBoundaryGenerator a) = 0 := by
  exact affineAugmentation_boundaryGenerator_degree_one a

private theorem normalForm {m : ℕ} (a : AffineSimplex m 0) :
    affineAugmentation m (Finsupp.single a 1) = 1 := by
  simp

end SphereTopologyAugmentationClient
