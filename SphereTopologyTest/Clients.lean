/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker A, Prism. See README.md for internal reuse.
module

import SphereTopology
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Clients regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace SphereTopologyTest

private theorem case001 {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : C(X, E)) (hV : ∀ x, V x ≠ 0) (x : X) :
    ‖ContinuousMap.normalizeOfNoZero V hV x‖ = 1 := by
  simp

private noncomputable def case002 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : C(Metric.sphere (0 : E) 1, E))
    (hW_norm : ∀ p, ‖W p‖ = 1)
    (hW_orth : ∀ p, inner ℝ p.1 (W p) = 0) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (Metric.sphere (0 : E) 1))
      (Metric.Sphere.antipodal (E := E)) :=
  Metric.Sphere.homotopyAntipodalOfUnitOrthogonal W hW_norm hW_orth

private noncomputable def case003 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : C(Metric.sphere (0 : E) 1, E))
    (hV_ne : ∀ p, V p ≠ 0)
    (hV_orth : ∀ p, inner ℝ p.1 (V p) = 0) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (Metric.sphere (0 : E) 1))
      (Metric.Sphere.antipodal (E := E)) :=
  Metric.Sphere.homotopyAntipodalOfNowhereZeroOrthogonal V hV_ne hV_orth

private noncomputable def case004
    (V : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      EuclideanSpace ℝ (Fin 3)))
    (hV_ne : ∀ p, V p ≠ 0)
    (hV_orth : ∀ p, inner ℝ p.1 (V p) = 0) :
    ContinuousMap.Homotopy
      (ContinuousMap.id
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
      (Metric.Sphere.antipodal (E := EuclideanSpace ℝ (Fin 3))) :=
  Metric.Sphere.homotopyAntipodalOfNowhereZeroOrthogonal V hV_ne hV_orth

end SphereTopologyTest
