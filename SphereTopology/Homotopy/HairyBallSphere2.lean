/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

public import SphereTopology.Homology.Singular.SphereAntipodal

/-!
# A hairy-ball consequence for the standard two-sphere

This module combines the tangent-field homotopy with the integral-homology
obstruction for the literal standard metric two-sphere.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace SphereTopology

/-- Every continuous field orthogonal to the radius on the standard two-sphere
vanishes somewhere. -/
theorem sphere2_exists_zero_of_orthogonal_field
    (V : C(sphere2, E3))
    (hV_orth : ∀ p, inner ℝ p.1 (V p) = 0) :
    ∃ p, V p = 0 := by
  by_contra hV_zero
  have hV_ne : ∀ p, V p ≠ 0 := by
    intro p hp
    exact hV_zero ⟨p, hp⟩
  have hHomotopy :=
    Metric.Sphere.homotopyAntipodalOfNowhereZeroOrthogonal V hV_ne hV_orth
  apply sphere2_id_not_homotopic_antipodal
  change ContinuousMap.Homotopic (ContinuousMap.id sphere2)
    (Metric.Sphere.antipodal (E := E3))
  exact ⟨hHomotopy⟩

end SphereTopology
