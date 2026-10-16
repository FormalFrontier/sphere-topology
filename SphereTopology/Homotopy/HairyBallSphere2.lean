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
obstruction for the standard metric two-sphere in real Euclidean three-space.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Example I.1.2.2, motivates the tangent-field obstruction. That passage rules
  out two independent fields; the theorem here is the stronger one-field
  continuous orthogonal-field result, not the source's algebraic conclusion.
* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 13, §5,
  for the antipodal degree underlying the homology obstruction.
* Formal Frontier Agents' earlier sphere-field proof exposition and the
  tangent-field, ordered-cover and antipodal constructions in this library,
  built on Mathlib's inner-product, homotopy and singular-homology APIs
  (the latter formalized by Joël Riou); see `docs/CREDITS.md`.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace SphereTopology

/-- Every continuous field orthogonal to the radius on the standard two-sphere
vanishes somewhere.

This one-field theorem strengthens the two-independent-field obstruction
motivating Charles A. Weibel, *The K-book: An Introduction to Algebraic
K-theory*, Example I.1.2.2. The project's normalization/rotation and homology
proof uses the antipodal sign (see J. Peter May, *A Concise Course in Algebraic
Topology*, Chapter 13, §5) and Mathlib's homotopy-invariant singular homology.
It does not assert the algebraic kernel or unimodular-row conclusions of Weibel's example. -/
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
