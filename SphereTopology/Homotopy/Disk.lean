/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.CircleDegree
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Circle-valued maps on the closed unit disk

The boundary restriction of a continuous map from the complex closed unit disk
into the circle has degree zero. Consequently, no such map restricts to the
identity on the boundary.

The disk is `Metric.closedBall (0 : ℂ) 1`, and its boundary inclusion is the
stock `ContinuousMap.inclusion` associated to `Metric.sphere_subset_closedBall`.
The circle and degree are the existing `Circle` and `Circle.degree`.

The proof contracts the convex closed ball, postcomposes by the given map,
and restricts the nullhomotopy to the boundary. Free-homotopy invariance of
degree gives zero; the identity has degree one. No basedness is required.

## Limitations

These results concern only the complex closed unit disk and its unit-circle
boundary. They assert neither a higher-dimensional disk theorem nor a converse
extension criterion for circle maps of degree zero.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §6,
  p. 10, for the disk non-retraction theorem, and §7 for circle-map degree.
* Mathlib's convex-set contractibility and nullhomotopy composition APIs,
  together with `SphereTopology.Homotopy.CircleDegree`, supply the underlying
  objects and comparison APIs.
-/

@[expose] public section

namespace Circle

/-- The restriction to the boundary of a circle-valued disk map has degree zero.
This is the degree obstruction underlying May, Chapter 1, §6, p. 10, using §7. -/
theorem degree_comp_closedBall_inclusion
    (G : C(Metric.closedBall (0 : ℂ) 1, Circle)) :
    degree (G.comp
      (ContinuousMap.inclusion
        (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1)) :
          C(Circle, Metric.closedBall (0 : ℂ) 1))) = 0 := by
  let : ContractibleSpace (Metric.closedBall (0 : ℂ) 1) :=
    (convex_closedBall (0 : ℂ) 1).contractibleSpace
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have hG : G.Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using
      (id_nullhomotopic (Metric.closedBall (0 : ℂ) 1)).comp_right G
  obtain ⟨c, hc⟩ := hG.comp_left
    (ContinuousMap.inclusion
      (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1)) :
        C(Circle, Metric.closedBall (0 : ℂ) 1))
  exact (degree_eq_of_homotopic hc).trans (degree_const c)

/-- No continuous disk map is the identity on its boundary.
This is May's disk non-retraction theorem, Chapter 1, §6, p. 10, for the
complex closed unit disk. -/
theorem comp_closedBall_inclusion_ne_id
    (G : C(Metric.closedBall (0 : ℂ) 1, Circle)) :
    G.comp
      (ContinuousMap.inclusion
        (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := 1)) :
          C(Circle, Metric.closedBall (0 : ℂ) 1)) ≠
      ContinuousMap.id Circle := by
  intro h
  have hdeg := congrArg degree h
  exact zero_ne_one
    ((degree_comp_closedBall_inclusion G).symm.trans (hdeg.trans degree_id))

end Circle
