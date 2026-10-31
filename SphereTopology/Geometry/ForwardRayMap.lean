/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Geometry.ForwardRay
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Continuous forward-ray maps to spheres

An ambient-valued continuous map on a closed ball that avoids the inclusion
induces a sphere-valued continuous map: continue the ray from the image through
the original point to its forward intersection with the sphere. If the ambient
map sends boundary points into the closed ball, the sphere map is a left inverse
to the boundary inclusion. No image condition is imposed on interior points.

May's disk argument starts with a fixed-point-free selfmap of the closed disk,
continues the ray from `f(x)` through `x`, observes that the resulting map fixes
the boundary circle, and obtains continuity from a formula. Here the construction
is generalized to real inner-product affine torsors, arbitrary real radii, and
ambient-valued maps, with only a boundary-image condition for the boundary
identity. These are generalizations of that construction, not a fixed-point
theorem in this generality.

## Implementation notes

The formula, sphere membership, and off-diagonal continuity come from
`SphereTopology.Geometry.ForwardRay`; no second intersection formula is defined
here. Bundling and inclusion use Mathlib's `ContinuousMap` API. Continuity of a
bundled map is available through `map_continuous`.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §6,
  printed p. 10 (PDF p. 18): the fixed-point-free disk selfmap and its
  boundary-fixing forward-ray construction. The formula used here is supplied by
  `SphereTopology.Geometry.ForwardRay`, rather than printed in that passage.
* Formal Frontier Agents, `SphereTopology.Geometry.ForwardRay`, for the affine
  forward intersection and its geometric and continuity results.
* Nicolò Cavalleri and Yury Kudryashov's Mathlib `ContinuousMap` formalization,
  including the map constructor and the inclusion API.
-/

@[expose] public section

noncomputable section

namespace EuclideanGeometry

universe u v

variable {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- The sphere-valued forward-ray map associated to a continuous ambient map
avoiding the closed-ball inclusion. Its value at `x` is the forward intersection
of the ray from `f x` through `x` with `s`.

This generalizes May's closed-disk selfmap construction (Chapter 1, §6) to affine
torsors and arbitrary real radii. The map `f` need not take values in the ball;
only avoidance of the inclusion is required. -/
def Sphere.rayInterMap (s : Sphere P)
    (f : C(Metric.closedBall s.center s.radius, P))
    (hf : ∀ x, f x ≠ (x : P)) :
    C(Metric.closedBall s.center s.radius, (s : Set P)) where
  toFun x := ⟨s.rayInter (f x) (x : P), Sphere.rayInter_mem x.property (hf x)⟩
  continuous_toFun := by
    exact ((s.continuousOn_rayInter).comp_continuous
      ((map_continuous f).prodMk continuous_subtype_val)
      (fun x => hf x)).subtype_mk (fun x => Sphere.rayInter_mem x.property (hf x))

/-- The ambient value of the sphere-valued forward-ray map. -/
@[simp]
theorem Sphere.coe_rayInterMap_apply (s : Sphere P)
    (f : C(Metric.closedBall s.center s.radius, P))
    (hf : ∀ x, f x ≠ (x : P)) (x : Metric.closedBall s.center s.radius) :
    (s.rayInterMap f hf x : P) = s.rayInter (f x) (x : P) :=
  rfl

section Boundary

variable (s : Sphere P)

local notation "B" => Metric.closedBall s.center s.radius
local notation "S" => (s : Set P)
local notation "ι" =>
  (ContinuousMap.inclusion
    (Metric.sphere_subset_closedBall (x := s.center) (ε := s.radius)) : C(S, B))

/-- If the ambient map sends boundary points into the closed ball, its forward-ray
map is a left inverse to the boundary inclusion. This generalizes the
boundary-fixing step in May's disk argument, Chapter 1, §6: only boundary images,
not all images, are required to lie in the ball. -/
theorem Sphere.leftInverse_rayInterMap (f : C(B, P))
    (hf : ∀ x, f x ≠ (x : P)) (hboundary : ∀ y : S, f (ι y) ∈ B) :
    Function.LeftInverse (s.rayInterMap f hf) ι := by
  intro y
  apply Subtype.ext
  rw [Sphere.coe_rayInterMap_apply]
  exact Sphere.rayInter_eq_of_mem (hboundary y) y.property

/-- The bundled boundary identity for the forward-ray map, under the same
boundary-only image condition as `Sphere.leftInverse_rayInterMap`. -/
theorem Sphere.rayInterMap_comp_inclusion (f : C(B, P))
    (hf : ∀ x, f x ≠ (x : P)) (hboundary : ∀ y : S, f (ι y) ∈ B) :
    (s.rayInterMap f hf).comp ι = ContinuousMap.id S := by
  exact ContinuousMap.ext (s.leftInverse_rayInterMap f hf hboundary)

/-- A fixed-point-free continuous closed-ball selfmap yields a forward-ray map
that is a left inverse to the boundary inclusion. This is the selfmap
specialization of `Sphere.leftInverse_rayInterMap`. -/
theorem Sphere.leftInverse_rayInterMap_of_self_map (g : C(B, B))
    (hg : ∀ x, g x ≠ x) :
    Function.LeftInverse
      (s.rayInterMap ((ContinuousMap.subtypeVal B).comp g)
        (fun x h => hg x (Subtype.ext h))) ι := by
  exact s.leftInverse_rayInterMap ((ContinuousMap.subtypeVal B).comp g)
    (fun x h => hg x (Subtype.ext h)) (fun y => (g (ι y)).property)

end Boundary

end EuclideanGeometry
