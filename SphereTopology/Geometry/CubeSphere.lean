/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Geometry.OnePointSphere
public import FundamentalGroupoids.Topology.Homotopy.Cube.Coordinates
public import FundamentalGroupoids.Topology.Compactification.OnePoint.Collapse

/-!
# From finite cubes to last-axis spheres

The one-point compactification of the complement of the boundary of the
`n`-cube is identified with the unit sphere in real `(n + 1)`-space. The
coordinate on each open interval is the increasing coordinate supplied by
`Cube.boundaryComplHomeomorphPi`. The real product is identified with Euclidean
space by `PiLp.homeomorph`, without reordering its coordinates. Infinity maps
to `EuclideanSpace.northPoint n`, the last-axis north pole.

`Cube.collapseToSphere` composes this homeomorphism with the collapse of the
cube boundary. Its inverse image of the north pole is exactly the boundary.
The construction includes `n = 0`: the cube point maps to the south pole,
while the separate point at infinity maps to the north pole. No surjectivity
of the collapse map is asserted in dimension zero.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 9, §1,
  p. 65, uses based maps from spheres to describe homotopy groups.
* Fundamental Groupoids supplies the increasing cube coordinates and
  `OnePoint.collapse`, using Mathlib's cube and one-point compactification APIs.
* Mathlib supplies `PiLp.homeomorph` and `Homeomorph.onePointCongr`.
* The sphere coordinates and last-axis pole are those of this library's
  `EuclideanSpace.onePointHomeomorphSphere`.
-/

@[expose] public section

noncomputable section

open scoped unitInterval Topology OnePoint

namespace Cube

/-- Compactify the increasing coordinates on the boundary complement of a finite
cube and use inverse stereographic projection at the last-axis north pole. -/
def onePointBoundaryComplHomeomorphSphere (n : ℕ) :
    OnePoint ((boundary (Fin n))ᶜ : Set (I^(Fin n))) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ((boundaryComplHomeomorphPi (Fin n)).trans
    (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).symm).onePointCongr.trans
      (EuclideanSpace.onePointHomeomorphSphere n)

/-- The point at infinity maps to the specified last-axis north pole. -/
@[simp]
theorem onePointBoundaryComplHomeomorphSphere_apply_infty (n : ℕ) :
    onePointBoundaryComplHomeomorphSphere n ∞ = EuclideanSpace.northPoint n := by
  change EuclideanSpace.onePointHomeomorphSphere n ∞ = _
  exact EuclideanSpace.onePointHomeomorphSphere_apply_infty n

/-- The inverse sends the north pole to infinity. -/
@[simp]
theorem onePointBoundaryComplHomeomorphSphere_symm_apply_northPoint (n : ℕ) :
    (onePointBoundaryComplHomeomorphSphere n).symm (EuclideanSpace.northPoint n) =
      ∞ := by
  apply (onePointBoundaryComplHomeomorphSphere n).symm_apply_eq.mpr
  exact (onePointBoundaryComplHomeomorphSphere_apply_infty n).symm

/-- A finite point is sent through the increasing cube coordinates, in their
original order, and then through the Euclidean one-point sphere comparison. -/
theorem onePointBoundaryComplHomeomorphSphere_apply_coe (n : ℕ)
    (u : ((boundary (Fin n))ᶜ : Set (I^(Fin n)))) :
    onePointBoundaryComplHomeomorphSphere n
        (u : OnePoint ((boundary (Fin n))ᶜ : Set (I^(Fin n)))) =
      EuclideanSpace.onePointHomeomorphSphere n
        ((WithLp.toLp 2 (boundaryComplHomeomorphPi (Fin n) u) :
          EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) := by
  rfl

/-- Collapse the boundary of the finite cube to the north pole, retaining the
increasing coordinate convention on its complement. -/
def collapseToSphere (n : ℕ) :
    C(I^(Fin n), Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  (onePointBoundaryComplHomeomorphSphere n :
      C(OnePoint ((boundary (Fin n))ᶜ : Set (I^(Fin n))),
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).comp
    (OnePoint.collapse
      (⟨(boundary (Fin n))ᶜ, (isClosed_boundary (Fin n)).isOpen_compl⟩ :
        TopologicalSpace.Opens (I^(Fin n))))

/-- On the boundary complement, the collapse agrees with the finite-point
inclusion followed by the sphere homeomorphism. -/
theorem collapseToSphere_apply_coe (n : ℕ)
    (u : ((boundary (Fin n))ᶜ : Set (I^(Fin n)))) :
    collapseToSphere n u.val = onePointBoundaryComplHomeomorphSphere n
      (u : OnePoint ((boundary (Fin n))ᶜ : Set (I^(Fin n)))) := by
  exact congrArg (onePointBoundaryComplHomeomorphSphere n)
    (OnePoint.collapse_coe
      (⟨(boundary (Fin n))ᶜ, (isClosed_boundary (Fin n)).isOpen_compl⟩ :
        TopologicalSpace.Opens (I^(Fin n))) u)

/-- Exactly the cube boundary maps to the north pole. This includes the empty
boundary in dimension zero. -/
@[simp]
theorem collapseToSphere_eq_northPoint_iff (n : ℕ) (t : I^(Fin n)) :
    collapseToSphere n t = EuclideanSpace.northPoint n ↔
      t ∈ boundary (Fin n) := by
  change onePointBoundaryComplHomeomorphSphere n
      (OnePoint.collapse
        (⟨(boundary (Fin n))ᶜ, (isClosed_boundary (Fin n)).isOpen_compl⟩ :
          TopologicalSpace.Opens (I^(Fin n))) t) = _ ↔ _
  rw [← onePointBoundaryComplHomeomorphSphere_apply_infty n,
    (onePointBoundaryComplHomeomorphSphere n).injective.eq_iff,
    OnePoint.collapse_eq_infty_iff]
  simp only [TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, not_not]

/-- The unique point of the zero-dimensional cube maps to the south pole. -/
@[simp]
theorem collapseToSphere_zero (t : I^(Fin 0)) :
    collapseToSphere 0 t = -EuclideanSpace.northPoint 0 := by
  let u : ((boundary (Fin 0))ᶜ : Set (I^(Fin 0))) :=
    ⟨t, mem_boundary_compl_iff.mpr (fun i ↦ Fin.elim0 i)⟩
  have hzero : (WithLp.toLp 2 (boundaryComplHomeomorphPi (Fin 0) u) :
      EuclideanSpace ℝ (Fin 0)) = 0 := by
    apply PiLp.ext
    intro i
    exact Fin.elim0 i
  simpa only [onePointBoundaryComplHomeomorphSphere_apply_coe, hzero,
    EuclideanSpace.onePointHomeomorphSphere_apply_zero] using collapseToSphere_apply_coe 0 u

end Cube
