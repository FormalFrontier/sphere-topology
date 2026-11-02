/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.HomotopyGroup.SphereCogroup
public import SphereTopology.Homotopy.SphereCogroup

/-!
# Cocommutativity of higher metric sphere cogroups

The specified metric sphere cogroup is commutative as a stock group object in
the ordinary opposite of the based-homotopy category in sphere dimensions at
least two. The sphere dimension is `n + 2`, and the selected group object is
`Metric.Sphere.cogroup (n + 1)`. Its carrier, north pole, universe lift and
multiplication remain those of the original metric sphere and ordered pinch.

The conclusion uses Mathlib's `IsCommMonObj` for the existing named
`Metric.Sphere.cogroupMonObj`, the `toMonObj` field of
`Metric.Sphere.cogroupGrpObj`, not a replacement monoid structure. It supplies
`IsCommMonObj.mul_comm` for the pinch class and, with the specified group object,
`CategoryTheory.Hom.commGroup` for incoming morphisms in the opposite category.
The cartesian structure, its cartesian braiding and the sphere monoid-object
structure are enabled only locally; the commutativity result is a named
property, not a global instance.

The proof applies `HomotopyGroup.mulOppositeEquivSphereHom` to every incoming
domain and uses Mathlib's Eckmann--Hilton commutativity in degree `n + 2`.
The group-valued Yoneda multiplication in this comparison is induced by the
same monoid-object data.

The circle is excluded. No group structure on zero-sphere classes, change of
based-homotopy category or extra condition on based target spaces is involved.

## References

* Mathlib supplies `IsCommMonObj`, its incoming-morphism commutativity criterion
  and the Eckmann--Hilton commutativity of higher homotopy groups.
* This library supplies `HomotopyGroup.mulOppositeEquivSphereHom`, comparing
  the homotopy-group multiplication with the specified sphere cogroup.
  Its `Metric.Sphere.pinch_homotopicRel_swap` also expresses the north-relative
  factor-swap law for the original higher sphere pinch.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

attribute [local instance] BasedTopCat.homotopyOppositeCartesianMonoidalCategory
  CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
  Metric.Sphere.cogroupMonObj

namespace Metric.Sphere

/-- The specified cogroup of the original metric sphere of dimension `n + 2`
is commutative in the ordinary opposite based-homotopy category. The monoid
object is the one underlying `Metric.Sphere.cogroup (n + 1)`, whose multiplication
is the class of the original ordered pinch. The proof uses the sphere-map group
comparison and Mathlib's Eckmann--Hilton commutativity of higher homotopy groups. -/
theorem cogroup_isCommMonObj (n : ℕ) :
    IsCommMonObj (cogroupCarrier.{u} (n + 1)) := by
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro Y
  let e := HomotopyGroup.mulOppositeEquivSphereHom (n + 1) Y.unop.as
  refine ⟨⟨fun f g ↦ ?_⟩⟩
  apply e.symm.injective
  exact (e.symm.map_mul f g).trans
    ((mul_comm (e.symm f) (e.symm g)).trans (e.symm.map_mul g f).symm)

end Metric.Sphere
