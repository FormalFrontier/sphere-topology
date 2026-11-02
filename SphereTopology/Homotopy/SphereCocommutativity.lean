/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.CircleBouquet.FundamentalGroup
public import SphereTopology.Homotopy.HomotopyGroup.SphereCogroup
public import SphereTopology.Homotopy.SphereCogroup

/-!
# Cocommutativity and sharpness of metric sphere cogroups

The sharp criterion states that the specified metric sphere cogroup of sphere
dimension `n + 1` is commutative exactly when `0 < n`. Its carrier, north pole,
universe lift and multiplication remain those of the original metric sphere
and ordered pinch.

The conclusions use Mathlib's `IsCommMonObj` for the existing named
`Metric.Sphere.cogroupMonObj`, the `toMonObj` field of
`Metric.Sphere.cogroupGrpObj`, not a replacement monoid structure. In the
commutative cases this supplies `IsCommMonObj.mul_comm` for the pinch class and,
with the specified group object, `CategoryTheory.Hom.commGroup` for incoming
morphisms in the opposite category. The cartesian structure, its cartesian
braiding and the sphere monoid-object structure are enabled only locally;
commutativity is a named property, not a global instance.

The higher-dimensional case `Metric.Sphere.cogroup_isCommMonObj` concerns
`Metric.Sphere.cogroup (n + 1)`, of sphere dimension `n + 2`. Its proof applies
`HomotopyGroup.mulOppositeEquivSphereHom` to every incoming domain and uses
Mathlib's Eckmann--Hilton commutativity in degree `n + 2`. The group-valued Yoneda
multiplication in this comparison is induced by the same monoid-object data.

For the circle, this library's original two-circle bouquet provides noncommuting
positive loop classes in every ambient universe. The same sphere-map comparison
in degree one, Mathlib's first-homotopy-group comparison and its stock
commutativity-transfer lemmas relate this obstruction to the specified circle
cogroup. The multiplicative opposite in the comparison is distinct from the
categorical opposite. No group structure on zero-sphere classes, change of
based-homotopy category or extra condition on based target spaces is involved.

## References

* Mathlib supplies `IsCommMonObj`, its incoming-morphism commutativity criterion,
  the Eckmann--Hilton commutativity of higher homotopy groups,
  `HomotopyGroup.pi1MulEquivFundamentalGroup`,
  `Function.Surjective.isMulCommutative` and
  `MulOpposite.isMulCommutative_op_iff`.
* This library supplies `HomotopyGroup.mulOppositeEquivSphereHom`, comparing
  the homotopy-group multiplication with the specified sphere cogroup.
  Its `Metric.Sphere.pinch_homotopicRel_swap` also expresses the north-relative
  factor-swap law for the original higher sphere pinch. Its original
  `CircleBouquet.space`, `CircleBouquet.positiveGenerator` and
  `CircleBouquet.positiveGenerator_mul_ne_mul` supply the topological circle
  obstruction with independent ambient and label universes.
* Fundamental Groupoids supplies the underlying based category, its ordinary
  based-homotopy quotient and the named opposite-homotopy cartesian structure.
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

/-- The specified cogroup of the original metric circle is not commutative in
the ordinary opposite based-homotopy category. The obstruction is given by this
library's noncommuting positive generators of the original two-circle bouquet,
through `HomotopyGroup.mulOppositeEquivSphereHom` in degree one and Mathlib's
`HomotopyGroup.pi1MulEquivFundamentalGroup` and stock commutativity-transfer API. -/
theorem cogroup_not_isCommMonObj_zero :
    ¬ IsCommMonObj (cogroupCarrier.{u} 0) := by
  intro h
  let X : BasedTopCat.{u} :=
    BasedTopCat.of (CircleBouquet.space.{u, 0} (Fin 2))
      (CircleBouquet.basepoint.{u, 0} (Fin 2))
  have hhom := (isCommMonObj_iff_isMulCommutative (cogroupCarrier.{u} 0)).1 h
    (Opposite.op ((BasedTopCat.homotopyQuotient.{u}).obj X))
  let e := HomotopyGroup.mulOppositeEquivSphereHom 0 X
  have hop :
      IsMulCommutative (HomotopyGroup (Fin 1) X.right (BasedTopCat.point X))ᵐᵒᵖ :=
    Function.Surjective.isMulCommutative (f := e.symm) e.symm.surjective hhom
  have hpi : IsMulCommutative (HomotopyGroup (Fin 1) X.right (BasedTopCat.point X)) :=
    MulOpposite.isMulCommutative_op_iff.mp hop
  let e₁ := HomotopyGroup.pi1MulEquivFundamentalGroup
    (X := X.right) (x := BasedTopCat.point X)
  have hfund := Function.Surjective.isMulCommutative (f := e₁) e₁.surjective hpi
  exact CircleBouquet.positiveGenerator_mul_ne_mul.{u, 0}
    (by decide : (1 : Fin 2) ≠ 0) (isMulCommutative_iff.mp hfund _ _)

/-- The specified cogroup of the original metric sphere of dimension `n + 1`
is commutative exactly in sphere dimensions at least two. The successor case is
`cogroup_isCommMonObj`; the excluded circle case is
`cogroup_not_isCommMonObj_zero`, using the original bouquet's positive generators. -/
theorem cogroup_isCommMonObj_iff (n : ℕ) :
    IsCommMonObj (cogroupCarrier.{u} n) ↔ 0 < n := by
  cases n with
  | zero =>
      exact ⟨fun h ↦ (cogroup_not_isCommMonObj_zero h).elim,
        fun h ↦ (Nat.lt_irrefl 0 h).elim⟩
  | succ n =>
      exact ⟨fun _ ↦ Nat.succ_pos n, fun _ ↦ cogroup_isCommMonObj n⟩

end Metric.Sphere
