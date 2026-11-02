/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.HomotopyGroup.SphereHom
public import SphereTopology.Homotopy.SphereCogroup
public import Mathlib.Algebra.Group.Opposite

/-!
# Homotopy groups and the sphere cogroup

For every based space `X`, the multiplicative opposite of the finite-cube
homotopy group on `Fin (n + 1)` is compared with the group of sphere maps
specified by `Metric.Sphere.cogroup n` and `CategoryTheory.yonedaGrp`.
The underlying bijection applies `HomotopyGroup.equivSphereHom (n + 1) X`
after `MulOpposite.unop`, then takes the ordinary categorical opposite of the
resulting morphism. Its values are incoming morphisms to the cogroup carrier
in the ordinary opposite based-homotopy category; their unops are outgoing
based-homotopy classes of maps from the lifted metric sphere to `X`.

The multiplicative opposite of the source and the two categorical opposites
in the Yoneda evaluation have different roles. The ordered sphere fold obeys
`Metric.Sphere.pinch_fold_class`: folding `F` on the left and `G` on the right
represents the class of `G` times the class of `F`. This order accounts for the
multiplicative opposite, also when `n = 0` and the sphere is `S¹`.

## Limitations

Only positive-dimensional spheres are considered; no group structure on
zero-sphere classes or commutativity for circle classes is asserted. Targets
are arbitrary based topological spaces in any universe, with no separation,
compactness or connectedness hypothesis. The comparison uses ordinary based
maps and homotopies, not a compactly generated mapping-space convention.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 9, §1,
  for the sphere-class interpretation of based homotopy groups.
* Mathlib supplies `MulOpposite.opEquiv`, `Quiver.Hom.opEquiv` and
  `CategoryTheory.yonedaGrp`, including the group structure on incoming morphisms.
* Fundamental Groupoids supplies the based-homotopy quotient, based
  postcomposition on homotopy groups and the named cartesian structure.
* This library supplies `HomotopyGroup.equivSphereHom`, the metric sphere cogroup
  and the ordered pinch-fold comparison.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

attribute [local instance] BasedTopCat.homotopyOppositeCartesianMonoidalCategory

namespace HomotopyGroup

open CategoryTheory.Limits in
private theorem equivSphereHom_symm_pinchToWedge (n : ℕ) (X : BasedTopCat.{u})
    (k : BasedTopCat.basedWedge
      (pairFunction (Metric.Sphere.basedSpace.{u} n) (Metric.Sphere.basedSpace.{u} n)) ⟶ X) :
    (equivSphereHom (n + 1) X).symm
        (BasedTopCat.homotopyQuotient.map (Metric.Sphere.pinchToWedge n ≫ k)) =
      (equivSphereHom (n + 1) X).symm
          (BasedTopCat.homotopyQuotient.map
            (BasedTopCat.basedWedgeι
              (pairFunction (Metric.Sphere.basedSpace.{u} n) (Metric.Sphere.basedSpace.{u} n))
              WalkingPair.right ≫ k)) *
        (equivSphereHom (n + 1) X).symm
          (BasedTopCat.homotopyQuotient.map
            (BasedTopCat.basedWedgeι
              (pairFunction (Metric.Sphere.basedSpace.{u} n) (Metric.Sphere.basedSpace.{u} n))
              WalkingPair.left ≫ k)) := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1
  let P := pairFunction (Metric.Sphere.basedSpace.{u} n) (Metric.Sphere.basedSpace.{u} n)
  let r : (Metric.Sphere.basedSpace.{u} n ⟶ X) →
      {F : C(S, X.right) // F (EuclideanSpace.northPoint (n + 1)) = BasedTopCat.point X} :=
    fun h ↦ ⟨h.right.hom.comp
      (⟨ULift.up, continuous_uliftUp⟩ : C(S, ULift.{u} S)), BasedTopCat.map_point h⟩
  have hr (h : Metric.Sphere.basedSpace.{u} n ⟶ X) :
      (equivSphereHom (n + 1) X).symm (BasedTopCat.homotopyQuotient.map h) =
        (equivSphereClasses (n + 1) (BasedTopCat.point X)).symm
          (ZerothHomotopy.mk (r h)) :=
    (equivSphereHom_symm_map (n + 1) X h).trans
      (equivSphereClasses_symm_mk (n + 1) (BasedTopCat.point X) (r h)).symm
  have hfold : r (Metric.Sphere.pinchToWedge n ≫ k) =
      Metric.Sphere.pinchFold n (BasedTopCat.point X)
        (r (BasedTopCat.basedWedgeι P WalkingPair.left ≫ k),
         r (BasedTopCat.basedWedgeι P WalkingPair.right ≫ k)) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    exact Metric.Sphere.pinchToWedge_comp_apply n X k s
  calc
    _ = (equivSphereClasses (n + 1) (BasedTopCat.point X)).symm
        (ZerothHomotopy.mk (r (Metric.Sphere.pinchToWedge n ≫ k))) := hr _
    _ = (equivSphereClasses (n + 1) (BasedTopCat.point X)).symm
        (ZerothHomotopy.mk (Metric.Sphere.pinchFold n (BasedTopCat.point X)
          (r (BasedTopCat.basedWedgeι P WalkingPair.left ≫ k),
           r (BasedTopCat.basedWedgeι P WalkingPair.right ≫ k)))) :=
      congrArg (fun F ↦ (equivSphereClasses (n + 1) (BasedTopCat.point X)).symm
        (ZerothHomotopy.mk F)) hfold
    _ = (equivSphereClasses (n + 1) (BasedTopCat.point X)).symm
          (ZerothHomotopy.mk (r (BasedTopCat.basedWedgeι P WalkingPair.right ≫ k))) *
        (equivSphereClasses (n + 1) (BasedTopCat.point X)).symm
          (ZerothHomotopy.mk (r (BasedTopCat.basedWedgeι P WalkingPair.left ≫ k))) :=
      Metric.Sphere.pinch_fold_class n (BasedTopCat.point X)
        (r (BasedTopCat.basedWedgeι P WalkingPair.left ≫ k))
        (r (BasedTopCat.basedWedgeι P WalkingPair.right ≫ k))
    _ = _ := congrArg₂ (fun a b : HomotopyGroup (Fin (n + 1)) X.right
        (BasedTopCat.point X) ↦ a * b)
      (hr (BasedTopCat.basedWedgeι P WalkingPair.right ≫ k)).symm
      (hr (BasedTopCat.basedWedgeι P WalkingPair.left ≫ k)).symm

open CategoryTheory.Limits in
private theorem equivSphereHom_symm_mul (n : ℕ) (X : BasedTopCat.{u})
    (f g : ↥((CategoryTheory.yonedaGrp.obj (Metric.Sphere.cogroup.{u} n)).obj
      (Opposite.op (Opposite.op ((BasedTopCat.homotopyQuotient.{u}).obj X))))) :
    (equivSphereHom (n + 1) X).symm (f * g).unop =
      (equivSphereHom (n + 1) X).symm g.unop *
        (equivSphereHom (n + 1) X).symm f.unop := by
  let Q := BasedTopCat.homotopyQuotient.{u}
  let P := pairFunction (Metric.Sphere.basedSpace.{u} n) (Metric.Sphere.basedSpace.{u} n)
  let W := BasedTopCat.basedWedge P
  let f₀ : Opposite.op (Q.obj X) ⟶
      Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)) := f
  let g₀ : Opposite.op (Q.obj X) ⟶
      Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)) := g
  let m : Opposite.op (Q.obj X) ⟶
      Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)) :=
    (f * g : ↥((CategoryTheory.yonedaGrp.obj (Metric.Sphere.cogroup.{u} n)).obj
      (Opposite.op (Opposite.op (Q.obj X)))))
  let l : Opposite.op (Q.obj X) ⟶ Opposite.op (Q.obj W) :=
    CartesianMonoidalCategory.lift f₀ g₀
  let i₀ : Metric.Sphere.basedSpace.{u} n ⟶ W :=
    BasedTopCat.basedWedgeι P WalkingPair.left
  let i₁ : Metric.Sphere.basedSpace.{u} n ⟶ W :=
    BasedTopCat.basedWedgeι P WalkingPair.right
  -- Fullness supplies a representative of the stock lift itself. Its restrictions
  -- are identified only as homotopy classes, not as strict representatives.
  let k : W ⟶ X := Q.preimage l.unop
  have hk : Q.map k = l.unop := Q.map_preimage _
  -- Resolve the chosen projections as concrete arrows before taking their unops.
  have hleft_op : l ≫ (Q.map i₀).op = f₀ :=
    (congrArg
      (fun q : Opposite.op (Q.obj W) ⟶
          Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)) ↦ l ≫ q)
      (BasedTopCat.homotopyOpposite_fst
        (Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)))
        (Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n))))).symm.trans
      (CartesianMonoidalCategory.lift_fst f₀ g₀)
  have hright_op : l ≫ (Q.map i₁).op = g₀ :=
    (congrArg
      (fun q : Opposite.op (Q.obj W) ⟶
          Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)) ↦ l ≫ q)
      (BasedTopCat.homotopyOpposite_snd
        (Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)))
        (Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n))))).symm.trans
      (CartesianMonoidalCategory.lift_snd f₀ g₀)
  have hleft : Q.map (i₀ ≫ k) = f₀.unop := by
    calc
      _ = Q.map i₀ ≫ Q.map k := Q.map_comp i₀ k
      _ = Q.map i₀ ≫ l.unop :=
        congrArg (fun q : Q.obj W ⟶ Q.obj X ↦ Q.map i₀ ≫ q) hk
      _ = (l ≫ (Q.map i₀).op).unop :=
        (unop_comp (f := l) (g := (Q.map i₀).op)).symm
      _ = f₀.unop :=
        congrArg (fun q : Opposite.op (Q.obj X) ⟶
          Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)) ↦ q.unop) hleft_op
  have hright : Q.map (i₁ ≫ k) = g₀.unop := by
    calc
      _ = Q.map i₁ ≫ Q.map k := Q.map_comp i₁ k
      _ = Q.map i₁ ≫ l.unop :=
        congrArg (fun q : Q.obj W ⟶ Q.obj X ↦ Q.map i₁ ≫ q) hk
      _ = (l ≫ (Q.map i₁).op).unop :=
        (unop_comp (f := l) (g := (Q.map i₁).op)).symm
      _ = g₀.unop :=
        congrArg (fun q : Opposite.op (Q.obj X) ⟶
          Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)) ↦ q.unop) hright_op
  -- This term uses exactly the monoid-object dictionary stored by the bundled cogroup.
  have hmul_op : m = l ≫ Metric.Sphere.cogroupMul.{u} n :=
    (@Hom.mul_def _ _ BasedTopCat.homotopyOppositeCartesianMonoidalCategory
      (Metric.Sphere.cogroupCarrier.{u} n) (Opposite.op (Q.obj X))
      (Metric.Sphere.cogroupGrpObj.{u} n).toMonObj f₀ g₀).trans
      (congrArg
        (fun q : Opposite.op (Q.obj W) ⟶
            Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)) ↦ l ≫ q)
        (Metric.Sphere.cogroupGrpObj_mul.{u} n))
  have hmul : m.unop = Q.map (Metric.Sphere.pinchToWedge n ≫ k) :=
    (congrArg (fun q : Opposite.op (Q.obj X) ⟶
      Opposite.op (Q.obj (Metric.Sphere.basedSpace.{u} n)) ↦ q.unop) hmul_op).trans
      ((unop_comp (f := l) (g := Metric.Sphere.cogroupMul.{u} n)).trans
        ((congrArg (fun q : Q.obj (Metric.Sphere.basedSpace.{u} n) ⟶ Q.obj W ↦
          q ≫ l.unop) (Metric.Sphere.cogroupMul_unop_eq_map.{u} n)).trans
          ((congrArg (fun q : Q.obj W ⟶ Q.obj X ↦
            Q.map (Metric.Sphere.pinchToWedge n) ≫ q) hk.symm).trans
              (Q.map_comp (Metric.Sphere.pinchToWedge n) k).symm)))
  let e : (Q.obj (Metric.Sphere.basedSpace.{u} n) ⟶ Q.obj X) →
      HomotopyGroup (Fin (n + 1)) X.right (BasedTopCat.point X) :=
    (equivSphereHom (n + 1) X).symm
  have hpinch : e (Q.map (Metric.Sphere.pinchToWedge n ≫ k)) =
      e (Q.map (i₁ ≫ k)) * e (Q.map (i₀ ≫ k)) :=
    equivSphereHom_symm_pinchToWedge n X k
  exact (congrArg e hmul).trans
    (hpinch.trans (congrArg₂ (fun a b :
      HomotopyGroup (Fin (n + 1)) X.right (BasedTopCat.point X) ↦ a * b)
      (congrArg e hright) (congrArg e hleft)))

/-- The multiplicative opposite of the positive-dimensional homotopy group
compared with the sphere-map group specified by the bundled metric sphere cogroup.
The categorical opposites in the target encode outgoing sphere maps and are
separate from the multiplicative opposite in the source. -/
@[no_expose]
def mulOppositeEquivSphereHom (n : ℕ) (X : BasedTopCat.{u}) :
    (HomotopyGroup (Fin (n + 1)) X.right (BasedTopCat.point X))ᵐᵒᵖ ≃*
      ↥((CategoryTheory.yonedaGrp.obj (Metric.Sphere.cogroup.{u} n)).obj
        (Opposite.op (Opposite.op ((BasedTopCat.homotopyQuotient.{u}).obj X)))) where
  toEquiv := (MulOpposite.opEquiv.symm.trans (equivSphereHom (n + 1) X)).trans
    Quiver.Hom.opEquiv
  map_mul' := by
    intro a b
    apply Quiver.Hom.unop_inj
    apply (equivSphereHom (n + 1) X).symm.injective
    rw [equivSphereHom_symm_mul]
    change (equivSphereHom (n + 1) X).symm
        (equivSphereHom (n + 1) X (a * b).unop) =
      (equivSphereHom (n + 1) X).symm (equivSphereHom (n + 1) X b.unop) *
        (equivSphereHom (n + 1) X).symm (equivSphereHom (n + 1) X a.unop)
    simp only [Equiv.symm_apply_apply, MulOpposite.unop_mul]

/-- On a homotopy class, the comparison takes the ordinary categorical opposite
of its sphere-map class, without inversion or a change of representative. -/
@[simp]
theorem mulOppositeEquivSphereHom_apply_op (n : ℕ) (X : BasedTopCat.{u})
    (a : HomotopyGroup (Fin (n + 1)) X.right (BasedTopCat.point X)) :
    mulOppositeEquivSphereHom n X (MulOpposite.op a) =
      (equivSphereHom (n + 1) X a).op := by
  rfl

/-- On every incoming morphism in the sphere-map group, the inverse comparison
unops the morphism, uses the inverse sphere-map equivalence and takes the
multiplicative opposite of the resulting homotopy class. -/
@[simp]
theorem mulOppositeEquivSphereHom_symm_apply (n : ℕ) (X : BasedTopCat.{u})
    (f : ↥((CategoryTheory.yonedaGrp.obj (Metric.Sphere.cogroup.{u} n)).obj
      (Opposite.op (Opposite.op ((BasedTopCat.homotopyQuotient.{u}).obj X))))) :
    (mulOppositeEquivSphereHom n X).symm f =
      MulOpposite.op ((equivSphereHom (n + 1) X).symm f.unop) := by
  rfl

/-- The sphere-map comparison commutes with based postcomposition on homotopy
classes and the target action of the group-valued Yoneda functor. The double
categorical opposite of the quotient morphism gives the covariant action on
based targets. -/
theorem mulOppositeEquivSphereHom_naturality (n : ℕ) {X Y : BasedTopCat.{u}}
    (h : X ⟶ Y)
    (a : (HomotopyGroup (Fin (n + 1)) X.right (BasedTopCat.point X))ᵐᵒᵖ) :
    mulOppositeEquivSphereHom n Y
      (MulOpposite.op (HomotopyGroup.mapFun (Fin (n + 1)) h.right.hom
        (BasedTopCat.map_point h) a.unop)) =
      ((CategoryTheory.yonedaGrp.obj (Metric.Sphere.cogroup.{u} n)).map
        (((BasedTopCat.homotopyQuotient.{u}).map h).op.op))
          (mulOppositeEquivSphereHom n X a) := by
  apply Quiver.Hom.unop_inj
  change equivSphereHom (n + 1) Y
      (HomotopyGroup.mapFun (Fin (n + 1)) h.right.hom
        (BasedTopCat.map_point h) a.unop) =
    equivSphereHom (n + 1) X a.unop ≫ (BasedTopCat.homotopyQuotient.{u}).map h
  exact equivSphereHom_map (n + 1) h a.unop

end HomotopyGroup
