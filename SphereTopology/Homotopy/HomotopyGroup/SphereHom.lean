/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.HomotopyGroup.Sphere
public import FundamentalGroupoids.Topology.Category.TopCat.Based
public import Mathlib.Data.Setoid.Basic

/-!
# Sphere representatives in the based-homotopy category

The representative conversion uses precomposition by `ULift.down` and
`ULift.up`. The target is an object of the under category, not necessarily an
object presented by `BasedTopCat.of`.

`HomotopyGroup.equivSphereHom` compares `HomotopyGroup (Fin n)` with
morphisms in the based-homotopy category from the lifted unit `n`-sphere in
`EuclideanSpace ℝ (Fin (n + 1))`, for every `n : ℕ`. The inverse on a
based-map representative pulls back along `Cube.collapseToSphere n`.
The last ambient axis specifies `EuclideanSpace.northPoint n`;
`n = 0` gives `S⁰` and `Fin 0` generalized loops, while `n = 1` gives `S¹`
and `Fin 1` loops. In dimension zero, north is fixed and south can have any
target value, as in `GenLoop.sphereHomeomorph_zero_apply_neg_northPoint`;
the unique cube point collapses to south.

## Limitations

The comparison is an equivalence of sets. No group structure on a categorical
hom-set, compatibility with multiplication, or opposite-group convention is
specified, and no group structure in dimension zero is asserted. The target
needs no separation, compactness or connectedness hypothesis. Mapping spaces
use the ordinary compact-open topology, not May's compactly generated
mapping-space convention.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 9, §1,
  p. 65, gives background for the sphere-class interpretation. The comparison
  here uses the ordinary compact-open model, not May's compactly generated
  mapping-space convention.
* This library supplies `HomotopyGroup.equivSphereClasses`, the original
  last-axis sphere coordinates and the cube collapse.
* Fundamental Groupoids supplies `BasedTopCat.homotopyQuotient_map_eq_iff`.
  Mathlib supplies the under category, fullness of its category quotient,
  `Quotient.congr` and `Setoid.quotientKerEquivOfRightInverse`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped unitInterval Topology

namespace BasedTopCat

private def sphereMapEquiv (d : ℕ) (X : BasedTopCat.{u}) :
    {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, X.right) //
      F (EuclideanSpace.northPoint d) = point X} ≃
    (of (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1))
      (ULift.up (EuclideanSpace.northPoint d)) ⟶ X) where
  toFun F := Under.homMk (TopCat.ofHom (F.val.comp
    (⟨ULift.down, continuous_uliftDown⟩ : C(ULift.{u}
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1),
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)))) (by
        apply TopCat.ext
        intro t
        cases t
        change F.val (EuclideanSpace.northPoint d) = point X
        exact F.property)
  invFun f := ⟨f.right.hom.comp
    (⟨ULift.up, continuous_uliftUp⟩ : C(
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1,
      ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1))),
    map_point f⟩
  left_inv F := by
    apply Subtype.ext
    ext s
    rfl
  right_inv f := by
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    intro s
    rfl

private theorem sphereMapEquiv_homotopicRel_iff (d : ℕ) (X : BasedTopCat.{u})
    (F G : {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, X.right) //
      F (EuclideanSpace.northPoint d) = point X}) :
    ContinuousMap.HomotopicRel (sphereMapEquiv d X F).right.hom
      (sphereMapEquiv d X G).right.hom
      {point (of (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1))
        (ULift.up (EuclideanSpace.northPoint d)))} ↔
    F.val.HomotopicRel G.val {EuclideanSpace.northPoint d} := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1
  let up : C(S, ULift.{u} S) := ⟨ULift.up, continuous_uliftUp⟩
  let down : C(ULift.{u} S, S) := ⟨ULift.down, continuous_uliftDown⟩
  change (F.val.comp down).HomotopicRel (G.val.comp down)
    ({ULift.up (EuclideanSpace.northPoint d)} : Set (ULift.{u} S)) ↔
      F.val.HomotopicRel G.val {EuclideanSpace.northPoint d}
  constructor
  · intro H
    have H' := H.precomp_continuousMap (T := {EuclideanSpace.northPoint d}) up (by
      intro s hs
      rcases Set.mem_singleton_iff.mp hs with rfl
      exact Set.mem_singleton_iff.mpr rfl)
    exact H'
  · intro H
    exact H.precomp_continuousMap down (by
      intro s hs
      rcases Set.mem_singleton_iff.mp hs with rfl
      exact Set.mem_singleton_iff.mpr rfl)

private theorem sphereMapEquiv_map_eq_iff (d : ℕ) (X : BasedTopCat.{u})
    (F G : {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, X.right) //
      F (EuclideanSpace.northPoint d) = point X}) :
    homotopyQuotient.map (sphereMapEquiv d X F) =
      homotopyQuotient.map (sphereMapEquiv d X G) ↔
    F.val.HomotopicRel G.val {EuclideanSpace.northPoint d} :=
  (homotopyQuotient_map_eq_iff _ _).trans (sphereMapEquiv_homotopicRel_iff d X F G)

end BasedTopCat

namespace HomotopyGroup

/-- Finite cube homotopy classes are morphisms from the lifted unit `n`-sphere
in the based-homotopy category. This is a set equivalence for every `n : ℕ`,
including zero, and every based target `X : BasedTopCat.{u}`. The sphere lies in
`EuclideanSpace ℝ (Fin (n + 1))` and is based at `EuclideanSpace.northPoint n`. -/
@[no_expose]
def equivSphereHom (n : ℕ) (X : BasedTopCat.{u}) :
    HomotopyGroup (Fin n) X.right (BasedTopCat.point X) ≃
    (BasedTopCat.homotopyQuotient.obj
      (BasedTopCat.of
        (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
        (ULift.up (EuclideanSpace.northPoint n))) ⟶
      BasedTopCat.homotopyQuotient.obj X) :=
  (equivSphereClasses n (BasedTopCat.point X)).trans
    ((Quotient.congr
      (ra := pathSetoid
        {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X.right) //
          F (EuclideanSpace.northPoint n) = BasedTopCat.point X})
      (rb := Setoid.ker (fun f : BasedTopCat.of
        (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
        (ULift.up (EuclideanSpace.northPoint n)) ⟶ X ↦
          BasedTopCat.homotopyQuotient.map f))
      (BasedTopCat.sphereMapEquiv n X)
      (fun F G ↦ by
        change Joined F G ↔ _
        exact (show Joined F G ↔ ZerothHomotopy.mk F = ZerothHomotopy.mk G from
          ⟨fun h ↦ Quotient.sound h, fun h ↦ Quotient.exact h⟩).trans
            ((ZerothHomotopy.sphere_mk_eq_mk_iff_homotopicRel n
              (BasedTopCat.point X) F G).trans
                (BasedTopCat.sphereMapEquiv_map_eq_iff n X F G).symm))).trans
      (Setoid.quotientKerEquivOfRightInverse
        (fun f : BasedTopCat.of
          (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
          (ULift.up (EuclideanSpace.northPoint n)) ⟶ X ↦
            BasedTopCat.homotopyQuotient.map f)
        (fun g ↦ BasedTopCat.homotopyQuotient.preimage g)
        (fun g ↦ BasedTopCat.homotopyQuotient.map_preimage g)))

/-- A representative on the `Fin n` cube maps to the class of its unit `n`-sphere
representative, precomposed with `ULift.down` on the universe-lifted source.
This formula includes `n = 0`. -/
@[simp]
theorem equivSphereHom_class (n : ℕ) (X : BasedTopCat.{u})
    (p : GenLoop (Fin n) X.right (BasedTopCat.point X)) :
    equivSphereHom n X (⟦p⟧ : HomotopyGroup (Fin n) X.right (BasedTopCat.point X)) =
      BasedTopCat.homotopyQuotient.map
        (Under.homMk (TopCat.ofHom
          ((GenLoop.sphereHomeomorph n (BasedTopCat.point X) p).val.comp
            (⟨ULift.down, continuous_uliftDown⟩ : C(ULift.{u}
              (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
              Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))) (by
                apply TopCat.ext
                intro t
                cases t
                change (GenLoop.sphereHomeomorph n (BasedTopCat.point X) p).val
                  (EuclideanSpace.northPoint n) = BasedTopCat.point X
                exact (GenLoop.sphereHomeomorph n (BasedTopCat.point X) p).property)) := by
  -- Keep this a propositional simp rule: the equivalence's body is not exposed.
  rfl

/-- The set comparison commutes with postcomposition by any based target map,
in every dimension, including zero. -/
theorem equivSphereHom_map (n : ℕ) {X Y : BasedTopCat.{u}} (h : X ⟶ Y)
    (a : HomotopyGroup (Fin n) X.right (BasedTopCat.point X)) :
    equivSphereHom n Y
        (mapFun (Fin n) h.right.hom (BasedTopCat.map_point h) a) =
      equivSphereHom n X a ≫ (BasedTopCat.homotopyQuotient.{u}).map h := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [mapFun_class, equivSphereHom_class, equivSphereHom_class, ← Functor.map_comp]
  apply congrArg BasedTopCat.homotopyQuotient.map
  apply Under.UnderMorphism.ext
  apply TopCat.ext
  intro z
  change
    (GenLoop.sphereHomeomorph n (BasedTopCat.point Y)
      (GenLoop.map h.right.hom (BasedTopCat.map_point h) p)).val z.down =
    h.right.hom ((GenLoop.sphereHomeomorph n (BasedTopCat.point X) p).val z.down)
  exact DFunLike.congr_fun
    (congrArg Subtype.val
      (GenLoop.sphereHomeomorph_map n h.right.hom (BasedTopCat.map_point h) p)) z.down

/-- The inverse on a based unit `n`-sphere map class is represented by
precomposition with `ULift.up` followed by `Cube.collapseToSphere n`.
The formula applies to every `n : ℕ`, including zero. -/
theorem equivSphereHom_symm_map (n : ℕ) (X : BasedTopCat.{u})
    (f : BasedTopCat.of
      (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
      (ULift.up (EuclideanSpace.northPoint n)) ⟶ X) :
    (equivSphereHom n X).symm (BasedTopCat.homotopyQuotient.map f) =
      (⟦(GenLoop.sphereHomeomorph n (BasedTopCat.point X)).symm
        ⟨f.right.hom.comp
          (⟨ULift.up, continuous_uliftUp⟩ : C(
            Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
            ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))),
          BasedTopCat.map_point f⟩⟧ :
            HomotopyGroup (Fin n) X.right (BasedTopCat.point X)) := by
  let e := GenLoop.sphereHomeomorph n (BasedTopCat.point X)
  let s := BasedTopCat.sphereMapEquiv n X
  apply (equivSphereHom n X).injective
  rw [Equiv.apply_symm_apply, equivSphereHom_class]
  change BasedTopCat.homotopyQuotient.map f =
    BasedTopCat.homotopyQuotient.map (s (e (e.symm (s.symm f))))
  exact (congrArg BasedTopCat.homotopyQuotient.map
    ((congrArg s (e.apply_symm_apply (s.symm f))).trans (s.apply_symm_apply f))).symm

/-- Any generalized loop on the `Fin n` cube whose values are the pullback of a
based unit `n`-sphere map along the lifted `Cube.collapseToSphere n` represents
its inverse image, including in dimension zero. -/
theorem equivSphereHom_symm_map_eq_class (n : ℕ) (X : BasedTopCat.{u})
    (f : BasedTopCat.of
      (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
      (ULift.up (EuclideanSpace.northPoint n)) ⟶ X)
    (p : GenLoop (Fin n) X.right (BasedTopCat.point X))
    (hp : ∀ t, p t = f.right.hom (ULift.up (Cube.collapseToSphere n t))) :
    (equivSphereHom n X).symm (BasedTopCat.homotopyQuotient.map f) =
      (⟦p⟧ : HomotopyGroup (Fin n) X.right (BasedTopCat.point X)) := by
  rw [equivSphereHom_symm_map]
  apply congrArg (fun q : GenLoop (Fin n) X.right (BasedTopCat.point X) ↦
    (⟦q⟧ : HomotopyGroup (Fin n) X.right (BasedTopCat.point X)))
  apply GenLoop.ext
  intro t
  exact (GenLoop.sphereHomeomorph_symm_apply_apply n (BasedTopCat.point X) _ t).trans
    (hp t).symm

end HomotopyGroup
