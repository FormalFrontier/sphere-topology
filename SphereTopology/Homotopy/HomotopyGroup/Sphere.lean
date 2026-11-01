/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Geometry.CubeSphere
public import FundamentalGroupoids.Topology.Homotopy.GenLoop.OnePoint
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Generalized loops and based sphere-map classes

`GenLoop.sphereHomeomorph` identifies finite generalized-loop spaces with the
subtype of continuous sphere maps taking the specified last-axis north pole
to the chosen point. It composes the one-point compactification comparison
with the compact-open arrow homeomorphism and restricts to the pole predicate.
Its inverse is precomposition with `Cube.collapseToSphere`.

`HomotopyGroup.equivSphereClasses` identifies the existing boundary-relative
homotopy quotient with the existing path-component set of this sphere-map
subtype. The equivalence is natural in based continuous maps of targets in
independent universes. The component relation corresponds to homotopy relative
to the singleton north pole: the constrained-homotopy comparison uses local
compactness of the finite sphere, not any condition on the target.

In dimension one, `HomotopyGroup.pi1MulEquivFundamentalGroup_sphereHomeomorph`
identifies the component associated with a based path with that path's class
in the fundamental group.

Both constructions include dimension zero. A generalized loop with arbitrary
value `z` then gives a sphere map taking north to the chosen point and south
to `z`. Only a topology and a chosen point are required of a target.

## Limitations

These are comparisons of spaces and sets of classes. Continuous-map spaces
carry the ordinary compact-open topology, and the fixed-pole subtypes carry
the induced topology. No compactly generated modification is made; these
mapping spaces do not use May's compactly generated mapping-space convention.
No sphere group operation, pinch map or loop-space iteration is specified here.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 8, §§1–2,
  pp. 57–58, and Chapter 9, §1, p. 65, for based mapping spaces and the
  sphere description of homotopy classes.
* Mathlib's generalized loops and homotopy groups are due to Roberto Alvarez;
  its relative homotopies to Shing Tak Lam and contributors. Mathlib supplies
  the compact-open arrow homeomorphism, subtype homeomorphisms, path components
  and quotient congruence.
* Fundamental Groupoids supplies `GenLoop.onePointHomeomorph`,
  `HomotopyGroup.equivZerothHomotopy` and the constrained-homotopy comparison
  `ContinuousMap.HomotopyWith.nonempty_iff_joined`.
* This library supplies the last-axis sphere coordinates and cube collapse.
-/

@[expose] public section

noncomputable section

universe v w

open scoped unitInterval Topology OnePoint

private theorem joined_iff_homotopicRel_singleton {A : Type w} {X : Type v}
    [TopologicalSpace A] [LocallyCompactSpace A] [TopologicalSpace X]
    (a : A) (x : X) (F G : {F : C(A, X) // F a = x}) :
    Joined F G ↔ F.val.HomotopicRel G.val ({a} : Set A) := by
  refine (ContinuousMap.HomotopyWith.nonempty_iff_joined
    (f := F.val) (g := G.val) (P := fun f ↦ f a = x)
    F.property G.property).symm.trans ?_
  constructor
  · rintro ⟨H⟩
    refine ⟨{ toHomotopy := H.toHomotopy, prop' := ?_ }⟩
    intro t b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact (H.prop t).trans F.property.symm
  · rintro ⟨H⟩
    exact ⟨{ toHomotopy := H.toHomotopy
             prop' := fun t ↦
               (H.eq_fst t (Set.mem_singleton_iff.mpr rfl)).trans F.property }⟩

namespace GenLoop

/-- Generalized loops on the finite cube are the compact-open sphere maps taking
the last-axis north pole to the chosen point. The inverse pulls back along
`Cube.collapseToSphere`. -/
def sphereHomeomorph {X : Type v} [TopologicalSpace X] (n : ℕ) (x : X) :
    GenLoop (Fin n) X x ≃ₜ
      {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
        F (EuclideanSpace.northPoint n) = x} := by
  let e := Cube.onePointBoundaryComplHomeomorphSphere n
  have hi : e.symm (EuclideanSpace.northPoint n) = ∞ :=
    Cube.onePointBoundaryComplHomeomorphSphere_symm_apply_northPoint n
  exact (onePointHomeomorph (Fin n) x).trans
    ((e.arrowCongr (Homeomorph.refl X)).subtype
      (p := fun F ↦ F ∞ = x)
      (q := fun F ↦ F (EuclideanSpace.northPoint n) = x)
      (fun F ↦ by
        change F ∞ = x ↔ F (e.symm (EuclideanSpace.northPoint n)) = x
        rw [hi]))

/-- The forward comparison extends the loop by the basepoint at infinity, then
uses the inverse sphere coordinate. -/
theorem sphereHomeomorph_apply {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X) (p : GenLoop (Fin n) X x)
    (s : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (sphereHomeomorph n x p).val s =
      OnePoint.rec x
        (fun u : ((Cube.boundary (Fin n))ᶜ : Set (I^(Fin n))) ↦ p u.val)
        ((Cube.onePointBoundaryComplHomeomorphSphere n).symm s) := by
  change (onePointHomeomorph (Fin n) x p).val
    ((Cube.onePointBoundaryComplHomeomorphSphere n).symm s) = _
  exact congrFun (coe_onePointHomeomorph_apply (Fin n) x p) _

/-- Every generalized loop gives a sphere map with the prescribed north-pole value. -/
@[simp]
theorem sphereHomeomorph_apply_northPoint {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X) (p : GenLoop (Fin n) X x) :
    (sphereHomeomorph n x p).val (EuclideanSpace.northPoint n) = x := by
  exact (sphereHomeomorph n x p).property

/-- At finite points of the compactification, the comparison preserves the
values of the generalized loop on the boundary complement. -/
@[simp]
theorem sphereHomeomorph_apply_coe {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X) (p : GenLoop (Fin n) X x)
    (u : ((Cube.boundary (Fin n))ᶜ : Set (I^(Fin n)))) :
    (sphereHomeomorph n x p).val
        (Cube.onePointBoundaryComplHomeomorphSphere n
          (u : OnePoint ((Cube.boundary (Fin n))ᶜ : Set (I^(Fin n))))) =
      p u.val := by
  change (onePointHomeomorph (Fin n) x p).val
    ((Cube.onePointBoundaryComplHomeomorphSphere n).symm
      (Cube.onePointBoundaryComplHomeomorphSphere n
        (u : OnePoint ((Cube.boundary (Fin n))ᶜ : Set (I^(Fin n)))))) = _
  simpa only [Homeomorph.symm_apply_apply] using
    onePointHomeomorph_apply_coe (Fin n) x p u

/-- The inverse comparison is precomposition with the cube-to-sphere collapse. -/
@[simp]
theorem coe_sphereHomeomorph_symm_apply {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X)
    (F : {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
      F (EuclideanSpace.northPoint n) = x}) :
    ((sphereHomeomorph n x).symm F).val = F.val.comp (Cube.collapseToSphere n) := by
  change ((onePointHomeomorph (Fin n) x).symm _).val = _
  exact coe_onePointHomeomorph_symm_apply (Fin n) x _

/-- Evaluate the inverse comparison at any point of the cube. -/
@[simp]
theorem sphereHomeomorph_symm_apply_apply {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X)
    (F : {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
      F (EuclideanSpace.northPoint n) = x}) (t : I^(Fin n)) :
    (sphereHomeomorph n x).symm F t = F.val (Cube.collapseToSphere n t) := by
  exact congrArg (fun g : C(I^(Fin n), X) ↦ g t)
    (coe_sphereHomeomorph_symm_apply n x F)

/-- The constant generalized loop maps to the constant sphere map. -/
@[simp]
theorem sphereHomeomorph_const {X : Type v} [TopologicalSpace X] (n : ℕ) (x : X) :
    sphereHomeomorph n x (GenLoop.const : GenLoop (Fin n) X x) =
      ⟨ContinuousMap.const _ x, rfl⟩ := by
  apply (sphereHomeomorph n x).symm.injective
  apply GenLoop.ext
  intro t
  simp only [Homeomorph.symm_apply_apply, sphereHomeomorph_symm_apply_apply,
    ContinuousMap.const_apply, GenLoop.const_apply]

/-- The constant sphere map pulls back to the constant generalized loop. -/
@[simp]
theorem sphereHomeomorph_symm_const {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X) :
    (sphereHomeomorph n x).symm ⟨ContinuousMap.const _ x, rfl⟩ = GenLoop.const := by
  apply (sphereHomeomorph n x).injective
  simpa only [Homeomorph.apply_symm_apply] using (sphereHomeomorph_const n x).symm

/-- In dimension zero, the south-pole value can be any point of the target,
independently of the prescribed north-pole value. -/
@[simp]
theorem sphereHomeomorph_zero_apply_neg_northPoint {X : Type v} [TopologicalSpace X]
    (x z : X) :
    (sphereHomeomorph 0 x ((genLoopHomeoOfIsEmpty (Fin 0) x).symm z)).val
      (-EuclideanSpace.northPoint 0) = z := by
  have h := sphereHomeomorph_symm_apply_apply 0 x
    (sphereHomeomorph 0 x ((genLoopHomeoOfIsEmpty (Fin 0) x).symm z))
    (0 : I^(Fin 0))
  have hz : ((genLoopHomeoOfIsEmpty (Fin 0) x).symm z) (0 : I^(Fin 0)) = z := by
    change genLoopHomeoOfIsEmpty (Fin 0) x
      ((genLoopHomeoOfIsEmpty (Fin 0) x).symm z) = z
    exact (genLoopHomeoOfIsEmpty (Fin 0) x).apply_symm_apply z
  simpa only [Homeomorph.symm_apply_apply, Cube.collapseToSphere_zero, hz] using h.symm

/-- The sphere comparison commutes with ordinary based postcomposition. -/
theorem sphereHomeomorph_map {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) {x : X} {y : Y}
    (f : C(X, Y)) (hf : f x = y) (p : GenLoop (Fin n) X x) :
    let post : C(
        {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
          F (EuclideanSpace.northPoint n) = x},
        {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, Y) //
          F (EuclideanSpace.northPoint n) = y}) :=
      ⟨(fun F ↦ ⟨f.comp F.val, (congrArg f F.property).trans hf⟩),
        ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk
          (fun F ↦ (congrArg f F.property).trans hf)⟩
    sphereHomeomorph n y (GenLoop.map f hf p) = post (sphereHomeomorph n x p) := by
  dsimp only
  apply (sphereHomeomorph n y).symm.injective
  apply GenLoop.ext
  intro t
  rw [Homeomorph.symm_apply_apply, sphereHomeomorph_symm_apply_apply, GenLoop.map_apply]
  change f (p t) = f ((sphereHomeomorph n x p).val (Cube.collapseToSphere n t))
  simpa only [Homeomorph.symm_apply_apply] using
    congrArg f (sphereHomeomorph_symm_apply_apply n x (sphereHomeomorph n x p) t)

/-- Homotopy relative to the cube boundary corresponds to homotopy relative to
the singleton north pole on the sphere. -/
theorem homotopic_iff_sphere_homotopicRel {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X) (p q : GenLoop (Fin n) X x) :
    GenLoop.Homotopic p q ↔
      (sphereHomeomorph n x p).val.HomotopicRel (sphereHomeomorph n x q).val
        ({EuclideanSpace.northPoint n} :
          Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
  rw [homotopic_iff_joined]
  refine Iff.trans ?_ (joined_iff_homotopicRel_singleton
    (EuclideanSpace.northPoint n) x (sphereHomeomorph n x p) (sphereHomeomorph n x q))
  constructor
  · intro h
    exact h.map (sphereHomeomorph n x).continuous
  · intro h
    have h' := h.map (sphereHomeomorph n x).symm.continuous
    change Joined ((sphereHomeomorph n x).symm (sphereHomeomorph n x p))
      ((sphereHomeomorph n x).symm (sphereHomeomorph n x q)) at h'
    simpa only [Homeomorph.symm_apply_apply] using h'

end GenLoop

namespace HomotopyGroup

/-- Boundary-relative cube classes are the path components of the compact-open
subtype of sphere maps fixing the specified north pole. This is a set equivalence,
without a choice of sphere group operation. -/
def equivSphereClasses {X : Type v} [TopologicalSpace X] (n : ℕ) (x : X) :
    HomotopyGroup (Fin n) X x ≃
      ZerothHomotopy
        {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
          F (EuclideanSpace.northPoint n) = x} := by
  let R := GenLoop.sphereHomeomorph n x
  exact (equivZerothHomotopy (Fin n) x).trans
    (Quotient.congr
      (ra := pathSetoid (GenLoop (Fin n) X x))
      (rb := pathSetoid
        {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
          F (EuclideanSpace.northPoint n) = x})
      R.toEquiv (fun p q ↦
        ⟨fun h ↦ h.map R.continuous,
          fun h ↦ by
            change Joined p q
            have h' := h.map R.symm.continuous
            change Joined (R.symm (R p)) (R.symm (R q)) at h'
            simpa only [R.symm_apply_apply] using h'⟩))

/-- A cube representative maps to the component of its corresponding sphere map. -/
@[simp]
theorem equivSphereClasses_class {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X) (p : GenLoop (Fin n) X x) :
    equivSphereClasses n x (⟦p⟧ : HomotopyGroup (Fin n) X x) =
      ZerothHomotopy.mk (GenLoop.sphereHomeomorph n x p) := by
  rfl

/-- A sphere-map component pulls back to the class represented by its
precomposition with the cube collapse. -/
@[simp]
theorem equivSphereClasses_symm_mk {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X)
    (F : {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
      F (EuclideanSpace.northPoint n) = x}) :
    (equivSphereClasses n x).symm (ZerothHomotopy.mk F) =
      (⟦(GenLoop.sphereHomeomorph n x).symm F⟧ : HomotopyGroup (Fin n) X x) := by
  apply (equivSphereClasses n x).symm_apply_eq.mpr
  rw [equivSphereClasses_class, Homeomorph.apply_symm_apply]

/-- The sphere-map component associated with a based path represents that path's
class under the comparison with the fundamental group. -/
theorem pi1MulEquivFundamentalGroup_sphereHomeomorph {X : Type v} [TopologicalSpace X]
    (x : X) (p : Path x x) :
    pi1MulEquivFundamentalGroup (X := X) (x := x)
      ((equivSphereClasses 1 x).symm
        (ZerothHomotopy.mk
          (GenLoop.sphereHomeomorph 1 x
            ((genLoopEquivOfUnique (Fin 1)).symm p)))) =
      FundamentalGroup.fromPath ⟦p⟧ := by
  rw [equivSphereClasses_symm_mk, Homeomorph.symm_apply_apply]
  exact congrArg (fun q : Path x x ↦ FundamentalGroup.fromPath ⟦q⟧)
    ((genLoopEquivOfUnique (Fin 1)).apply_symm_apply p)

/-- The chosen constant class maps to the component of the constant sphere map. -/
theorem equivSphereClasses_const {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X) :
    equivSphereClasses n x (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) X x) =
      ZerothHomotopy.mk
        (⟨ContinuousMap.const _ x, rfl⟩ :
          {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
            F (EuclideanSpace.northPoint n) = x}) := by
  rw [equivSphereClasses_class, GenLoop.sphereHomeomorph_const]

/-- The component of the constant sphere map pulls back to the constant class. -/
theorem equivSphereClasses_symm_const {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X) :
    (equivSphereClasses n x).symm
        (ZerothHomotopy.mk
          (⟨ContinuousMap.const _ x, rfl⟩ :
            {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
              F (EuclideanSpace.northPoint n) = x})) =
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) X x) := by
  exact (equivSphereClasses n x).symm_apply_eq.mpr (equivSphereClasses_const n x).symm

/-- The class comparison is natural under based continuous maps of targets.
The right-hand component map is induced by ordinary continuous-map
postcomposition on the fixed-pole subtype. -/
theorem equivSphereClasses_mapFun {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) {x : X} {y : Y}
    (f : C(X, Y)) (hf : f x = y) (a : HomotopyGroup (Fin n) X x) :
    let post : C(
        {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
          F (EuclideanSpace.northPoint n) = x},
        {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, Y) //
          F (EuclideanSpace.northPoint n) = y}) :=
      ⟨(fun F ↦ ⟨f.comp F.val, (congrArg f F.property).trans hf⟩),
        ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk
          (fun F ↦ (congrArg f F.property).trans hf)⟩
    equivSphereClasses n y (mapFun (Fin n) f hf a) =
      ZerothHomotopy.map post (equivSphereClasses n x a) := by
  dsimp only
  refine Quotient.inductionOn a ?_
  intro p
  simp only [mapFun_class, equivSphereClasses_class, ZerothHomotopy.map_mk]
  exact congrArg ZerothHomotopy.mk (GenLoop.sphereHomeomorph_map n f hf p)

end HomotopyGroup

namespace ZerothHomotopy

/-- Equality of components in the fixed-north-pole sphere-map subtype is
homotopy relative to that singleton. The constrained-homotopy comparison
`ContinuousMap.HomotopyWith.nonempty_iff_joined` applies because the source
sphere is locally compact; the target needs only a topology. -/
theorem sphere_mk_eq_mk_iff_homotopicRel {X : Type v} [TopologicalSpace X]
    (n : ℕ) (x : X)
    (F G : {F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) //
      F (EuclideanSpace.northPoint n) = x}) :
    mk F = mk G ↔ F.val.HomotopicRel G.val
      ({EuclideanSpace.northPoint n} :
        Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
  refine Iff.trans ?_ (joined_iff_homotopicRel_singleton
    (EuclideanSpace.northPoint n) x F G)
  exact ⟨fun h ↦ Quotient.exact h, fun h ↦ Quotient.sound h⟩

end ZerothHomotopy
