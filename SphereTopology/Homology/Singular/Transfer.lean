/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.SingularLifts
public import SimplicialObjects.FiniteFiberTransfer
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

import SimplicialObjects.ChainCoordinates
import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-!
# Singular transfer for finite-fiber covering maps

A covering map with finite point fibers gives a transfer on the all-simplex
singular chain complex, with a coefficient object in a preadditive category
with the requisite coproducts. Applying homology gives the ordinary singular
homology transfer. The spaces need not be connected, locally connected or
nonempty, and the covering need not be surjective or have constant degree.

The construction uses evaluation of singular lifts and the finite-fiber
simplicial transfer. These are Mathlib's singular chain and homology objects;
no normalized-chain, tensor-coefficient, CGWH, negative-degree, reduced,
relative or deck-equivariant comparison is made.

## References

May, *A Concise Course in Algebraic Topology*, revised edition, §16, Problem 3,
motivates the covering transfer and its sheet identity. Mathlib supplies the
singular chain and homology functors; Simplicial Objects supplies the
equifibered finite-fiber transfer specialized here.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe w v u

namespace IsCoveringMap

variable {X Y : TopCat.{w}} {p : Y ⟶ X}

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Transfer on singular chains for a covering map with finite point fibers.
The coefficient is an arbitrary object, with no constant-sheet assumption. -/
noncomputable def singularChainComplexTransfer (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) :
    ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ⟶
      ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj Y :=
  SSet.chainComplexTransfer (TopCat.toSSet.map p) hp.toSSet_map_equifibered
    (fun s => by
      let := hf (X.toSSetObjEquiv (op ⦋0⦌) s default)
      exact hp.finite_singularLift (op ⦋0⦌) s default) R

/-- Each component is the finite-fiber coproduct transfer. -/
theorem singularChainComplexTransfer_f (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (n : ℕ) :
    (hp.singularChainComplexTransfer hf R).f n =
      sigmaConstTransfer ((TopCat.toSSet.map p).app (op ⦋n⦌))
        (fun s => by
          let := hf (X.toSSetObjEquiv (op ⦋n⦌) s default)
          exact hp.finite_singularLift (op ⦋n⦌) s default) R :=
  rfl

/-- A singular simplex transfers to the sum of all of its lifts. -/
theorem summandι_singularChainComplexTransfer_f (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C)
    {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) s ≫
        (hp.singularChainComplexTransfer hf R).f n =
      ∑ᶠ t : {t : (TopCat.toSSet.obj Y) _⦋n⦌ // (TopCat.toSSet.map p).app _ t = s},
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) t.val := by
  rw [singularChainComplexTransfer_f]
  exact ι_sigmaConstTransfer _ _ _ _

/-- Transfer followed by pushforward multiplies singular chains by the sheet
number, as in May, §16, Problem 3. Finiteness is required separately from the
cardinality equality. -/
theorem singularChainComplexTransfer_comp_map (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (d : ℕ)
    (hd : ∀ x : X, Nat.card {y : Y // p y = x} = d) :
    hp.singularChainComplexTransfer hf R ≫
        ((AlgebraicTopology.singularChainComplexFunctor C).obj R).map p =
      d • 𝟙 (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X) := by
  apply SSet.chainComplexTransfer_comp_map (TopCat.toSSet.map p)
    hp.toSSet_map_equifibered
    (fun s => by
      let := hf (X.toSSetObjEquiv (op ⦋0⦌) s default)
      exact hp.finite_singularLift (op ⦋0⦌) s default) R d
  intro s
  exact (Nat.card_congr (hp.singularLiftEquiv (op ⦋0⦌) s default)).trans
    (hd (X.toSSetObjEquiv (op ⦋0⦌) s default))

variable [CategoryWithHomology C]

/-- The ordinary singular homology transfer induced by the chain transfer. -/
noncomputable def singularHomologyTransfer (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (q : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor C q).obj R).obj X ⟶
      ((AlgebraicTopology.singularHomologyFunctor C q).obj R).obj Y :=
  SSet.homologyTransfer (TopCat.toSSet.map p) hp.toSSet_map_equifibered
    (fun s => by
      let := hf (X.toSSetObjEquiv (op ⦋0⦌) s default)
      exact hp.finite_singularLift (op ⦋0⦌) s default) R q

/-- The homology transfer is the image of the chain transfer under homology. -/
theorem singularHomologyTransfer_eq_map (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (q : ℕ) :
    hp.singularHomologyTransfer hf R q =
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) q).map
        (hp.singularChainComplexTransfer hf R) :=
  rfl

/-- Transfer followed by pushforward multiplies ordinary singular homology by
the sheet number, in every nonnegative degree, as in May, §16, Problem 3. -/
theorem singularHomologyTransfer_comp_map (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (d q : ℕ)
    (hd : ∀ x : X, Nat.card {y : Y // p y = x} = d) :
    hp.singularHomologyTransfer hf R q ≫
        ((AlgebraicTopology.singularHomologyFunctor C q).obj R).map p =
      d • 𝟙 (((AlgebraicTopology.singularHomologyFunctor C q).obj R).obj X) := by
  apply SSet.homologyTransfer_comp_map (TopCat.toSSet.map p)
    hp.toSSet_map_equifibered
    (fun s => by
      let := hf (X.toSSetObjEquiv (op ⦋0⦌) s default)
      exact hp.finite_singularLift (op ⦋0⦌) s default) R d q
  intro s
  exact (Nat.card_congr (hp.singularLiftEquiv (op ⦋0⦌) s default)).trans
    (hd (X.toSSetObjEquiv (op ⦋0⦌) s default))

end IsCoveringMap

end

open CategoryTheory Limits Opposite Convexity AlgebraicTopology
open scoped Simplicial

noncomputable section

namespace SphereTopologyTest.SingularTransfer

universe w v u

private abbrev circleBase : TopCat := TopCat.of Circle
private abbrev circleTotal : TopCat := TopCat.of (Circle × Fin 2)

private def projection : circleTotal ⟶ circleBase :=
  TopCat.ofHom ContinuousMap.fst

private theorem projection_covering : IsCoveringMap projection := by
  exact (FiberBundle.isCoveringMap (F := Fin 2)
    (E := Bundle.Trivial Circle (Fin 2))).comp_homeomorph
      (Bundle.Trivial.homeomorphProd Circle (Fin 2)).symm

private def pointFiberEquiv (x : circleBase) :
    {y : circleTotal // projection y = x} ≃ Fin 2 where
  toFun y := y.val.2
  invFun i := ⟨(x, i), rfl⟩
  left_inv y := by
    apply Subtype.ext
    exact Prod.ext y.property.symm rfl
  right_inv _ := rfl

private theorem projection_finite (x : circleBase) :
    Finite {y : circleTotal // projection y = x} :=
  Finite.of_equiv (Fin 2) (pointFiberEquiv x).symm

private theorem projection_card (x : circleBase) :
    Nat.card {y : circleTotal // projection y = x} = 2 :=
  (Nat.card_congr (pointFiberEquiv x)).trans (Nat.card_fin 2)

private def edgeMap : C(StdSimplex ℝ (Fin 2), Circle) :=
  (Circle.loop 1).toContinuousMap.comp
    (StdSimplex.homeomorphI : C(StdSimplex ℝ (Fin 2), unitInterval))

private def edge : (TopCat.toSSet.obj circleBase) _⦋1⦌ :=
  (circleBase.toSSetObjEquiv (op ⦋1⦌)).symm edgeMap

private theorem edge_nonconstant : ¬ ∀ x y, edgeMap x = edgeMap y := by
  intro h
  have hp : Circle.loop 1 = Path.refl 1 := by
    apply Path.ext
    funext t
    have ht := h (StdSimplex.homeomorphI.symm t) (StdSimplex.homeomorphI.symm 0)
    change (Circle.loop 1) (StdSimplex.homeomorphI (StdSimplex.homeomorphI.symm t)) =
      (Circle.loop 1) (StdSimplex.homeomorphI (StdSimplex.homeomorphI.symm 0)) at ht
    change (Circle.loop 1) t = 1
    simpa only [Homeomorph.apply_symm_apply, Path.source] using ht
  apply Circle.loop_one_ne_one
  rw [hp]
  rfl

private def liftedEdge (i : Fin 2) : (TopCat.toSSet.obj circleTotal) _⦋1⦌ :=
  (circleTotal.toSSetObjEquiv (op ⦋1⦌)).symm
    (edgeMap.prodMk (ContinuousMap.const _ i))

private def edgeLift (i : Fin 2) :
    {t : (TopCat.toSSet.obj circleTotal) _⦋1⦌ //
      (TopCat.toSSet.map projection).app _ t = edge} :=
  ⟨liftedEdge i, by
    apply (circleBase.toSSetObjEquiv (op ⦋1⦌)).injective
    rw [TopCat.toSSetObjEquiv_map]
    simp [liftedEdge, edge, projection]
    rfl⟩

private theorem liftedEdge_map (i : Fin 2) :
    (TopCat.toSSet.map projection).app _ (liftedEdge i) = edge :=
  (edgeLift i).property

private def edgeLiftEquiv :
    {t : (TopCat.toSSet.obj circleTotal) _⦋1⦌ //
      (TopCat.toSSet.map projection).app _ t = edge} ≃ Fin 2 :=
  (projection_covering.singularLiftEquiv (op ⦋1⦌) edge default).trans
    (pointFiberEquiv _)

private theorem edgeLiftEquiv_apply (i : Fin 2) : edgeLiftEquiv (edgeLift i) = i := by
  change ((projection_covering.singularLiftEquiv (op ⦋1⦌) edge default)
    (edgeLift i)).val.2 = i
  rw [IsCoveringMap.singularLiftEquiv_apply]
  simp [edgeLift, liftedEdge]

private theorem edgeLiftEquiv_symm (i : Fin 2) :
    edgeLiftEquiv.symm i = edgeLift i :=
  edgeLiftEquiv.symm_apply_eq.mpr (edgeLiftEquiv_apply i).symm

private theorem liftedEdge_injective : Function.Injective liftedEdge := by
  intro i j h
  exact (edgeLiftEquiv_apply i).symm.trans
    ((congrArg edgeLiftEquiv (Subtype.ext h)).trans (edgeLiftEquiv_apply j))

private abbrev chains (X : TopCat) :=
  (TopCat.toSSet.obj X).chainComplex integerCoefficients

private def unitCoefficient : integerCoefficients := ULift.up (1 : ℤ)

private def edgeChain : (chains circleBase).X 1 :=
  ((TopCat.toSSet.obj circleBase).ιChainComplex
    (R := integerCoefficients) edge).hom unitCoefficient

private theorem edgeChain_coordinate :
    (chainGroupIsoFinsupp (TopCat.toSSet.obj circleBase) 1).hom.hom edgeChain =
      Finsupp.single edge (1 : ℤ) :=
  chainGroupIsoFinsupp_hom_ι _ edge

private theorem edgeChain_ne_zero : edgeChain ≠ 0 := by
  intro h
  have he := congrArg (chainGroupIsoFinsupp (TopCat.toSSet.obj circleBase) 1).hom.hom h
  rw [edgeChain_coordinate, map_zero] at he
  have h1 := congrArg (fun f : (TopCat.toSSet.obj circleBase) _⦋1⦌ →₀ ℤ => f edge) he
  exact (one_ne_zero : (1 : ℤ) ≠ 0)
    (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using h1)

private theorem twice_edgeChain_ne_zero : (2 : ℕ) • edgeChain ≠ 0 := by
  intro h
  have he := congrArg (chainGroupIsoFinsupp (TopCat.toSSet.obj circleBase) 1).hom.hom h
  rw [map_nsmul, edgeChain_coordinate, map_zero] at he
  have h2 := congrArg (fun f : (TopCat.toSSet.obj circleBase) _⦋1⦌ →₀ ℤ => f edge) he
  rw [Finsupp.smul_apply, Finsupp.single_eq_same] at h2
  norm_num at h2

/-! ## Degree-one integral transfer and pushforward -/

private def transfer : chains circleBase ⟶ chains circleTotal :=
  projection_covering.singularChainComplexTransfer projection_finite integerCoefficients

private theorem transfer_edge :
    (TopCat.toSSet.obj circleBase).ιChainComplex (R := integerCoefficients) edge ≫ transfer.f 1 =
      (TopCat.toSSet.obj circleTotal).ιChainComplex
          (R := integerCoefficients) (liftedEdge 0) +
        (TopCat.toSSet.obj circleTotal).ιChainComplex
          (R := integerCoefficients) (liftedEdge 1) := by
  have h := SSet.ι_chainComplexTransfer_f (TopCat.toSSet.map projection)
    projection_covering.toSSet_map_equifibered
    (fun s => by
      let := projection_finite (circleBase.toSSetObjEquiv (op ⦋0⦌) s default)
      exact projection_covering.finite_singularLift (op ⦋0⦌) s default)
    integerCoefficients edge
  change (TopCat.toSSet.obj circleBase).ιChainComplex (R := integerCoefficients) edge ≫
    transfer.f 1 = _ at h
  rw [h]
  calc
    _ = ∑ᶠ i : Fin 2, (TopCat.toSSet.obj circleTotal).ιChainComplex
        (R := integerCoefficients) (liftedEdge i) :=
      finsum_eq_of_bijective edgeLiftEquiv edgeLiftEquiv.bijective (fun t => by
        have ht := congrArg Subtype.val (edgeLiftEquiv_symm (edgeLiftEquiv t))
        simpa [edgeLift] using congrArg
          (fun s => (TopCat.toSSet.obj circleTotal).ιChainComplex
            (R := integerCoefficients) s) ht)
    _ = _ := by simp only [finsum_eq_sum_of_fintype, Fin.sum_univ_two]

private theorem transfer_edge_coordinates :
    (chainGroupIsoFinsupp (TopCat.toSSet.obj circleTotal) 1).hom.hom
        ((transfer.f 1).hom edgeChain) =
      Finsupp.single (liftedEdge 0) (1 : ℤ) + Finsupp.single (liftedEdge 1) (1 : ℤ) := by
  have h := congrArg (fun f => f.hom unitCoefficient) transfer_edge
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
    LinearMap.add_apply] at h
  change (transfer.f 1).hom edgeChain = _ at h
  rw [h, map_add]
  exact congrArg₂ (· + ·) (chainGroupIsoFinsupp_hom_ι _ _) (chainGroupIsoFinsupp_hom_ι _ _)

private theorem transfer_edge_coefficients (i : Fin 2) :
    ((chainGroupIsoFinsupp (TopCat.toSSet.obj circleTotal) 1).hom.hom
      ((transfer.f 1).hom edgeChain)) (liftedEdge i) = 1 := by
  rw [transfer_edge_coordinates]
  fin_cases i <;> simp [liftedEdge_injective.eq_iff]

private theorem transfer_edge_push :
    ((SSet.chainComplexMap (TopCat.toSSet.map projection) integerCoefficients).f 1).hom
      ((transfer.f 1).hom edgeChain) = (2 : ℕ) • edgeChain := by
  have h : (TopCat.toSSet.obj circleBase).ιChainComplex (R := integerCoefficients) edge ≫
      transfer.f 1 ≫
        (SSet.chainComplexMap (TopCat.toSSet.map projection) integerCoefficients).f 1 =
      (2 : ℕ) • (TopCat.toSSet.obj circleBase).ιChainComplex
        (R := integerCoefficients) edge := by
    rw [← Category.assoc, transfer_edge, Preadditive.add_comp,
      SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f,
      liftedEdge_map 0, liftedEdge_map 1, two_nsmul]
  have he := congrArg (fun f => f.hom unitCoefficient) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_nsmul,
    LinearMap.smul_apply, edgeChain] using he

private theorem transfer_edge_push_ne_zero :
    ((SSet.chainComplexMap (TopCat.toSSet.map projection) integerCoefficients).f 1).hom
      ((transfer.f 1).hom edgeChain) ≠ 0 := by
  rw [transfer_edge_push]
  exact twice_edgeChain_ne_zero

/-! ## Covering-transfer formulas on the two-sheet projection -/

private theorem transfer_edge_lift_sum :
    (TopCat.toSSet.obj circleBase).ιChainComplex (R := integerCoefficients) edge ≫
        transfer.f 1 =
      ∑ᶠ t : {t : (TopCat.toSSet.obj circleTotal) _⦋1⦌ //
        (TopCat.toSSet.map projection).app _ t = edge},
        (TopCat.toSSet.obj circleTotal).ιChainComplex (R := integerCoefficients) t.val :=
  projection_covering.summandι_singularChainComplexTransfer_f projection_finite
    integerCoefficients edge

private theorem transfer_push :
    transfer ≫ ((singularChainComplexFunctor (ModuleCat ℤ)).obj integerCoefficients).map
      projection = (2 : ℕ) • 𝟙 (chains circleBase) :=
  projection_covering.singularChainComplexTransfer_comp_map projection_finite
    integerCoefficients 2 projection_card

private theorem homology_zero_sheet_use :
    projection_covering.singularHomologyTransfer projection_finite integerCoefficients 0 ≫
        ((singularHomologyFunctor (ModuleCat ℤ) 0).obj integerCoefficients).map projection =
      (2 : ℕ) • 𝟙 (((singularHomologyFunctor (ModuleCat ℤ) 0).obj
        integerCoefficients).obj circleBase) :=
  projection_covering.singularHomologyTransfer_comp_map projection_finite
    integerCoefficients 2 0 projection_card

/-! ## Identity and empty-total boundaries -/

private theorem identity_covering : IsCoveringMap (𝟙 circleBase) :=
  isLocalHomeomorph_iff_isCoveringMap.mp (Homeomorph.refl Circle).isLocalHomeomorph

private theorem identity_finite (x : circleBase) :
    Finite {y : circleBase // (𝟙 circleBase) y = x} := by
  change Finite {y : circleBase // y = x}
  infer_instance

private def identity_transfer : chains circleBase ⟶ chains circleBase :=
  identity_covering.singularChainComplexTransfer identity_finite integerCoefficients

private def emptyProjection (X : TopCat) : TopCat.of Empty ⟶ X :=
  TopCat.ofHom ⟨Empty.elim, continuous_of_discreteTopology⟩

private theorem empty_covering (X : TopCat) : IsCoveringMap (emptyProjection X) :=
  IsCoveringMap.of_isEmpty _

private theorem empty_finite (X : TopCat) (x : X) :
    Finite {y : TopCat.of Empty // emptyProjection X y = x} := inferInstance

private theorem empty_card (X : TopCat) (x : X) :
    Nat.card {y : TopCat.of Empty // emptyProjection X y = x} = 0 :=
  Nat.card_of_isEmpty

private theorem empty_sheet_use (X : TopCat) :
    (empty_covering X).singularChainComplexTransfer (empty_finite X) integerCoefficients ≫
        ((singularChainComplexFunctor (ModuleCat ℤ)).obj integerCoefficients).map
          (emptyProjection X) = 0 := by
  simpa using (empty_covering X).singularChainComplexTransfer_comp_map
    (empty_finite X) integerCoefficients 0 (empty_card X)

end SphereTopologyTest.SingularTransfer

end
