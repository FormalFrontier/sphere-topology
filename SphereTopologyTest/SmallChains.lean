/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

import SphereTopology.Homology.Singular.SmallChains

/-!
# SmallChains regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open CategoryTheory Convexity TopologicalSpace
open scoped Simplicial

noncomputable section

namespace SphereTopologyTest

universe u

section ArbitraryUniverse

variable {X Y : TopCat.{u}} {ι κ : Type*}

private noncomputable def case001 (U : ι → Opens X) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  AlgebraicTopology.smallSingularChainComplex U

private noncomputable def case002 (U : ι → Opens X) :=
  AlgebraicTopology.smallSingularChainInclusion U

private theorem case003 (U : ι → Opens X) (hU : IsOpenCover U) :
    QuasiIso (AlgebraicTopology.smallSingularChainInclusion U) :=
  AlgebraicTopology.quasiIso_smallSingularChainInclusion U hU

private theorem case004 (f : X ⟶ Y) (U : ι → Opens X) (V : κ → Opens Y)
    (h : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    AlgebraicTopology.smallSingularChainMap f U V h ≫
        AlgebraicTopology.smallSingularChainInclusion V =
      AlgebraicTopology.smallSingularChainInclusion U ≫
        SSet.chainComplexMap (TopCat.toSSet.map f)
          AlgebraicTopology.integerCoefficients :=
  AlgebraicTopology.smallSingularChainMap_comp_inclusion f U V h

end ArbitraryUniverse

private theorem case005 {X : TopCat} {ι : Type*} (U : ι → Opens X)
    {n : SimplexCategoryᵒᵖ} (x : (TopCat.toSSet.obj X).obj n) :
    x ∈ (TopCat.smallSingularSet U).obj n ↔
      ∃ i, Set.range (X.toSSetObjEquiv n x) ⊆ U i :=
  TopCat.mem_smallSingularSet_iff U x

private theorem case006 {X : TopCat} {ι : Type*} (U : ι → Opens X) {n : ℕ}
    (x : (TopCat.smallSingularSet U : SSet) _⦋n + 1⦌)
    (i : Fin (n + 2)) :
    AlgebraicTopology.IsCoverSmall U ((TopCat.toSSet.obj X).δ i x.1) :=
  ((TopCat.smallSingularSet U : SSet).δ i x).property

private theorem case007 {X : TopCat} {ι : Type*} (U : ι → Opens X) {n : ℕ}
    (x : (TopCat.smallSingularSet U : SSet) _⦋n⦌)
    (i : Fin (n + 1)) :
    AlgebraicTopology.IsCoverSmall U ((TopCat.toSSet.obj X).σ i x.1) :=
  ((TopCat.smallSingularSet U : SSet).σ i x).property

private theorem case008 (X : TopCat) (n : ℕ)
    (c : AlgebraicTopology.SingularChainFinsupp X (n + 1)) :
    AlgebraicTopology.singularFinsuppBoundary X n
        (AlgebraicTopology.singularSubdivision X (n + 1) c) =
      AlgebraicTopology.singularSubdivision X n
        (AlgebraicTopology.singularFinsuppBoundary X n c) :=
  AlgebraicTopology.singularSubdivision_boundary X n c

private theorem case009 {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (c : AlgebraicTopology.SingularChainFinsupp X n) :
    AlgebraicTopology.singularFinsuppMap f n
        (AlgebraicTopology.singularSubdivision X n c) =
      AlgebraicTopology.singularSubdivision Y n
        (AlgebraicTopology.singularFinsuppMap f n c) :=
  AlgebraicTopology.singularSubdivision_naturality f n c

private theorem case010 {X : TopCat} {n : ℕ}
    (c : AlgebraicTopology.SingularChainFinsupp X n)
    {y : (TopCat.toSSet.obj X) _⦋n⦌}
    (hy : y ∈ (AlgebraicTopology.singularSubdivision X n c).support) :
    ∃ x ∈ c.support,
      Set.range (X.toSSetObjEquiv _ y) ⊆
        Set.range (X.toSSetObjEquiv _ x) :=
  AlgebraicTopology.mem_support_singularSubdivision c hy

private theorem case011 (X : TopCat) (c : AlgebraicTopology.SingularChainFinsupp X 0) :
    AlgebraicTopology.singularSubdivision X 0 c = c :=
  AlgebraicTopology.singularSubdivision_degree_zero X c

private theorem case012 {X : TopCat} {ι : Type*} (U : ι → Opens X)
    (hU : IsOpenCover U) (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    AlgebraicTopology.IsCoverSmall U x :=
  AlgebraicTopology.isCoverSmall_zero U hU x

private theorem case013 {X : TopCat} {ι κ : Type*} {U : ι → Opens X} {V : κ → Opens X}
    (h : ∀ i, ∃ j, U i ≤ V j) :
    AlgebraicTopology.smallSingularChainMapOfRefinement h ≫
        AlgebraicTopology.smallSingularChainInclusion V =
      AlgebraicTopology.smallSingularChainInclusion U :=
  AlgebraicTopology.smallSingularChainMapOfRefinement_comp_inclusion h

private theorem case014 {X : TopCat} {ι : Type*} (U : ι → Opens X) (hU : IsOpenCover U) :
    QuasiIso (AlgebraicTopology.smallSingularChainInclusion U) :=
  AlgebraicTopology.quasiIso_smallSingularChainInclusion U hU

private theorem case015 :
    let X : TopCat := TopCat.of Empty
    let U : Empty → Opens X := Empty.elim
    QuasiIso (AlgebraicTopology.smallSingularChainInclusion U) := by
  dsimp
  apply AlgebraicTopology.quasiIso_smallSingularChainInclusion
  rw [IsOpenCover]
  ext x
  exact x.elim

end SphereTopologyTest
