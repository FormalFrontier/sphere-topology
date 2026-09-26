/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker A, Prism. See README.md for internal reuse.
module

import SphereTopology.Homology.Singular.ReducedMayerVietoris
import Mathlib.Analysis.Convex.Contractible

/-!
# ReducedMayerVietoris regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open CategoryTheory Limits AlgebraicTopology TopologicalSpace

noncomputable section

namespace SphereTopologyTest

universe u

private noncomputable def case001 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    TopCat.reducedSingularHomology X 1 ⟶
      TopCat.reducedSingularHomology ((Opens.toTopCat X).obj (U ⊓ V)) 0 :=
  twoOpenReducedMayerVietorisδZero U V hUV

private theorem case002 {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    twoOpenMayerVietorisIntersectionMap f U V U' V' hU hV n =
      HomologicalComplex.homologyMap
        (integralSingularChainMap
          (twoOpenIntersectionMap f U V U' V' hU hV)) n :=
  twoOpenMayerVietorisIntersectionMap_eq f U V U' V' hU hV n

private theorem case003 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hPrev : IsZero
      (integralSingularHomology ((Opens.toTopCat X).obj U) (n + 1) ⊞
        integralSingularHomology ((Opens.toTopCat X).obj V) (n + 1)))
    (hNext : IsZero
      (integralSingularHomology ((Opens.toTopCat X).obj U) n ⊞
        integralSingularHomology ((Opens.toTopCat X).obj V) n)) :
    IsIso (twoOpenMayerVietorisδ U V hUV n) :=
  twoOpenMayerVietorisδ_isIso_of_isZero_outer U V hUV n hPrev hNext

private theorem case004 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    twoOpenReducedMayerVietorisδZero U V hUV ≫
        TopCat.reducedSingularHomologyZeroInclusion
          ((Opens.toTopCat X).obj (U ⊓ V)) ≫
        (twoOpenIntersectionHomologyIso U V 0).hom =
      (TopCat.reducedSingularHomologyIsoOfNeZero X 1 (by simp)).hom ≫
        twoOpenMayerVietorisδ U V hUV 0 :=
  twoOpenReducedMayerVietorisδZero_ordinary U V hUV

private theorem case005 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (ShortComplex.mk
      (twoOpenReducedMayerVietorisδZero U V hUV)
      (twoOpenReducedMayerVietorisFromIntersectionZero U V)
      (twoOpenReducedMayerVietorisδZero_comp_fromIntersection U V hUV)).Exact :=
  twoOpenReducedMayerVietoris_exact_intersectionZero U V hUV

private theorem case006 {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) :
    twoOpenReducedMayerVietorisδZero U V hUV ≫
        TopCat.reducedSingularHomologyMap
          (twoOpenIntersectionMap f U V U' V' hU hV) 0 =
      TopCat.reducedSingularHomologyMap f 1 ≫
        twoOpenReducedMayerVietorisδZero U' V' hU'V' :=
  twoOpenReducedMayerVietorisδZero_naturality
    f U V U' V' hU hV hUV hU'V'

private theorem case007 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (hVU : V ⊔ U = ⊤) :
    twoOpenReducedMayerVietorisδZero U V hUV ≫
        TopCat.reducedSingularHomologyMap
          (twoOpenIntersectionSwapMap U V) 0 =
      -(twoOpenReducedMayerVietorisδZero V U hVU) :=
  twoOpenReducedMayerVietorisδZero_swap_eq_neg U V hUV hVU

private theorem case008 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (hVU : V ⊔ U = ⊤) :
    twoOpenReducedMayerVietorisδZero V U hVU ≫
        TopCat.reducedSingularHomologyMap
          (twoOpenIntersectionSwapMap V U) 0 =
      -(twoOpenReducedMayerVietorisδZero U V hUV) :=
  twoOpenReducedMayerVietorisδZero_swap_eq_neg V U hVU hUV

private theorem case009 {X : TopCat.{u}} (U V : Opens X) :
    twoOpenIntersectionSwapMap U V ≫
      twoOpenIntersectionSwapMap V U = 𝟙 _ :=
  twoOpenIntersectionSwapMap_comp U V

private theorem case010 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (hU₀ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 0))
    (hV₀ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj V) 0))
    (hU₁ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj U) 1))
    (hV₁ : IsZero
      (TopCat.reducedSingularHomology ((Opens.toTopCat X).obj V) 1)) :
    IsIso (twoOpenReducedMayerVietorisδZero U V hUV) :=
  twoOpenReducedMayerVietorisδZero_isIso_of_acyclic_opens
    U V hUV hU₀ hV₀ hU₁ hV₁

private noncomputable def case011 {X : TopCat.{u}} :
    TopCat.reducedSingularHomology X 1 ⟶
      TopCat.reducedSingularHomology
        ((Opens.toTopCat X).obj ((⊤ : Opens X) ⊓ ⊤)) 0 :=
  twoOpenReducedMayerVietorisδZero ⊤ ⊤ (by simp)

private noncomputable def case012 {X : TopCat.{u}} :
    TopCat.reducedSingularHomology X 1 ⟶
      TopCat.reducedSingularHomology
        ((Opens.toTopCat X).obj ((⊥ : Opens X) ⊓ ⊤)) 0 :=
  twoOpenReducedMayerVietorisδZero ⊥ ⊤ (by simp)

private noncomputable def case013 {X : TopCat.{u}} :
    TopCat.reducedSingularHomology X 1 ⟶
      TopCat.reducedSingularHomology
        ((Opens.toTopCat X).obj ((⊤ : Opens X) ⊓ ⊥)) 0 :=
  twoOpenReducedMayerVietorisδZero ⊤ ⊥ (by simp)

private noncomputable def case014 :
    TopCat.reducedSingularHomology TopCat.emptySpace.{u} 1 ⟶
      TopCat.reducedSingularHomology
        ((Opens.toTopCat TopCat.emptySpace.{u}).obj
          ((⊥ : Opens TopCat.emptySpace.{u}) ⊓ ⊥)) 0 :=
  twoOpenReducedMayerVietorisδZero ⊥ ⊥ (by ext x; exact x.down.elim)

private theorem case015 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (hDisjoint : U ⊓ V = ⊥) : U ⊓ V = ⊥ := by
  have _ := twoOpenReducedMayerVietorisδZero U V hUV
  have _ := twoOpenReducedMayerVietoris_exact_intersectionZero U V hUV
  exact hDisjoint

private theorem case016 (X : TopCat.{u + 1}) [ContractibleSpace (X : Type (u + 1))]
    (n : ℕ) : IsZero (TopCat.reducedSingularHomology X n) :=
  TopCat.isZero_reducedSingularHomology_of_contractible X n

private theorem case017 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) : U ⊔ V = ⊤ := by
  have hUId : Set.MapsTo (𝟙 X) U U := fun _ hx ↦ hx
  have hVId : Set.MapsTo (𝟙 X) V V := fun _ hx ↦ hx
  have _ := twoOpenReducedMayerVietorisδZero_naturality
    (𝟙 X) U V U V hUId hVId hUV hUV
  exact hUV

private theorem case018 {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U V : Opens X) (U'' V'' : Opens Z)
    (hU : Set.MapsTo (f ≫ g) U U'') (hV : Set.MapsTo (f ≫ g) V V'')
    (hUV : U ⊔ V = ⊤) (hU''V'' : U'' ⊔ V'' = ⊤) : U ⊔ V = ⊤ := by
  have _ := twoOpenReducedMayerVietorisδZero_naturality
    (f ≫ g) U V U'' V'' hU hV hUV hU''V''
  exact hUV

end SphereTopologyTest
