/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

import SphereTopology.Homology.Singular.ReducedMayerVietoris
import Mathlib.Analysis.Convex.Contractible

/-!
# ReducedMayerVietoris regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.

The two-point space gives a nonzero reduced sum for the repeated whole-space
cover. Its disjoint singleton cover has exactness at the reduced biproduct but
no terminal epimorphism under the nonnegative convention.
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

/-! ## The two-point space -/

private theorem twoPointReducedHomology_not_isZero :
    ¬ IsZero (TopCat.reducedSingularHomology TopCat.twoPointSpace 0) := by
  intro h
  have hℤ : IsZero (ModuleCat.of ℤ ℤ) :=
    h.of_iso ((TopCat.reducedSingularHomologyZeroIso TopCat.twoPointSpace) ≪≫
      TopCat.reducedSingularHomologyZeroTwoPointIntegerIso).symm
  let _ : Subsingleton ℤ := ModuleCat.subsingleton_of_isZero hℤ
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (Subsingleton.elim _ _)

private theorem twoPointTopCover_sum_epi :
    Epi (twoOpenReducedMayerVietorisFromBiprodZero
      (⊤ : Opens TopCat.twoPointSpace) ⊤) :=
  twoOpenReducedMayerVietorisFromBiprodZero_epi ⊤ ⊤ (by simp)
    ⟨⟨false, by simp⟩⟩

/-- The reduced sum sends the first summand's two-point basis to the ambient
basis, so its value is nonzero in the integer coefficient coordinate. -/
private theorem twoPointTopCover_sum_basis :
    TopCat.twoPointReducedBasis ≫
        (TopCat.reducedSingularHomologyZeroIso TopCat.twoPointSpace).inv ≫
        TopCat.reducedSingularHomologyMap
          (Opens.inclusionTopIso TopCat.twoPointSpace).inv 0 ≫
        biprod.inl ≫
        twoOpenReducedMayerVietorisFromBiprodZero
          (⊤ : Opens TopCat.twoPointSpace) ⊤ ≫
        (TopCat.reducedSingularHomologyZeroIso TopCat.twoPointSpace).hom ≫
        TopCat.reducedSingularHomologyZeroTwoPointIso.hom =
      𝟙 TopCat.singularHomologyIntegerCoefficients := by
  rw [twoOpenReducedMayerVietorisFromBiprodZero_inl_assoc]
  have htop : (⊤ : Opens TopCat.twoPointSpace).inclusion' =
      (Opens.inclusionTopIso TopCat.twoPointSpace).hom := rfl
  rw [htop, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    (TopCat.reducedSingularHomologyFunctor 0).map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc]
  exact TopCat.reducedSingularHomologyZeroTwoPointIso.inv_hom_id

/-- For the repeated whole-space cover, exactness identifies a nonzero
image of the difference with the kernel of the sum. In integer coordinates
that image contains the vector `(e,-e)` for a nonzero two-point class `e`. -/
private theorem twoPointTopCover_exact_nonzero_difference :
    (ShortComplex.mk
      (twoOpenReducedMayerVietorisFromIntersectionZero
        (⊤ : Opens TopCat.twoPointSpace) ⊤)
      (twoOpenReducedMayerVietorisFromBiprodZero
        (⊤ : Opens TopCat.twoPointSpace) ⊤)
      (twoOpenReducedMayerVietorisFromIntersectionZero_comp_fromBiprod
        (⊤ : Opens TopCat.twoPointSpace) ⊤)).Exact ∧
      twoOpenReducedMayerVietorisFromIntersectionZero
        (⊤ : Opens TopCat.twoPointSpace) ⊤ ≠ 0 := by
  refine ⟨twoOpenReducedMayerVietoris_exact_biprodZero
    (⊤ : Opens TopCat.twoPointSpace) ⊤ (by simp), ?_⟩
  intro h
  have hleft : TopCat.reducedSingularHomologyMap
      (twoOpenIntersectionToLeft (⊤ : Opens TopCat.twoPointSpace) ⊤) 0 = 0 := by
    simpa only [twoOpenReducedMayerVietorisFromIntersectionZero,
      biprod.lift_fst, zero_comp] using congrArg (· ≫ biprod.fst) h
  have hzero : TopCat.reducedSingularHomologyMap
      (((⊤ : Opens TopCat.twoPointSpace) ⊓ ⊤).inclusion') 0 = 0 := by
    rw [← twoOpenIntersectionToLeft_comp]
    calc
      _ = TopCat.reducedSingularHomologyMap
          (twoOpenIntersectionToLeft (⊤ : Opens TopCat.twoPointSpace) ⊤) 0 ≫
          TopCat.reducedSingularHomologyMap
            (⊤ : Opens TopCat.twoPointSpace).inclusion' 0 :=
        (TopCat.reducedSingularHomologyFunctor 0).map_comp _ _
      _ = 0 := by rw [hleft, zero_comp]
  have hIso (U : Opens TopCat.twoPointSpace) (hU : U = ⊤) : IsIso U.inclusion' := by
    subst U
    exact (inferInstance : IsIso (Opens.inclusionTopIso TopCat.twoPointSpace).hom)
  have : IsIso (((⊤ : Opens TopCat.twoPointSpace) ⊓ ⊤).inclusion') :=
    hIso _ (by simp)
  exact twoPointReducedHomology_not_isZero
    (IsZero.of_epi_eq_zero _ hzero)

private def twoPointFalseOpen : Opens TopCat.twoPointSpace :=
  ⟨{false}, isOpen_discrete _⟩

private def twoPointTrueOpen : Opens TopCat.twoPointSpace :=
  ⟨{true}, isOpen_discrete _⟩

private theorem twoPointSingletonCover :
    twoPointFalseOpen ⊔ twoPointTrueOpen = ⊤ := by
  ext b
  cases b <;> simp [twoPointFalseOpen, twoPointTrueOpen]

private theorem twoPointSingletonOpens_nonempty :
    Nonempty ((Opens.toTopCat TopCat.twoPointSpace).obj twoPointFalseOpen) ∧
      Nonempty ((Opens.toTopCat TopCat.twoPointSpace).obj twoPointTrueOpen) := by
  exact ⟨⟨⟨false, by simp [twoPointFalseOpen]⟩⟩,
    ⟨⟨true, by simp [twoPointTrueOpen]⟩⟩⟩

private theorem twoPointSingletonIntersection_isEmpty :
    IsEmpty ((Opens.toTopCat TopCat.twoPointSpace).obj
      (twoPointFalseOpen ⊓ twoPointTrueOpen)) := by
  refine ⟨?_⟩
  rintro ⟨b, hb⟩
  cases b <;> simp [twoPointFalseOpen, twoPointTrueOpen] at hb

/-- The disjoint singleton cover has exactness at the reduced biproduct, which
is zero, but a nonzero ambient reduced group prevents the sum from being epic. -/
private theorem twoPointDisjointCover_boundary :
    (ShortComplex.mk
      (twoOpenReducedMayerVietorisFromIntersectionZero
        twoPointFalseOpen twoPointTrueOpen)
      (twoOpenReducedMayerVietorisFromBiprodZero
        twoPointFalseOpen twoPointTrueOpen)
      (twoOpenReducedMayerVietorisFromIntersectionZero_comp_fromBiprod
        twoPointFalseOpen twoPointTrueOpen)).Exact ∧
      IsZero
        (TopCat.reducedSingularHomology
            ((Opens.toTopCat TopCat.twoPointSpace).obj twoPointFalseOpen) 0 ⊞
          TopCat.reducedSingularHomology
            ((Opens.toTopCat TopCat.twoPointSpace).obj twoPointTrueOpen) 0) ∧
      ¬ IsZero (TopCat.reducedSingularHomology TopCat.twoPointSpace 0) ∧
      ¬ Epi (twoOpenReducedMayerVietorisFromBiprodZero
        twoPointFalseOpen twoPointTrueOpen) := by
  refine ⟨twoOpenReducedMayerVietoris_exact_biprodZero
    twoPointFalseOpen twoPointTrueOpen twoPointSingletonCover, ?_⟩
  have hU : IsZero (TopCat.reducedSingularHomology
      ((Opens.toTopCat TopCat.twoPointSpace).obj twoPointFalseOpen) 0) := by
    let _ := twoPointSingletonOpens_nonempty.1
    let _ : Subsingleton ((Opens.toTopCat TopCat.twoPointSpace).obj twoPointFalseOpen) :=
      ⟨fun x y ↦ Subtype.ext (by
        have hx : x.val = false := x.property
        have hy : y.val = false := y.property
        exact hx.trans hy.symm)⟩
    exact TopCat.isZero_reducedSingularHomology_of_contractible _ 0
  have hV : IsZero (TopCat.reducedSingularHomology
      ((Opens.toTopCat TopCat.twoPointSpace).obj twoPointTrueOpen) 0) := by
    let _ := twoPointSingletonOpens_nonempty.2
    let _ : Subsingleton ((Opens.toTopCat TopCat.twoPointSpace).obj twoPointTrueOpen) :=
      ⟨fun x y ↦ Subtype.ext (by
        have hx : x.val = true := x.property
        have hy : y.val = true := y.property
        exact hx.trans hy.symm)⟩
    exact TopCat.isZero_reducedSingularHomology_of_contractible _ 0
  have hB := (biprod_isZero_iff _ _).2 ⟨hU, hV⟩
  refine ⟨hB, twoPointReducedHomology_not_isZero, ?_⟩
  intro hEpi
  exact twoPointReducedHomology_not_isZero
    (hB.of_epi (twoOpenReducedMayerVietorisFromBiprodZero
      twoPointFalseOpen twoPointTrueOpen))

end SphereTopologyTest
