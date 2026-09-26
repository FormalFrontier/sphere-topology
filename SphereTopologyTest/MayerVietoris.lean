/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker A, Prism. See README.md for internal reuse.
module

import SphereTopology.Homology.Singular.MayerVietoris

/-!
# MayerVietoris regression checks

Persistent private clients preserve the earlier example statements and proofs.
Axiom diagnostics are scoped to names visible in the imported environment; they
do not establish a full stored-occurrence census or separate proof recheck.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace SphereTopologyTest

open AlgebraicTopology

universe u

/- The chain complex, cover-small inclusion, accepted quasi-isomorphism and
resulting short exact sequence all expose the ambient universe. -/
private theorem case001 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) : True := by
  have _ := integralSingularChains X
  have _ := smallSingularChainInclusion (TopCat.twoOpenCover U V)
  have _ := quasiIso_smallSingularChainInclusion (TopCat.twoOpenCover U V)
    (TopCat.isOpenCover_twoOpenCover hUV)
  have _ := twoOpenSmallShortExact (X := X) U V
  have _ := smallSingularHomologyIso (TopCat.twoOpenCover U V)
    (TopCat.isOpenCover_twoOpenCover hUV) n
  trivial

private theorem case002 {X : TopCat.{u}} (U V : Opens X)
    (hUId : Set.MapsTo (𝟙 X) U U) (hVId : Set.MapsTo (𝟙 X) V V)
    (hUV : U ⊔ V = ⊤) (n : ℕ) :
    twoOpenMayerVietorisSpaceMap (𝟙 X) U V U V hUId hVId hUV hUV n = 𝟙 _ := by
  have _ : Set.MapsTo (𝟙 X) U U := fun _ hx ↦ hx
  have _ : Set.MapsTo (𝟙 X) V V := fun _ hx ↦ hx
  rw [twoOpenMayerVietorisSpaceMap_eq]
  simp [integralSingularChainMap]

private theorem case003 {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U V : Opens X) (U' V' : Opens Y) (U'' V'' : Opens Z)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hU' : Set.MapsTo g U' U'') (hV' : Set.MapsTo g V' V'')
    (hUcomp : Set.MapsTo (f ≫ g) U U'') (hVcomp : Set.MapsTo (f ≫ g) V V'')
    (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤)
    (hU''V'' : U'' ⊔ V'' = ⊤) (n : ℕ) :
    twoOpenMayerVietorisSpaceMap (f ≫ g) U V U'' V''
        hUcomp hVcomp hUV hU''V'' n =
      twoOpenMayerVietorisSpaceMap f U V U' V' hU hV hUV hU'V' n ≫
        twoOpenMayerVietorisSpaceMap g U' V' U'' V'' hU' hV' hU'V' hU''V'' n := by
  have _ : Set.MapsTo (f ≫ g) U U'' := fun _ hx ↦ hU' (hU hx)
  have _ : Set.MapsTo (f ≫ g) V V'' := fun _ hx ↦ hV' (hV hx)
  rw [twoOpenMayerVietorisSpaceMap_eq, twoOpenMayerVietorisSpaceMap_eq,
    twoOpenMayerVietorisSpaceMap_eq, ← HomologicalComplex.homologyMap_comp]
  simp [integralSingularChainMap]

/- The two degenerate ordered covers use the same generic exactness API. -/
private theorem case004 (X : TopCat.{u}) (n : ℕ) : True := by
  have _ := twoOpenMayerVietoris_exact_at_space
    (X := X) (⊤ : Opens X) ⊥ (by simp) n
  trivial

private theorem case005 (X : TopCat.{u}) (n : ℕ) : True := by
  have _ := twoOpenMayerVietoris_exact_at_space
    (X := X) (⊥ : Opens X) ⊤ (by simp) n
  trivial

/- The construction also applies to the empty ambient space. -/
private theorem case006 (n : ℕ) : True := by
  have _ := twoOpenMayerVietoris_exact_at_intersection
    (X := TopCat.of Empty) ⊤ ⊥ (by simp) n
  trivial

/- An empty intersection, including a disjoint two-open cover, requires no
nonemptiness or connectedness hypothesis. -/
private theorem case007 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (hdisjoint : U ⊓ V = ⊥) (n : ℕ) : True := by
  have _ := hdisjoint
  have _ := twoOpenMayerVietoris_exact_at_intersection
    (X := X) U V hUV n
  trivial

/- At `n = 0` this is the exact segment ending in the connecting boundary
`H₁(X;ℤ) ⟶ H₀(U∩V;ℤ)`. -/
private theorem case008 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) : True := by
  have _ := twoOpenMayerVietoris_exact_at_space (X := X) U V hUV 0
  trivial

private theorem case009 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) : True := by
  have _ := twoOpenMayerVietorisδ (X := X) U V hUV 0
  trivial

/- Naturality is universe-polymorphic and displays the ordinary
singular-homology map induced by the continuous map. -/
private theorem case010 {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) (n : ℕ) : True := by
  have _ := twoOpenMayerVietorisδ_naturality_induced
    (X := X) (Y := Y) f U V U' V' hU hV hUV hU'V' n
  trivial

/- Identity and composite maps instantiate the same naturality surface. -/
private theorem case011 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) : True := by
  have _ := twoOpenMayerVietorisδ_naturality_induced
    (X := X) (Y := X) (𝟙 X) U V U V (fun _ hx ↦ hx) (fun _ hx ↦ hx)
      hUV hUV n
  trivial

private theorem case012 {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U V : Opens X) (U' V' : Opens Y) (U'' V'' : Opens Z)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hU' : Set.MapsTo g U' U'') (hV' : Set.MapsTo g V' V'')
    (hUV : U ⊔ V = ⊤) (hU''V'' : U'' ⊔ V'' = ⊤) (n : ℕ) : True := by
  have _ := twoOpenMayerVietorisδ_naturality_induced
    (X := X) (Y := Z) (f ≫ g) U V U'' V''
      (fun _ hx ↦ hU' (hU hx)) (fun _ hx ↦ hV' (hV hx)) hUV hU''V'' n
  trivial

/- The ordered swap has a visible integral minus sign; cover reindexing itself
acts as the identity on ambient homology. -/
private theorem case013 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (n : ℕ) : True := by
  have _ := twoOpenMayerVietorisδ_swap_eq_neg (X := X) U V hUV
    (by simpa [sup_comm] using hUV) n
  trivial

private theorem case014 {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (n : ℕ) : True := by
  have _ := twoOpenMayerVietorisSwapSpaceMap_eq_id (X := X) U V hUV
    (by simpa [sup_comm] using hUV) n
  trivial

/- The explicit chain maps retain the ordered `(c,-c)`/sum convention. -/
private theorem case015 {X : TopCat.{u}} (U V : Opens X) : True := by
  have _ := twoOpenDifference_comp_sum (X := X) U V
  trivial

end SphereTopologyTest
