/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

public import SphereTopology.Homology.Singular.SmallChains
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Singular Mayer--Vietoris for two open sets

This file fixes the ordered convention

`C(U ∩ V) → C(U) ⊕ C(V),  c ↦ (c, -c)`

followed by addition into the chains small in the ordered cover `(U,V)`.
The resulting degreewise short exact sequence gives the ordinary integral
singular Mayer--Vietoris connecting morphism and its long exact sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace
open scoped Simplicial

noncomputable section

universe u

namespace TopCat

/-- The simplicial subset of singular simplices of `X` whose image is contained
in the open subset `U`. -/
def openSingularSet {X : TopCat.{u}} (U : Opens X) :
    (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map U.inclusion')

/-- Membership in `openSingularSet U` means exactly that the range of the
singular simplex is contained in `U`. -/
theorem mem_openSingularSet_iff {X : TopCat.{u}} (U : Opens X)
    {n : SimplexCategoryᵒᵖ} (x : (TopCat.toSSet.obj X).obj n) :
    x ∈ (openSingularSet U).obj n ↔
      Set.range (X.toSSetObjEquiv n x) ⊆ U := by
  constructor
  · rintro ⟨y, rfl⟩ _ ⟨z, rfl⟩
    exact (((Opens.toTopCat X).obj U).toSSetObjEquiv n y z).2
  · intro hx
    let y' : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)),
        (Opens.toTopCat X).obj U) :=
      ⟨fun z ↦ ⟨X.toSSetObjEquiv n x z, hx ⟨z, rfl⟩⟩,
        Continuous.subtype_mk (X.toSSetObjEquiv n x).continuous _⟩
    let y := (((Opens.toTopCat X).obj U).toSSetObjEquiv n).symm y'
    refine ⟨y, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext z
    change (y' z).1 = X.toSSetObjEquiv n x z
    rfl

/-- The map on ambient open-singular subcomplexes induced by a map of spaces
which sends one open subset into another. -/
def openSingularSetMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U : Opens X) (W : Opens Y) (h : Set.MapsTo f U W) :
    (openSingularSet U : SSet.{u}) ⟶ (openSingularSet W : SSet.{u}) where
  app n := ↾fun x ↦ ⟨(TopCat.toSSet.map f).app n x.1, by
    rw [mem_openSingularSet_iff]
    rintro _ ⟨z, rfl⟩
    apply h
    change X.toSSetObjEquiv n x.1 z ∈ U
    exact (mem_openSingularSet_iff U x.1).mp x.2 ⟨z, rfl⟩⟩
  naturality _ _ _ := by rfl

@[reassoc]
theorem openSingularSetMap_comp_inclusion {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U : Opens X) (W : Opens Y) (h : Set.MapsTo f U W) :
    openSingularSetMap f U W h ≫ (openSingularSet W).ι =
      (openSingularSet U).ι ≫ TopCat.toSSet.map f := rfl

/-- The induced map on intersections of two ambient open-singular
subcomplexes. -/
def openSingularSetInfMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    ((openSingularSet U ⊓ openSingularSet V :
        (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) ⟶
      ((openSingularSet U' ⊓ openSingularSet V' :
        (TopCat.toSSet.obj Y).Subcomplex) : SSet.{u}) where
  app n := ↾fun x ↦ ⟨(TopCat.toSSet.map f).app n x.1, by
    constructor
    · exact ((openSingularSetMap f U U' hU).app n ⟨x.1, x.2.1⟩).2
    · exact ((openSingularSetMap f V V' hV).app n ⟨x.1, x.2.2⟩).2⟩
  naturality _ _ _ := by rfl

/-- The induced map on unions of two ambient open-singular subcomplexes. -/
def openSingularSetSupMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    ((openSingularSet U ⊔ openSingularSet V :
        (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) ⟶
      ((openSingularSet U' ⊔ openSingularSet V' :
        (TopCat.toSSet.obj Y).Subcomplex) : SSet.{u}) where
  app n := ↾fun x ↦ ⟨(TopCat.toSSet.map f).app n x.1, by
    rcases x.2 with hx | hx
    · exact Or.inl ((openSingularSetMap f U U' hU).app n ⟨x.1, hx⟩).2
    · exact Or.inr ((openSingularSetMap f V V' hV).app n ⟨x.1, hx⟩).2⟩
  naturality _ _ _ := by rfl

@[reassoc]
theorem openSingularSetInfMap_comp_left {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    openSingularSetInfMap f U V U' V' hU hV ≫
        SSet.Subcomplex.homOfLE inf_le_left =
      SSet.Subcomplex.homOfLE inf_le_left ≫ openSingularSetMap f U U' hU := by
  rfl

@[reassoc]
theorem openSingularSetInfMap_comp_right {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    openSingularSetInfMap f U V U' V' hU hV ≫
        SSet.Subcomplex.homOfLE inf_le_right =
      SSet.Subcomplex.homOfLE inf_le_right ≫ openSingularSetMap f V V' hV := by
  rfl

@[reassoc]
theorem openSingularSetMap_comp_supLeft {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    openSingularSetMap f U U' hU ≫ SSet.Subcomplex.homOfLE le_sup_left =
      SSet.Subcomplex.homOfLE le_sup_left ≫
        openSingularSetSupMap f U V U' V' hU hV := by
  rfl

@[reassoc]
theorem openSingularSetMap_comp_supRight {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    openSingularSetMap f V V' hV ≫ SSet.Subcomplex.homOfLE le_sup_right =
      SSet.Subcomplex.homOfLE le_sup_right ≫
        openSingularSetSupMap f U V U' V' hU hV := by
  rfl

private noncomputable def openSingularSetToOpen {X : TopCat.{u}} (U : Opens X) :
    (openSingularSet U : SSet.{u}) ⟶ TopCat.toSSet.obj ((Opens.toTopCat X).obj U) where
  app n := ↾fun x ↦ (((Opens.toTopCat X).obj U).toSSetObjEquiv n).symm
    ⟨fun z ↦ ⟨X.toSSetObjEquiv n x.1 z,
      (mem_openSingularSet_iff U x.1).mp x.2 ⟨z, rfl⟩⟩,
      Continuous.subtype_mk (X.toSSetObjEquiv n x.1).continuous _⟩
  naturality n m f := by
    ext x
    apply (((Opens.toTopCat X).obj U).toSSetObjEquiv m).injective
    ext z
    apply Subtype.ext
    rfl

/-- Singular simplices of the open subspace `U` identify with singular
simplices of `X` whose image is contained in `U`. -/
@[no_expose]
noncomputable def openSingularSetIso {X : TopCat.{u}} (U : Opens X) :
    TopCat.toSSet.obj ((Opens.toTopCat X).obj U) ≅ (openSingularSet U : SSet.{u}) where
  hom := SSet.Subcomplex.toRange (TopCat.toSSet.map U.inclusion')
  inv := openSingularSetToOpen U
  hom_inv_id := by
    ext n y
    apply (((Opens.toTopCat X).obj U).toSSetObjEquiv n).injective
    ext z
    apply Subtype.ext
    rfl
  inv_hom_id := by
    ext n x
    apply Subtype.ext
    apply (X.toSSetObjEquiv n).injective
    ext z
    rfl

/-- The ordered two-member family `(U,V)`.  The Boolean value `false` indexes
`U`, and `true` indexes `V`. -/
def twoOpenCover {X : TopCat.{u}} (U V : Opens X) : Bool → Opens X :=
  fun b ↦ if b then V else U

/-- The ordered family `(U,V)` covers exactly when `U ⊔ V = ⊤`. -/
theorem isOpenCover_twoOpenCover {X : TopCat.{u}} {U V : Opens X}
    (hUV : U ⊔ V = ⊤) : IsOpenCover (twoOpenCover U V) := by
  rw [IsOpenCover]
  rw [show ⨆ b : Bool, twoOpenCover U V b = U ⊔ V by
    ext x
    simp [twoOpenCover]]
  exact hUV

/-- Intersecting the ambient singular subcomplexes agrees with taking the
singular subcomplex of the intersection. -/
theorem openSingularSet_inf {X : TopCat.{u}} (U V : Opens X) :
    openSingularSet U ⊓ openSingularSet V = openSingularSet (U ⊓ V) := by
  ext n x
  change (x ∈ (openSingularSet U).obj n ∧ x ∈ (openSingularSet V).obj n) ↔
    x ∈ (openSingularSet (U ⊓ V)).obj n
  rw [mem_openSingularSet_iff, mem_openSingularSet_iff,
    mem_openSingularSet_iff]
  simp only [Opens.coe_inf, Set.subset_inter_iff]

/-- The union of the two ambient singular subcomplexes is the accepted
cover-small singular set for the ordered family `(U,V)`. -/
theorem openSingularSet_sup {X : TopCat.{u}} (U V : Opens X) :
    openSingularSet U ⊔ openSingularSet V = smallSingularSet (twoOpenCover U V) := by
  ext n x
  change (x ∈ (openSingularSet U).obj n ∨ x ∈ (openSingularSet V).obj n) ↔
    x ∈ (smallSingularSet (twoOpenCover U V)).obj n
  rw [mem_openSingularSet_iff, mem_openSingularSet_iff,
    mem_smallSingularSet_iff]
  constructor
  · rintro (hx | hx)
    · exact ⟨false, by simpa [twoOpenCover] using hx⟩
    · exact ⟨true, by simpa [twoOpenCover] using hx⟩
  · rintro ⟨i, hi⟩
    cases i with
    | false => exact Or.inl (by simpa [twoOpenCover] using hi)
    | true => exact Or.inr (by simpa [twoOpenCover] using hi)

/-- A continuous map restricted to a map between open subspaces. -/
def openMap {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Opens X) (W : Opens Y)
    (h : Set.MapsTo f U W) : (Opens.toTopCat X).obj U ⟶ (Opens.toTopCat Y).obj W :=
  TopCat.ofHom ⟨fun x ↦ ⟨f x.1, h x.2⟩,
    Continuous.subtype_mk (f.hom.continuous.comp continuous_subtype_val) _⟩

@[reassoc]
theorem openMap_comp_inclusion {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U : Opens X) (W : Opens Y) (h : Set.MapsTo f U W) :
    openMap f U W h ≫ W.inclusion' = U.inclusion' ≫ f := rfl

/-- A map respecting `U` and `V` respects the corresponding ordered Boolean
covers without changing the index. -/
theorem mapsTo_twoOpenCover {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    ∀ i, ∃ j, Set.MapsTo f (twoOpenCover U V i) (twoOpenCover U' V' j) := by
  intro i
  refine ⟨i, ?_⟩
  cases i with
  | false => simpa [twoOpenCover] using hU
  | true => simpa [twoOpenCover] using hV

end TopCat

namespace AlgebraicTopology

/-- The chain isomorphism identifying ordinary singular chains of an open
subspace with the corresponding simplicial subcomplex in the ambient space. -/
noncomputable def openSingularChainIso {X : TopCat.{u}} (U : Opens X) :
    ((TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).chainComplex integerCoefficients.{u}) ≅
      ((TopCat.openSingularSet U : SSet.{u}).chainComplex integerCoefficients.{u}) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).mapIso
    (TopCat.openSingularSetIso U)

private theorem chainComplexFunctor_preservesWalkingSpan :
    PreservesColimitsOfShape WalkingSpan
      ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}) := by
  have : PreservesColimitsOfShape WalkingSpan
      (alternatingFaceMapComplex (ModuleCat.{u} ℤ)) := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape WalkingSpan
      ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{u} ℤ)).obj
        (op (SimplexCategory.mk n)))
    infer_instance
  change PreservesColimitsOfShape WalkingSpan
    (((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (ModuleCat.{u} ℤ)).obj
      (sigmaConst.obj integerCoefficients.{u})) ⋙
      alternatingFaceMapComplex (ModuleCat.{u} ℤ))
  infer_instance

/-- Integer simplicial chains preserve pushout squares of simplicial sets. -/
theorem isPushout_chainComplexMap
    {W X Y Z : SSet.{u}} {f : W ⟶ X} {g : W ⟶ Y}
    {i : X ⟶ Z} {j : Y ⟶ Z} (h : IsPushout f g i j) :
    IsPushout (SSet.chainComplexMap f integerCoefficients.{u})
      (SSet.chainComplexMap g integerCoefficients.{u})
      (SSet.chainComplexMap i integerCoefficients.{u})
      (SSet.chainComplexMap j integerCoefficients.{u}) := by
  let : PreservesColimitsOfShape WalkingSpan
      ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}) :=
    chainComplexFunctor_preservesWalkingSpan
  exact h.map ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u})

/-- An inclusion of simplicial subcomplexes induces a monomorphism on integer
chain complexes. -/
theorem mono_chainComplexMap_subcomplex {X : SSet.{u}} {A B : X.Subcomplex}
    (h : A ≤ B) :
    Mono (SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) integerCoefficients.{u}) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono ((sigmaConst.obj integerCoefficients.{u}).map
    ((SSet.Subcomplex.homOfLE h).app (op (SimplexCategory.mk n))))
  infer_instance

/-- The pushout square formed by the intersection and union of two simplicial
subcomplexes. -/
theorem subcomplex_inter_union_isPushout {X : SSet.{u}} (A B : X.Subcomplex) :
    IsPushout
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
      (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
      (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) :=
  (show SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) from
    { sup_eq := rfl
      inf_eq := rfl }).isPushout

/-- The ordered difference/sum short complex of integer chains associated to
two simplicial subcomplexes.  Its first map is `(c,-c)` and its second map is
addition. -/
def subcomplexUnionShortComplex {X : SSet.{u}} (A B : X.Subcomplex) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  (isPushout_chainComplexMap (subcomplex_inter_union_isPushout A B)).shortComplex

/-- The difference/sum chain complex for two simplicial subcomplexes is short
exact. -/
theorem subcomplexUnionShortExact {X : SSet.{u}} (A B : X.Subcomplex) :
    (subcomplexUnionShortComplex A B).ShortExact := by
  let h := isPushout_chainComplexMap (subcomplex_inter_union_isPushout A B)
  have hmonoLeft : Mono
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        integerCoefficients.{u}) :=
    mono_chainComplexMap_subcomplex _
  have hmono : Mono h.shortComplex.f := by
    change Mono (biprod.lift
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        integerCoefficients.{u})
      (-(SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
        integerCoefficients.{u})))
    infer_instance
  have hepi : Epi h.shortComplex.g := h.epi_shortComplex_g
  exact
    { exact := ShortComplex.exact_of_g_is_cokernel _ h.isColimitCokernelCofork
      mono_f := hmono
      epi_g := hepi }

/-- Swapping the two intersection factors at chain level. -/
noncomputable def subcomplexInfSwapChainIso {X : SSet.{u}} (A B : X.Subcomplex) :
    ((A ⊓ B : X.Subcomplex) : SSet.{u}).chainComplex integerCoefficients.{u} ≅
      ((B ⊓ A : X.Subcomplex) : SSet.{u}).chainComplex integerCoefficients.{u} :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).mapIso
    (SSet.Subcomplex.eqToIso (inf_comm A B))

/-- Swapping the two union factors at chain level. -/
noncomputable def subcomplexSupSwapChainIso {X : SSet.{u}} (A B : X.Subcomplex) :
    ((A ⊔ B : X.Subcomplex) : SSet.{u}).chainComplex integerCoefficients.{u} ≅
      ((B ⊔ A : X.Subcomplex) : SSet.{u}).chainComplex integerCoefficients.{u} :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).mapIso
    (SSet.Subcomplex.eqToIso (sup_comm A B))

/-- Swapping the two members of the ordered difference/sum sequence.  The
intersection term is multiplied by `-1`, the middle term is braided, and the
union term is merely transported across commutativity of union. -/
noncomputable def subcomplexUnionSwapIso {X : SSet.{u}} (A B : X.Subcomplex) :
    subcomplexUnionShortComplex A B ≅ subcomplexUnionShortComplex B A :=
  ShortComplex.isoMk (-(subcomplexInfSwapChainIso A B))
    (biprod.braiding _ _) (subcomplexSupSwapChainIso A B)
    (by
      dsimp [subcomplexUnionShortComplex, CommSq.shortComplex,
        subcomplexInfSwapChainIso]
      apply biprod.hom_ext
      · simp [← Functor.map_comp]
        congr 1
      · simp [← Functor.map_comp]
        congr 1)
    (by
      dsimp [subcomplexUnionShortComplex, CommSq.shortComplex,
        subcomplexSupSwapChainIso]
      apply biprod.hom_ext'
      · simp [← Functor.map_comp]
        congr 1
      · simp [← Functor.map_comp]
        congr 1)

/-- The connecting map of the union short exact sequence, from degree `n+1`
to degree `n`. -/
def subcomplexUnionδ {X : SSet.{u}} (A B : X.Subcomplex) (n : ℕ) :
    ((A ⊔ B : X.Subcomplex) : SSet.{u}).homology integerCoefficients.{u} (n + 1) ⟶
      ((A ⊓ B : X.Subcomplex) : SSet.{u}).homology integerCoefficients.{u} n :=
  (subcomplexUnionShortExact A B).δ (n + 1) n (by simp)

/-- Exactness at the intersection term after the connecting map. -/
theorem subcomplexUnion_exact₁ {X : SSet.{u}} (A B : X.Subcomplex) (n : ℕ) :
    (ShortComplex.mk
      (subcomplexUnionδ A B n)
      (HomologicalComplex.homologyMap (subcomplexUnionShortComplex A B).f n)
      ((subcomplexUnionShortExact A B).δ_comp (n + 1) n (by simp))).Exact :=
  (subcomplexUnionShortExact A B).homology_exact₁ (n + 1) n (by simp)

/-- Exactness at the direct-sum chain-complex homology term. -/
theorem subcomplexUnion_exact₂ {X : SSet.{u}} (A B : X.Subcomplex) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (subcomplexUnionShortComplex A B).f n)
      (HomologicalComplex.homologyMap (subcomplexUnionShortComplex A B).g n)
      (by
        rw [← HomologicalComplex.homologyMap_comp,
          (subcomplexUnionShortComplex A B).zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  (subcomplexUnionShortExact A B).homology_exact₂ n

/-- Exactness at the union term before the connecting map. -/
theorem subcomplexUnion_exact₃ {X : SSet.{u}} (A B : X.Subcomplex) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (subcomplexUnionShortComplex A B).g (n + 1))
      (subcomplexUnionδ A B n)
      ((subcomplexUnionShortExact A B).comp_δ (n + 1) n (by simp))).Exact :=
  (subcomplexUnionShortExact A B).homology_exact₃ (n + 1) n (by simp)

/-- Swapping the ordered pair multiplies the connecting morphism by `-1`,
after the canonical transports across commutativity of intersection and union.
This records the sign convention independently of any topological client. -/
theorem subcomplexUnionδ_swap {X : SSet.{u}} (A B : X.Subcomplex) (n : ℕ) :
    subcomplexUnionδ A B n ≫
        HomologicalComplex.homologyMap (subcomplexInfSwapChainIso A B).hom n =
      -(HomologicalComplex.homologyMap (subcomplexSupSwapChainIso A B).hom (n + 1) ≫
        subcomplexUnionδ B A n) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (subcomplexUnionSwapIso A B).hom
    (subcomplexUnionShortExact A B) (subcomplexUnionShortExact B A)
    (n + 1) n (by simp)
  change subcomplexUnionδ A B n ≫
      HomologicalComplex.homologyMap (-(subcomplexInfSwapChainIso A B).hom) n =
    HomologicalComplex.homologyMap (subcomplexSupSwapChainIso A B).hom (n + 1) ≫
      subcomplexUnionδ B A n at h
  rw [HomologicalComplex.homologyMap_neg, Preadditive.comp_neg] at h
  exact neg_eq_iff_eq_neg.mp h

/-- The integral singular chain complex of a topological space. -/
abbrev integralSingularChains (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).obj X

/-- The integral singular chain map induced by a continuous map. -/
def integralSingularChainMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    integralSingularChains X ⟶ integralSingularChains Y :=
  ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map f

/-- Inclusion of `U ∩ V` into the first open set. -/
def twoOpenIntersectionToLeft {X : TopCat.{u}} (U V : Opens X) :
    (Opens.toTopCat X).obj (U ⊓ V) ⟶ (Opens.toTopCat X).obj U :=
  TopCat.openMap (f := 𝟙 X) (U ⊓ V) U (fun _ hx ↦ hx.1)

/-- Inclusion of `U ∩ V` into the second open set. -/
def twoOpenIntersectionToRight {X : TopCat.{u}} (U V : Opens X) :
    (Opens.toTopCat X).obj (U ⊓ V) ⟶ (Opens.toTopCat X).obj V :=
  TopCat.openMap (f := 𝟙 X) (U ⊓ V) V (fun _ hx ↦ hx.2)

@[reassoc]
theorem twoOpenIntersectionToLeft_comp {X : TopCat.{u}} (U V : Opens X) :
    twoOpenIntersectionToLeft U V ≫ U.inclusion' = (U ⊓ V).inclusion' := by
  simpa [twoOpenIntersectionToLeft] using
    TopCat.openMap_comp_inclusion (𝟙 X) (U ⊓ V) U (fun _ hx ↦ hx.1)

@[reassoc]
theorem twoOpenIntersectionToRight_comp {X : TopCat.{u}} (U V : Opens X) :
    twoOpenIntersectionToRight U V ≫ V.inclusion' = (U ⊓ V).inclusion' := by
  simpa [twoOpenIntersectionToRight] using
    TopCat.openMap_comp_inclusion (𝟙 X) (U ⊓ V) V (fun _ hx ↦ hx.2)

/-- The ordered chain difference `c ↦ (c,-c)` induced by the two
intersection inclusions. -/
def twoOpenDifferenceChainMap {X : TopCat.{u}} (U V : Opens X) :
    integralSingularChains ((Opens.toTopCat X).obj (U ⊓ V)) ⟶
      integralSingularChains ((Opens.toTopCat X).obj U) ⊞
        integralSingularChains ((Opens.toTopCat X).obj V) :=
  biprod.lift
    (integralSingularChainMap (twoOpenIntersectionToLeft U V))
    (-integralSingularChainMap (twoOpenIntersectionToRight U V))

/-- The ordered chain sum induced by the inclusions of `U` and `V` into `X`. -/
def twoOpenSumChainMap {X : TopCat.{u}} (U V : Opens X) :
    integralSingularChains ((Opens.toTopCat X).obj U) ⊞
        integralSingularChains ((Opens.toTopCat X).obj V) ⟶
      integralSingularChains X :=
  biprod.desc (integralSingularChainMap U.inclusion')
    (integralSingularChainMap V.inclusion')

/-- The ordered difference followed by the sum is zero. -/
@[reassoc]
theorem twoOpenDifference_comp_sum {X : TopCat.{u}} (U V : Opens X) :
    twoOpenDifferenceChainMap U V ≫ twoOpenSumChainMap U V = 0 := by
  simp only [twoOpenDifferenceChainMap, twoOpenSumChainMap,
    biprod.lift_desc, Preadditive.neg_comp, integralSingularChainMap,
    ← Functor.map_comp]
  rw [twoOpenIntersectionToLeft_comp, twoOpenIntersectionToRight_comp]
  exact add_neg_cancel _

/-- The map of intersection subspaces induced by a map respecting an ordered
pair of opens. -/
def twoOpenIntersectionMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    (Opens.toTopCat X).obj (U ⊓ V) ⟶ (Opens.toTopCat Y).obj (U' ⊓ V') :=
  TopCat.openMap f (U ⊓ V) (U' ⊓ V')
    (fun _ hx ↦ ⟨hU hx.1, hV hx.2⟩)

/-- The direct-sum chain map induced by a map respecting the ordered pair. -/
def twoOpenBiprodChainMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    integralSingularChains ((Opens.toTopCat X).obj U) ⊞
        integralSingularChains ((Opens.toTopCat X).obj V) ⟶
      integralSingularChains ((Opens.toTopCat Y).obj U') ⊞
        integralSingularChains ((Opens.toTopCat Y).obj V') :=
  biprod.map
    (integralSingularChainMap (TopCat.openMap f U U' hU))
    (integralSingularChainMap (TopCat.openMap f V V' hV))

/-- The cover-small chain map induced by a map respecting the ordered pair. -/
def twoOpenSmallChainMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    smallSingularChainComplex (TopCat.twoOpenCover U V) ⟶
      smallSingularChainComplex (TopCat.twoOpenCover U' V') :=
  smallSingularChainMap f (TopCat.twoOpenCover U V) (TopCat.twoOpenCover U' V')
    (TopCat.mapsTo_twoOpenCover f U V U' V' hU hV)

/-- The chain-level difference/sum sequence inside the singular set of `X`. -/
abbrev twoOpenAmbientShortComplex {X : TopCat.{u}} (U V : Opens X) :=
  subcomplexUnionShortComplex (TopCat.openSingularSet U) (TopCat.openSingularSet V)

/-- Naturality of the ambient difference/sum short complex for maps respecting
ordered pairs of opens. -/
noncomputable def twoOpenAmbientShortComplexMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    twoOpenAmbientShortComplex U V ⟶ twoOpenAmbientShortComplex U' V' where
  τ₁ := SSet.chainComplexMap
    (TopCat.openSingularSetInfMap f U V U' V' hU hV) integerCoefficients.{u}
  τ₂ := biprod.map
    (SSet.chainComplexMap (TopCat.openSingularSetMap f U U' hU) integerCoefficients.{u})
    (SSet.chainComplexMap (TopCat.openSingularSetMap f V V' hV) integerCoefficients.{u})
  τ₃ := SSet.chainComplexMap
    (TopCat.openSingularSetSupMap f U V U' V' hU hV) integerCoefficients.{u}
  comm₁₂ := by
    dsimp [twoOpenAmbientShortComplex, subcomplexUnionShortComplex,
      CommSq.shortComplex]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst,
        biprod.lift_fst_assoc, biprod.map_fst]
      rw [← Functor.map_comp, ← Functor.map_comp,
        TopCat.openSingularSetInfMap_comp_left]
    · simp only [Category.assoc, biprod.lift_snd,
        biprod.lift_snd_assoc, biprod.map_snd, Preadditive.comp_neg,
        Preadditive.neg_comp]
      rw [← Functor.map_comp, ← Functor.map_comp,
        TopCat.openSingularSetInfMap_comp_right]
  comm₂₃ := by
    dsimp [twoOpenAmbientShortComplex, subcomplexUnionShortComplex,
      CommSq.shortComplex]
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc,
        biprod.inl_desc_assoc]
      rw [← Functor.map_comp, ← Functor.map_comp,
        TopCat.openSingularSetMap_comp_supLeft]
    · simp only [biprod.inr_map_assoc, biprod.inr_desc,
        biprod.inr_desc_assoc]
      rw [← Functor.map_comp, ← Functor.map_comp,
        TopCat.openSingularSetMap_comp_supRight]

/-- Ordinary chains on `U ∩ V` identify with the first term of the ambient
difference/sum sequence. -/
noncomputable def twoOpenIntersectionChainIso {X : TopCat.{u}} (U V : Opens X) :
    integralSingularChains ((Opens.toTopCat X).obj (U ⊓ V)) ≅
      (twoOpenAmbientShortComplex U V).X₁ :=
  (openSingularChainIso (U ⊓ V)).trans
    (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).mapIso
      (SSet.Subcomplex.eqToIso (TopCat.openSingularSet_inf U V).symm))

/-- The direct sum of ordinary chains on `U` and `V` identifies with the
middle term of the ambient difference/sum sequence. -/
noncomputable def twoOpenBiprodChainIso {X : TopCat.{u}} (U V : Opens X) :
    integralSingularChains ((Opens.toTopCat X).obj U) ⊞
        integralSingularChains ((Opens.toTopCat X).obj V) ≅
      (twoOpenAmbientShortComplex U V).X₂ :=
  biprod.mapIso (openSingularChainIso U) (openSingularChainIso V)

/-- The last ambient term identifies with chains small in the ordered cover
`(U,V)`. -/
noncomputable def twoOpenUnionChainIso {X : TopCat.{u}} (U V : Opens X) :
    (twoOpenAmbientShortComplex U V).X₃ ≅
      smallSingularChainComplex (TopCat.twoOpenCover U V) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).mapIso
    (SSet.Subcomplex.eqToIso (TopCat.openSingularSet_sup U V))

/-- The ordinary-chain / cover-small-chain short complex for the ordered pair
`(U,V)`.  Its first map uses the convention `(c,-c)`. -/
noncomputable def twoOpenSmallShortComplex {X : TopCat.{u}} (U V : Opens X) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk
    ((twoOpenIntersectionChainIso U V).hom ≫
      (twoOpenAmbientShortComplex U V).f ≫
      (twoOpenBiprodChainIso U V).inv)
    ((twoOpenBiprodChainIso U V).hom ≫
      (twoOpenAmbientShortComplex U V).g ≫
      (twoOpenUnionChainIso U V).hom)
    (by simp only [Category.assoc, Iso.inv_hom_id_assoc,
      (twoOpenAmbientShortComplex U V).zero_assoc, zero_comp, comp_zero])

/-- The ordinary/open-chain short complex identified with its ambient
subcomplex model. -/
noncomputable def twoOpenSmallToAmbientIso {X : TopCat.{u}} (U V : Opens X) :
    twoOpenSmallShortComplex U V ≅ twoOpenAmbientShortComplex U V :=
  ShortComplex.isoMk (twoOpenIntersectionChainIso U V)
    (twoOpenBiprodChainIso U V) (twoOpenUnionChainIso U V).symm
    (by simp [twoOpenSmallShortComplex])
    (by simp [twoOpenSmallShortComplex])

/-- The ordinary-chain / cover-small-chain sequence is short exact. -/
theorem twoOpenSmallShortExact {X : TopCat.{u}} (U V : Opens X) :
    (twoOpenSmallShortComplex U V).ShortExact := by
  exact ShortComplex.shortExact_of_iso
    (twoOpenSmallToAmbientIso U V).symm
    (subcomplexUnionShortExact (TopCat.openSingularSet U)
      (TopCat.openSingularSet V))

/-- Swapping the two opens in the cover-small short complex.  The first
component includes the sign forced by the convention `c ↦ (c,-c)`, the middle
component braids the two summands, and the last component reindexes the same
cover-small chains. -/
noncomputable def twoOpenSmallShortComplexSwapIso {X : TopCat.{u}}
    (U V : Opens X) :
    twoOpenSmallShortComplex U V ≅ twoOpenSmallShortComplex V U :=
  (twoOpenSmallToAmbientIso U V).trans
    ((subcomplexUnionSwapIso (TopCat.openSingularSet U)
      (TopCat.openSingularSet V)).trans
    (twoOpenSmallToAmbientIso V U).symm)

/-- The sign-free transport between the intersection-chain terms when the
ordered pair is swapped.  The minus sign removes the sign already present in
the first component of `twoOpenSmallShortComplexSwapIso`. -/
noncomputable def twoOpenIntersectionSwapChainIso {X : TopCat.{u}}
    (U V : Opens X) :
    (twoOpenSmallShortComplex U V).X₁ ≅
      (twoOpenSmallShortComplex V U).X₁ :=
  -(asIso (twoOpenSmallShortComplexSwapIso U V).hom.τ₁)

/-- Reindexing the same cover-small chains after swapping the two opens. -/
noncomputable def twoOpenCoverSwapChainIso {X : TopCat.{u}} (U V : Opens X) :
    (twoOpenSmallShortComplex U V).X₃ ≅
      (twoOpenSmallShortComplex V U).X₃ :=
  asIso (twoOpenSmallShortComplexSwapIso U V).hom.τ₃

/-- Swapping the two entries only reindexes cover-small chains: after inclusion
in all singular chains, the swap map is the identity. -/
@[reassoc]
theorem twoOpenCoverSwapChainIso_comp_inclusion {X : TopCat.{u}}
    (U V : Opens X) :
    (twoOpenCoverSwapChainIso U V).hom ≫
        smallSingularChainInclusion (TopCat.twoOpenCover V U) =
      smallSingularChainInclusion (TopCat.twoOpenCover U V) := by
  change (((twoOpenUnionChainIso U V).inv ≫
      (subcomplexSupSwapChainIso (TopCat.openSingularSet U)
        (TopCat.openSingularSet V)).hom ≫
      (twoOpenUnionChainIso V U).hom) ≫
      smallSingularChainInclusion (TopCat.twoOpenCover V U)) =
    smallSingularChainInclusion (TopCat.twoOpenCover U V)
  change (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
        (SSet.Subcomplex.eqToIso (TopCat.openSingularSet_sup U V)).inv ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
        (SSet.Subcomplex.eqToIso
          (sup_comm (TopCat.openSingularSet U) (TopCat.openSingularSet V))).hom ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
        (SSet.Subcomplex.eqToIso (TopCat.openSingularSet_sup V U)).hom) ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
        (TopCat.smallSingularSet (TopCat.twoOpenCover V U)).ι =
    ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
      (TopCat.smallSingularSet (TopCat.twoOpenCover U V)).ι
  simp only [Category.assoc, ← Functor.map_comp]
  congr 1

/-- The natural map between the short exact chain sequences associated to a
continuous map respecting ordered pairs of opens. -/
noncomputable def twoOpenSmallShortComplexMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    twoOpenSmallShortComplex U V ⟶ twoOpenSmallShortComplex U' V' where
  τ₁ := (twoOpenIntersectionChainIso U V).hom ≫
    (twoOpenAmbientShortComplexMap f U V U' V' hU hV).τ₁ ≫
    (twoOpenIntersectionChainIso U' V').inv
  τ₂ := (twoOpenBiprodChainIso U V).hom ≫
    (twoOpenAmbientShortComplexMap f U V U' V' hU hV).τ₂ ≫
    (twoOpenBiprodChainIso U' V').inv
  τ₃ := (twoOpenUnionChainIso U V).inv ≫
    (twoOpenAmbientShortComplexMap f U V U' V' hU hV).τ₃ ≫
    (twoOpenUnionChainIso U' V').hom
  comm₁₂ := by
    simp only [twoOpenSmallShortComplex, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [(twoOpenAmbientShortComplexMap f U V U' V' hU hV).comm₁₂_assoc]
  comm₂₃ := by
    simp only [twoOpenSmallShortComplex, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [(twoOpenAmbientShortComplexMap f U V U' V' hU hV).comm₂₃_assoc]

/-- The last component of the natural map of short complexes agrees, after
cover-small inclusion, with the ordinary singular chain map induced by `f`. -/
@[reassoc]
theorem twoOpenSmallShortComplexMap_comp_inclusion {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    (twoOpenSmallShortComplexMap f U V U' V' hU hV).τ₃ ≫
        smallSingularChainInclusion (TopCat.twoOpenCover U' V') =
      smallSingularChainInclusion (TopCat.twoOpenCover U V) ≫
        integralSingularChainMap f := by
  change (((twoOpenUnionChainIso U V).inv ≫
      (twoOpenAmbientShortComplexMap f U V U' V' hU hV).τ₃ ≫
      (twoOpenUnionChainIso U' V').hom) ≫
      smallSingularChainInclusion (TopCat.twoOpenCover U' V')) =
    smallSingularChainInclusion (TopCat.twoOpenCover U V) ≫
      integralSingularChainMap f
  change (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
        (SSet.Subcomplex.eqToIso (TopCat.openSingularSet_sup U V)).inv ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
        (TopCat.openSingularSetSupMap f U V U' V' hU hV) ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
        (SSet.Subcomplex.eqToIso (TopCat.openSingularSet_sup U' V')).hom) ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
        (TopCat.smallSingularSet (TopCat.twoOpenCover U' V')).ι =
    ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
        (TopCat.smallSingularSet (TopCat.twoOpenCover U V)).ι ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).map
        (TopCat.toSSet.map f)
  simp only [Category.assoc, ← Functor.map_comp]
  congr 1

/-- Integral singular homology in degree `n`. -/
abbrev integralSingularHomology (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} ℤ :=
  (integralSingularChains X).homology n

set_option linter.style.haveILetI false in
/-- A cover-small homology group is canonically isomorphic to ordinary
singular homology when the family is an open cover. -/
noncomputable def smallSingularHomologyIso {X : TopCat.{u}} {ι : Type*}
    (W : ι → Opens X) (hW : IsOpenCover W) (n : ℕ) :
    (smallSingularChainComplex W).homology n ≅ integralSingularHomology X n := by
  letI : QuasiIso (smallSingularChainInclusion W) :=
    quasiIso_smallSingularChainInclusion W hW
  exact isoOfQuasiIsoAt (smallSingularChainInclusion W) n

/-- The last term of the two-open short complex has ordinary singular
homology, via the accepted cover-small quasi-isomorphism. -/
noncomputable def twoOpenSpaceHomologyIso {X : TopCat.{u}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) :
    ((twoOpenSmallShortComplex U V).X₃).homology n ≅
      integralSingularHomology X n :=
  smallSingularHomologyIso (TopCat.twoOpenCover U V)
    (TopCat.isOpenCover_twoOpenCover hUV) n

set_option linter.style.haveILetI false in
/-- The middle homology term is canonically the direct sum
`Hₙ(U;ℤ) ⊕ Hₙ(V;ℤ)`. -/
noncomputable def twoOpenMiddleHomologyIso {X : TopCat.{u}} (U V : Opens X)
    (n : ℕ) :
    ((twoOpenSmallShortComplex U V).X₂).homology n ≅
      integralSingularHomology ((Opens.toTopCat X).obj U) n ⊞
        integralSingularHomology ((Opens.toTopCat X).obj V) n :=
  by
    let F := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ)
      (ComplexShape.down ℕ) n
    letI : PreservesFiniteBiproducts F :=
      Functor.preservesFiniteBiproductsOfAdditive F
    letI : PreservesBinaryBiproducts F :=
      preservesBinaryBiproducts_of_preservesBiproducts F
    exact F.mapBiprod
      (integralSingularChains ((Opens.toTopCat X).obj U))
      (integralSingularChains ((Opens.toTopCat X).obj V))

/-- The ordinary Mayer--Vietoris connecting morphism for the ordered cover
`(U,V)`, with the chain convention `c ↦ (c,-c)`. -/
noncomputable def twoOpenMayerVietorisδ {X : TopCat.{u}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) :
    integralSingularHomology X (n + 1) ⟶
      ((twoOpenSmallShortComplex U V).X₁).homology n :=
  (twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
    (twoOpenSmallShortExact U V).δ (n + 1) n (by simp)

/-- The ordinary homology self-map induced by reindexing the ordered cover
`(U,V)` as `(V,U)`.  It conjugates the cover-small swap map by the accepted
cover-small/ordinary homology isomorphisms. -/
noncomputable def twoOpenMayerVietorisSwapSpaceMap {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ) :
    integralSingularHomology X n ⟶ integralSingularHomology X n :=
  (twoOpenSpaceHomologyIso U V hUV n).inv ≫
    HomologicalComplex.homologyMap (twoOpenCoverSwapChainIso U V).hom n ≫
    (twoOpenSpaceHomologyIso V U hVU n).hom

/-- Reindexing the two-member cover induces the identity on ordinary singular
homology of the ambient space. -/
theorem twoOpenMayerVietorisSwapSpaceMap_eq_id {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ) :
    twoOpenMayerVietorisSwapSpaceMap U V hUV hVU n = 𝟙 _ := by
  let g : smallSingularChainComplex (TopCat.twoOpenCover U V) ⟶
      smallSingularChainComplex (TopCat.twoOpenCover V U) :=
    (twoOpenCoverSwapChainIso U V).hom
  change (smallSingularHomologyIso (TopCat.twoOpenCover U V)
      (TopCat.isOpenCover_twoOpenCover hUV) n).inv ≫
      HomologicalComplex.homologyMap g n ≫
      (smallSingularHomologyIso (TopCat.twoOpenCover V U)
        (TopCat.isOpenCover_twoOpenCover hVU) n).hom = 𝟙 _
  have hg : g ≫ smallSingularChainInclusion (TopCat.twoOpenCover V U) =
      smallSingularChainInclusion (TopCat.twoOpenCover U V) :=
    twoOpenCoverSwapChainIso_comp_inclusion U V
  dsimp [smallSingularHomologyIso]
  rw [isoOfQuasiIsoAt_hom, ← HomologicalComplex.homologyMap_comp, hg,
    isoOfQuasiIsoAt_inv_hom_id]

/-- Swapping the ordered cover changes the ordinary Mayer--Vietoris
connecting morphism by `-1`, after the sign-free transport of the intersection
term and the canonical cover reindexing on the space term.  Thus the sign from
the chain convention `c ↦ (c,-c)` remains visible over `ℤ`. -/
theorem twoOpenMayerVietorisδ_swap {X : TopCat.{u}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ) :
    twoOpenMayerVietorisδ U V hUV n ≫
        HomologicalComplex.homologyMap
          (twoOpenIntersectionSwapChainIso U V).hom n =
      -(twoOpenMayerVietorisSwapSpaceMap U V hUV hVU (n + 1) ≫
        twoOpenMayerVietorisδ V U hVU n) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (twoOpenSmallShortComplexSwapIso U V).hom
    (twoOpenSmallShortExact U V) (twoOpenSmallShortExact V U)
    (n + 1) n (by simp)
  change (twoOpenSmallShortExact U V).δ (n + 1) n (by simp) ≫
      HomologicalComplex.homologyMap
        (twoOpenSmallShortComplexSwapIso U V).hom.τ₁ n =
    HomologicalComplex.homologyMap
        (twoOpenSmallShortComplexSwapIso U V).hom.τ₃ (n + 1) ≫
      (twoOpenSmallShortExact V U).δ (n + 1) n (by simp) at h
  change ((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
      (twoOpenSmallShortExact U V).δ (n + 1) n (by simp)) ≫
      HomologicalComplex.homologyMap
        (-(twoOpenSmallShortComplexSwapIso U V).hom.τ₁) n =
    -(((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
      HomologicalComplex.homologyMap
        (twoOpenSmallShortComplexSwapIso U V).hom.τ₃ (n + 1) ≫
      (twoOpenSpaceHomologyIso V U hVU (n + 1)).hom) ≫
      ((twoOpenSpaceHomologyIso V U hVU (n + 1)).inv ≫
        (twoOpenSmallShortExact V U).δ (n + 1) n (by simp)))
  simp only [HomologicalComplex.homologyMap_neg, Preadditive.comp_neg,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [h]

/-- In the ordinary formulation, where reindexing the cover acts identically
on `H(X;ℤ)`, swapping `U` and `V` negates the connecting morphism. -/
theorem twoOpenMayerVietorisδ_swap_eq_neg {X : TopCat.{u}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ) :
    twoOpenMayerVietorisδ U V hUV n ≫
        HomologicalComplex.homologyMap
          (twoOpenIntersectionSwapChainIso U V).hom n =
      -(twoOpenMayerVietorisδ V U hVU n) := by
  rw [twoOpenMayerVietorisδ_swap U V hUV hVU n,
    twoOpenMayerVietorisSwapSpaceMap_eq_id U V hUV hVU (n + 1),
    Category.id_comp]

/-- The map from the middle homology term to ordinary homology of `X`. -/
noncomputable def twoOpenMayerVietorisToSpace {X : TopCat.{u}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) :
    ((twoOpenSmallShortComplex U V).X₂).homology n ⟶
      integralSingularHomology X n :=
  HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).g n ≫
    (twoOpenSpaceHomologyIso U V hUV n).hom

/-- The difference map on homology, displayed with target
`Hₙ(U) ⊕ Hₙ(V)`. -/
noncomputable def twoOpenMayerVietorisFromIntersection {X : TopCat.{u}}
    (U V : Opens X) (n : ℕ) :
    ((twoOpenSmallShortComplex U V).X₁).homology n ⟶
      integralSingularHomology ((Opens.toTopCat X).obj U) n ⊞
        integralSingularHomology ((Opens.toTopCat X).obj V) n :=
  HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n ≫
    (twoOpenMiddleHomologyIso U V n).hom

/-- The sum map on homology, displayed with source
`Hₙ(U) ⊕ Hₙ(V)`. -/
noncomputable def twoOpenMayerVietorisFromBiprod {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    integralSingularHomology ((Opens.toTopCat X).obj U) n ⊞
        integralSingularHomology ((Opens.toTopCat X).obj V) n ⟶
      integralSingularHomology X n :=
  (twoOpenMiddleHomologyIso U V n).inv ≫
    twoOpenMayerVietorisToSpace U V hUV n

@[reassoc]
theorem twoOpenMayerVietorisδ_comp {X : TopCat.{u}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) :
    twoOpenMayerVietorisδ U V hUV n ≫
      HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n = 0 := by
  simp only [twoOpenMayerVietorisδ, Category.assoc]
  rw [(twoOpenSmallShortExact U V).δ_comp (n + 1) n (by simp), comp_zero]

@[reassoc]
theorem twoOpenMayerVietoris_comp_toSpace {X : TopCat.{u}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) :
    HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n ≫
      twoOpenMayerVietorisToSpace U V hUV n = 0 := by
  change HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n ≫
    (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).g n ≫
      (twoOpenSpaceHomologyIso U V hUV n).hom) = 0
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    (twoOpenSmallShortComplex U V).zero,
    HomologicalComplex.homologyMap_zero, zero_comp]

@[reassoc]
theorem twoOpenMayerVietoris_toSpace_comp_δ {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    twoOpenMayerVietorisToSpace U V hUV (n + 1) ≫
      twoOpenMayerVietorisδ U V hUV n = 0 := by
  change (HomologicalComplex.homologyMap
      (twoOpenSmallShortComplex U V).g (n + 1) ≫
    (twoOpenSpaceHomologyIso U V hUV (n + 1)).hom) ≫
    ((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
      (twoOpenSmallShortExact U V).δ (n + 1) n (by simp)) = 0
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact (twoOpenSmallShortExact U V).comp_δ (n + 1) n (by simp)

/-- The map on the intersection homology term induced by a continuous map
respecting ordered pairs. -/
noncomputable def twoOpenMayerVietorisIntersectionMap {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    ((twoOpenSmallShortComplex U V).X₁).homology n ⟶
      ((twoOpenSmallShortComplex U' V').X₁).homology n :=
  HomologicalComplex.homologyMap
    (twoOpenSmallShortComplexMap f U V U' V' hU hV).τ₁ n

/-- The ordinary-space homology map obtained naturally from the two-open
short complexes.  It is defined by conjugating the cover-small map by the
accepted cover-small/ordinary homology isomorphisms. -/
noncomputable def twoOpenMayerVietorisSpaceMap {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) (n : ℕ) :
    integralSingularHomology X n ⟶ integralSingularHomology Y n :=
  (twoOpenSpaceHomologyIso U V hUV n).inv ≫
    HomologicalComplex.homologyMap
      (twoOpenSmallShortComplexMap f U V U' V' hU hV).τ₃ n ≫
    (twoOpenSpaceHomologyIso U' V' hU'V' n).hom

/-- The space map used in Mayer--Vietoris naturality is the ordinary singular
homology map induced by the underlying continuous map. -/
theorem twoOpenMayerVietorisSpaceMap_eq {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) (n : ℕ) :
    twoOpenMayerVietorisSpaceMap f U V U' V' hU hV hUV hU'V' n =
      HomologicalComplex.homologyMap (integralSingularChainMap f) n := by
  let g : smallSingularChainComplex (TopCat.twoOpenCover U V) ⟶
      smallSingularChainComplex (TopCat.twoOpenCover U' V') :=
    (twoOpenSmallShortComplexMap f U V U' V' hU hV).τ₃
  change (smallSingularHomologyIso (TopCat.twoOpenCover U V)
      (TopCat.isOpenCover_twoOpenCover hUV) n).inv ≫
      HomologicalComplex.homologyMap g n ≫
      (smallSingularHomologyIso (TopCat.twoOpenCover U' V')
        (TopCat.isOpenCover_twoOpenCover hU'V') n).hom =
    HomologicalComplex.homologyMap (integralSingularChainMap f) n
  have hg : g ≫ smallSingularChainInclusion (TopCat.twoOpenCover U' V') =
      smallSingularChainInclusion (TopCat.twoOpenCover U V) ≫
        integralSingularChainMap f :=
    twoOpenSmallShortComplexMap_comp_inclusion f U V U' V' hU hV
  dsimp [smallSingularHomologyIso]
  rw [isoOfQuasiIsoAt_hom, ← HomologicalComplex.homologyMap_comp, hg,
    HomologicalComplex.homologyMap_comp,
    isoOfQuasiIsoAt_inv_hom_id_assoc]

/-- Naturality of the ordinary two-open Mayer--Vietoris connecting
morphism. -/
theorem twoOpenMayerVietorisδ_naturality {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) (n : ℕ) :
    twoOpenMayerVietorisδ U V hUV n ≫
        twoOpenMayerVietorisIntersectionMap f U V U' V' hU hV n =
      twoOpenMayerVietorisSpaceMap f U V U' V' hU hV hUV hU'V' (n + 1) ≫
        twoOpenMayerVietorisδ U' V' hU'V' n := by
  simp only [twoOpenMayerVietorisδ, twoOpenMayerVietorisIntersectionMap,
    twoOpenMayerVietorisSpaceMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [HomologicalComplex.HomologySequence.δ_naturality
    (twoOpenSmallShortComplexMap f U V U' V' hU hV)
    (twoOpenSmallShortExact U V) (twoOpenSmallShortExact U' V')
    (n + 1) n (by simp)]

/-- Naturality of the connecting morphism with the standard ordinary singular
homology map of the underlying continuous map displayed explicitly. -/
theorem twoOpenMayerVietorisδ_naturality_induced {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) (n : ℕ) :
    twoOpenMayerVietorisδ U V hUV n ≫
        twoOpenMayerVietorisIntersectionMap f U V U' V' hU hV n =
      HomologicalComplex.homologyMap (integralSingularChainMap f) (n + 1) ≫
        twoOpenMayerVietorisδ U' V' hU'V' n := by
  rw [← twoOpenMayerVietorisSpaceMap_eq
    f U V U' V' hU hV hUV hU'V' (n + 1)]
  exact twoOpenMayerVietorisδ_naturality
    f U V U' V' hU hV hUV hU'V' n

/-- Exactness at `Hₙ(U∩V)` in the ordinary Mayer--Vietoris sequence. -/
theorem twoOpenMayerVietoris_exact_intersection {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (twoOpenMayerVietorisδ U V hUV n)
      (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n)
      (by
        change ((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
          (twoOpenSmallShortExact U V).δ (n + 1) n (by simp)) ≫
          HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n = 0
        rw [Category.assoc,
          (twoOpenSmallShortExact U V).δ_comp (n + 1) n (by simp), comp_zero]))
      |>.Exact := by
  let hS := twoOpenSmallShortExact U V
  let e : (ShortComplex.mk
      (twoOpenMayerVietorisδ U V hUV n)
      (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n)
      (by
        change ((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
          hS.δ (n + 1) n (by simp)) ≫
          HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n = 0
        rw [Category.assoc, hS.δ_comp (n + 1) n (by simp), comp_zero])) ≅
      (ShortComplex.mk
        (hS.δ (n + 1) n (by simp))
        (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n)
        (hS.δ_comp (n + 1) n (by simp))) :=
    ShortComplex.isoMk
      (twoOpenSpaceHomologyIso U V hUV (n + 1)).symm
      (Iso.refl _) (Iso.refl _)
      (by simp [twoOpenMayerVietorisδ])
  exact ShortComplex.exact_of_iso e.symm
    (hS.homology_exact₁ (n + 1) n (by simp))

/-- Exactness at the middle term in the ordinary Mayer--Vietoris sequence. -/
theorem twoOpenMayerVietoris_exact_middle {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n)
      (twoOpenMayerVietorisToSpace U V hUV n)
      (by
        change HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n ≫
          (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).g n ≫
            (twoOpenSpaceHomologyIso U V hUV n).hom) = 0
        rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
          (twoOpenSmallShortComplex U V).zero,
          HomologicalComplex.homologyMap_zero, zero_comp])).Exact := by
  let hS := twoOpenSmallShortExact U V
  let e : (ShortComplex.mk
      (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n)
      (twoOpenMayerVietorisToSpace U V hUV n)
      (by
        change HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n ≫
          (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).g n ≫
            (twoOpenSpaceHomologyIso U V hUV n).hom) = 0
        rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
          (twoOpenSmallShortComplex U V).zero,
          HomologicalComplex.homologyMap_zero, zero_comp])) ≅
      (ShortComplex.mk
        (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n)
        (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).g n)
        (by
          rw [← HomologicalComplex.homologyMap_comp,
            (twoOpenSmallShortComplex U V).zero,
            HomologicalComplex.homologyMap_zero])) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (twoOpenSpaceHomologyIso U V hUV n).symm
      (by simp)
      (by simp [twoOpenMayerVietorisToSpace, Category.assoc])
  exact ShortComplex.exact_of_iso e.symm (hS.homology_exact₂ n)

/-- Exactness at `Hₙ₊₁(X)` before the connecting morphism. -/
theorem twoOpenMayerVietoris_exact_space {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (twoOpenMayerVietorisToSpace U V hUV (n + 1))
      (twoOpenMayerVietorisδ U V hUV n)
      (by
        change (HomologicalComplex.homologyMap
            (twoOpenSmallShortComplex U V).g (n + 1) ≫
          (twoOpenSpaceHomologyIso U V hUV (n + 1)).hom) ≫
          ((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
            (twoOpenSmallShortExact U V).δ (n + 1) n (by simp)) = 0
        rw [Category.assoc, Iso.hom_inv_id_assoc]
        exact (twoOpenSmallShortExact U V).comp_δ (n + 1) n (by simp))).Exact := by
  let hS := twoOpenSmallShortExact U V
  let e : (ShortComplex.mk
      (twoOpenMayerVietorisToSpace U V hUV (n + 1))
      (twoOpenMayerVietorisδ U V hUV n)
      (by
        change (HomologicalComplex.homologyMap
            (twoOpenSmallShortComplex U V).g (n + 1) ≫
          (twoOpenSpaceHomologyIso U V hUV (n + 1)).hom) ≫
          ((twoOpenSpaceHomologyIso U V hUV (n + 1)).inv ≫
            hS.δ (n + 1) n (by simp)) = 0
        rw [Category.assoc, Iso.hom_inv_id_assoc]
        exact hS.comp_δ (n + 1) n (by simp))) ≅
      (ShortComplex.mk
        (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).g (n + 1))
        (hS.δ (n + 1) n (by simp))
        (hS.comp_δ (n + 1) n (by simp))) :=
    ShortComplex.isoMk (Iso.refl _)
      (twoOpenSpaceHomologyIso U V hUV (n + 1)).symm
      (Iso.refl _)
      (by simp [twoOpenMayerVietorisToSpace, Category.assoc])
      (by simp [twoOpenMayerVietorisδ])
  exact ShortComplex.exact_of_iso e.symm
    (hS.homology_exact₃ (n + 1) n (by simp))

/-- Exactness at `Hₙ(U∩V)` with the middle term displayed as
`Hₙ(U) ⊕ Hₙ(V)`. -/
theorem twoOpenMayerVietoris_exact_at_intersection {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (twoOpenMayerVietorisδ U V hUV n)
      (twoOpenMayerVietorisFromIntersection U V n)
      (by
        change (twoOpenMayerVietorisδ U V hUV n ≫
          HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n) ≫
            (twoOpenMiddleHomologyIso U V n).hom = 0
        rw [twoOpenMayerVietorisδ_comp U V hUV n,
          zero_comp])).Exact := by
  let S := ShortComplex.mk
    (twoOpenMayerVietorisδ U V hUV n)
    (twoOpenMayerVietorisFromIntersection U V n)
    (by
      change (twoOpenMayerVietorisδ U V hUV n ≫
        HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n) ≫
          (twoOpenMiddleHomologyIso U V n).hom = 0
      rw [twoOpenMayerVietorisδ_comp U V hUV n,
        zero_comp])
  let T := ShortComplex.mk
    (twoOpenMayerVietorisδ U V hUV n)
    (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n)
    (twoOpenMayerVietorisδ_comp U V hUV n)
  let e : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (twoOpenMiddleHomologyIso U V n).symm
    (by simp [S, T])
    (by simp [S, T, twoOpenMayerVietorisFromIntersection, Category.assoc])
  exact ShortComplex.exact_of_iso e.symm
    (twoOpenMayerVietoris_exact_intersection U V hUV n)

/-- Exactness at `Hₙ(U) ⊕ Hₙ(V)`. -/
theorem twoOpenMayerVietoris_exact_at_biprod {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (twoOpenMayerVietorisFromIntersection U V n)
      (twoOpenMayerVietorisFromBiprod U V hUV n)
      (by
        simp only [twoOpenMayerVietorisFromIntersection,
          twoOpenMayerVietorisFromBiprod, Category.assoc,
          Iso.hom_inv_id_assoc]
        exact twoOpenMayerVietoris_comp_toSpace U V hUV n)).Exact := by
  let S := ShortComplex.mk
    (twoOpenMayerVietorisFromIntersection U V n)
    (twoOpenMayerVietorisFromBiprod U V hUV n)
    (by
      simp only [twoOpenMayerVietorisFromIntersection,
        twoOpenMayerVietorisFromBiprod, Category.assoc,
        Iso.hom_inv_id_assoc]
      exact twoOpenMayerVietoris_comp_toSpace U V hUV n)
  let T := ShortComplex.mk
    (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n)
    (twoOpenMayerVietorisToSpace U V hUV n)
    (twoOpenMayerVietoris_comp_toSpace U V hUV n)
  let e : S ≅ T := ShortComplex.isoMk (Iso.refl _)
    (twoOpenMiddleHomologyIso U V n).symm (Iso.refl _)
    (by simp [S, T, twoOpenMayerVietorisFromIntersection, Category.assoc])
    (by simp [S, T, twoOpenMayerVietorisFromBiprod])
  exact ShortComplex.exact_of_iso e.symm
    (twoOpenMayerVietoris_exact_middle U V hUV n)

/-- Exactness at `Hₙ₊₁(X)` with the preceding term displayed as
`Hₙ₊₁(U) ⊕ Hₙ₊₁(V)`. -/
theorem twoOpenMayerVietoris_exact_at_space {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (twoOpenMayerVietorisFromBiprod U V hUV (n + 1))
      (twoOpenMayerVietorisδ U V hUV n)
      (by
        change (twoOpenMiddleHomologyIso U V (n + 1)).inv ≫
          (twoOpenMayerVietorisToSpace U V hUV (n + 1) ≫
            twoOpenMayerVietorisδ U V hUV n) = 0
        rw [twoOpenMayerVietoris_toSpace_comp_δ U V hUV n,
          comp_zero])).Exact := by
  let S := ShortComplex.mk
    (twoOpenMayerVietorisFromBiprod U V hUV (n + 1))
    (twoOpenMayerVietorisδ U V hUV n)
    (by
      change (twoOpenMiddleHomologyIso U V (n + 1)).inv ≫
        (twoOpenMayerVietorisToSpace U V hUV (n + 1) ≫
          twoOpenMayerVietorisδ U V hUV n) = 0
      rw [twoOpenMayerVietoris_toSpace_comp_δ U V hUV n,
        comp_zero])
  let T := ShortComplex.mk
    (twoOpenMayerVietorisToSpace U V hUV (n + 1))
    (twoOpenMayerVietorisδ U V hUV n)
    (twoOpenMayerVietoris_toSpace_comp_δ U V hUV n)
  let e : S ≅ T := ShortComplex.isoMk
    (twoOpenMiddleHomologyIso U V (n + 1)).symm
    (Iso.refl _) (Iso.refl _)
    (by simp [S, T, twoOpenMayerVietorisFromBiprod])
    (by simp [S, T])
  exact ShortComplex.exact_of_iso e.symm
    (twoOpenMayerVietoris_exact_space U V hUV n)

private theorem twoOpenIntersectionToLeft_sset {X : TopCat.{u}}
    (U V : Opens X) :
    TopCat.toSSet.map (twoOpenIntersectionToLeft U V) ≫
        (TopCat.openSingularSetIso U).hom =
      (TopCat.openSingularSetIso (U ⊓ V)).hom ≫
        (SSet.Subcomplex.eqToIso
          (TopCat.openSingularSet_inf U V).symm).hom ≫
        SSet.Subcomplex.homOfLE inf_le_left := by
  ext n x
  apply Subtype.ext
  rfl

private theorem twoOpenIntersectionToRight_sset {X : TopCat.{u}}
    (U V : Opens X) :
    TopCat.toSSet.map (twoOpenIntersectionToRight U V) ≫
        (TopCat.openSingularSetIso V).hom =
      (TopCat.openSingularSetIso (U ⊓ V)).hom ≫
        (SSet.Subcomplex.eqToIso
          (TopCat.openSingularSet_inf U V).symm).hom ≫
        SSet.Subcomplex.homOfLE inf_le_right := by
  ext n x
  apply Subtype.ext
  rfl

/-- The left projection of the first map in the two-open small short complex
is induced by the literal inclusion `U ∩ V → U`. -/
theorem twoOpenSmallShortComplex_f_fst {X : TopCat.{u}}
    (U V : Opens X) :
    (twoOpenSmallShortComplex U V).f ≫ biprod.fst =
      integralSingularChainMap (twoOpenIntersectionToLeft U V) := by
  apply (cancel_mono (openSingularChainIso U).hom).1
  change (((twoOpenIntersectionChainIso U V).hom ≫
      biprod.lift
        (SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE
            (inf_le_left : TopCat.openSingularSet U ⊓
              TopCat.openSingularSet V ≤ TopCat.openSingularSet U))
          integerCoefficients.{u})
        (-(SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE
            (inf_le_right : TopCat.openSingularSet U ⊓
              TopCat.openSingularSet V ≤ TopCat.openSingularSet V))
          integerCoefficients.{u})) ≫
      (biprod.mapIso (openSingularChainIso U)
        (openSingularChainIso V)).inv) ≫ biprod.fst) ≫
        (openSingularChainIso U).hom = _
  simp only [biprod.mapIso, Category.assoc, biprod.map_fst]
  erw [biprod.lift_fst_assoc]
  erw [Iso.inv_hom_id]
  erw [Category.comp_id]
  let F := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
    integerCoefficients.{u}
  change (F.map (TopCat.openSingularSetIso (U ⊓ V)).hom ≫
      F.map (SSet.Subcomplex.eqToIso
        (TopCat.openSingularSet_inf U V).symm).hom) ≫
      F.map (SSet.Subcomplex.homOfLE inf_le_left) =
    F.map (TopCat.toSSet.map (twoOpenIntersectionToLeft U V)) ≫
      F.map (TopCat.openSingularSetIso U).hom
  have h := congrArg (fun k ↦ F.map k)
    (twoOpenIntersectionToLeft_sset U V)
  simpa only [Functor.map_comp, Category.assoc] using h.symm

/-- The right projection of the first map in the two-open small short complex
is minus the map induced by the literal inclusion `U ∩ V → V`. -/
theorem twoOpenSmallShortComplex_f_snd {X : TopCat.{u}}
    (U V : Opens X) :
    (twoOpenSmallShortComplex U V).f ≫ biprod.snd =
      -integralSingularChainMap (twoOpenIntersectionToRight U V) := by
  apply (cancel_mono (openSingularChainIso V).hom).1
  change (((twoOpenIntersectionChainIso U V).hom ≫
      biprod.lift
        (SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE
            (inf_le_left : TopCat.openSingularSet U ⊓
              TopCat.openSingularSet V ≤ TopCat.openSingularSet U))
          integerCoefficients.{u})
        (-(SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE
            (inf_le_right : TopCat.openSingularSet U ⊓
              TopCat.openSingularSet V ≤ TopCat.openSingularSet V))
          integerCoefficients.{u})) ≫
      (biprod.mapIso (openSingularChainIso U)
        (openSingularChainIso V)).inv) ≫ biprod.snd) ≫
        (openSingularChainIso V).hom = _
  simp only [biprod.mapIso, Category.assoc, biprod.map_snd]
  erw [biprod.lift_snd_assoc]
  erw [Iso.inv_hom_id]
  erw [Category.comp_id]
  let F := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
    integerCoefficients.{u}
  have h := congrArg (fun k ↦ F.map k)
    (twoOpenIntersectionToRight_sset U V)
  erw [Preadditive.comp_neg, Preadditive.neg_comp]
  exact congrArg Neg.neg (by
    change (F.map (TopCat.openSingularSetIso (U ⊓ V)).hom ≫
        F.map (SSet.Subcomplex.eqToIso
          (TopCat.openSingularSet_inf U V).symm).hom) ≫
        F.map (SSet.Subcomplex.homOfLE inf_le_right) =
      F.map (TopCat.toSSet.map (twoOpenIntersectionToRight U V)) ≫
        F.map (TopCat.openSingularSetIso V).hom
    simpa only [Functor.map_comp, Category.assoc] using h.symm)

/-- The first map of the two-open small short complex is the accepted ordered
difference map `c ↦ (c,-c)`. -/
theorem twoOpenSmallShortComplex_f_eq_difference {X : TopCat.{u}}
    (U V : Opens X) :
    (twoOpenSmallShortComplex U V).f = twoOpenDifferenceChainMap U V := by
  apply biprod.hom_ext
  · exact (twoOpenSmallShortComplex_f_fst U V).trans
      (biprod.lift_fst _ _).symm
  · exact (twoOpenSmallShortComplex_f_snd U V).trans
      (biprod.lift_snd _ _).symm

/-- The homology of the literal open intersection is canonically the first
homology object of the accepted two-open small short complex. -/
noncomputable def twoOpenIntersectionHomologyIso {X : TopCat.{u}}
    (U V : Opens X) (n : ℕ) :
    integralSingularHomology ((Opens.toTopCat X).obj (U ⊓ V)) n ≅
      (twoOpenSmallShortComplex U V).X₁.homology n :=
  Iso.refl _

/-- The left projection of the displayed ordinary difference map is induced
by `U ∩ V → U`. -/
theorem twoOpenMayerVietorisFromIntersection_fst {X : TopCat.{u}}
    (U V : Opens X) (n : ℕ) :
    twoOpenMayerVietorisFromIntersection U V n ≫ biprod.fst =
      (twoOpenIntersectionHomologyIso U V n).inv ≫
        HomologicalComplex.homologyMap
          (integralSingularChainMap (twoOpenIntersectionToLeft U V)) n := by
  simp only [twoOpenMayerVietorisFromIntersection,
    twoOpenIntersectionHomologyIso, twoOpenSmallShortComplex_f_eq_difference,
    twoOpenDifferenceChainMap, twoOpenMiddleHomologyIso,
    Iso.refl_inv]
  erw [Category.assoc, biprod.lift_fst]
  erw [← HomologicalComplex.homologyMap_comp, biprod.lift_fst]
  exact (Category.id_comp _).symm

/-- The right projection of the displayed ordinary difference map is minus
the map induced by `U ∩ V → V`. -/
theorem twoOpenMayerVietorisFromIntersection_snd {X : TopCat.{u}}
    (U V : Opens X) (n : ℕ) :
    twoOpenMayerVietorisFromIntersection U V n ≫ biprod.snd =
      (twoOpenIntersectionHomologyIso U V n).inv ≫
        (-HomologicalComplex.homologyMap
          (integralSingularChainMap (twoOpenIntersectionToRight U V)) n) := by
  simp only [twoOpenMayerVietorisFromIntersection,
    twoOpenIntersectionHomologyIso, twoOpenSmallShortComplex_f_eq_difference,
    twoOpenDifferenceChainMap, twoOpenMiddleHomologyIso,
    Iso.refl_inv]
  erw [Category.assoc, biprod.lift_snd]
  erw [← HomologicalComplex.homologyMap_comp, biprod.lift_snd,
    HomologicalComplex.homologyMap_neg]
  exact (Category.id_comp _).symm

private theorem twoOpenIntersectionMap_sset {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    TopCat.toSSet.map (twoOpenIntersectionMap f U V U' V' hU hV) ≫
        (TopCat.openSingularSetIso (U' ⊓ V')).hom ≫
        (SSet.Subcomplex.eqToIso
          (TopCat.openSingularSet_inf U' V').symm).hom =
      (TopCat.openSingularSetIso (U ⊓ V)).hom ≫
        (SSet.Subcomplex.eqToIso
          (TopCat.openSingularSet_inf U V).symm).hom ≫
        TopCat.openSingularSetInfMap f U V U' V' hU hV := by
  ext n x
  apply Subtype.ext
  rfl

/-- The first component of the accepted map of two-open small short complexes
is the chain map induced by the literal map of open intersections. -/
theorem integralSingularChainMap_twoOpenIntersectionMap {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    integralSingularChainMap
        (twoOpenIntersectionMap f U V U' V' hU hV) =
      (twoOpenSmallShortComplexMap f U V U' V' hU hV).τ₁ := by
  apply (cancel_mono (twoOpenIntersectionChainIso U' V').hom).1
  change integralSingularChainMap
      (twoOpenIntersectionMap f U V U' V' hU hV) ≫
        (twoOpenIntersectionChainIso U' V').hom =
    ((twoOpenIntersectionChainIso U V).hom ≫
      (twoOpenAmbientShortComplexMap f U V U' V' hU hV).τ₁ ≫
      (twoOpenIntersectionChainIso U' V').inv) ≫
        (twoOpenIntersectionChainIso U' V').hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let F := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
    integerCoefficients.{u}
  change F.map (TopCat.toSSet.map
      (twoOpenIntersectionMap f U V U' V' hU hV)) ≫
        (F.map (TopCat.openSingularSetIso (U' ⊓ V')).hom ≫
          F.map (SSet.Subcomplex.eqToIso
            (TopCat.openSingularSet_inf U' V').symm).hom) =
    (F.map (TopCat.openSingularSetIso (U ⊓ V)).hom ≫
      F.map (SSet.Subcomplex.eqToIso
        (TopCat.openSingularSet_inf U V).symm).hom) ≫
      F.map (TopCat.openSingularSetInfMap f U V U' V' hU hV)
  have h := congrArg (fun k ↦ F.map k)
    (twoOpenIntersectionMap_sset f U V U' V' hU hV)
  simpa only [Functor.map_comp, Category.assoc] using h

/-- The accepted map on the intersection homology term is the ordinary
homology map induced by the literal open-intersection map. -/
theorem twoOpenMayerVietorisIntersectionMap_eq {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    twoOpenMayerVietorisIntersectionMap f U V U' V' hU hV n =
      HomologicalComplex.homologyMap
        (integralSingularChainMap
          (twoOpenIntersectionMap f U V U' V' hU hV)) n := by
  unfold twoOpenMayerVietorisIntersectionMap
  rw [integralSingularChainMap_twoOpenIntersectionMap]
  rfl

/-- Naturality of the literal-intersection identification. -/
@[reassoc]
theorem twoOpenIntersectionHomologyIso_naturality {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    (twoOpenIntersectionHomologyIso U V n).hom ≫
        twoOpenMayerVietorisIntersectionMap f U V U' V' hU hV n =
      HomologicalComplex.homologyMap
          (integralSingularChainMap
            (twoOpenIntersectionMap f U V U' V' hU hV)) n ≫
        (twoOpenIntersectionHomologyIso U' V' n).hom := by
  unfold twoOpenIntersectionHomologyIso
  rw [twoOpenMayerVietorisIntersectionMap_eq]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The sign-free map from the literal intersection `U ∩ V` to the literal
intersection `V ∩ U`. -/
def twoOpenIntersectionSwapMap {X : TopCat.{u}} (U V : Opens X) :
    (Opens.toTopCat X).obj (U ⊓ V) ⟶
      (Opens.toTopCat X).obj (V ⊓ U) :=
  TopCat.openMap (𝟙 X) (U ⊓ V) (V ⊓ U) (fun _ hx ↦ ⟨hx.2, hx.1⟩)

private theorem twoOpenIntersectionSwapMap_sset {X : TopCat.{u}}
    (U V : Opens X) :
    TopCat.toSSet.map (twoOpenIntersectionSwapMap U V) ≫
        (TopCat.openSingularSetIso (V ⊓ U)).hom ≫
        (SSet.Subcomplex.eqToIso
          (TopCat.openSingularSet_inf V U).symm).hom =
      (TopCat.openSingularSetIso (U ⊓ V)).hom ≫
        (SSet.Subcomplex.eqToIso
          (TopCat.openSingularSet_inf U V).symm).hom ≫
        (SSet.Subcomplex.eqToIso
          (inf_comm (TopCat.openSingularSet U)
            (TopCat.openSingularSet V))).hom := by
  ext n x
  apply Subtype.ext
  rfl

/-- The chain map induced by the sign-free literal-intersection swap is the
accepted intersection swap chain isomorphism. -/
theorem integralSingularChainMap_twoOpenIntersectionSwapMap
    {X : TopCat.{u}} (U V : Opens X) :
    integralSingularChainMap (twoOpenIntersectionSwapMap U V) =
      (twoOpenIntersectionSwapChainIso U V).hom := by
  have hswap : (twoOpenIntersectionSwapChainIso U V).hom =
      (twoOpenIntersectionChainIso U V).hom ≫
        (subcomplexInfSwapChainIso (TopCat.openSingularSet U)
          (TopCat.openSingularSet V)).hom ≫
        (twoOpenIntersectionChainIso V U).inv := by
    have h1 : (twoOpenSmallToAmbientIso U V).hom.τ₁ =
        (twoOpenIntersectionChainIso U V).hom := rfl
    have h2 : (subcomplexUnionSwapIso (TopCat.openSingularSet U)
        (TopCat.openSingularSet V)).hom.τ₁ =
        -(subcomplexInfSwapChainIso (TopCat.openSingularSet U)
          (TopCat.openSingularSet V)).hom := rfl
    have h3 : ((twoOpenSmallToAmbientIso V U).symm).hom.τ₁ =
        (twoOpenIntersectionChainIso V U).inv := rfl
    change -(((twoOpenSmallToAmbientIso U V).hom.τ₁ ≫
        (subcomplexUnionSwapIso (TopCat.openSingularSet U)
          (TopCat.openSingularSet V)).hom.τ₁) ≫
        ((twoOpenSmallToAmbientIso V U).symm).hom.τ₁) = _
    calc
      _ = (((twoOpenSmallToAmbientIso U V).hom.τ₁ ≫
          (-((subcomplexUnionSwapIso (TopCat.openSingularSet U)
            (TopCat.openSingularSet V)).hom.τ₁))) ≫
          ((twoOpenSmallToAmbientIso V U).symm).hom.τ₁) := by
        simp only [Preadditive.comp_neg, Preadditive.neg_comp]
      _ = _ := by
        rw [h1, h2, h3]
        erw [neg_neg]
        exact Category.assoc _ _ _
  have htransport : integralSingularChainMap
      (twoOpenIntersectionSwapMap U V) ≫
      (twoOpenIntersectionChainIso V U).hom =
    (twoOpenIntersectionChainIso U V).hom ≫
      (subcomplexInfSwapChainIso (TopCat.openSingularSet U)
        (TopCat.openSingularSet V)).hom := by
    let F := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integerCoefficients.{u}
    change F.map (TopCat.toSSet.map (twoOpenIntersectionSwapMap U V)) ≫
          (F.map (TopCat.openSingularSetIso (V ⊓ U)).hom ≫
            F.map (SSet.Subcomplex.eqToIso
              (TopCat.openSingularSet_inf V U).symm).hom) =
      (F.map (TopCat.openSingularSetIso (U ⊓ V)).hom ≫
        F.map (SSet.Subcomplex.eqToIso
          (TopCat.openSingularSet_inf U V).symm).hom) ≫
        F.map (SSet.Subcomplex.eqToIso
          (inf_comm (TopCat.openSingularSet U)
            (TopCat.openSingularSet V))).hom
    have h := congrArg (fun k ↦ F.map k)
      (twoOpenIntersectionSwapMap_sset U V)
    simpa only [Functor.map_comp, Category.assoc] using h
  rw [hswap]
  apply (cancel_mono (twoOpenIntersectionChainIso V U).hom).1
  rw [htransport]
  have hcancel :
      (((subcomplexInfSwapChainIso (TopCat.openSingularSet U)
          (TopCat.openSingularSet V)).hom ≫
        (twoOpenIntersectionChainIso V U).inv) ≫
        (twoOpenIntersectionChainIso V U).hom) =
      (subcomplexInfSwapChainIso (TopCat.openSingularSet U)
        (TopCat.openSingularSet V)).hom := by
    let b := (subcomplexInfSwapChainIso (TopCat.openSingularSet U)
      (TopCat.openSingularSet V)).hom
    let e := twoOpenIntersectionChainIso V U
    exact (Category.assoc b e.inv e.hom).trans
      ((congrArg (b ≫ ·) e.inv_hom_id).trans (Category.comp_id b))
  exact congrArg ((twoOpenIntersectionChainIso U V).hom ≫ ·) hcancel.symm

/-- On homology, the map induced by the sign-free literal-intersection swap is
the accepted swap map. -/
theorem integralSingularHomologyMap_twoOpenIntersectionSwapMap
    {X : TopCat.{u}} (U V : Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (integralSingularChainMap (twoOpenIntersectionSwapMap U V)) n =
      HomologicalComplex.homologyMap
        (twoOpenIntersectionSwapChainIso U V).hom n := by
  rw [integralSingularChainMap_twoOpenIntersectionSwapMap]
  rfl

/-- The literal-intersection identification intertwines the actual sign-free
swap map with the accepted swap map. -/
@[reassoc]
theorem twoOpenIntersectionHomologyIso_swap {X : TopCat.{u}}
    (U V : Opens X) (n : ℕ) :
    (twoOpenIntersectionHomologyIso U V n).hom ≫
        HomologicalComplex.homologyMap
          (twoOpenIntersectionSwapChainIso U V).hom n =
      HomologicalComplex.homologyMap
          (integralSingularChainMap (twoOpenIntersectionSwapMap U V)) n ≫
        (twoOpenIntersectionHomologyIso V U n).hom := by
  unfold twoOpenIntersectionHomologyIso
  rw [integralSingularHomologyMap_twoOpenIntersectionSwapMap]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Swapping the literal intersection twice is the identity. -/
theorem twoOpenIntersectionSwapMap_comp {X : TopCat.{u}}
    (U V : Opens X) :
    twoOpenIntersectionSwapMap U V ≫
      twoOpenIntersectionSwapMap V U = 𝟙 _ := by
  ext x
  rfl

/-- A self-map which exchanges an ordered two-open cover and whose literal
intersection map agrees on homology with the sign-free swap acts by `-1` on
the next ordinary integral homology group, provided the displayed connecting
morphism is monic.  The minus sign comes from the ordered Mayer--Vietoris
convention; it is not part of the intersection transport hypothesis. -/
theorem integralSingularHomologyMap_eq_neg_id_of_twoOpen_swap
    {X : TopCat.{u}} (f : X ⟶ X) (U V : Opens X)
    (hU : Set.MapsTo f U V) (hV : Set.MapsTo f V U)
    (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ)
    (hIntersection :
      HomologicalComplex.homologyMap
          (integralSingularChainMap
            (twoOpenIntersectionMap f V U U V hV hU)) n ≫
        HomologicalComplex.homologyMap
          (integralSingularChainMap
            (twoOpenIntersectionSwapMap U V)) n = 𝟙 _)
    [Mono (twoOpenMayerVietorisδ U V hUV n)] :
    HomologicalComplex.homologyMap (integralSingularChainMap f) (n + 1) =
      -𝟙 _ := by
  let s := HomologicalComplex.homologyMap
    (integralSingularChainMap (twoOpenIntersectionSwapMap U V)) n
  let t := HomologicalComplex.homologyMap
    (integralSingularChainMap (twoOpenIntersectionSwapMap V U)) n
  have hSwap : s ≫ t = 𝟙 _ := by
    dsimp [s, t]
    rw [← HomologicalComplex.homologyMap_comp]
    simp [integralSingularChainMap, ← Functor.map_comp,
      twoOpenIntersectionSwapMap_comp]
  have hIntersectionMap :
      HomologicalComplex.homologyMap
          (integralSingularChainMap
            (twoOpenIntersectionMap f V U U V hV hU)) n =
        HomologicalComplex.homologyMap
          (integralSingularChainMap
            (twoOpenIntersectionSwapMap V U)) n := by
    let a := HomologicalComplex.homologyMap
      (integralSingularChainMap
        (twoOpenIntersectionMap f V U U V hV hU)) n
    change a = t
    calc
      a = a ≫ 𝟙 _ := (Category.comp_id a).symm
      _ = a ≫ (s ≫ t) := by rw [hSwap]
      _ = (a ≫ s) ≫ t := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ t := by
        dsimp [a, s]
        rw [hIntersection]
      _ = t := Category.id_comp t
  apply (cancel_mono (twoOpenMayerVietorisδ U V hUV n)).1
  rw [← twoOpenMayerVietorisδ_naturality_induced
    f V U U V hV hU hVU hUV n]
  rw [twoOpenMayerVietorisIntersectionMap_eq, hIntersectionMap,
    integralSingularHomologyMap_twoOpenIntersectionSwapMap,
    twoOpenMayerVietorisδ_swap_eq_neg V U hVU hUV n]
  simp

set_option linter.style.haveILetI false in
/-- If the two outer biproduct terms vanish, the ordinary two-open
Mayer--Vietoris connecting morphism is an isomorphism. -/
theorem twoOpenMayerVietorisδ_isIso_of_isZero_outer
    {X : TopCat.{u}} (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hPrev : IsZero
      (integralSingularHomology ((Opens.toTopCat X).obj U) (n + 1) ⊞
        integralSingularHomology ((Opens.toTopCat X).obj V) (n + 1)))
    (hNext : IsZero
      (integralSingularHomology ((Opens.toTopCat X).obj U) n ⊞
        integralSingularHomology ((Opens.toTopCat X).obj V) n)) :
    IsIso (twoOpenMayerVietorisδ U V hUV n) := by
  have hSpace := twoOpenMayerVietoris_exact_at_space U V hUV n
  have hIntersection := twoOpenMayerVietoris_exact_at_intersection U V hUV n
  letI : Mono (twoOpenMayerVietorisδ U V hUV n) :=
    (hSpace.mono_g_iff).2
      (hPrev.eq_of_src (twoOpenMayerVietorisFromBiprod U V hUV (n + 1)) 0)
  letI : Epi (twoOpenMayerVietorisδ U V hUV n) :=
    (hIntersection.epi_f_iff).2
      (hNext.eq_of_tgt (twoOpenMayerVietorisFromIntersection U V n) 0)
  exact isIso_of_mono_of_epi _

end AlgebraicTopology
