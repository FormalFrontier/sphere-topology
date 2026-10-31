/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributor: Prism; earlier client lineage in docs/CREDITS.md.
module

import SphereTopology

/-!
# Ordinary aggregate-import clients

These private consumers use only the advertised ordinary root import. They test
the stated conclusions, data interfaces, empty cases and metric sphere models. The
existing focused clients separately retain the full ordered-cover and universe
regressions. No source repository is a dependency of this library.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped RealInnerProductSpace
open AlgebraicTopology SphereTopology

namespace SphereTopologyPublicClient

universe u

private theorem puncturedSphereSimplyConnected
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Metric.sphere (0 : E) 1) :
    SimplyConnectedSpace ({p}ᶜ : Set (Metric.sphere (0 : E) 1)) := by
  let := contractibleSpace_sphere_compl_singleton p
  exact SimplyConnectedSpace.ofContractible _

-- For a distinct, non-antipodal second pole, zero remains in the chart image.
private theorem stereographicOverlap_contains_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q : Metric.sphere (0 : E) 1) (hpq : p ≠ q) (hq : q ≠ -p) :
    ∃ x : ({p}ᶜ ∩ {q}ᶜ : Set (Metric.sphere (0 : E) 1)),
      ((stereographicOverlapHomeomorph p q hpq x : (ℝ ∙ (p : E))ᗮ) : E) = 0 := by
  let x : ({p}ᶜ ∩ {q}ᶜ : Set (Metric.sphere (0 : E) 1)) := ⟨-p, by
    constructor
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (ne_neg_of_mem_unit_sphere ℝ p).symm
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hq.symm⟩
  refine ⟨x, ?_⟩
  simp only [stereographicOverlapHomeomorph_apply_coe, x, stereographic_apply_neg,
    Submodule.coe_zero]

private theorem normalize {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : C(X, E)) (hV : ∀ x, V x ≠ 0) (x : X) :
    ‖ContinuousMap.normalizeOfNoZero V hV x‖ = 1 := by
  simp

private noncomputable def orthogonalHomotopy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : C(Metric.sphere (0 : E) 1, E))
    (hV : ∀ p, V p ≠ 0) (hOrth : ∀ p, inner ℝ p.1 (V p) = 0) :
    ContinuousMap.Homotopy (ContinuousMap.id (Metric.sphere (0 : E) 1))
      (Metric.Sphere.antipodal (E := E)) :=
  Metric.Sphere.homotopyAntipodalOfNowhereZeroOrthogonal V hV hOrth

private theorem subdivisionZero (X : TopCat) (c : SingularChainFinsupp X 0) :
    singularSubdivision X 0 c = c :=
  singularSubdivision_degree_zero X c

private theorem subdivisionBoundary (X : TopCat) (n : ℕ)
    (c : SingularChainFinsupp X (n + 1)) :
    singularFinsuppBoundary X n (singularSubdivision X (n + 1) c) =
      singularSubdivision X n (singularFinsuppBoundary X n c) :=
  singularSubdivision_boundary X n c

private theorem coverInclusion {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) (hU : IsOpenCover U) :
    QuasiIso (smallSingularChainInclusion U) :=
  quasiIso_smallSingularChainInclusion U hU

private theorem emptyCover :
    let X : TopCat := TopCat.of Empty
    let U : Empty → Opens X := Empty.elim
    QuasiIso (smallSingularChainInclusion U) := by
  dsimp
  apply quasiIso_smallSingularChainInclusion
  rw [IsOpenCover]
  ext x
  exact x.elim

private noncomputable def reducedConnecting {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    TopCat.reducedSingularHomology X 1 ⟶
      TopCat.reducedSingularHomology ((Opens.toTopCat X).obj (U ⊓ V)) 0 :=
  twoOpenReducedMayerVietorisδZero U V hUV

private theorem emptyReducedZero :
    IsZero (TopCat.reducedSingularHomology TopCat.emptySpace 0) :=
  TopCat.isZero_reducedSingularHomologyZero_empty

private theorem disconnectedPathEndpoints {X : Type*} [TopologicalSpace X]
    [TotallyDisconnectedSpace X] {x y : X} (p : Path x y) : x = y :=
  TopCat.path_endpoints_eq_of_totallyDisconnected p

private theorem circleModel :
    sphere1 = TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := rfl

private theorem sphereModel :
    sphere2 = TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := rfl

private noncomputable def circleHomology :
    TopCat.reducedSingularHomology sphere1 1 ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularHomologyOneSphereOneIntegerIso

private noncomputable def sphereHomology :
    TopCat.reducedSingularHomology sphere2 2 ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularHomologyTwoSphereTwoIntegerIso

private theorem antipodalAction :
    TopCat.reducedSingularHomologyMap sphere2Antipodal 2 = -𝟙 _ :=
  reducedSingularHomologyMap_sphere2Antipodal_two

private theorem antipodalCoordinate :
    reducedSingularHomologyTwoSphereTwoIntegerIso.inv ≫
      TopCat.reducedSingularHomologyMap sphere2Antipodal 2 ≫
      reducedSingularHomologyTwoSphereTwoIntegerIso.hom =
    -𝟙 (ModuleCat.of ℤ ℤ) :=
  reducedSingularHomologyTwoSphereTwoIntegerIso_antipodal

private theorem nonhomotopy :
    ¬ ContinuousMap.Homotopic (ContinuousMap.id sphere2) sphere2Antipodal.hom :=
  sphere2_id_not_homotopic_antipodal

private theorem hairyBall (V : C(sphere2, E3))
    (hOrth : ∀ p, inner ℝ p.1 (V p) = 0) : ∃ p, V p = 0 :=
  sphere2_exists_zero_of_orthogonal_field V hOrth

-- Bundling a continuous orthogonal field on the standard metric sphere.
private theorem unbundledField
    (V : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (hContinuous : Continuous V) (hOrth : ∀ p, inner ℝ p.1 (V p) = 0) :
    ∃ p, V p = 0 := by
  let bundled : C(sphere2, E3) := ⟨V, hContinuous⟩
  obtain ⟨p, hp⟩ := sphere2_exists_zero_of_orthogonal_field bundled hOrth
  exact ⟨p, hp⟩

private theorem zeroField : ∃ p : sphere2, (ContinuousMap.const sphere2 (0 : E3)) p = 0 := by
  apply sphere2_exists_zero_of_orthogonal_field (ContinuousMap.const sphere2 (0 : E3))
  intro p
  simp

-- The real unit sphere has distinct antipodes with the same projective image.
-- This uses the maker's scalar-equivalence API, not the covering theorem.
private theorem realProjectivization_antipodalFiber :
    ∃ p : Metric.sphere (0 : ℝ) 1,
      p ≠ -p ∧
        Metric.Sphere.toProjectivization p = Metric.Sphere.toProjectivization (-p) := by
  let p : Metric.sphere (0 : ℝ) 1 := ⟨1, by simp⟩
  refine ⟨p, ne_neg_of_mem_unit_sphere ℝ p, ?_⟩
  exact (Metric.Sphere.toProjectivization_neg p).symm

-- With the stock product norm, the coordinate unit vectors have projective images
-- separated by a proper nonempty open set. Its preimage is the saturated open
-- predicate that the first coordinate is nonzero, so this also checks the topology.
private theorem realPlaneProjectivization_axisOpen :
    let e₁ : Metric.sphere (0 : ℝ × ℝ) 1 :=
      ⟨(1, 0), by simp [Prod.norm_def]⟩
    let e₂ : Metric.sphere (0 : ℝ × ℝ) 1 :=
      ⟨(0, 1), by simp [Prod.norm_def]⟩
    ∃ U : Set (Projectivization ℝ (ℝ × ℝ)),
      IsOpen U ∧ Metric.Sphere.toProjectivization e₁ ∈ U ∧
        Metric.Sphere.toProjectivization e₂ ∉ U := by
  dsimp only
  let A : Set {v : ℝ × ℝ // v ≠ 0} := {v | v.1.1 ≠ 0}
  let U : Set (Projectivization ℝ (ℝ × ℝ)) := Projectivization.mk' ℝ '' A
  have hpre : (Projectivization.mk' ℝ (V := ℝ × ℝ)) ⁻¹' U = A := by
    ext v
    constructor
    · rintro ⟨w, hw, hwv⟩
      have hmk : Projectivization.mk ℝ (w : ℝ × ℝ) w.2 =
          Projectivization.mk ℝ (v : ℝ × ℝ) v.2 := hwv
      obtain ⟨a, ha⟩ :=
        (Projectivization.mk_eq_mk_iff ℝ (w : ℝ × ℝ) (v : ℝ × ℝ) w.2 v.2).mp hmk
      change v.1.1 ≠ 0
      intro hv
      apply hw
      have hcoord := congrArg Prod.fst ha
      simpa [Units.smul_def, hv] using hcoord.symm
    · intro hv
      exact ⟨v, hv, rfl⟩
  have hU : IsOpen U := by
    apply (Projectivization.isQuotientMap_mk' ℝ (V := ℝ × ℝ)).isCoinducing.isOpen_preimage.mp
    rw [hpre]
    exact isOpen_ne.preimage (continuous_fst.comp continuous_subtype_val)
  refine ⟨U, hU, ?_, ?_⟩
  · rw [Metric.Sphere.toProjectivization_apply]
    exact ⟨⟨(1, 0), by simp⟩, by simp [A], rfl⟩
  · rw [Metric.Sphere.toProjectivization_apply]
    intro h
    have hz : (⟨(0, 1), by simp⟩ : {v : ℝ × ℝ // v ≠ 0}) ∈ A := by
      rw [← hpre]
      exact h
    simp [A] at hz

end SphereTopologyPublicClient
