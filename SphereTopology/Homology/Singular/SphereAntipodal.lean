/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

public import SphereTopology.Homology.Singular.Sphere
public import SphereTopology.Homotopy.TangentField

/-!
# The antipodal action on the standard two-sphere

This module computes the action of the literal antipodal self-map of the
standard metric two-sphere on integral homology.  The north/south puncture
cover is exchanged, while the resulting sign-free endomorphism of the literal
puncture intersection is homotopic to the identity.  The ordered
Mayer--Vietoris swap is therefore the unique source of the final minus sign.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap
open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The bundled antipodal self-map of the literal standard two-sphere. -/
def sphere2Antipodal : sphere2 ⟶ sphere2 :=
  TopCat.ofHom (Metric.Sphere.antipodal (E := E3))

@[simp]
theorem sphere2Antipodal_apply (p : sphere2) :
    sphere2Antipodal p = -p := rfl

@[simp]
theorem sphere2Antipodal_north :
    sphere2Antipodal sphere2NorthPoint = sphere2SouthPoint := rfl

@[simp]
theorem sphere2Antipodal_south :
    sphere2Antipodal sphere2SouthPoint = sphere2NorthPoint := by
  change -sphere2SouthPoint = sphere2NorthPoint
  simp [sphere2SouthPoint]

/-- Antipodal negation sends the north-punctured open into the
south-punctured open. -/
theorem sphere2Antipodal_mapsTo_north_south :
    Set.MapsTo sphere2Antipodal sphere2NorthPunctured
      sphere2SouthPunctured := by
  intro p hp
  change p ≠ sphere2NorthPoint at hp
  change -p ≠ sphere2SouthPoint
  simpa [sphere2SouthPoint] using hp

/-- Antipodal negation sends the south-punctured open into the
north-punctured open. -/
theorem sphere2Antipodal_mapsTo_south_north :
    Set.MapsTo sphere2Antipodal sphere2SouthPunctured
      sphere2NorthPunctured := by
  intro p hp
  change p ≠ sphere2SouthPoint at hp
  change -p ≠ sphere2NorthPoint
  intro h
  apply hp
  have hneg := congrArg Neg.neg h
  simpa [sphere2SouthPoint] using hneg

/-- Antipodal negation as a point of the literal puncture intersection. -/
def sphere2PunctureIntersectionAntipodalPoint
    (p : sphere2PunctureIntersection) : sphere2PunctureIntersection :=
  ⟨-p.1, by
    have hpN : p.1 ≠ sphere2NorthPoint := by
      simpa [sphere2NorthPunctured] using p.2.1
    have hpS : p.1 ≠ sphere2SouthPoint := by
      simpa [sphere2SouthPunctured] using p.2.2
    constructor
    · change -p.1 ≠ sphere2NorthPoint
      intro h
      exact hpS (by
        have hneg := congrArg Neg.neg h
        simpa [sphere2SouthPoint] using hneg)
    · change -p.1 ≠ sphere2SouthPoint
      simpa [sphere2SouthPoint] using hpN⟩

/-- The antipodal endomorphism of the literal puncture intersection. -/
def sphere2PunctureIntersectionAntipodal :
    C(sphere2PunctureIntersection, sphere2PunctureIntersection) :=
  ⟨sphere2PunctureIntersectionAntipodalPoint,
    (continuous_neg.comp continuous_subtype_val).subtype_mk _⟩

/-- The sign-free endomorphism induced from the swapped two-open cover: first
restrict antipodal negation to the south/north intersection, then forget the
order by the accepted swap map. -/
def sphere2PunctureIntersectionAntipodalInduced :
    TopCat.of sphere2PunctureIntersection ⟶
      TopCat.of sphere2PunctureIntersection :=
  AlgebraicTopology.twoOpenIntersectionMap sphere2Antipodal
      sphere2NorthPunctured sphere2SouthPunctured
      sphere2SouthPunctured sphere2NorthPunctured
      sphere2Antipodal_mapsTo_north_south
      sphere2Antipodal_mapsTo_south_north ≫
    AlgebraicTopology.twoOpenIntersectionSwapMap
      sphere2SouthPunctured sphere2NorthPunctured

/-- The induced sign-free endomorphism is literally antipodal negation. -/
theorem sphere2PunctureIntersectionAntipodalInduced_eq :
    sphere2PunctureIntersectionAntipodalInduced =
      TopCat.ofHom sphere2PunctureIntersectionAntipodal := by
  ext p
  rfl

@[simp]
theorem sphere2PunctureIntersectionAntipodal_coe
    (p : sphere2PunctureIntersection) :
    ((sphere2PunctureIntersectionAntipodal p).1.1 : E3) =
      -(p.1.1 : E3) := by
  rfl

/-- Antipodal negation is involutive on the literal puncture intersection. -/
theorem sphere2PunctureIntersectionAntipodal_comp :
    sphere2PunctureIntersectionAntipodal.comp
      sphere2PunctureIntersectionAntipodal =
        ContinuousMap.id sphere2PunctureIntersection := by
  ext p
  apply Subtype.ext
  apply Subtype.ext
  simp

/-- Antipodal negation on the literal equator. -/
def sphere2EquatorAntipodalPoint (p : sphere2Equator) : sphere2Equator :=
  ⟨-p.1, by simpa using p.2⟩

/-- Continuous antipodal negation on the literal equator, preserving its zero
third coordinate. -/
def sphere2EquatorAntipodal : C(sphere2Equator, sphere2Equator) :=
  ⟨sphere2EquatorAntipodalPoint, by
    apply Continuous.subtype_mk
    exact continuous_neg.comp continuous_subtype_val⟩

@[simp]
theorem sphere2EquatorAntipodal_coe (p : sphere2Equator) :
    ((sphere2EquatorAntipodal p).1.1 : E3) = -(p.1.1 : E3) := by
  rfl

/-- Rotate an equator point through angle `π t` in its first two
coordinates, keeping the third coordinate fixed at zero. -/
def sphere2EquatorHalfTurnVector
    (t : unitInterval) (p : sphere2Equator) : E3 :=
  WithLp.toLp 2 ![
    Real.cos (Real.pi * (t : ℝ)) * (p.1.1 : E3) 0 -
      Real.sin (Real.pi * (t : ℝ)) * (p.1.1 : E3) 1,
    Real.sin (Real.pi * (t : ℝ)) * (p.1.1 : E3) 0 +
      Real.cos (Real.pi * (t : ℝ)) * (p.1.1 : E3) 1,
    0]

@[simp]
theorem sphere2EquatorHalfTurnVector_first
    (t : unitInterval) (p : sphere2Equator) :
    sphere2EquatorHalfTurnVector t p 0 =
      Real.cos (Real.pi * (t : ℝ)) * (p.1.1 : E3) 0 -
        Real.sin (Real.pi * (t : ℝ)) * (p.1.1 : E3) 1 := by
  simp [sphere2EquatorHalfTurnVector]

@[simp]
theorem sphere2EquatorHalfTurnVector_second
    (t : unitInterval) (p : sphere2Equator) :
    sphere2EquatorHalfTurnVector t p 1 =
      Real.sin (Real.pi * (t : ℝ)) * (p.1.1 : E3) 0 +
        Real.cos (Real.pi * (t : ℝ)) * (p.1.1 : E3) 1 := by
  simp [sphere2EquatorHalfTurnVector]

@[simp]
theorem sphere2EquatorHalfTurnVector_third
    (t : unitInterval) (p : sphere2Equator) :
    sphere2EquatorHalfTurnVector t p 2 = 0 := by
  simp [sphere2EquatorHalfTurnVector]

theorem sphere2EquatorHalfTurnVector_norm
    (t : unitInterval) (p : sphere2Equator) :
    ‖sphere2EquatorHalfTurnVector t p‖ = 1 := by
  have hpNorm : ‖(p.1.1 : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
  have hpSq := EuclideanSpace.real_norm_sq_eq (p.1.1 : E3)
  rw [hpNorm, Fin.sum_univ_three, p.2] at hpSq
  have htrig := Real.cos_sq_add_sin_sq (Real.pi * (t : ℝ))
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [sphere2EquatorHalfTurnVector_first,
    sphere2EquatorHalfTurnVector_second,
    sphere2EquatorHalfTurnVector_third]
  nlinarith

/-- The equatorial half-turn as a point of the literal equator. -/
def sphere2EquatorHalfTurnPoint
    (t : unitInterval) (p : sphere2Equator) : sphere2Equator :=
  ⟨⟨sphere2EquatorHalfTurnVector t p,
      mem_sphere_zero_iff_norm.mpr (sphere2EquatorHalfTurnVector_norm t p)⟩,
    sphere2EquatorHalfTurnVector_third t p⟩

theorem continuous_sphere2EquatorHalfTurnPoint :
    Continuous (fun q : unitInterval × sphere2Equator ↦
      sphere2EquatorHalfTurnPoint q.1 q.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  unfold sphere2EquatorHalfTurnVector
  apply (PiLp.continuous_toLp 2 _).comp
  fun_prop

/-- The jointly continuous equatorial rotation by angle `π * t`, from the
identity at time zero to antipodal negation at time one. The rotation uses the
ordered first two coordinates and leaves the third coordinate zero. -/
def sphere2EquatorHalfTurnMap :
    C(unitInterval × sphere2Equator, sphere2Equator) :=
  ⟨fun q ↦ sphere2EquatorHalfTurnPoint q.1 q.2,
    continuous_sphere2EquatorHalfTurnPoint⟩

theorem sphere2EquatorHalfTurnPoint_zero (p : sphere2Equator) :
    sphere2EquatorHalfTurnPoint 0 p = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [sphere2EquatorHalfTurnPoint,
    sphere2EquatorHalfTurnVector, p.2]

theorem sphere2EquatorHalfTurnPoint_one (p : sphere2Equator) :
    sphere2EquatorHalfTurnPoint 1 p = sphere2EquatorAntipodal p := by
  apply Subtype.ext
  apply Subtype.ext
  change sphere2EquatorHalfTurnVector 1 p =
    ((sphere2EquatorAntipodal p).1.1 : E3)
  rw [sphere2EquatorAntipodal_coe]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [sphere2EquatorHalfTurnVector, p.2]

/-- The explicit equatorial half-turn from the identity to antipodal
negation. -/
def sphere2EquatorHalfTurnHomotopy :
    (ContinuousMap.id sphere2Equator).Homotopy sphere2EquatorAntipodal :=
  ⟨sphere2EquatorHalfTurnMap,
    sphere2EquatorHalfTurnPoint_zero,
    sphere2EquatorHalfTurnPoint_one⟩

/-- The accepted radial deformation is equivariant for antipodal negation at
the unnormalized-vector level. -/
theorem sphere2PunctureIntersectionLinearVector_antipodal
    (t : unitInterval) (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionLinearVector t
        (sphere2PunctureIntersectionAntipodal p) =
      -sphere2PunctureIntersectionLinearVector t p := by
  unfold sphere2PunctureIntersectionLinearVector
  rw [sphere2PunctureIntersectionAntipodal_coe]
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp

/-- The accepted normalized radial deformation commutes with antipodal
negation. -/
theorem sphere2PunctureIntersectionRadialPoint_antipodal
    (t : unitInterval) (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionRadialPoint t
        (sphere2PunctureIntersectionAntipodal p) =
      sphere2PunctureIntersectionAntipodal
        (sphere2PunctureIntersectionRadialPoint t p) := by
  apply Subtype.ext
  apply Subtype.ext
  change sphere2PunctureIntersectionRadialVector t
      (sphere2PunctureIntersectionAntipodal p) =
    -sphere2PunctureIntersectionRadialVector t p
  rw [sphere2PunctureIntersectionRadialVector,
    sphere2PunctureIntersectionRadialVector,
    sphere2PunctureIntersectionLinearVector_antipodal]
  simp

/-- Equatorial projection commutes with antipodal negation. -/
theorem sphere2PunctureIntersectionToEquator_antipodal
    (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionToEquator
        (sphere2PunctureIntersectionAntipodal p) =
      sphere2EquatorAntipodal
        (sphere2PunctureIntersectionToEquator p) := by
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (fun q : sphere2PunctureIntersection ↦ q.1.1)
    (sphere2PunctureIntersectionRadialPoint_antipodal 0 p)
  change (sphere2PunctureIntersectionRadialPoint 0
      (sphere2PunctureIntersectionAntipodal p)).1.1 =
    -(sphere2PunctureIntersectionRadialPoint 0 p).1.1
  exact h.trans
    (sphere2PunctureIntersectionAntipodal_coe
      (sphere2PunctureIntersectionRadialPoint 0 p))

/-- Equator inclusion commutes with antipodal negation. -/
theorem sphere2EquatorToPunctureIntersection_antipodal
    (p : sphere2Equator) :
    sphere2EquatorToPunctureIntersection (sphere2EquatorAntipodal p) =
      sphere2PunctureIntersectionAntipodal
        (sphere2EquatorToPunctureIntersection p) := by
  apply Subtype.ext
  apply Subtype.ext
  change -(p.1.1 : E3) = -(p.1.1 : E3)
  rfl

theorem sphere2PunctureIntersectionAntipodal_projection_eq :
    sphere2PunctureIntersectionAntipodal.comp
        (sphere2EquatorToPunctureIntersection.comp
          sphere2PunctureIntersectionToEquator) =
      sphere2EquatorToPunctureIntersection.comp
        (sphere2EquatorAntipodal.comp
          sphere2PunctureIntersectionToEquator) := by
  ext p
  exact (sphere2EquatorToPunctureIntersection_antipodal
    (sphere2PunctureIntersectionToEquator p)).symm

/-- The sign-free antipodal endomorphism of the literal puncture intersection
is homotopic to the identity. -/
theorem sphere2PunctureIntersectionAntipodal_homotopic_id :
    ContinuousMap.Homotopic sphere2PunctureIntersectionAntipodal
      (ContinuousMap.id sphere2PunctureIntersection) := by
  let P := sphere2EquatorToPunctureIntersection.comp
    sphere2PunctureIntersectionToEquator
  have hRadial : ContinuousMap.Homotopic P
      (ContinuousMap.id sphere2PunctureIntersection) :=
    ⟨sphere2PunctureIntersectionRadialHomotopy⟩
  have hFirst : ContinuousMap.Homotopic
      sphere2PunctureIntersectionAntipodal
      (sphere2EquatorToPunctureIntersection.comp
        (sphere2EquatorAntipodal.comp
          sphere2PunctureIntersectionToEquator)) := by
    rw [← sphere2PunctureIntersectionAntipodal_projection_eq]
    exact (ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.refl
        sphere2PunctureIntersectionAntipodal) hRadial).symm
  have hMiddle : ContinuousMap.Homotopic
      (sphere2EquatorToPunctureIntersection.comp
        (sphere2EquatorAntipodal.comp
          sphere2PunctureIntersectionToEquator)) P := by
    exact ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.refl sphere2EquatorToPunctureIntersection)
      (ContinuousMap.Homotopic.comp
        ⟨sphere2EquatorHalfTurnHomotopy.symm⟩
        (ContinuousMap.Homotopic.refl sphere2PunctureIntersectionToEquator))
  exact hFirst.trans (hMiddle.trans hRadial)

/-- On ordinary integral homology, the antipodal restriction followed by the
sign-free intersection swap acts as the identity. -/
theorem sphere2PunctureIntersectionAntipodal_homology_eq_id (n : ℕ) :
    HomologicalComplex.homologyMap
          (AlgebraicTopology.integralSingularChainMap
            (AlgebraicTopology.twoOpenIntersectionMap sphere2Antipodal
              sphere2NorthPunctured sphere2SouthPunctured
              sphere2SouthPunctured sphere2NorthPunctured
              sphere2Antipodal_mapsTo_north_south
              sphere2Antipodal_mapsTo_south_north)) n ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.integralSingularChainMap
            (AlgebraicTopology.twoOpenIntersectionSwapMap
              sphere2SouthPunctured sphere2NorthPunctured)) n = 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp]
  simp only [AlgebraicTopology.integralSingularChainMap,
    ← Functor.map_comp]
  change HomologicalComplex.homologyMap
    (AlgebraicTopology.integralSingularChainMap
      sphere2PunctureIntersectionAntipodalInduced) n = 𝟙 _
  rw [sphere2PunctureIntersectionAntipodalInduced_eq]
  have htop : TopCat.Homotopy
      (TopCat.ofHom sphere2PunctureIntersectionAntipodal) (𝟙 _) :=
    sphere2PunctureIntersectionAntipodal_homotopic_id.some
  have h := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    htop AlgebraicTopology.integerCoefficients n
  simpa [AlgebraicTopology.integralSingularChainMap] using h

set_option linter.style.haveILetI false in
/-- The connecting morphism for the reversed south/north cover is an
isomorphism.  This is derived from the accepted north/south isomorphism and
the ordered-cover swap theorem. -/
theorem sphere2MayerVietorisδOne_reversed_isIso :
    IsIso (AlgebraicTopology.twoOpenMayerVietorisδ
      sphere2SouthPunctured sphere2NorthPunctured
      sphere2Punctured_join_reversed 1) := by
  letI := sphere2MayerVietorisδOne_isIso
  let eSwap := HomologicalComplex.homologyMapIso
    (AlgebraicTopology.twoOpenIntersectionSwapChainIso
      sphere2SouthPunctured sphere2NorthPunctured) 1
  let eTarget := -(asIso (AlgebraicTopology.twoOpenMayerVietorisδ
    sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1)) ≪≫
      eSwap.symm
  have hδ : AlgebraicTopology.twoOpenMayerVietorisδ
      sphere2SouthPunctured sphere2NorthPunctured
        sphere2Punctured_join_reversed 1 = eTarget.hom := by
    apply (cancel_mono eSwap.hom).1
    change AlgebraicTopology.twoOpenMayerVietorisδ
        sphere2SouthPunctured sphere2NorthPunctured
          sphere2Punctured_join_reversed 1 ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.twoOpenIntersectionSwapChainIso
            sphere2SouthPunctured sphere2NorthPunctured).hom 1 =
      eTarget.hom ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.twoOpenIntersectionSwapChainIso
            sphere2SouthPunctured sphere2NorthPunctured).hom 1
    rw [AlgebraicTopology.twoOpenMayerVietorisδ_swap_eq_neg
      sphere2SouthPunctured sphere2NorthPunctured
      sphere2Punctured_join_reversed sphere2Punctured_join 1]
    simp [eTarget, eSwap]
  rw [hδ]
  infer_instance

/-- The literal antipodal map acts by `-1` on ordinary integral second
homology of the literal standard two-sphere. -/
theorem integralSingularHomologyMap_sphere2Antipodal_two :
    HomologicalComplex.homologyMap
        (AlgebraicTopology.integralSingularChainMap sphere2Antipodal) 2 =
      -𝟙 _ := by
  let _ := sphere2MayerVietorisδOne_reversed_isIso
  exact
    AlgebraicTopology.integralSingularHomologyMap_eq_neg_id_of_twoOpen_swap
      sphere2Antipodal sphere2SouthPunctured sphere2NorthPunctured
      sphere2Antipodal_mapsTo_south_north
      sphere2Antipodal_mapsTo_north_south
      sphere2Punctured_join_reversed sphere2Punctured_join 1
      (sphere2PunctureIntersectionAntipodal_homology_eq_id 1)

/-- The matching positive-degree reduced integral homology action is `-1`. -/
theorem reducedSingularHomologyMap_sphere2Antipodal_two :
    TopCat.reducedSingularHomologyMap sphere2Antipodal 2 = -𝟙 _ := by
  exact integralSingularHomologyMap_sphere2Antipodal_two

/-- In the accepted fixed integer coordinate on reduced `H₂`, the literal
antipodal map is multiplication by `-1`. -/
theorem reducedSingularHomologyTwoSphereTwoIntegerIso_antipodal :
    reducedSingularHomologyTwoSphereTwoIntegerIso.inv ≫
        TopCat.reducedSingularHomologyMap sphere2Antipodal 2 ≫
        reducedSingularHomologyTwoSphereTwoIntegerIso.hom =
      -𝟙 (ModuleCat.of ℤ ℤ) := by
  rw [reducedSingularHomologyMap_sphere2Antipodal_two]
  simp

/-- The identity and literal antipodal self-maps of the standard two-sphere
are not homotopic. -/
theorem sphere2_id_not_homotopic_antipodal :
    ¬ ContinuousMap.Homotopic (ContinuousMap.id sphere2)
      sphere2Antipodal.hom := by
  intro h
  have hMaps := TopCat.reducedSingularHomologyMap_eq_of_homotopy
    (h.some : TopCat.Homotopy (𝟙 sphere2) sphere2Antipodal) 2
  have hMaps' : TopCat.reducedSingularHomologyMap (𝟙 sphere2) 2 =
      TopCat.reducedSingularHomologyMap sphere2Antipodal 2 := by
    change TopCat.reducedSingularHomologyMap
      (TopCat.ofHom (ContinuousMap.id sphere2)) 2 = _
    exact hMaps
  have hCoordinate :
      (𝟙 (ModuleCat.of ℤ ℤ)) = -𝟙 (ModuleCat.of ℤ ℤ) := by
    calc
      𝟙 (ModuleCat.of ℤ ℤ) =
          reducedSingularHomologyTwoSphereTwoIntegerIso.inv ≫
            TopCat.reducedSingularHomologyMap (𝟙 sphere2) 2 ≫
            reducedSingularHomologyTwoSphereTwoIntegerIso.hom := by simp
      _ = reducedSingularHomologyTwoSphereTwoIntegerIso.inv ≫
            TopCat.reducedSingularHomologyMap sphere2Antipodal 2 ≫
            reducedSingularHomologyTwoSphereTwoIntegerIso.hom := by rw [hMaps']
      _ = -𝟙 (ModuleCat.of ℤ ℤ) :=
        reducedSingularHomologyTwoSphereTwoIntegerIso_antipodal
  have hOne := congrArg
    (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ ↦ f (1 : ℤ))
    hCoordinate
  norm_num at hOne

end SphereTopology
