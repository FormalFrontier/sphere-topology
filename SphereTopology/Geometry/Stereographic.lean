/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Stereographic coordinates on punctured spheres

Stereographic projection identifies the unit sphere with one pole removed with
that pole's orthogonal complement. Removing a distinct second pole removes its
stereographic image from the model space, not necessarily the origin.

* `stereographicHomeomorph` normalizes the source and target of Mathlib's
  `stereographic` to the canonical singleton-complement subtype and orthogonal
  complement.
* `stereographicOverlapHomeomorph` restricts the same map to the complement of two
  distinct poles.

The coordinate maps require a real inner-product space, but neither completeness
nor a dimension hypothesis. The deleted pole is `p`; its antipode maps to zero.
The forward and inverse maps retain Mathlib's normalization, with forward factor
`2 / (1 - inner ℝ p x)`.

The topology-only puncture and simple-connectivity APIs live in
`SphereTopology.Homotopy.Sphere` and are stated for arbitrary real normed spaces
with their original norm; they do not depend on these orthogonal coordinates.

## References

* Heather Macbeth's stereographic sphere charts in
  `Mathlib.Geometry.Manifold.Instances.Sphere` supply the projection and its inverse
  laws. Mathlib's partial-homeomorphism and homeomorphism contributors supply the
  restriction and subtype-normalization constructions.
* Formal Frontier Agents' finite sphere and circle puncture formalizations in
  `SphereTopology.Homology.Singular.Sphere` and
  `SphereTopology.Homology.Singular.Circle` use the same chart-normalization approach.
-/

@[expose] public section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inverse stereographic projection sends zero to the antipode of the deleted
pole. -/
@[simp]
theorem stereographic_symm_apply_zero (p : Metric.sphere (0 : E) 1) :
    (stereographic (norm_eq_of_mem_sphere p)).symm 0 = -p := by
  have hneg : -p ∈ (stereographic (norm_eq_of_mem_sphere p)).source := by
    simpa only [stereographic_source, Set.mem_compl_iff, Set.mem_singleton_iff]
      using (ne_neg_of_mem_unit_sphere ℝ p).symm
  simpa only [stereographic_apply_neg] using
    (stereographic (norm_eq_of_mem_sphere p)).left_inv hneg

/-- Stereographic coordinates on the unit sphere with the pole `p` removed, taking
values in the orthogonal complement of the line through `p`. -/
noncomputable def stereographicHomeomorph (p : Metric.sphere (0 : E) 1) :
    ({p}ᶜ : Set (Metric.sphere (0 : E) 1)) ≃ₜ (ℝ ∙ (p : E))ᗮ :=
  (Homeomorph.setCongr
      (stereographic_source (norm_eq_of_mem_sphere p)).symm).trans
    (stereographic (norm_eq_of_mem_sphere p)).toHomeomorphSourceTarget |>.trans
    (Homeomorph.setCongr (stereographic_target (norm_eq_of_mem_sphere p))) |>.trans
    (Homeomorph.Set.univ _)

/-- The normalized one-pole chart is Mathlib's stereographic projection. -/
@[simp]
theorem stereographicHomeomorph_apply (p : Metric.sphere (0 : E) 1)
    (x : ({p}ᶜ : Set (Metric.sphere (0 : E) 1))) :
    stereographicHomeomorph p x = stereographic (norm_eq_of_mem_sphere p) x.1 :=
  rfl

/-- The inverse one-pole chart has the same underlying sphere point as the inverse
stereographic projection. -/
@[simp]
theorem stereographicHomeomorph_symm_apply_coe (p : Metric.sphere (0 : E) 1)
    (w : (ℝ ∙ (p : E))ᗮ) :
    ((stereographicHomeomorph p).symm w : Metric.sphere (0 : E) 1) =
      (stereographic (norm_eq_of_mem_sphere p)).symm w :=
  rfl

/-- Stereographic coordinates on the unit sphere with distinct poles `p` and `q`
removed. The deleted point in the orthogonal complement is the stereographic image
of `q`, which equals zero only when `q` is the antipode of `p`. -/
noncomputable def stereographicOverlapHomeomorph (p q : Metric.sphere (0 : E) 1)
    (hpq : p ≠ q) :
    ({p}ᶜ ∩ {q}ᶜ : Set (Metric.sphere (0 : E) 1)) ≃ₜ
      ({stereographic (norm_eq_of_mem_sphere p) q}ᶜ : Set (ℝ ∙ (p : E))ᗮ) := by
  let σ := stereographic (norm_eq_of_mem_sphere p)
  have hsub : ({p}ᶜ ∩ {q}ᶜ : Set (Metric.sphere (0 : E) 1)) ⊆ σ.source := by
    intro x hx
    simpa only [σ, stereographic_source] using hx.1
  have hq : q ∈ σ.source := by
    simpa only [σ, stereographic_source, Set.mem_compl_iff, Set.mem_singleton_iff]
      using hpq.symm
  refine σ.homeomorphOfImageSubsetSource hsub ?_
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    change σ x ≠ σ q
    intro h
    exact hx.2 (σ.injOn (hsub hx) hq h)
  · intro hw
    change w ≠ σ q at hw
    have ht : w ∈ σ.target := by trivial
    refine ⟨σ.symm w, ⟨?_, ?_⟩, σ.right_inv ht⟩
    · simpa only [σ, stereographic_source] using σ.map_target ht
    · change σ.symm w ≠ q
      intro heq
      apply hw
      calc
        w = σ (σ.symm w) := (σ.right_inv ht).symm
        _ = σ q := congrArg σ heq

/-- The two-pole chart is the restriction of the same stereographic projection. -/
@[simp]
theorem stereographicOverlapHomeomorph_apply_coe (p q : Metric.sphere (0 : E) 1)
    (hpq : p ≠ q) (x : ({p}ᶜ ∩ {q}ᶜ : Set (Metric.sphere (0 : E) 1))) :
    (stereographicOverlapHomeomorph p q hpq x : (ℝ ∙ (p : E))ᗮ) =
      stereographic (norm_eq_of_mem_sphere p) x.1 :=
  rfl

/-- The inverse two-pole chart is the restriction of inverse stereographic
projection. -/
@[simp]
theorem stereographicOverlapHomeomorph_symm_apply_coe (p q : Metric.sphere (0 : E) 1)
    (hpq : p ≠ q)
    (w : ({stereographic (norm_eq_of_mem_sphere p) q}ᶜ : Set (ℝ ∙ (p : E))ᗮ)) :
    ((stereographicOverlapHomeomorph p q hpq).symm w : Metric.sphere (0 : E) 1) =
      (stereographic (norm_eq_of_mem_sphere p)).symm w.1 :=
  rfl
