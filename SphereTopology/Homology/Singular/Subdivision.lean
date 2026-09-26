/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formalization Worker A, Formalization Worker B, Prism.
-- See README.md for internal reuse.
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Analysis.Convex.MetricSpace
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Sets.OpenCover

/-!
# Affine barycentric subdivision

This file constructs signed barycentric subdivision and its cone/prism homotopy
on integer chains.  The orientation convention is the simplicial boundary

`∂[v₀, …, vₙ] = ∑ i, (-1)^i [v₀, …, v̂ᵢ, …, vₙ]`.

It then realizes these operators on singular simplices.  Every simplex produced
by subdivision or the homotopy has range contained in the range of an input
simplex.  Iterated subdivision eventually makes every simplex in a finitely
supported chain small relative to an open cover.
-/

@[expose] public section

open CategoryTheory Convexity
open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

/-- The continuous affine map specified by the images of the vertices. -/
def affineContinuousMap {m n : ℕ}
    (v : Fin (n + 1) → StdSimplex ℝ (Fin (m + 1))) :
    C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (m + 1))) :=
  ⟨affineMapMk v, by
    classical
    rw [(isEmbedding_toFun_comp_weights ℝ (Fin (m + 1))).continuous_iff]
    apply continuous_pi
    intro j
    change Continuous (fun x ↦ (iConvexComb x v).weights j)
    simp only [iConvexComb, weights_sConvexComb]
    change Continuous (fun (x : StdSimplex ℝ (Fin (n + 1))) ↦
      ((x.weights.mapDomain v).sum fun d r ↦ r • d.weights) j)
    simp only [Finsupp.sum_apply]
    simp_rw [Finsupp.sum_mapDomain_index
      (h := fun (d : StdSimplex ℝ (Fin (m + 1))) (r : ℝ) ↦ (r • d.weights) j)
      (fun _ ↦ by simp only [zero_smul, Finsupp.zero_apply])
      (fun _ _ _ ↦ by simp only [add_smul, Finsupp.add_apply])]
    have hfun :
        (fun (x : StdSimplex ℝ (Fin (n + 1))) ↦
          x.weights.sum fun a r ↦ (r • (v a).weights) j) =
        (fun x ↦ ∑ a, x.weights a * (v a).weights j) := by
      funext x
      rw [Finsupp.sum_fintype]
      · rfl
      · intro a
        rw [zero_smul]
        rfl
    rw [hfun]
    fun_prop⟩

@[simp]
theorem affineContinuousMap_single {m n : ℕ}
    (v : Fin (n + 1) → StdSimplex ℝ (Fin (m + 1))) (i : Fin (n + 1)) :
    affineContinuousMap v (.single i) = v i :=
  by
    change affineMapMk (R := ℝ) v (.single i) = v i
    exact affineMapMk_single (R := ℝ) v i

/-- An affine `n`-simplex in the real standard `m`-simplex, specified by its
ordered `n + 1` vertices. The associated affine map is `affineMapMk`. -/
abbrev AffineSimplex (m n : ℕ) :=
  Fin (n + 1) → StdSimplex ℝ (Fin (m + 1))

/-- Finite integer linear combinations of affine `n`-simplices in the standard
`m`-simplex, represented by finitely supported coefficient functions. -/
abbrev AffineChain (m n : ℕ) := AffineSimplex m n →₀ ℤ

/-- The simplicial set of ordered tuples of points of the standard `m`-simplex.
Its simplicial operators select or repeat vertices by the given order map. -/
def affineSSet (m : ℕ) : SSet where
  obj n := Fin (n.unop.len + 1) → StdSimplex ℝ (Fin (m + 1))
  map f := ↾fun a ↦ a ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The integers as a module over themselves, used as coefficients for affine
simplicial chains. -/
abbrev affineIntegerCoefficients : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- Identify the degree-`n` simplicial chain object of `affineSSet m` with
finitely supported integer coefficients on affine `n`-simplices. -/
noncomputable def affineChainIso (m n : ℕ) :
    ((affineSSet m).chainComplex affineIntegerCoefficients).X n ≅
      ModuleCat.of ℤ (AffineChain m n) :=
  ((affineSSet m).isColimitChainComplexXCofan affineIntegerCoefficients n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (AffineSimplex m n))

@[reassoc]
theorem affineChainIso_ι (m n : ℕ) (a : AffineSimplex m n) :
    (affineSSet m).ιChainComplex a ≫ (affineChainIso m n).hom =
      ModuleCat.ofHom (Finsupp.lsingle a (R := ℤ) (M := ModuleCat.of ℤ ℤ)) := by
  change ((affineSSet m).chainComplexXCofan affineIntegerCoefficients n).ι.app ⟨a⟩ ≫
      (affineChainIso m n).hom =
    (ModuleCat.finsuppCocone ℤ ℤ (AffineSimplex m n)).ι.app ⟨a⟩
  exact CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
    ((affineSSet m).isColimitChainComplexXCofan affineIntegerCoefficients n)
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (AffineSimplex m n)) ⟨a⟩

/-- The categorical simplicial differential from degree `n + 1` to degree `n`,
transported through `affineChainIso` to finitely supported affine chains. -/
noncomputable def affineBoundaryHom (m n : ℕ) :
    ModuleCat.of ℤ (AffineChain m (n + 1)) ⟶ ModuleCat.of ℤ (AffineChain m n) :=
  (affineChainIso m (n + 1)).inv ≫
    ((affineSSet m).chainComplex affineIntegerCoefficients).d (n + 1) n ≫
      (affineChainIso m n).hom

/-- The `i`th face of an affine simplex, obtained by deleting vertex `i`
and retaining the order of the remaining vertices. -/
def AffineSimplex.face {m n : ℕ} (a : AffineSimplex m (n + 1))
    (i : Fin (n + 2)) : AffineSimplex m n :=
  fun j ↦ a (i.succAbove j)

set_option backward.isDefEq.respectTransparency false in
theorem lsingle_comp_affineBoundaryHom {m n : ℕ} (a : AffineSimplex m (n + 1)) :
    ModuleCat.ofHom (Finsupp.lsingle a (R := ℤ) (M := ModuleCat.of ℤ ℤ)) ≫
        affineBoundaryHom m n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ModuleCat.ofHom (Finsupp.lsingle (a.face i)
          (R := ℤ) (M := ModuleCat.of ℤ ℤ)) := by
  rw [← affineChainIso_ι]
  simp only [affineBoundaryHom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [SSet.ιChainComplex_d_assoc]
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Preadditive.zsmul_comp, affineChainIso_ι]
  rfl

theorem affineBoundaryHom_squared (m n : ℕ) :
    affineBoundaryHom m (n + 1) ≫ affineBoundaryHom m n = 0 := by
  simp only [affineBoundaryHom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [HomologicalComplex.d_comp_d_assoc]
  simp

/-- Cone an affine simplex to the apex `b`, inserting `b` as its first vertex. -/
def AffineSimplex.cone {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1)))
    (a : AffineSimplex m n) : AffineSimplex m (n + 1) :=
  Fin.cases b a

/-- The affine zero-simplex whose unique vertex is `b`. -/
def AffineSimplex.point {m : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) :
    AffineSimplex m 0 := fun _ ↦ b

/-- The oriented boundary of one affine simplex: the finite sum of its faces
with coefficient `(-1)^i` on the face obtained by deleting vertex `i`. -/
def affineBoundaryGenerator {m n : ℕ} (a : AffineSimplex m (n + 1)) :
    AffineChain m n :=
  ∑ i, (-1 : ℤ) ^ i.val • Finsupp.single (a.face i) 1

/-- Extend the alternating face boundary integer-linearly to affine chains. -/
def affineBoundary (m n : ℕ) : AffineChain m (n + 1) →ₗ[ℤ] AffineChain m n :=
  Finsupp.lift (AffineChain m n) ℤ (AffineSimplex m (n + 1))
    affineBoundaryGenerator

/-- The integer-linear cone operator on affine chains, prepending the common
apex `b` to each simplex and raising degree by one. -/
def affineCone (m n : ℕ) (b : StdSimplex ℝ (Fin (m + 1))) :
    AffineChain m n →ₗ[ℤ] AffineChain m (n + 1) :=
  Finsupp.lift (AffineChain m (n + 1)) ℤ (AffineSimplex m n)
    (fun a ↦ Finsupp.single (a.cone b) 1)

/-- The augmentation of affine zero-chains, summing their integer coefficients. -/
def affineAugmentation (m : ℕ) : AffineChain m 0 →ₗ[ℤ] ℤ :=
  Finsupp.lift ℤ ℤ (AffineSimplex m 0) (fun _ ↦ 1)

@[simp]
theorem affineBoundary_single {m n : ℕ} (a : AffineSimplex m (n + 1)) :
    affineBoundary m n (Finsupp.single a 1) = affineBoundaryGenerator a := by
  simp [affineBoundary]

theorem lsingle_comp_affineBoundary {m n : ℕ} (a : AffineSimplex m (n + 1)) :
    ModuleCat.ofHom (Finsupp.lsingle a (R := ℤ) (M := ModuleCat.of ℤ ℤ)) ≫
        ModuleCat.ofHom (affineBoundary m n) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ModuleCat.ofHom (Finsupp.lsingle (a.face i)
          (R := ℤ) (M := ModuleCat.of ℤ ℤ)) := by
  ext z
  simp [affineBoundary, affineBoundaryGenerator]

theorem affineBoundaryHom_eq (m n : ℕ) :
    affineBoundaryHom m n = ModuleCat.ofHom (affineBoundary m n) := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext
  intro z
  exact congrArg (fun f ↦ f z) (lsingle_comp_affineBoundaryHom a |>.trans
    (lsingle_comp_affineBoundary a).symm)

theorem affineBoundary_squared {m n : ℕ} (c : AffineChain m (n + 2)) :
    affineBoundary m n (affineBoundary m (n + 1) c) = 0 := by
  have h := affineBoundaryHom_squared m n
  rw [affineBoundaryHom_eq, affineBoundaryHom_eq] at h
  exact congrArg (fun f ↦ f c) h

@[simp]
theorem affineCone_single {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1)))
    (a : AffineSimplex m n) :
    affineCone m n b (Finsupp.single a 1) = Finsupp.single (a.cone b) 1 := by
  simp [affineCone]

@[simp]
theorem affineAugmentation_single {m : ℕ} (a : AffineSimplex m 0) (z : ℤ) :
    affineAugmentation m (Finsupp.single a z) = z := by
  simp [affineAugmentation]

theorem AffineSimplex.face_cone_zero {m n : ℕ}
    (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m n) :
    (a.cone b).face 0 = a := by
  funext j
  simp [AffineSimplex.face, AffineSimplex.cone]

theorem AffineSimplex.face_cone_one {m : ℕ}
    (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m 0) :
    (a.cone b).face 1 = AffineSimplex.point b := by
  funext j
  fin_cases j
  rfl

theorem AffineSimplex.face_cone_succ {m n : ℕ}
    (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m (n + 1))
    (i : Fin (n + 2)) :
    (a.cone b).face i.succ = (a.face i).cone b := by
  funext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [AffineSimplex.face, AffineSimplex.cone]
  · simp [AffineSimplex.face, AffineSimplex.cone, Fin.succ_succAbove_succ]

/-- Compose affine simplices by applying the affine map determined by `a`
to every vertex of `b`. Thus `b` parametrizes a simplex in the domain of `a`. -/
def AffineSimplex.comp {m n k : ℕ} (a : AffineSimplex m n)
    (b : AffineSimplex n k) : AffineSimplex m k :=
  fun j ↦ affineMapMk a (b j)

theorem AffineSimplex.comp_face {m n k : ℕ} (a : AffineSimplex m n)
    (b : AffineSimplex n (k + 1)) (i : Fin (k + 2)) :
    (a.comp b).face i = a.comp (b.face i) := rfl

theorem AffineSimplex.comp_cone {m n k : ℕ} (a : AffineSimplex m n)
    (b : AffineSimplex n k) (x : StdSimplex ℝ (Fin (n + 1))) :
    a.comp (b.cone x) = (a.comp b).cone (affineMapMk a x) := by
  funext j
  refine Fin.cases ?_ (fun j ↦ ?_) j <;> rfl

theorem affineBoundary_cone_single {m n : ℕ}
    (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m (n + 1)) :
    affineBoundary m (n + 1) (affineCone m (n + 1) b (Finsupp.single a 1)) =
      Finsupp.single a 1 -
        affineCone m n b (affineBoundary m n (Finsupp.single a 1)) := by
  simp only [affineCone_single, affineBoundary_single, affineBoundaryGenerator]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, AffineSimplex.face_cone_zero]
  rw [map_sum]
  simp only [map_smul, affineCone_single, AffineSimplex.face_cone_succ,
    Fin.val_succ, pow_succ]
  simp only [mul_neg, mul_one, neg_smul]
  rw [Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]

theorem affineBoundary_cone_degree_zero_single {m : ℕ}
    (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m 0) :
    affineBoundary m 0 (affineCone m 0 b (Finsupp.single a 1)) =
      Finsupp.single a 1 - Finsupp.single (AffineSimplex.point b) 1 := by
  simp only [affineCone_single, affineBoundary_single, affineBoundaryGenerator]
  rw [Fin.sum_univ_two]
  simp only [AffineSimplex.face_cone_zero, AffineSimplex.face_cone_one,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul]
  rw [sub_eq_add_neg]

theorem affineBoundary_cone_degree_zero {m : ℕ}
    (b : StdSimplex ℝ (Fin (m + 1))) (c : AffineChain m 0) :
    affineBoundary m 0 (affineCone m 0 b c) =
      c - affineAugmentation m c • Finsupp.single (AffineSimplex.point b) 1 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add, hf, hg]
      module
  | single a z =>
      have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
      calc
        affineBoundary m 0 (affineCone m 0 b (Finsupp.single a z)) =
            z • affineBoundary m 0
              (affineCone m 0 b (Finsupp.single a 1)) := by rw [hc, map_smul, map_smul]
        _ = z • (Finsupp.single a 1 -
            Finsupp.single (AffineSimplex.point b) 1) := by
              rw [affineBoundary_cone_degree_zero_single]
        _ = Finsupp.single a z - affineAugmentation m (Finsupp.single a z) •
            Finsupp.single (AffineSimplex.point b) 1 := by simp [smul_sub]

theorem affineBoundary_cone {m n : ℕ}
    (b : StdSimplex ℝ (Fin (m + 1))) (c : AffineChain m (n + 1)) :
    affineBoundary m (n + 1) (affineCone m (n + 1) b c) =
      c - affineCone m n b (affineBoundary m n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add, hf, hg]
      module
  | single a z =>
      have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
      rw [hc]
      simp only [map_smul, affineBoundary_cone_single, smul_sub]

/-- The center of an affine simplex, obtained by mapping the domain barycenter
through its affine map; equivalently, the equally weighted average of its vertices. -/
def AffineSimplex.center {m n : ℕ} (a : AffineSimplex m n) :
    StdSimplex ℝ (Fin (m + 1)) :=
  affineMapMk a (barycenter (K := ℝ) (M := Fin (n + 1)))

theorem AffineSimplex.comp_center {m n k : ℕ} (a : AffineSimplex m n)
    (b : AffineSimplex n k) :
    (a.comp b).center = affineMapMk a b.center := by
  change affineMapMk (a.comp b) (barycenter (K := ℝ) (M := Fin (k + 1))) =
    affineMapMk a (affineMapMk b (barycenter (K := ℝ) (M := Fin (k + 1))))
  have h := StdSimplex.comp_affineMapMk (affineMapMk a) b
  exact DFunLike.congr_fun h.symm (barycenter (K := ℝ) (M := Fin (k + 1)))

/-- Push affine chains forward along the affine map determined by `a`, adding
coefficients when distinct simplices have the same image. -/
def mapAffineChain {m n : ℕ} (a : AffineSimplex m n) (k : ℕ) :
    AffineChain n k →ₗ[ℤ] AffineChain m k :=
  Finsupp.lmapDomain ℤ ℤ (AffineSimplex.comp a)

@[simp]
theorem mapAffineChain_single {m n k : ℕ} (a : AffineSimplex m n)
    (b : AffineSimplex n k) :
    mapAffineChain a k (Finsupp.single b 1) = Finsupp.single (a.comp b) 1 := by
  simp [mapAffineChain]

theorem mapAffineChain_cone {m n k : ℕ} (a : AffineSimplex m n)
    (b : StdSimplex ℝ (Fin (n + 1))) (c : AffineChain n k) :
    mapAffineChain a (k + 1) (affineCone n k b c) =
      affineCone m k (affineMapMk a b) (mapAffineChain a k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single c z =>
      have hc : Finsupp.single c z = z • Finsupp.single c 1 := by simp
      rw [hc]
      simp only [map_smul, affineCone_single, mapAffineChain_single]
      rw [a.comp_cone]

/-- Signed barycentric subdivision of an affine simplex. A zero-simplex is
unchanged; in positive degree, cone the subdivided oriented boundary to its center. -/
noncomputable def subdivideSimplex {m : ℕ} (n : ℕ) : AffineSimplex m n → AffineChain m n :=
  match n with
  | 0 => fun a ↦ Finsupp.single a 1
  | n + 1 => fun a ↦
    affineCone m n a.center
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • subdivideSimplex n (a.face i))

/-- Extend signed barycentric subdivision integer-linearly to affine chains. -/
def affineSubdivision (m n : ℕ) : AffineChain m n →ₗ[ℤ] AffineChain m n :=
  Finsupp.lift (AffineChain m n) ℤ (AffineSimplex m n) (subdivideSimplex n)

@[simp]
theorem affineSubdivision_single {m n : ℕ} (a : AffineSimplex m n) :
    affineSubdivision m n (Finsupp.single a 1) = subdivideSimplex n a := by
  simp [affineSubdivision]

@[simp]
theorem subdivideSimplex_zero {m : ℕ} (a : AffineSimplex m 0) :
    subdivideSimplex 0 a = Finsupp.single a 1 := rfl

theorem subdivideSimplex_succ {m n : ℕ} (a : AffineSimplex m (n + 1)) :
    subdivideSimplex (n + 1) a =
      affineCone m n a.center
        (affineSubdivision m n (affineBoundaryGenerator a)) := by
  simp only [subdivideSimplex, affineBoundaryGenerator]
  rw [map_sum, map_sum]
  simp only [map_smul, affineSubdivision_single]
  rw [map_sum]
  simp only [map_smul]

theorem mapAffineChain_subdivideSimplex {m n k : ℕ} (a : AffineSimplex m n)
    (b : AffineSimplex n k) :
    mapAffineChain a k (subdivideSimplex k b) = subdivideSimplex k (a.comp b) := by
  induction k with
  | zero => simp [subdivideSimplex]
  | succ k ih =>
      simp only [subdivideSimplex]
      rw [mapAffineChain_cone, a.comp_center]
      congr 1
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, ih]
      rfl

@[simp↓]
theorem affineAugmentation_subdivide_zero {m : ℕ} (a : AffineSimplex m 0) :
    affineAugmentation m (subdivideSimplex 0 a) = 1 := by
  simp

theorem affineAugmentation_affineSubdivision_zero {m : ℕ} (c : AffineChain m 0) :
    affineAugmentation m (affineSubdivision m 0 c) = affineAugmentation m c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single a z =>
      have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
      rw [hc]
      simp only [map_smul, affineSubdivision_single, affineAugmentation_subdivide_zero,
        affineAugmentation_single]

theorem affineAugmentation_boundaryGenerator_degree_one {m : ℕ}
    (a : AffineSimplex m 1) :
    affineAugmentation m (affineBoundaryGenerator a) = 0 := by
  simp [affineBoundaryGenerator, Fin.sum_univ_two]

theorem affineSubdivision_boundary (m n : ℕ) (c : AffineChain m (n + 1)) :
    affineBoundary m n (affineSubdivision m (n + 1) c) =
      affineSubdivision m n (affineBoundary m n c) := by
  induction n with
  | zero =>
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add, hf, hg]
      | single a z =>
          have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
          rw [hc]
          simp only [map_smul]
          rw [affineSubdivision_single, subdivideSimplex_succ,
            affineBoundary_cone_degree_zero, affineBoundary_single]
          have haug : affineAugmentation m
              (affineSubdivision m 0 (affineBoundaryGenerator a)) = 0 := by
            rw [affineAugmentation_affineSubdivision_zero,
              affineAugmentation_boundaryGenerator_degree_one]
          rw [haug]
          simp
  | succ n ih =>
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add, hf, hg]
      | single a z =>
          have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
          rw [hc]
          simp only [map_smul]
          rw [affineSubdivision_single, subdivideSimplex_succ,
            affineBoundary_cone, affineBoundary_single]
          have hcycle : affineBoundary m n
              (affineSubdivision m (n + 1) (affineBoundaryGenerator a)) = 0 := by
            rw [ih, ← affineBoundary_single]
            rw [affineBoundary_squared]
            simp
          rw [hcycle]
          simp

/-- The degree-raising subdivision homotopy on one affine simplex. It is zero
in degree zero and otherwise cones `a - Sd(a) - H(∂a)` to the center of `a`.
This convention gives `∂H + H∂ = id - Sd`. -/
noncomputable def homotopySimplex {m : ℕ} (n : ℕ) : AffineSimplex m n → AffineChain m (n + 1) :=
  match n with
  | 0 => fun _ ↦ 0
  | n + 1 => fun a ↦
    affineCone m (n + 1) a.center
      (Finsupp.single a 1 - subdivideSimplex (n + 1) a -
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • homotopySimplex n (a.face i))

/-- Extend `homotopySimplex` integer-linearly, giving the degree-raising affine
chain homotopy with boundary identity `∂H + H∂ = id - Sd`. -/
def affineHomotopy (m n : ℕ) : AffineChain m n →ₗ[ℤ] AffineChain m (n + 1) :=
  Finsupp.lift (AffineChain m (n + 1)) ℤ (AffineSimplex m n) (homotopySimplex n)

@[simp]
theorem affineHomotopy_single {m n : ℕ} (a : AffineSimplex m n) :
    affineHomotopy m n (Finsupp.single a 1) = homotopySimplex n a := by
  simp [affineHomotopy]

@[simp]
theorem homotopySimplex_zero {m : ℕ} (a : AffineSimplex m 0) :
    homotopySimplex 0 a = 0 := rfl

theorem homotopySimplex_succ {m n : ℕ} (a : AffineSimplex m (n + 1)) :
    homotopySimplex (n + 1) a =
      affineCone m (n + 1) a.center
        (Finsupp.single a 1 - subdivideSimplex (n + 1) a -
          affineHomotopy m n (affineBoundaryGenerator a)) := by
  simp only [homotopySimplex, affineBoundaryGenerator]
  rw [map_sum]
  simp only [map_smul, affineHomotopy_single]

theorem mapAffineChain_homotopySimplex {m n k : ℕ} (a : AffineSimplex m n)
    (b : AffineSimplex n k) :
    mapAffineChain a (k + 1) (homotopySimplex k b) =
      homotopySimplex k (a.comp b) := by
  induction k with
  | zero => simp [homotopySimplex]
  | succ k ih =>
      simp only [homotopySimplex]
      rw [mapAffineChain_cone, a.comp_center]
      congr 1
      rw [map_sub, map_sub, mapAffineChain_single, mapAffineChain_subdivideSimplex,
        map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, ih]
      rfl

theorem affineHomotopy_degree_zero (m : ℕ) (c : AffineChain m 0) :
    affineBoundary m 0 (affineHomotopy m 0 c) = c - affineSubdivision m 0 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; module
  | single a z =>
      have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
      rw [hc]
      simp only [map_smul, affineHomotopy_single, homotopySimplex_zero,
        map_zero, affineSubdivision_single, subdivideSimplex_zero]
      module

theorem affineHomotopy_boundary (m n : ℕ) (c : AffineChain m (n + 1)) :
    affineBoundary m (n + 1) (affineHomotopy m (n + 1) c) +
        affineHomotopy m n (affineBoundary m n c) =
      c - affineSubdivision m (n + 1) c := by
  induction n with
  | zero =>
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg =>
          simp only [map_add]
          rw [add_add_add_comm, hf, hg]
          abel
      | single a z =>
          have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
          rw [hc]
          simp only [map_smul]
          rw [affineHomotopy_single, homotopySimplex_succ,
            affineBoundary_cone, affineBoundary_single, affineSubdivision_single]
          have hcycle : affineBoundary m 0
              (Finsupp.single a 1 - subdivideSimplex 1 a -
                affineHomotopy m 0 (affineBoundaryGenerator a)) = 0 := by
            rw [← affineSubdivision_single]
            simp only [map_sub, affineBoundary_single, affineSubdivision_boundary,
              affineHomotopy_degree_zero]
            module
          rw [hcycle]
          simp only [map_zero, sub_zero]
          module
  | succ n ih =>
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg =>
          simp only [map_add]
          rw [add_add_add_comm, hf, hg]
          abel
      | single a z =>
          have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
          rw [hc]
          simp only [map_smul]
          rw [affineHomotopy_single, homotopySimplex_succ,
            affineBoundary_cone, affineBoundary_single, affineSubdivision_single]
          have hb2 : affineBoundary m n (affineBoundaryGenerator a) = 0 := by
            rw [← affineBoundary_single]
            exact affineBoundary_squared (Finsupp.single a 1)
          have hT : affineBoundary m (n + 1)
              (affineHomotopy m (n + 1) (affineBoundaryGenerator a)) =
                affineBoundaryGenerator a -
                  affineSubdivision m (n + 1) (affineBoundaryGenerator a) := by
            have h := ih (affineBoundaryGenerator a)
            rw [hb2, map_zero, add_zero] at h
            exact h
          have hcycle : affineBoundary m (n + 1)
              (Finsupp.single a 1 - subdivideSimplex (n + 2) a -
                affineHomotopy m (n + 1) (affineBoundaryGenerator a)) = 0 := by
            rw [← affineSubdivision_single]
            simp only [map_sub, affineBoundary_single, affineSubdivision_boundary, hT]
            module
          rw [hcycle]
          simp only [map_zero, sub_zero]
          module

/-- The metric pulled back from the finite real weight-function space along the
standard simplex's weight embedding, with its existing topology. -/
local instance stdSimplexMetricSpace (M : Type*) [Fintype M] :
    MetricSpace (StdSimplex ℝ M) :=
  Topology.IsEmbedding.comapMetricSpace (fun t : StdSimplex ℝ M ↦ (t.weights : M → ℝ))
    (isEmbedding_toFun_comp_weights ℝ M)

theorem stdSimplex_dist_eq_weights {M : Type*} [Fintype M] (x y : StdSimplex ℝ M) :
    dist x y = dist (x.weights : M → ℝ) y.weights := rfl

local instance stdSimplexIsConvexDist (M : Type*) [Fintype M] :
    IsConvexDist (StdSimplex ℝ M) where
  dist_iConvexComb_fst_snd_le f := by
    have hweights (g : (StdSimplex ℝ M × StdSimplex ℝ M) → StdSimplex ℝ M) :
        (f.iConvexComb g).weights =
          f.weights.sum (fun i r ↦ r • (g i).weights) := by
      simp [iConvexComb, Finsupp.sum_mapDomain_index, add_smul]
    rw [stdSimplex_dist_eq_weights, hweights, hweights, iConvexComb_eq_sum]
    convert (dist_iConvexComb_le (X := M → ℝ) f
      (fun p ↦ (p.1.weights : M → ℝ)) (fun p ↦ (p.2.weights : M → ℝ))) using 1 <;>
        simp only [iConvexComb_eq_sum]
    all_goals simp [stdSimplex_dist_eq_weights]

/-- The diameter of the finite set of vertices, using the metric pulled back
from the standard simplex's real weight functions. -/
def AffineSimplex.vertexDiameter {m n : ℕ} (a : AffineSimplex m n) : ℝ :=
  Metric.diam (Set.range a)

theorem AffineSimplex.vertexDiameter_nonneg {m n : ℕ} (a : AffineSimplex m n) :
    0 ≤ a.vertexDiameter := Metric.diam_nonneg

theorem AffineSimplex.dist_le_vertexDiameter {m n : ℕ} (a : AffineSimplex m n)
    (i j : Fin (n + 1)) : dist (a i) (a j) ≤ a.vertexDiameter :=
  Metric.dist_le_diam_of_mem (Set.finite_range a |>.isBounded) ⟨i, rfl⟩ ⟨j, rfl⟩

theorem AffineSimplex.dist_center_vertex {m n : ℕ} (a : AffineSimplex m n)
    (i : Fin (n + 1)) :
    dist a.center (a i) ≤ (n : ℝ) / (n + 1) * a.vertexDiameter := by
  change dist ((barycenter (K := ℝ) (M := Fin (n + 1))).iConvexComb a) (a i) ≤ _
  refine (dist_iConvexComb_left_le _ _ _).trans ?_
  rw [iConvexComb_eq_sum, Finsupp.sum_fintype]
  · simp_rw [weights_barycenter_apply]
    simp only [Fintype.card_fin, smul_eq_mul]
    rw [← Finset.sum_erase_add Finset.univ (fun j ↦
      (↑(n + 1) : ℝ)⁻¹ * dist (a j) (a i)) (Finset.mem_univ i)]
    simp only [dist_self, mul_zero, add_zero]
    calc
      ∑ j ∈ Finset.univ.erase i, (↑(n + 1) : ℝ)⁻¹ * dist (a j) (a i) ≤
          ∑ _j ∈ Finset.univ.erase i, (↑(n + 1) : ℝ)⁻¹ * a.vertexDiameter := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (a.dist_le_vertexDiameter j i) (by positivity)
      _ = (n : ℝ) / (n + 1) * a.vertexDiameter := by
        rw [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
        simp only [Fintype.card_fin, Nat.add_sub_cancel]
        push_cast
        field_simp
  · intro j
    simp

theorem AffineSimplex.dist_center_affineMapMk {m n k : ℕ} (a : AffineSimplex m n)
    (x : StdSimplex ℝ (Fin (k + 1))) (v : Fin (k + 1) → Fin (n + 1)) :
    dist a.center (affineMapMk (a ∘ v) x) ≤
      (n : ℝ) / (n + 1) * a.vertexDiameter := by
  change dist a.center (x.iConvexComb (a ∘ v)) ≤ _
  refine (dist_iConvexComb_right_le a.center x (a ∘ v)).trans ?_
  rw [iConvexComb_eq_sum]
  calc
    x.weights.sum (fun i r ↦ r • dist a.center (a (v i))) ≤
        x.weights.sum (fun _i r ↦ r •
          ((n : ℝ) / (n + 1) * a.vertexDiameter)) := by
      apply Finsupp.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (a.dist_center_vertex (v i)) (x.weights_nonneg i)
    _ = (n : ℝ) / (n + 1) * a.vertexDiameter := by
      simp only [smul_eq_mul]
      rw [← Finsupp.sum_mul]
      simp

theorem exists_mem_support_of_mem_support_sum {α β : Type*} [Fintype β]
    (c : β → α →₀ ℤ) {a : α} (ha : a ∈ (∑ i, c i).support) :
    ∃ i, a ∈ (c i).support := by
  classical
  by_contra h
  simp only [not_exists, Finsupp.mem_support_iff, ne_eq, not_not] at h
  exact Finsupp.mem_support_iff.mp ha (by simp [h])

theorem affineCone_eq_mapDomain {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1)))
    (c : AffineChain m n) :
    affineCone m n b c = c.mapDomain (AffineSimplex.cone b) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.mapDomain_add, hf, hg]
  | single a z =>
      have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
      rw [hc]
      simp only [map_smul, affineCone_single, Finsupp.mapDomain_smul]
      simp

theorem mem_support_affineCone {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1)))
    (c : AffineChain m n) {a : AffineSimplex m (n + 1)}
    (ha : a ∈ (affineCone m n b c).support) :
    ∃ a' ∈ c.support, a = a'.cone b := by
  classical
  rw [affineCone_eq_mapDomain] at ha
  have ha' := Finsupp.mapDomain_support ha
  obtain ⟨a', ha'c, ha'eq⟩ := Finset.mem_image.mp ha'
  exact ⟨a', ha'c, ha'eq.symm⟩

/-- Every vertex of `b` lies in the affine image of `a`. Such a vertex may be
an interior point of that image; it need not equal one of the vertices of `a`. -/
def AffineSimplex.VerticesIn {m n k : ℕ} (a : AffineSimplex m n)
    (b : AffineSimplex m k) : Prop :=
  ∀ j, ∃ x : StdSimplex ℝ (Fin (n + 1)), b j = affineMapMk a x

theorem AffineSimplex.verticesIn_self {m n : ℕ} (a : AffineSimplex m n) :
    a.VerticesIn a := by
  intro j
  exact ⟨.single j, (affineMapMk_single a j).symm⟩

theorem AffineSimplex.VerticesIn.trans_face {m n k : ℕ}
    (a : AffineSimplex m (n + 1)) (i : Fin (n + 2)) {b : AffineSimplex m k}
    (h : (a.face i).VerticesIn b) : a.VerticesIn b := by
  intro j
  obtain ⟨x, hx⟩ := h j
  refine ⟨StdSimplex.map i.succAbove x, hx.trans ?_⟩
  simp only [affineMapMk_apply, iConvexComb_map]
  rfl

theorem AffineSimplex.VerticesIn.cone {m n k : ℕ}
    (a : AffineSimplex m n) {b : AffineSimplex m k} (h : a.VerticesIn b) :
    a.VerticesIn (b.cone a.center) := by
  intro j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · exact ⟨barycenter (K := ℝ) (M := Fin (n + 1)), rfl⟩
  · simpa [AffineSimplex.cone] using h j

theorem subdivideSimplex_support_verticesIn {m n : ℕ} (a : AffineSimplex m n)
    {b : AffineSimplex m n} (hb : b ∈ (subdivideSimplex n a).support) :
    a.VerticesIn b := by
  classical
  induction n with
  | zero =>
      have : b = a := by simpa using hb
      subst b
      exact a.verticesIn_self
  | succ n ih =>
      rw [subdivideSimplex] at hb
      obtain ⟨b', hb', rfl⟩ := mem_support_affineCone a.center _ hb
      obtain ⟨i, hi⟩ := exists_mem_support_of_mem_support_sum _ hb'
      have hi' : b' ∈ (subdivideSimplex n (a.face i)).support :=
        Finsupp.support_smul hi
      exact (ih (a.face i) hi' |>.trans_face a i).cone a

theorem homotopySimplex_support_verticesIn {m n : ℕ} (a : AffineSimplex m n)
    {b : AffineSimplex m (n + 1)} (hb : b ∈ (homotopySimplex n a).support) :
    a.VerticesIn b := by
  classical
  induction n with
  | zero => simp [homotopySimplex] at hb
  | succ n ih =>
      rw [homotopySimplex] at hb
      obtain ⟨b', hb', rfl⟩ := mem_support_affineCone a.center _ hb
      rcases Finset.mem_union.mp (Finsupp.support_sub hb') with hab | hsum
      · rcases Finset.mem_union.mp (Finsupp.support_sub hab) with ha | hsub
        · have : b' = a := by simpa using ha
          subst b'
          exact a.verticesIn_self.cone a
        · exact (subdivideSimplex_support_verticesIn a hsub).cone a
      · obtain ⟨i, hi⟩ := exists_mem_support_of_mem_support_sum _ hsum
        have hi' : b' ∈ (homotopySimplex n (a.face i)).support :=
          Finsupp.support_smul hi
        exact (ih (a.face i) hi' |>.trans_face a i).cone a

/-- Choose preimages of the vertices of `b` in the domain of `a`, using
`a.VerticesIn b`. Composing this simplex with `a` recovers `b`; no uniqueness
or invertibility of the chosen parametrization is asserted. -/
noncomputable def AffineSimplex.reparametrization {m n k : ℕ}
    (a : AffineSimplex m n) {b : AffineSimplex m k} (h : a.VerticesIn b) :
    AffineSimplex n k :=
  fun j ↦ Classical.choose (h j)

theorem AffineSimplex.comp_reparametrization {m n k : ℕ}
    (a : AffineSimplex m n) {b : AffineSimplex m k} (h : a.VerticesIn b) :
    a.comp (a.reparametrization h) = b := by
  funext j
  exact (Classical.choose_spec (h j)).symm

theorem AffineSimplex.range_affineContinuousMap_subset {m n k : ℕ}
    (a : AffineSimplex m n) {b : AffineSimplex m k} (h : a.VerticesIn b) :
    Set.range (affineContinuousMap b) ⊆ Set.range (affineContinuousMap a) := by
  rw [← a.comp_reparametrization h]
  rintro _ ⟨x, rfl⟩
  refine ⟨affineContinuousMap (a.reparametrization h) x, ?_⟩
  change affineMapMk a (affineMapMk (a.reparametrization h) x) =
    affineMapMk (a.comp (a.reparametrization h)) x
  have hcomp := StdSimplex.comp_affineMapMk (affineMapMk a) (a.reparametrization h)
  exact DFunLike.congr_fun hcomp x

theorem AffineSimplex.vertexDiameter_face_le {m n : ℕ}
    (a : AffineSimplex m (n + 1)) (i : Fin (n + 2)) :
    (a.face i).vertexDiameter ≤ a.vertexDiameter := by
  apply Metric.diam_mono _ (Set.finite_range a |>.isBounded)
  rintro _ ⟨j, rfl⟩
  exact ⟨i.succAbove j, rfl⟩

theorem AffineSimplex.vertexDiameter_cone_le {m n : ℕ}
    (a : AffineSimplex m (n + 1)) (i : Fin (n + 2)) (b : AffineSimplex m n)
    (hvertices : (a.face i).VerticesIn b)
    (hdiam : b.vertexDiameter ≤
      ((n + 1 : ℕ) : ℝ) / (n + 2) * a.vertexDiameter) :
    (b.cone a.center).vertexDiameter ≤
      ((n + 1 : ℕ) : ℝ) / (n + 2) * a.vertexDiameter := by
  have hnonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) / (n + 2) * a.vertexDiameter :=
    mul_nonneg (div_nonneg (by positivity) (by positivity)) a.vertexDiameter_nonneg
  apply Metric.diam_le_of_forall_dist_le
  · exact hnonneg
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
  refine Fin.cases ?_ (fun p ↦ ?_) p
  · refine Fin.cases ?_ (fun q ↦ ?_) q
    · simpa [AffineSimplex.cone] using hnonneg
    · obtain ⟨x, hx⟩ := hvertices q
      rw [show (b.cone a.center) 0 = a.center by rfl,
        show (b.cone a.center) q.succ = b q by rfl, hx]
      rw [show a.face i = a ∘ i.succAbove by rfl]
      have h := a.dist_center_affineMapMk x i.succAbove
      push_cast at h ⊢
      ring_nf at h ⊢
      exact h
  · refine Fin.cases ?_ (fun q ↦ ?_) q
    · rw [dist_comm]
      obtain ⟨x, hx⟩ := hvertices p
      rw [show (b.cone a.center) 0 = a.center by rfl,
        show (b.cone a.center) p.succ = b p by rfl, hx]
      rw [show a.face i = a ∘ i.succAbove by rfl]
      have h := a.dist_center_affineMapMk x i.succAbove
      push_cast at h ⊢
      ring_nf at h ⊢
      exact h
    · exact (b.dist_le_vertexDiameter p q).trans hdiam

theorem subdivideSimplex_support_vertexDiameter_le {m n : ℕ}
    (a : AffineSimplex m n) {b : AffineSimplex m n}
    (hb : b ∈ (subdivideSimplex n a).support) :
    b.vertexDiameter ≤ (n : ℝ) / (n + 1) * a.vertexDiameter := by
  classical
  induction n with
  | zero =>
      have hab : b = a := by simpa using hb
      subst b
      have hrange : (Set.range a).Subsingleton := by
        rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
        fin_cases i
        fin_cases j
        rfl
      rw [AffineSimplex.vertexDiameter, Metric.diam_subsingleton hrange]
      simp
  | succ n ih =>
      rw [subdivideSimplex] at hb
      obtain ⟨b', hb', rfl⟩ := mem_support_affineCone a.center _ hb
      obtain ⟨i, hi⟩ := exists_mem_support_of_mem_support_sum _ hb'
      have hi' : b' ∈ (subdivideSimplex n (a.face i)).support :=
        Finsupp.support_smul hi
      have hratio : (n : ℝ) / (n + 1) ≤ (n + 1 : ℝ) / (n + 2) := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < n + 1) (by positivity : (0 : ℝ) < n + 2)]
        nlinarith
      have hdiam : b'.vertexDiameter ≤
          (n + 1 : ℝ) / (n + 2) * a.vertexDiameter := calc
        b'.vertexDiameter ≤ (n : ℝ) / (n + 1) * (a.face i).vertexDiameter :=
          ih (a.face i) hi'
        _ ≤ (n : ℝ) / (n + 1) * a.vertexDiameter :=
          mul_le_mul_of_nonneg_left (a.vertexDiameter_face_le i) (by positivity)
        _ ≤ (n + 1 : ℝ) / (n + 2) * a.vertexDiameter :=
          mul_le_mul_of_nonneg_right hratio a.vertexDiameter_nonneg
      have hcone := a.vertexDiameter_cone_le i b'
        (subdivideSimplex_support_verticesIn (a.face i) hi') (by
          simpa only [Nat.cast_add, Nat.cast_one] using hdiam)
      push_cast at hcone ⊢
      ring_nf at hcone ⊢
      exact hcone

theorem mem_support_affineSubdivision {m n : ℕ} (c : AffineChain m n)
    {b : AffineSimplex m n} (hb : b ∈ (affineSubdivision m n c).support) :
    ∃ a ∈ c.support, b ∈ (subdivideSimplex n a).support := by
  classical
  let terms : c.support → AffineChain m n :=
    fun a ↦ c a • subdivideSimplex n a
  have heq : affineSubdivision m n c = ∑ a : c.support, terms a := by
    simp only [terms, affineSubdivision, Finsupp.lift]
    exact (Finset.sum_attach c.support
      (fun a ↦ c a • subdivideSimplex n a)).symm
  rw [heq] at hb
  obtain ⟨a, ha⟩ := exists_mem_support_of_mem_support_sum terms hb
  exact ⟨a, a.property, Finsupp.support_smul ha⟩

theorem affineSubdivision_iterate_support_vertexDiameter_le {m n N : ℕ}
    (c : AffineChain m n) (D : ℝ)
    (hc : ∀ a ∈ c.support, a.vertexDiameter ≤ D)
    {b : AffineSimplex m n}
    (hb : b ∈ ((affineSubdivision m n : AffineChain m n → AffineChain m n)^[N] c).support) :
    b.vertexDiameter ≤ ((n : ℝ) / (n + 1)) ^ N * D := by
  induction N generalizing b with
  | zero =>
      simpa using hc b hb
  | succ N ih =>
      rw [Function.iterate_succ_apply'] at hb
      obtain ⟨a, ha, hba⟩ := mem_support_affineSubdivision _ hb
      calc
        b.vertexDiameter ≤ (n : ℝ) / (n + 1) * a.vertexDiameter :=
          subdivideSimplex_support_vertexDiameter_le a hba
        _ ≤ (n : ℝ) / (n + 1) * (((n : ℝ) / (n + 1)) ^ N * D) :=
          mul_le_mul_of_nonneg_left (ih ha) (by positivity)
        _ = ((n : ℝ) / (n + 1)) ^ (N + 1) * D := by ring

theorem AffineSimplex.dist_center_affineMapMk_self {m n : ℕ}
    (a : AffineSimplex m n) (x : StdSimplex ℝ (Fin (n + 1))) :
    dist a.center (affineMapMk a x) ≤
      (n : ℝ) / (n + 1) * a.vertexDiameter := by
  simpa only [Function.comp_id] using a.dist_center_affineMapMk x id

theorem AffineSimplex.diam_range_affineContinuousMap_le {m n : ℕ}
    (a : AffineSimplex m n) :
    Metric.diam (Set.range (affineContinuousMap a)) ≤ 2 * a.vertexDiameter := by
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg (by norm_num) a.vertexDiameter_nonneg)
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hratio : (n : ℝ) / (n + 1) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < n + 1)]
    norm_num
  have hx := a.dist_center_affineMapMk_self x
  have hy := a.dist_center_affineMapMk_self y
  calc
    dist (affineContinuousMap a x) (affineContinuousMap a y) ≤
        dist (affineContinuousMap a x) a.center +
          dist a.center (affineContinuousMap a y) := dist_triangle _ _ _
    _ ≤ ((n : ℝ) / (n + 1) * a.vertexDiameter) +
          ((n : ℝ) / (n + 1) * a.vertexDiameter) :=
      add_le_add (by simpa [dist_comm, affineContinuousMap] using hx)
        (by simpa [affineContinuousMap] using hy)
    _ ≤ a.vertexDiameter + a.vertexDiameter :=
      add_le_add (mul_le_of_le_one_left a.vertexDiameter_nonneg hratio)
        (mul_le_of_le_one_left a.vertexDiameter_nonneg hratio)
    _ = 2 * a.vertexDiameter := by ring

/-- The standard affine simplex, with its `i`th vertex the `i`th unit weight vector. -/
def AffineSimplex.standard (n : ℕ) : AffineSimplex n n :=
  fun i ↦ .single i

theorem exists_affineSubdivision_iterate_diam_lt {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ {b : AffineSimplex n n},
      b ∈ (((affineSubdivision n n : AffineChain n n → AffineChain n n)^[N])
        (Finsupp.single (AffineSimplex.standard n) 1)).support →
      Metric.diam (Set.range (affineContinuousMap b)) < ε := by
  let q : ℝ := (n : ℝ) / (n + 1)
  let D := (AffineSimplex.standard n).vertexDiameter
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one (by positivity : (0 : ℝ) < n + 1)]
    norm_num
  have ht : Filter.Tendsto (fun N : ℕ ↦ q ^ N * (2 * D)) Filter.atTop (nhds 0) :=
    by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (2 * D)
  have hev : ∀ᶠ N : ℕ in Filter.atTop, q ^ N * (2 * D) < ε :=
    (tendsto_order.1 ht).2 ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun {b} hb ↦ ?_⟩
  have hbv : b.vertexDiameter ≤ q ^ N * D := by
    apply affineSubdivision_iterate_support_vertexDiameter_le
      (Finsupp.single (AffineSimplex.standard n) 1) D
    · intro a ha
      have : a = AffineSimplex.standard n := by simpa using ha
      subst a
      exact le_rfl
    · exact hb
  calc
    Metric.diam (Set.range (affineContinuousMap b)) ≤ 2 * b.vertexDiameter :=
      b.diam_range_affineContinuousMap_le
    _ ≤ 2 * (q ^ N * D) := mul_le_mul_of_nonneg_left hbv (by norm_num)
    _ = q ^ N * (2 * D) := by ring
    _ < ε := hN N le_rfl

theorem exists_affineSubdivision_iterate_cover_small
    {X : Type*} [TopologicalSpace X] {ι : Type*} (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) {n : ℕ}
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ N, ∀ {b : AffineSimplex n n},
      b ∈ (((affineSubdivision n n : AffineChain n n → AffineChain n n)^[N])
        (Finsupp.single (AffineSimplex.standard n) 1)).support →
      ∃ i, Set.range (σ.comp (affineContinuousMap b)) ⊆ U i := by
  rcases n.eq_zero_or_pos with rfl | hn
  · refine ⟨0, fun {b} hb ↦ ?_⟩
    obtain ⟨i, hi⟩ := hU.exists_mem (σ (barycenter (K := ℝ) (M := Fin 1)))
    refine ⟨i, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hx : affineContinuousMap b x = barycenter (K := ℝ) (M := Fin 1) :=
      Subsingleton.elim _ _
    change σ (affineContinuousMap b x) ∈ U i
    rw [hx]
    exact hi
  · obtain ⟨ε, hε, hLeb⟩ := CompactSpace.lebesgue_number_lemma
      (fun i ↦ σ ⁻¹' (U i : Set X))
      (fun i ↦ (U i).isOpen.preimage σ.continuous) (by
        rw [← Set.preimage_iUnion, hU.iSup_set_eq_univ]
        simp)
    obtain ⟨N, hN⟩ := exists_affineSubdivision_iterate_diam_lt hn hε
    refine ⟨N, fun {b} hb ↦ ?_⟩
    obtain ⟨i, hi⟩ := hLeb (Set.range (affineContinuousMap b))
      (Set.range_nonempty (affineContinuousMap b))
      (hN hb).le
    refine ⟨i, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hi ⟨x, rfl⟩

end Convexity.StdSimplex

namespace AlgebraicTopology

open Convexity Convexity.StdSimplex

universe u

/-- Finite integer linear combinations of singular `n`-simplices in `X`,
represented as finitely supported functions on its native singular simplicial set. -/
abbrev SingularChainFinsupp (X : TopCat.{u}) (n : ℕ) :=
  (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ

/-- Postcomposition of finitely supported singular chains by a continuous map. -/
def singularFinsuppMap {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    SingularChainFinsupp X n →ₗ[ℤ] SingularChainFinsupp Y n :=
  Finsupp.lmapDomain ℤ ℤ ((TopCat.toSSet.map f).app _)

@[simp]
theorem singularFinsuppMap_single {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularFinsuppMap f n (Finsupp.single x 1) =
      Finsupp.single ((TopCat.toSSet.map f).app _ x) 1 := by
  simp [singularFinsuppMap]

/-- Turn an affine `k`-simplex in the standard `n`-simplex into a singular
`k`-simplex in `X`. Despite the name, this precomposes the singular simplex `x`
with the continuous affine map determined by `a`. -/
def affinePostcompose {X : TopCat.{u}} {n k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (a : AffineSimplex n k) :
    (TopCat.toSSet.obj X) _⦋k⦌ :=
  (X.toSSetObjEquiv _).symm
    ((X.toSSetObjEquiv _ x).comp (affineContinuousMap a))

/-- Map an affine chain in the domain of a singular simplex `x` to a singular
chain in `X`, adding coefficients whenever the resulting singular simplices coincide. -/
def realizeAffineChain {X : TopCat.{u}} {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (k : ℕ) :
    AffineChain n k →ₗ[ℤ] SingularChainFinsupp X k :=
  Finsupp.lmapDomain ℤ ℤ (affinePostcompose x)

theorem mem_support_realizeAffineChain {X : TopCat.{u}} {n k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (c : AffineChain n k)
    {y : (TopCat.toSSet.obj X) _⦋k⦌}
    (hy : y ∈ (realizeAffineChain x k c).support) :
    ∃ a ∈ c.support, y = affinePostcompose x a := by
  classical
  change y ∈ (Finsupp.mapDomain (affinePostcompose x) c).support at hy
  have hy' := Finsupp.mapDomain_support hy
  obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp hy'
  exact ⟨a, ha, hay.symm⟩

theorem affinePostcompose_range_subset {X : TopCat.{u}} {n k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (a : AffineSimplex n k) :
    Set.range (X.toSSetObjEquiv _ (affinePostcompose x a)) ⊆
      Set.range (X.toSSetObjEquiv _ x) := by
  rintro _ ⟨z, rfl⟩
  refine ⟨affineContinuousMap a z, ?_⟩
  simp only [affinePostcompose, Equiv.apply_symm_apply, ContinuousMap.coe_comp,
    Function.comp_apply]

@[simp]
theorem realizeAffineChain_single {X : TopCat.{u}} {n k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (a : AffineSimplex n k) :
    realizeAffineChain x k (Finsupp.single a 1) =
      Finsupp.single (affinePostcompose x a) 1 := by
  simp [realizeAffineChain]

theorem affinePostcompose_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) {n k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (a : AffineSimplex n k) :
    (TopCat.toSSet.map f).app _ (affinePostcompose x a) =
      affinePostcompose ((TopCat.toSSet.map f).app _ x) a := by
  rfl

theorem singularFinsuppMap_realizeAffineChain {X Y : TopCat.{u}} (f : X ⟶ Y)
    {n k : ℕ} (x : (TopCat.toSSet.obj X) _⦋n⦌) (c : AffineChain n k) :
    singularFinsuppMap f k (realizeAffineChain x k c) =
      realizeAffineChain ((TopCat.toSSet.map f).app _ x) k c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single a z =>
      have hz : Finsupp.single a z = z • Finsupp.single a 1 := by simp
      rw [hz]
      simp only [map_smul, realizeAffineChain_single, singularFinsuppMap_single]
      rw [affinePostcompose_naturality]

theorem affinePostcompose_standard {X : TopCat.{u}} {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    affinePostcompose x (AffineSimplex.standard n) = x := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  simp only [affinePostcompose, Equiv.apply_symm_apply, ContinuousMap.coe_comp,
    Function.comp_apply]
  congr 1
  change iConvexComb z (fun i : Fin (n + 1) ↦ StdSimplex.single i) = z
  exact Convexity.StdSimplex.iConvexComb_single z

theorem affinePostcompose_face {X : TopCat.{u}} {n k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (a : AffineSimplex n (k + 1))
    (i : Fin (k + 2)) :
    affinePostcompose x (a.face i) =
      (TopCat.toSSet.obj X).δ i (affinePostcompose x a) := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  simp only [affinePostcompose, Equiv.apply_symm_apply, ContinuousMap.coe_comp,
    Function.comp_apply]
  change (X.toSSetObjEquiv _ x) (affineMapMk (a.face i) z) =
    (X.toSSetObjEquiv _ x) (affineMapMk a (StdSimplex.map i.succAbove z))
  congr 1
  simp only [affineMapMk_apply, iConvexComb_map]
  rfl

theorem affinePostcompose_comp {X : TopCat.{u}} {m n k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋m⦌) (a : AffineSimplex m n)
    (b : AffineSimplex n k) :
    affinePostcompose x (a.comp b) = affinePostcompose (affinePostcompose x a) b := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  simp only [affinePostcompose, Equiv.apply_symm_apply, ContinuousMap.coe_comp,
    Function.comp_apply]
  congr 1
  change affineMapMk (a.comp b) z = affineMapMk a (affineMapMk b z)
  have h := StdSimplex.comp_affineMapMk (affineMapMk a) b
  exact DFunLike.congr_fun h.symm z

theorem realizeAffineChain_mapAffineChain {X : TopCat.{u}} {m n k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋m⦌) (a : AffineSimplex m n)
    (c : AffineChain n k) :
    realizeAffineChain x k (mapAffineChain a k c) =
      realizeAffineChain (affinePostcompose x a) k c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single b z =>
      have hc : Finsupp.single b z = z • Finsupp.single b 1 := by simp
      rw [hc]
      simp only [map_smul, mapAffineChain_single, realizeAffineChain_single]
      rw [affinePostcompose_comp]

/-- The integer-linear singular boundary in finitely supported coordinates,
with coefficient `(-1)^i` on the `i`th face of each simplex. -/
def singularFinsuppBoundary (X : TopCat.{u}) (n : ℕ) :
    SingularChainFinsupp X (n + 1) →ₗ[ℤ] SingularChainFinsupp X n :=
  Finsupp.lift (SingularChainFinsupp X n) ℤ ((TopCat.toSSet.obj X) _⦋n + 1⦌)
    (fun x ↦ ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      Finsupp.single ((TopCat.toSSet.obj X).δ i x) 1)

@[simp]
theorem singularFinsuppBoundary_single {X : TopCat.{u}} {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    singularFinsuppBoundary X n (Finsupp.single x 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Finsupp.single ((TopCat.toSSet.obj X).δ i x) 1 := by
  simp [singularFinsuppBoundary]

theorem singularFinsuppBoundary_realizeAffineChain {X : TopCat.{u}} {n k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (c : AffineChain n (k + 1)) :
    singularFinsuppBoundary X k (realizeAffineChain x (k + 1) c) =
      realizeAffineChain x k (affineBoundary n k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single a z =>
      have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
      rw [hc]
      simp only [map_smul, realizeAffineChain_single, singularFinsuppBoundary_single,
        affineBoundary_single, affineBoundaryGenerator, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [affinePostcompose_face]

theorem AffineSimplex.comp_standard {m n : ℕ} (a : AffineSimplex m n) :
    a.comp (AffineSimplex.standard n) = a := by
  funext i
  exact affineMapMk_single a i

theorem realize_subdivide_face_standard {X : TopCat.{u}} {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 2)) :
    realizeAffineChain x n
        (subdivideSimplex n ((AffineSimplex.standard (n + 1)).face i)) =
      realizeAffineChain ((TopCat.toSSet.obj X).δ i x) n
        (subdivideSimplex n (AffineSimplex.standard n)) := by
  let f := (AffineSimplex.standard (n + 1)).face i
  have hsub := mapAffineChain_subdivideSimplex f (AffineSimplex.standard n)
  rw [AffineSimplex.comp_standard f] at hsub
  rw [← hsub]
  rw [realizeAffineChain_mapAffineChain]
  congr 2
  dsimp [f]
  rw [affinePostcompose_face, affinePostcompose_standard]

theorem realize_homotopy_face_standard {X : TopCat.{u}} {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 2)) :
    realizeAffineChain x (n + 1)
        (homotopySimplex n ((AffineSimplex.standard (n + 1)).face i)) =
      realizeAffineChain ((TopCat.toSSet.obj X).δ i x) (n + 1)
        (homotopySimplex n (AffineSimplex.standard n)) := by
  let f := (AffineSimplex.standard (n + 1)).face i
  have hhom := mapAffineChain_homotopySimplex f (AffineSimplex.standard n)
  rw [AffineSimplex.comp_standard f] at hhom
  rw [← hhom, realizeAffineChain_mapAffineChain]
  congr 2
  dsimp [f]
  rw [affinePostcompose_face, affinePostcompose_standard]

/-- Subdivide each singular simplex by realizing the signed barycentric
subdivision of its standard domain, then extend integer-linearly to chains. -/
def singularSubdivision (X : TopCat.{u}) (n : ℕ) :
    SingularChainFinsupp X n →ₗ[ℤ] SingularChainFinsupp X n :=
  Finsupp.lift (SingularChainFinsupp X n) ℤ ((TopCat.toSSet.obj X) _⦋n⦌)
    (fun x ↦ realizeAffineChain x n
      (subdivideSimplex n (AffineSimplex.standard n)))

/-- Apply singular subdivision `N` times. The zeroth iterate is the identity
linear map, and each successor composes the preceding iterate with subdivision. -/
noncomputable def singularSubdivisionIterate (X : TopCat.{u}) (n N : ℕ) :
    SingularChainFinsupp X n →ₗ[ℤ] SingularChainFinsupp X n :=
  match N with
  | 0 => LinearMap.id
  | Nat.succ N => (singularSubdivisionIterate X n N).comp (singularSubdivision X n)

@[simp]
theorem singularSubdivisionIterate_zero (X : TopCat.{u}) (n : ℕ) :
    singularSubdivisionIterate X n 0 = LinearMap.id := rfl

theorem singularSubdivisionIterate_succ (X : TopCat.{u}) (n N : ℕ) :
    singularSubdivisionIterate X n (N + 1) =
      (singularSubdivisionIterate X n N).comp (singularSubdivision X n) := rfl

theorem singularSubdivisionIterate_apply (X : TopCat.{u}) (n N : ℕ)
    (c : SingularChainFinsupp X n) :
    singularSubdivisionIterate X n N c =
      ((singularSubdivision X n : SingularChainFinsupp X n →
        SingularChainFinsupp X n)^[N]) c := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih =>
      rw [singularSubdivisionIterate_succ]
      change singularSubdivisionIterate X n N (singularSubdivision X n c) = _
      rw [ih, Function.iterate_succ_apply]

@[simp]
theorem singularSubdivision_single {X : TopCat.{u}} {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularSubdivision X n (Finsupp.single x 1) =
      realizeAffineChain x n
        (subdivideSimplex n (AffineSimplex.standard n)) := by
  simp [singularSubdivision]

/-- In degree zero barycentric subdivision is the identity. -/
theorem singularSubdivision_degree_zero (X : TopCat.{u}) (c : SingularChainFinsupp X 0) :
    singularSubdivision X 0 c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x z =>
      have hz : Finsupp.single x z = z • Finsupp.single x 1 := by simp
      rw [hz]
      simp only [map_smul]
      congr 1
      rw [singularSubdivision_single, subdivideSimplex_zero,
        realizeAffineChain_single, affinePostcompose_standard]

/-- Barycentric subdivision commutes with postcomposition of singular chains. -/
theorem singularSubdivision_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (c : SingularChainFinsupp X n) :
    singularFinsuppMap f n (singularSubdivision X n c) =
      singularSubdivision Y n (singularFinsuppMap f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x z =>
      have hz : Finsupp.single x z = z • Finsupp.single x 1 := by simp
      rw [hz]
      simp only [map_smul, singularSubdivision_single, singularFinsuppMap_single]
      rw [singularFinsuppMap_realizeAffineChain]

theorem mem_support_singularSubdivision {X : TopCat.{u}} {n : ℕ}
    (c : SingularChainFinsupp X n) {y : (TopCat.toSSet.obj X) _⦋n⦌}
    (hy : y ∈ (singularSubdivision X n c).support) :
    ∃ x ∈ c.support,
      Set.range (X.toSSetObjEquiv _ y) ⊆ Set.range (X.toSSetObjEquiv _ x) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp at hy
  | @single_add x z c hx hz ih =>
      rw [map_add] at hy
      rcases Finset.mem_union.mp (Finsupp.support_add hy) with hsingle | hc
      · have hsingle' : y ∈ (singularSubdivision X n
            (Finsupp.single x z)).support := hsingle
        have hzx : Finsupp.single x z = z • Finsupp.single x 1 := by simp
        rw [hzx, map_smul, singularSubdivision_single] at hsingle'
        have hrealize : y ∈ (realizeAffineChain x n
            (subdivideSimplex n (AffineSimplex.standard n))).support :=
          Finsupp.support_smul hsingle'
        obtain ⟨a, ha, rfl⟩ := mem_support_realizeAffineChain x _ hrealize
        have hcx : c x = 0 := by
          simpa only [Finsupp.mem_support_iff, not_not] using hx
        refine ⟨x, Finsupp.mem_support_iff.mpr ?_, affinePostcompose_range_subset x a⟩
        simpa [hcx] using hz
      · obtain ⟨x', hx'c, hrange⟩ := ih hc
        refine ⟨x', Finsupp.mem_support_iff.mpr ?_, hrange⟩
        have hne : x ≠ x' := by
          intro h
          apply hx
          simpa [h] using hx'c
        simpa [hne] using Finsupp.mem_support_iff.mp hx'c

theorem singularSubdivision_realizeAffineChain {X : TopCat.{u}} {m n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋m⦌) (c : AffineChain m n) :
    singularSubdivision X n (realizeAffineChain x n c) =
      realizeAffineChain x n (affineSubdivision m n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single a z =>
      have hc : Finsupp.single a z = z • Finsupp.single a 1 := by simp
      rw [hc]
      simp only [map_smul, realizeAffineChain_single, singularSubdivision_single,
        affineSubdivision_single]
      congr 1
      have hsub := mapAffineChain_subdivideSimplex a (AffineSimplex.standard n)
      rw [AffineSimplex.comp_standard a] at hsub
      rw [← hsub, realizeAffineChain_mapAffineChain]

theorem singularSubdivision_iterate_single {X : TopCat.{u}} {n N : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    ((singularSubdivision X n : SingularChainFinsupp X n → SingularChainFinsupp X n)^[N])
        (Finsupp.single x 1) =
      realizeAffineChain x n
        (((affineSubdivision n n : AffineChain n n → AffineChain n n)^[N])
          (Finsupp.single (AffineSimplex.standard n) 1)) := by
  induction N with
  | zero => simp [affinePostcompose_standard]
  | succ N ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact singularSubdivision_realizeAffineChain x _

theorem exists_singularSubdivision_iterate_cover_small
    {X : TopCat.{u}} {ι : Type*} (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    ∃ N, ∀ {y : (TopCat.toSSet.obj X) _⦋n⦌},
      y ∈ (((singularSubdivision X n : SingularChainFinsupp X n →
        SingularChainFinsupp X n)^[N]) (Finsupp.single x 1)).support →
      ∃ i, Set.range (X.toSSetObjEquiv _ y) ⊆ U i := by
  obtain ⟨N, hN⟩ := exists_affineSubdivision_iterate_cover_small U hU
    (X.toSSetObjEquiv _ x)
  refine ⟨N, fun {y} hy ↦ ?_⟩
  rw [singularSubdivision_iterate_single] at hy
  obtain ⟨b, hb, rfl⟩ := mem_support_realizeAffineChain x _ hy
  obtain ⟨i, hi⟩ := hN hb
  exact ⟨i, hi⟩

/-- The range of a singular simplex lies in one member of the family `U`.
This predicate itself does not assume that `U` covers the whole space. -/
def IsCoverSmall {X : TopCat.{u}} {ι : Type*}
    (U : ι → TopologicalSpace.Opens X) {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) : Prop :=
  ∃ i, Set.range (X.toSSetObjEquiv _ x) ⊆ U i

theorem isCoverSmall_of_mem_singularSubdivision
    {X : TopCat.{u}} {ι : Type*} (U : ι → TopologicalSpace.Opens X) {n : ℕ}
    {c : SingularChainFinsupp X n}
    (hc : ∀ x ∈ c.support, IsCoverSmall U x)
    {y : (TopCat.toSSet.obj X) _⦋n⦌}
    (hy : y ∈ (singularSubdivision X n c).support) :
    IsCoverSmall U y := by
  obtain ⟨x, hx, hyx⟩ := mem_support_singularSubdivision c hy
  obtain ⟨i, hxi⟩ := hc x hx
  exact ⟨i, hyx.trans hxi⟩

theorem isCoverSmall_of_mem_singularSubdivisionIterate
    {X : TopCat.{u}} {ι : Type*} (U : ι → TopologicalSpace.Opens X) {n N : ℕ}
    {c : SingularChainFinsupp X n}
    (hc : ∀ x ∈ c.support, IsCoverSmall U x)
    {y : (TopCat.toSSet.obj X) _⦋n⦌}
    (hy : y ∈ (singularSubdivisionIterate X n N c).support) :
    IsCoverSmall U y := by
  induction N generalizing c y with
  | zero => exact hc y hy
  | succ N ih =>
      rw [singularSubdivisionIterate_succ] at hy
      exact ih (fun x hx ↦ isCoverSmall_of_mem_singularSubdivision U hc hx) hy

theorem isCoverSmall_of_mem_singularSubdivisionIterate_of_le
    {X : TopCat.{u}} {ι : Type*} (U : ι → TopologicalSpace.Opens X) {n N M : ℕ}
    (hNM : N ≤ M) {c : SingularChainFinsupp X n}
    (hN : ∀ x ∈ (singularSubdivisionIterate X n N c).support,
      IsCoverSmall U x)
    {y : (TopCat.toSSet.obj X) _⦋n⦌}
    (hy : y ∈ (singularSubdivisionIterate X n M c).support) :
    IsCoverSmall U y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hNM
  rw [singularSubdivisionIterate_apply, Function.iterate_add_apply,
    ← singularSubdivisionIterate_apply, ← singularSubdivisionIterate_apply] at hy
  exact isCoverSmall_of_mem_singularSubdivisionIterate U hN hy

theorem exists_singularSubdivisionIterate_chain_cover_small
    {X : TopCat.{u}} {ι : Type*} (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) {n : ℕ}
    (c : SingularChainFinsupp X n) :
    ∃ N, ∀ {y : (TopCat.toSSet.obj X) _⦋n⦌},
      y ∈ (singularSubdivisionIterate X n N c).support → IsCoverSmall U y := by
  classical
  let exponent : c.support → ℕ := fun x ↦
    Classical.choose (exists_singularSubdivision_iterate_cover_small U hU
      (x : (TopCat.toSSet.obj X) _⦋n⦌))
  let N : ℕ := ∑ x : c.support, exponent x
  have hexponent (x : c.support) :
      ∀ {y : (TopCat.toSSet.obj X) _⦋n⦌},
        y ∈ (singularSubdivisionIterate X n (exponent x)
          (Finsupp.single (x : (TopCat.toSSet.obj X) _⦋n⦌) 1)).support →
        IsCoverSmall U y := by
    intro y hy
    rw [singularSubdivisionIterate_apply] at hy
    exact Classical.choose_spec
      (exists_singularSubdivision_iterate_cover_small U hU
        (x : (TopCat.toSSet.obj X) _⦋n⦌)) hy
  have hexponent_le (x : c.support) : exponent x ≤ N := by
    apply Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    exact Finset.mem_univ x
  have hgenerator (x : c.support) :
      ∀ {y : (TopCat.toSSet.obj X) _⦋n⦌},
        y ∈ (singularSubdivisionIterate X n N
          (Finsupp.single (x : (TopCat.toSSet.obj X) _⦋n⦌) 1)).support →
        IsCoverSmall U y := by
    intro y hy
    exact isCoverSmall_of_mem_singularSubdivisionIterate_of_le U
      (hexponent_le x) (fun y hy ↦ hexponent x hy) hy
  let terms : c.support → SingularChainFinsupp X n := fun x ↦
    c x • singularSubdivisionIterate X n N
      (Finsupp.single (x : (TopCat.toSSet.obj X) _⦋n⦌) 1)
  have hcdecomp :
      c = ∑ x : c.support,
        Finsupp.single (x : (TopCat.toSSet.obj X) _⦋n⦌) (c x) := by
    symm
    rw [← Finset.sum_subtype c.support (fun _ ↦ Iff.rfl)
      (fun x ↦ Finsupp.single x (c x))]
    exact Finsupp.sum_single c
  have hiterate : singularSubdivisionIterate X n N c = ∑ x : c.support, terms x := by
    calc
      singularSubdivisionIterate X n N c =
          singularSubdivisionIterate X n N
            (∑ x : c.support,
              Finsupp.single (x : (TopCat.toSSet.obj X) _⦋n⦌) (c x)) :=
        congrArg (singularSubdivisionIterate X n N) hcdecomp
      _ = ∑ x : c.support,
          singularSubdivisionIterate X n N
            (Finsupp.single (x : (TopCat.toSSet.obj X) _⦋n⦌) (c x)) := by
        rw [map_sum]
      _ = ∑ x : c.support, terms x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxsingle :
            Finsupp.single (x : (TopCat.toSSet.obj X) _⦋n⦌) (c x) =
              c x • Finsupp.single (x : (TopCat.toSSet.obj X) _⦋n⦌) 1 := by simp
        rw [hxsingle, map_smul]
  refine ⟨N, fun {y} hy ↦ ?_⟩
  rw [hiterate] at hy
  obtain ⟨x, hx⟩ := exists_mem_support_of_mem_support_sum terms hy
  apply hgenerator x
  exact Finsupp.support_smul hx

/-- Realize the affine subdivision homotopy on each singular simplex and extend
integer-linearly. It raises degree by one and has sign `∂H + H∂ = id - Sd`. -/
def singularHomotopy (X : TopCat.{u}) (n : ℕ) :
    SingularChainFinsupp X n →ₗ[ℤ] SingularChainFinsupp X (n + 1) :=
  Finsupp.lift (SingularChainFinsupp X (n + 1)) ℤ
    ((TopCat.toSSet.obj X) _⦋n⦌)
    (fun x ↦ realizeAffineChain x (n + 1)
      (homotopySimplex n (AffineSimplex.standard n)))

@[simp]
theorem singularHomotopy_single {X : TopCat.{u}} {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularHomotopy X n (Finsupp.single x 1) =
      realizeAffineChain x (n + 1)
        (homotopySimplex n (AffineSimplex.standard n)) := by
  simp [singularHomotopy]

/-- The subdivision prism homotopy commutes with postcomposition. -/
theorem singularHomotopy_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (c : SingularChainFinsupp X n) :
    singularFinsuppMap f (n + 1) (singularHomotopy X n c) =
      singularHomotopy Y n (singularFinsuppMap f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x z =>
      have hz : Finsupp.single x z = z • Finsupp.single x 1 := by simp
      rw [hz]
      simp only [map_smul, singularHomotopy_single, singularFinsuppMap_single]
      rw [singularFinsuppMap_realizeAffineChain]

theorem mem_support_singularHomotopy {X : TopCat.{u}} {n : ℕ}
    (c : SingularChainFinsupp X n) {y : (TopCat.toSSet.obj X) _⦋n + 1⦌}
    (hy : y ∈ (singularHomotopy X n c).support) :
    ∃ x ∈ c.support,
      Set.range (X.toSSetObjEquiv _ y) ⊆ Set.range (X.toSSetObjEquiv _ x) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp at hy
  | @single_add x z c hx hz ih =>
      rw [map_add] at hy
      rcases Finset.mem_union.mp (Finsupp.support_add hy) with hsingle | hc
      · have hsingle' : y ∈ (singularHomotopy X n
            (Finsupp.single x z)).support := hsingle
        have hzx : Finsupp.single x z = z • Finsupp.single x 1 := by simp
        rw [hzx, map_smul, singularHomotopy_single] at hsingle'
        have hrealize : y ∈ (realizeAffineChain x (n + 1)
            (homotopySimplex n (AffineSimplex.standard n))).support :=
          Finsupp.support_smul hsingle'
        obtain ⟨a, ha, rfl⟩ := mem_support_realizeAffineChain x _ hrealize
        have hcx : c x = 0 := by
          simpa only [Finsupp.mem_support_iff, not_not] using hx
        refine ⟨x, Finsupp.mem_support_iff.mpr ?_, affinePostcompose_range_subset x a⟩
        simpa [hcx] using hz
      · obtain ⟨x', hx'c, hrange⟩ := ih hc
        refine ⟨x', Finsupp.mem_support_iff.mpr ?_, hrange⟩
        have hne : x ≠ x' := by
          intro h
          apply hx
          simpa [h] using hx'c
        simpa [hne] using Finsupp.mem_support_iff.mp hx'c

theorem singularSubdivision_boundary (X : TopCat.{u}) (n : ℕ)
    (c : SingularChainFinsupp X (n + 1)) :
    singularFinsuppBoundary X n (singularSubdivision X (n + 1) c) =
      singularSubdivision X n (singularFinsuppBoundary X n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x z =>
      have hc : Finsupp.single x z = z • Finsupp.single x 1 := by simp
      rw [hc]
      simp only [map_smul]
      congr 1
      rw [singularSubdivision_single, singularFinsuppBoundary_realizeAffineChain,
        singularFinsuppBoundary_single, map_sum]
      have h := affineSubdivision_boundary (n + 1) n
        (Finsupp.single (AffineSimplex.standard (n + 1)) 1)
      rw [affineSubdivision_single, affineBoundary_single] at h
      rw [h, affineBoundaryGenerator, map_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, map_smul, map_smul, singularSubdivision_single,
        affineSubdivision_single]
      congr 1
      exact realize_subdivide_face_standard x i

theorem singularSubdivisionIterate_boundary (X : TopCat.{u}) (n N : ℕ)
    (c : SingularChainFinsupp X (n + 1)) :
    singularFinsuppBoundary X n (singularSubdivisionIterate X (n + 1) N c) =
      singularSubdivisionIterate X n N (singularFinsuppBoundary X n c) := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih =>
      rw [singularSubdivisionIterate_succ, singularSubdivisionIterate_succ]
      change singularFinsuppBoundary X n
          (singularSubdivisionIterate X (n + 1) N
            (singularSubdivision X (n + 1) c)) =
        singularSubdivisionIterate X n N
          (singularSubdivision X n (singularFinsuppBoundary X n c))
      rw [ih, singularSubdivision_boundary]

theorem singularHomotopy_degree_zero (X : TopCat.{u}) (c : SingularChainFinsupp X 0) :
    singularFinsuppBoundary X 0 (singularHomotopy X 0 c) =
      c - singularSubdivision X 0 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; module
  | single x z =>
      have hc : Finsupp.single x z = z • Finsupp.single x 1 := by simp
      rw [hc]
      simp only [map_smul]
      rw [singularHomotopy_single, singularSubdivision_single]
      simp only [homotopySimplex_zero, map_zero, subdivideSimplex_zero,
        realizeAffineChain_single, affinePostcompose_standard, sub_self]
      simp

theorem singularHomotopy_boundary (X : TopCat.{u}) (n : ℕ)
    (c : SingularChainFinsupp X (n + 1)) :
    singularFinsuppBoundary X (n + 1) (singularHomotopy X (n + 1) c) +
        singularHomotopy X n (singularFinsuppBoundary X n c) =
      c - singularSubdivision X (n + 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add]
      rw [add_add_add_comm, hf, hg]
      abel
  | single x z =>
      have hc : Finsupp.single x z = z • Finsupp.single x 1 := by simp
      rw [hc]
      simp only [map_smul]
      rw [← smul_add, ← smul_sub]
      congr 1
      rw [singularHomotopy_single, singularFinsuppBoundary_realizeAffineChain,
        singularFinsuppBoundary_single, map_sum, singularSubdivision_single]
      have h := affineHomotopy_boundary (n + 1) n
        (Finsupp.single (AffineSimplex.standard (n + 1)) 1)
      rw [affineHomotopy_single, affineBoundary_single, affineSubdivision_single] at h
      have hsum :
          (∑ i : Fin (n + 2), singularHomotopy X n
            ((-1 : ℤ) ^ i.val •
              Finsupp.single ((TopCat.toSSet.obj X).δ i x) 1)) =
            realizeAffineChain x (n + 1)
              (affineHomotopy (n + 1) n
                (affineBoundaryGenerator (AffineSimplex.standard (n + 1)))) := by
        rw [affineBoundaryGenerator, map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, map_smul, singularHomotopy_single]
        rw [affineHomotopy_single, map_smul,
          realize_homotopy_face_standard]
      rw [hsum, ← map_add, h, map_sub, realizeAffineChain_single,
        affinePostcompose_standard]

/-- The telescoping homotopy from `N` subdivisions to the identity: it is zero
for `N = 0` and satisfies `H_(N+1) = H + H_N ∘ Sd`. This is a sum of
degree-raising maps, not function iteration of `singularHomotopy`. -/
noncomputable def singularHomotopyIterate (X : TopCat.{u}) (n N : ℕ) :
    SingularChainFinsupp X n →ₗ[ℤ] SingularChainFinsupp X (n + 1) :=
  match N with
  | 0 => 0
  | Nat.succ N => singularHomotopy X n +
      (singularHomotopyIterate X n N).comp (singularSubdivision X n)

@[simp]
theorem singularHomotopyIterate_zero (X : TopCat.{u}) (n : ℕ) :
    singularHomotopyIterate X n 0 = 0 := rfl

theorem singularHomotopyIterate_succ (X : TopCat.{u}) (n N : ℕ) :
    singularHomotopyIterate X n (N + 1) = singularHomotopy X n +
      (singularHomotopyIterate X n N).comp (singularSubdivision X n) := rfl

theorem singularHomotopyIterate_degree_zero (X : TopCat.{u}) (N : ℕ)
    (c : SingularChainFinsupp X 0) :
    singularFinsuppBoundary X 0 (singularHomotopyIterate X 0 N c) =
      c - singularSubdivisionIterate X 0 N c := by
  induction N generalizing c with
  | zero => simp
  | succ N ih =>
      rw [singularHomotopyIterate_succ, singularSubdivisionIterate_succ]
      simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
      rw [singularHomotopy_degree_zero, ih]
      abel

theorem singularHomotopyIterate_boundary (X : TopCat.{u}) (n N : ℕ)
    (c : SingularChainFinsupp X (n + 1)) :
    singularFinsuppBoundary X (n + 1) (singularHomotopyIterate X (n + 1) N c) +
        singularHomotopyIterate X n N (singularFinsuppBoundary X n c) =
      c - singularSubdivisionIterate X (n + 1) N c := by
  induction N generalizing c with
  | zero => simp
  | succ N ih =>
      rw [singularHomotopyIterate_succ, singularHomotopyIterate_succ,
        singularSubdivisionIterate_succ]
      simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
      rw [← singularSubdivision_boundary X n c]
      calc
        singularFinsuppBoundary X (n + 1) (singularHomotopy X (n + 1) c) +
              singularFinsuppBoundary X (n + 1)
                (singularHomotopyIterate X (n + 1) N
                  (singularSubdivision X (n + 1) c)) +
            (singularHomotopy X n (singularFinsuppBoundary X n c) +
              singularHomotopyIterate X n N
                (singularFinsuppBoundary X n
                  (singularSubdivision X (n + 1) c))) =
            (singularFinsuppBoundary X (n + 1) (singularHomotopy X (n + 1) c) +
                singularHomotopy X n (singularFinsuppBoundary X n c)) +
              (singularFinsuppBoundary X (n + 1)
                  (singularHomotopyIterate X (n + 1) N
                    (singularSubdivision X (n + 1) c)) +
                singularHomotopyIterate X n N
                  (singularFinsuppBoundary X n
                    (singularSubdivision X (n + 1) c))) := by abel
        _ = (c - singularSubdivision X (n + 1) c) +
              (singularSubdivision X (n + 1) c -
                singularSubdivisionIterate X (n + 1) N
                  (singularSubdivision X (n + 1) c)) := by
            rw [singularHomotopy_boundary, ih]
        _ = c - singularSubdivisionIterate X (n + 1) N
              (singularSubdivision X (n + 1) c) := by abel

theorem mem_support_singularHomotopyIterate {X : TopCat.{u}} {n N : ℕ}
    (c : SingularChainFinsupp X n) {y : (TopCat.toSSet.obj X) _⦋n + 1⦌}
    (hy : y ∈ (singularHomotopyIterate X n N c).support) :
    ∃ x ∈ c.support,
      Set.range (X.toSSetObjEquiv _ y) ⊆ Set.range (X.toSSetObjEquiv _ x) := by
  classical
  induction N generalizing c y with
  | zero => simp at hy
  | succ N ih =>
      rw [singularHomotopyIterate_succ] at hy
      rcases Finset.mem_union.mp (Finsupp.support_add hy) with hH | hiter
      · exact mem_support_singularHomotopy c hH
      · obtain ⟨z, hz, hyz⟩ := ih (singularSubdivision X n c) hiter
        obtain ⟨x, hx, hzx⟩ := mem_support_singularSubdivision c hz
        exact ⟨x, hx, hyz.trans hzx⟩

theorem isCoverSmall_of_mem_singularHomotopyIterate
    {X : TopCat.{u}} {ι : Type*} (U : ι → TopologicalSpace.Opens X) {n N : ℕ}
    {c : SingularChainFinsupp X n}
    (hc : ∀ x ∈ c.support, IsCoverSmall U x)
    {y : (TopCat.toSSet.obj X) _⦋n + 1⦌}
    (hy : y ∈ (singularHomotopyIterate X n N c).support) :
    IsCoverSmall U y := by
  obtain ⟨x, hx, hyx⟩ := mem_support_singularHomotopyIterate c hy
  obtain ⟨i, hxi⟩ := hc x hx
  exact ⟨i, hyx.trans hxi⟩

end AlgebraicTopology
