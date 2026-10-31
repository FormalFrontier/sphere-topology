/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md.
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.LinearAlgebra.Dimension.Basic
import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover
import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Homotopies and simple connectivity of real unit spheres

Normalizing a segment joins two non-antipodal unit-sphere maps. The same
construction gives a homotopy equivalence from the unit sphere to the subspace
of pairs of unit vectors which are not antipodal. Its forward map is the
diagonal and its inverse is the first projection; the homotopy fixes the
diagonal pointwise.

The non-antipodal homotopies hold in any real normed vector space, including the
zero space, without finite-dimensionality or nonemptiness assumptions. Taking
the ambient space to be Euclidean `(n + 1)`-space recovers the statement for the
usual `n`-sphere.

The topology-only APIs concern the unit sphere for the given norm in an arbitrary
real normed space: a one-point complement is contractible, and a two-point
complement is path connected when the ambient cardinal rank exceeds two. The
same rank bound gives simple connectivity of the whole sphere. Neither
completeness nor finite-dimensionality is required. The one-point statement has
no rank premise, and the two removed points may coincide. Orthogonal-coordinate
charts belong instead to `SphereTopology.Geometry.Stereographic`.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  Problem (3), p. 20, asks for the diagonal homotopy equivalence for Euclidean
  spheres. The real-normed-space formulation here is a generalization.
* The two-open argument is from May, Chapter 2, §8. Chapter 3, §2 uses simple
  connectivity of the finite Euclidean spheres of dimension at least two in
  its universal-cover example.
* The puncture and connectivity statements here concern arbitrary real normed
  spaces with their original norm, extending the finite-dimensional setting.
  They use the generic sphere homotopies in this module and Mathlib's
  linear-algebra, path and contractibility APIs; no published proof in this
  full normed-space generality is being cited.
* Fundamental Groupoids supplies the general two-open simple-connectivity
  criterion `FundamentalGroup.simplyConnectedSpace_of_isOpenCover`.
* Mathlib's vector normalization, affine homotopy, sphere subtype and continuous
  homotopy APIs supply the analytic and topological foundations.
* The continuous normalization and sphere interpolation constructions are those
  previously used in this library's tangent-field and circle-degree modules.
-/

@[expose] public section

noncomputable section

namespace ContinuousMap

/-- Pointwise normalization of a nowhere-zero continuous vector-valued map. -/
noncomputable def normalizeOfNoZero
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : C(X, E)) (hV : ∀ x, V x ≠ 0) : C(X, E) where
  toFun x := NormedSpace.normalize (V x)
  continuous_toFun := by
    change Continuous ((fun x => ‖V x‖)⁻¹ • (V : X → E))
    exact (V.continuous.norm.inv₀ (fun x hx => hV x (norm_eq_zero.mp hx))).smul V.continuous

theorem normalizeOfNoZero_apply
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : C(X, E)) (hV : ∀ x, V x ≠ 0) (x : X) :
    normalizeOfNoZero V hV x = NormedSpace.normalize (V x) :=
  rfl

@[simp] theorem norm_normalizeOfNoZero
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : C(X, E)) (hV : ∀ x, V x ≠ 0) (x : X) :
    ‖normalizeOfNoZero V hV x‖ = 1 :=
  NormedSpace.norm_normalize (hV x)

end ContinuousMap

namespace Metric.Sphere

universe u v

variable {E : Type u} [NormedAddCommGroup E] [normedSpace : NormedSpace ℝ E]

local notation "S" => Metric.sphere (0 : E) 1
/-- A segment between non-antipodal unit vectors does not pass through zero. -/
theorem affine_ne_zero
    (x y : S) (hxy : x ≠ -y) (t : unitInterval) :
    (1 - (t : ℝ)) • (x : E) + (t : ℝ) • (y : E) ≠ 0 := by
  intro hz
  have heq : (1 - (t : ℝ)) • (x : E) = -((t : ℝ) • (y : E)) :=
    eq_neg_of_add_eq_zero_left hz
  have hx : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hy : ‖(y : E)‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
  have ht : 1 - (t : ℝ) = (t : ℝ) := by
    have hn := congrArg norm heq
    simpa only [norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr t.property.2), abs_of_nonneg t.property.1,
      hx, hy, mul_one] using hn
  have ht_ne : (t : ℝ) ≠ 0 := by
    intro ht_zero
    rw [ht_zero] at ht
    norm_num at ht
  apply hxy
  apply Subtype.ext
  apply smul_right_injective E ht_ne
  simpa only [ht, coe_neg_sphere, smul_neg] using heq

/-- The normalized affine homotopy between non-antipodal unit-sphere maps. -/
def homotopyOfNonAntipodal {X : Type v} [TopologicalSpace X]
    (f g : C(X, S)) (hfg : ∀ x, f x ≠ -g x) : f.Homotopy g := by
  let f' : C(X, E) := ⟨fun x => (f x : E), continuous_subtype_val.comp f.continuous⟩
  let g' : C(X, E) := ⟨fun x => (g x : E), continuous_subtype_val.comp g.continuous⟩
  let F := ContinuousMap.Homotopy.affine f' g'
  let V := F.toContinuousMap
  have hV : ∀ q, V q ≠ 0 := by
    rintro ⟨t, x⟩
    change AffineMap.lineMap (f x : E) (g x : E) (t : ℝ) ≠ 0
    rw [AffineMap.lineMap_apply_module]
    exact affine_ne_zero (f x) (g x) (hfg x) t
  let N := ContinuousMap.normalizeOfNoZero V hV
  exact {
    toFun q := ⟨N q, mem_sphere_zero_iff_norm.mpr
      (ContinuousMap.norm_normalizeOfNoZero V hV q)⟩
    continuous_toFun := N.continuous.subtype_mk _
    map_zero_left x := by
      apply Subtype.ext
      change NormedSpace.normalize (F (0, x)) = (f x : E)
      rw [F.apply_zero]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one
        (mem_sphere_zero_iff_norm.mp (f x).property)
    map_one_left x := by
      apply Subtype.ext
      change NormedSpace.normalize (F (1, x)) = (g x : E)
      rw [F.apply_one]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one
        (mem_sphere_zero_iff_norm.mp (g x).property) }

/-- The ambient-vector formula for the normalized affine sphere homotopy. -/
theorem homotopyOfNonAntipodal_apply {X : Type v} [TopologicalSpace X]
    (f g : C(X, S)) (hfg : ∀ x, f x ≠ -g x) (t : unitInterval) (x : X) :
    (homotopyOfNonAntipodal f g hfg (t, x) : E) =
      NormedSpace.normalize ((1 - (t : ℝ)) • (f x : E) + (t : ℝ) • (g x : E)) := by
  change NormedSpace.normalize (AffineMap.lineMap (f x : E) (g x : E) (t : ℝ)) = _
  rw [AffineMap.lineMap_apply_module]

/-- Sphere interpolation fixes every point where its endpoint maps agree. -/
theorem homotopyOfNonAntipodal_apply_of_eq {X : Type v} [TopologicalSpace X]
    (f g : C(X, S)) (hfg : ∀ x, f x ≠ -g x) (t : unitInterval) (x : X)
    (hx : f x = g x) : homotopyOfNonAntipodal f g hfg (t, x) = f x := by
  apply Subtype.ext
  rw [homotopyOfNonAntipodal_apply, ← hx, ← add_smul, sub_add_cancel, one_smul]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (mem_sphere_zero_iff_norm.mp (f x).property)

/-- Normalized interpolation never reaches the antipode of its initial vector. -/
private theorem normalize_affine_ne_neg
    (p q : S) (hpq : p ≠ -q) (t : unitInterval) :
    NormedSpace.normalize ((1 - (t : ℝ)) • (p : E) + (t : ℝ) • (q : E)) ≠ -(p : E) := by
  let v : E := (1 - (t : ℝ)) • (p : E) + (t : ℝ) • (q : E)
  have hv : v ≠ 0 := affine_ne_zero p q hpq t
  have hp : ‖(p : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.property
  have hq : ‖(q : E)‖ = 1 := mem_sphere_zero_iff_norm.mp q.property
  intro h
  change NormedSpace.normalize v = -(p : E) at h
  have hv_eq : v = -‖v‖ • (p : E) := by
    calc
      v = ‖v‖ • NormedSpace.normalize v := (NormedSpace.norm_smul_normalize v).symm
      _ = -‖v‖ • (p : E) := by rw [h, smul_neg, neg_smul]
  have heq : (1 - (t : ℝ) + ‖v‖) • (p : E) = -((t : ℝ) • (q : E)) := by
    apply eq_neg_of_add_eq_zero_left
    rw [add_smul]
    calc
      ((1 - (t : ℝ)) • (p : E) + ‖v‖ • (p : E)) + (t : ℝ) • (q : E) =
          v + ‖v‖ • (p : E) := by dsimp [v]; abel
      _ = -(‖v‖ • (p : E)) + ‖v‖ • (p : E) := by
        simpa only [neg_smul] using congrArg (fun w : E => w + ‖v‖ • (p : E)) hv_eq
      _ = 0 := neg_add_cancel _
  have hcoeff_nonneg : 0 ≤ 1 - (t : ℝ) + ‖v‖ :=
    add_nonneg (sub_nonneg.mpr t.property.2) (norm_nonneg v)
  have hcoeff : 1 - (t : ℝ) + ‖v‖ = (t : ℝ) := by
    have hn := congrArg norm heq
    simpa only [norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg hcoeff_nonneg, abs_of_nonneg t.property.1,
      hp, hq, mul_one] using hn
  have ht_pos : 0 < (t : ℝ) := by
    have hn_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    linarith [t.property.2]
  apply hpq
  apply Subtype.ext
  apply smul_right_injective E (ne_of_gt ht_pos)
  simpa only [hcoeff, coe_neg_sphere, smul_neg] using heq

/-- The normalized sphere homotopy stays away from the antipode of its initial map. -/
theorem homotopyOfNonAntipodal_ne_neg {X : Type v} [TopologicalSpace X]
    (f g : C(X, S)) (hfg : ∀ x, f x ≠ -g x) (t : unitInterval) (x : X) :
    (homotopyOfNonAntipodal f g hfg (t, x) : E) ≠ -(f x : E) := by
  rw [homotopyOfNonAntipodal_apply]
  exact normalize_affine_ne_neg (f x) (g x) (hfg x) t

include normedSpace in
/-- A real unit vector cannot equal its antipode. -/
theorem coe_ne_neg_self (p : S) : (p : E) ≠ -(p : E) := by
  intro h
  exact ne_neg_of_mem_unit_sphere ℝ p (Subtype.ext h)

include normedSpace in
/-- The diagonal into the subspace of non-antipodal unit-sphere pairs. -/
def nonAntipodalDiagonal :
    C(S, {z : S × S // (z.1 : E) ≠ -(z.2 : E)}) where
  toFun p := ⟨(p, p), coe_ne_neg_self p⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_id

@[simp] theorem nonAntipodalDiagonal_apply (p : S) :
    (nonAntipodalDiagonal p).val = (p, p) :=
  rfl

/-- First projection is a strict left inverse of the non-antipodal diagonal. -/
@[simp] theorem fst_comp_nonAntipodalDiagonal :
    ContinuousMap.fst.comp
      ((ContinuousMap.subtypeVal {z : S × S | ¬(z.1 : E) = -(z.2 : E)}).comp
        (nonAntipodalDiagonal (E := E))) = ContinuousMap.id S := by
  ext p
  rfl

/-- The normalized affine homotopy from diagonal after first projection to the
identity, fixed on the range of the diagonal. -/
def diagonalFstHomotopy :
    ContinuousMap.HomotopyRel
      (nonAntipodalDiagonal.comp (ContinuousMap.fst.comp
        (ContinuousMap.subtypeVal {z : S × S | (z.1 : E) ≠ -(z.2 : E)})))
      (ContinuousMap.id {z : S × S // (z.1 : E) ≠ -(z.2 : E)})
      (Set.range (nonAntipodalDiagonal (E := E))) := by
  let f : C({z : S × S // (z.1 : E) ≠ -(z.2 : E)}, S) := ContinuousMap.fst.comp
    (ContinuousMap.subtypeVal {z : S × S | (z.1 : E) ≠ -(z.2 : E)})
  let g : C({z : S × S // (z.1 : E) ≠ -(z.2 : E)}, S) := ContinuousMap.snd.comp
    (ContinuousMap.subtypeVal {z : S × S | (z.1 : E) ≠ -(z.2 : E)})
  have hfg : ∀ z, f z ≠ -g z := by
    intro z h
    exact z.property (congrArg Subtype.val h)
  let K := homotopyOfNonAntipodal f g hfg
  have hK (t : unitInterval) (z : {z : S × S // (z.1 : E) ≠ -(z.2 : E)}) :
      (z.val.1 : E) ≠ -(K (t, z) : E) := by
    intro h
    apply homotopyOfNonAntipodal_ne_neg f g hfg t z
    change (K (t, z) : E) = -(z.val.1 : E)
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  exact {
    toFun w := ⟨(w.2.val.1, K w), hK w.1 w.2⟩
    continuous_toFun := ((f.continuous.comp continuous_snd).prodMk K.continuous).subtype_mk _
    map_zero_left z := by
      apply Subtype.ext
      exact Prod.ext rfl (K.apply_zero z)
    map_one_left z := by
      apply Subtype.ext
      exact Prod.ext rfl (K.apply_one z)
    prop' t z hz := by
      rcases hz with ⟨p, rfl⟩
      apply Subtype.ext
      exact Prod.ext rfl
        (homotopyOfNonAntipodal_apply_of_eq f g hfg t (nonAntipodalDiagonal p) rfl) }

@[simp] theorem diagonalFstHomotopy_apply_fst (t : unitInterval)
    (z : {z : S × S // (z.1 : E) ≠ -(z.2 : E)}) :
    (diagonalFstHomotopy (t, z)).val.1 = z.val.1 :=
  rfl

/-- The second coordinate is the normalized segment from the first vector to the second. -/
theorem diagonalFstHomotopy_apply_snd (t : unitInterval)
    (z : {z : S × S // (z.1 : E) ≠ -(z.2 : E)}) :
    ((diagonalFstHomotopy (t, z)).val.2 : E) =
      NormedSpace.normalize
        ((1 - (t : ℝ)) • (z.val.1 : E) + (t : ℝ) • (z.val.2 : E)) := by
  exact homotopyOfNonAntipodal_apply _ _ _ t z

@[simp] theorem diagonalFstHomotopy_apply_diagonal (t : unitInterval) (p : S) :
    diagonalFstHomotopy (t, nonAntipodalDiagonal p) = nonAntipodalDiagonal p :=
  (diagonalFstHomotopy (E := E)).eq_snd t ⟨p, rfl⟩

/-- The diagonal is a homotopy equivalence onto the subspace of non-antipodal
pairs, with inverse the first projection.

This generalizes May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
Problem (3), from Euclidean spheres to unit spheres in real normed spaces. -/
def diagonalHomotopyEquiv :
    ContinuousMap.HomotopyEquiv S {z : S × S // (z.1 : E) ≠ -(z.2 : E)} where
  toFun := nonAntipodalDiagonal
  invFun := ContinuousMap.fst.comp
    (ContinuousMap.subtypeVal {z : S × S | (z.1 : E) ≠ -(z.2 : E)})
  left_inv := ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id S)).cast
    (fst_comp_nonAntipodalDiagonal (E := E)).symm rfl⟩
  right_inv := ⟨diagonalFstHomotopy.toHomotopy⟩

@[simp] theorem diagonalHomotopyEquiv_apply (p : S) :
    (diagonalHomotopyEquiv p).val = (p, p) :=
  rfl

@[simp] theorem diagonalHomotopyEquiv_symm_apply
    (z : {z : S × S // (z.1 : E) ≠ -(z.2 : E)}) :
    (diagonalHomotopyEquiv (E := E)).symm z = z.val.1 :=
  rfl

/-- Contract the complement of a unit-sphere point to its antipode, fixing that
antipode throughout. The sphere carries its given real norm; no rank,
completeness or finite-dimensionality hypothesis is needed. -/
def complSingletonContraction (p : S) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id ({p}ᶜ : Set S))
      (ContinuousMap.const ({p}ᶜ : Set S)
        ⟨-p, (ne_neg_of_mem_unit_sphere ℝ p).symm⟩)
      {⟨-p, (ne_neg_of_mem_unit_sphere ℝ p).symm⟩} := by
  let A : Set S := {p}ᶜ
  let a : A := ⟨-p, (ne_neg_of_mem_unit_sphere ℝ p).symm⟩
  let f : C(A, S) := ContinuousMap.const A (-p)
  let g : C(A, S) := ContinuousMap.subtypeVal A
  have hfg : ∀ x, f x ≠ -g x := by
    intro x hx
    have hx' : p = x.val := neg_injective hx
    exact x.property hx'.symm
  let K := homotopyOfNonAntipodal f g hfg
  have hK (z : unitInterval × A) : K z ∈ A := by
    change K z ≠ p
    intro hz
    apply homotopyOfNonAntipodal_ne_neg f g hfg z.1 z.2
    change (K z : E) = -(-(p : E))
    simpa only [neg_neg] using congrArg Subtype.val hz
  let H : ContinuousMap.HomotopyRel
      (ContinuousMap.const A a) (ContinuousMap.id A) {a} := {
    toFun z := ⟨K z, hK z⟩
    continuous_toFun := K.continuous.subtype_mk _
    map_zero_left x := Subtype.ext (K.apply_zero x)
    map_one_left x := Subtype.ext (K.apply_one x)
    prop' t x hx := by
      have hx : x = a := Set.mem_singleton_iff.mp hx
      subst x
      apply Subtype.ext
      exact homotopyOfNonAntipodal_apply_of_eq f g hfg t a rfl }
  exact H.symm

/-- In the whole sphere, the puncture contraction is the reversed non-antipodal
homotopy from the antipode to the subtype inclusion. -/
theorem complSingletonContraction_coe_apply (p : S) (t : unitInterval)
    (x : ({p}ᶜ : Set S)) :
    (complSingletonContraction p (t, x) : S) =
      homotopyOfNonAntipodal
        (ContinuousMap.const ({p}ᶜ : Set S) (-p))
        (ContinuousMap.subtypeVal ({p}ᶜ : Set S))
        (by
          intro y hy
          exact y.property (neg_injective hy).symm)
        (unitInterval.symm t, x) :=
  rfl

/-- The puncture contraction is normalized affine interpolation from the
original point to the antipode of the deleted point. -/
theorem complSingletonContraction_apply (p : S) (t : unitInterval)
    (x : ({p}ᶜ : Set S)) :
    ((complSingletonContraction p (t, x) : S) : E) =
      NormedSpace.normalize
        ((1 - (t : ℝ)) • ((x : S) : E) + (t : ℝ) • (-(p : E))) := by
  rw [complSingletonContraction_coe_apply, homotopyOfNonAntipodal_apply]
  change NormedSpace.normalize
    ((1 - (unitInterval.symm t : ℝ)) • (-(p : E)) +
      (unitInterval.symm t : ℝ) • ((x : S) : E)) = _
  simp only [unitInterval.coe_symm_eq, sub_sub_cancel]
  exact congrArg NormedSpace.normalize (add_comm _ _)

/-- The puncture contraction fixes the antipode of its deleted point. -/
@[simp] theorem complSingletonContraction_apply_antipode (p : S) (t : unitInterval) :
    complSingletonContraction p (t, ⟨-p, (ne_neg_of_mem_unit_sphere ℝ p).symm⟩) =
      ⟨-p, (ne_neg_of_mem_unit_sphere ℝ p).symm⟩ :=
  (complSingletonContraction p).eq_fst t (by simp)

end Metric.Sphere

universe w

/-- The complement of any point on a real normed unit sphere is contractible.

The construction uses this module's non-antipodal sphere homotopies and
Mathlib's contractibility API, with the original norm and without a rank,
completeness or finite-dimensionality hypothesis. -/
theorem contractibleSpace_sphere_compl_singleton
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Metric.sphere (0 : E) 1) :
    ContractibleSpace ({p}ᶜ : Set (Metric.sphere (0 : E) 1)) := by
  exact (contractible_iff_id_nullhomotopic _).mpr
    ⟨⟨-p, (ne_neg_of_mem_unit_sphere ℝ p).symm⟩,
      ⟨(Metric.Sphere.complSingletonContraction p).toHomotopy⟩⟩

private theorem span_pair_ne_top_of_two_lt_rank
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 2 < Module.rank ℝ E) (a b : E) :
    Submodule.span ℝ ({a, b} : Set E) ≠ ⊤ := by
  intro htop
  have hcard : Cardinal.mk ({a, b} : Set E) ≤ 2 := by
    simpa only [Cardinal.mk_singleton, one_add_one_eq_two] using
      (Cardinal.mk_insert_le (a := a) (s := {b}))
  have hrank := (rank_span_le (R := ℝ) ({a, b} : Set E)).trans hcard
  rw [htop, rank_top] at hrank
  exact (not_lt_of_ge hrank) h

private theorem normalize_notMem_submodule
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Submodule ℝ E) {v : E} (hv : v ∉ P) :
    NormedSpace.normalize v ∉ P := by
  intro hnorm
  apply hv
  rw [← NormedSpace.norm_smul_normalize v]
  exact P.smul_mem ‖v‖ hnorm

private theorem normalize_affine_ne_of_notMem_span
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p x r : Metric.sphere (0 : E) 1) (hxp : x ≠ p)
    (hr : (r : E) ∉ Submodule.span ℝ ({(p : E), (x : E)} : Set E))
    (t : unitInterval) :
    NormedSpace.normalize ((1 - (t : ℝ)) • (x : E) + (t : ℝ) • (r : E)) ≠
      (p : E) := by
  intro heq
  by_cases ht : (t : ℝ) = 0
  · apply hxp
    apply Subtype.ext
    simpa only [ht, sub_zero, one_smul, zero_smul, add_zero,
      NormedSpace.normalize_eq_self_of_norm_eq_one
        (mem_sphere_zero_iff_norm.mp x.property)] using heq
  · let P := Submodule.span ℝ ({(p : E), (x : E)} : Set E)
    have hp : (p : E) ∈ P := Submodule.subset_span (by simp)
    have hx : (x : E) ∈ P := Submodule.subset_span (by simp)
    have hv : (1 - (t : ℝ)) • (x : E) + (t : ℝ) • (r : E) ∈ P := by
      rw [← NormedSpace.norm_smul_normalize
        ((1 - (t : ℝ)) • (x : E) + (t : ℝ) • (r : E)), heq]
      exact P.smul_mem _ hp
    have htr : (t : ℝ) • (r : E) ∈ P := by
      simpa only [add_sub_cancel_left] using
        P.sub_mem hv (P.smul_mem (1 - (t : ℝ)) hx)
    exact hr ((P.smul_mem_iff ht).mp htr)

private theorem joinedIn_sphere_compl_poles_of_notMem_span
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q x r : Metric.sphere (0 : E) 1) (hxp : x ≠ p) (hxq : x ≠ q)
    (hrp : (r : E) ∉ Submodule.span ℝ ({(p : E), (x : E)} : Set E))
    (hrq : (r : E) ∉ Submodule.span ℝ ({(q : E), (x : E)} : Set E)) :
    JoinedIn ({p}ᶜ ∩ {q}ᶜ : Set (Metric.sphere (0 : E) 1)) x r := by
  have hxr : x ≠ -r := by
    intro heq
    apply hrp
    have hval : (x : E) = -(r : E) := congrArg Subtype.val heq
    have hr_eq : (r : E) = -(x : E) := by
      simpa only [neg_neg] using (congrArg Neg.neg hval).symm
    rw [hr_eq]
    exact (Submodule.span ℝ ({(p : E), (x : E)} : Set E)).neg_mem
      (Submodule.subset_span (by simp))
  let f := ContinuousMap.const Unit x
  let g := ContinuousMap.const Unit r
  let H := Metric.Sphere.homotopyOfNonAntipodal f g (fun _ => hxr)
  have hH (t : unitInterval) :
      ((H.evalAt ()) t : E) =
        NormedSpace.normalize ((1 - (t : ℝ)) • (x : E) + (t : ℝ) • (r : E)) :=
    Metric.Sphere.homotopyOfNonAntipodal_apply f g (fun _ => hxr) t ()
  refine ⟨H.evalAt (), ?_⟩
  intro t
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro heq
    apply normalize_affine_ne_of_notMem_span p x r hxp hrp t
    exact (hH t).symm.trans (congrArg Subtype.val heq)
  · intro heq
    apply normalize_affine_ne_of_notMem_span q x r hxq hrq t
    exact (hH t).symm.trans (congrArg Subtype.val heq)

/-- The complement of any two points on a real normed unit sphere is path
connected when the ambient cardinal rank exceeds two. The points may coincide.

The construction uses the generic sphere homotopies and Mathlib's
linear-algebra and path APIs in the original norm. Neither completeness nor
finite-dimensionality is required. -/
theorem pathConnectedSpace_sphere_compl_poles
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : Metric.sphere (0 : E) 1) (h : 2 < Module.rank ℝ E) :
    PathConnectedSpace ({p}ᶜ ∩ {q}ᶜ : Set (Metric.sphere (0 : E) 1)) := by
  classical
  apply isPathConnected_iff_pathConnectedSpace.mp
  rw [isPathConnected_iff]
  constructor
  · obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top
      (Submodule.span ℝ ({(p : E), (q : E)} : Set E))
      (span_pair_ne_top_of_two_lt_rank h (p : E) (q : E))
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv (Submodule.zero_mem _)
    let r : Metric.sphere (0 : E) 1 :=
      ⟨NormedSpace.normalize v, mem_sphere_zero_iff_norm.mpr
        (NormedSpace.norm_normalize hv0)⟩
    have hr : (r : E) ∉ Submodule.span ℝ ({(p : E), (q : E)} : Set E) :=
      normalize_notMem_submodule _ hv
    refine ⟨r, ?_⟩
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro heq
      apply hr
      rw [heq]
      exact Submodule.subset_span (by simp)
    · intro heq
      apply hr
      rw [heq]
      exact Submodule.subset_span (by simp)
  · intro x hx y hy
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff] at hx hy
    -- Avoid the four endpoint-pole planes; repetitions among them do not matter.
    let planes : Fin 4 → Submodule ℝ E := fun i =>
      if i = 0 then Submodule.span ℝ ({(p : E), (x : E)} : Set E)
      else if i = 1 then Submodule.span ℝ ({(q : E), (x : E)} : Set E)
      else if i = 2 then Submodule.span ℝ ({(p : E), (y : E)} : Set E)
      else Submodule.span ℝ ({(q : E), (y : E)} : Set E)
    have hplanes (i : Fin 4) : planes i ≠ ⊤ := by
      dsimp only [planes]
      split_ifs <;> exact span_pair_ne_top_of_two_lt_rank h _ _
    obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top planes hplanes
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv 0 (Submodule.zero_mem _)
    let r : Metric.sphere (0 : E) 1 :=
      ⟨NormedSpace.normalize v, mem_sphere_zero_iff_norm.mpr
        (NormedSpace.norm_normalize hv0)⟩
    have hr (i : Fin 4) : (r : E) ∉ planes i :=
      normalize_notMem_submodule (planes i) (hv i)
    have hxr := joinedIn_sphere_compl_poles_of_notMem_span p q x r hx.1 hx.2
      (by simpa [planes] using hr 0) (by simpa [planes] using hr 1)
    have hyr := joinedIn_sphere_compl_poles_of_notMem_span p q y r hy.1 hy.2
      (by simpa [planes] using hr 2) (by simpa [planes] using hr 3)
    exact hxr.trans hyr.symm

/-- The unit sphere in a real normed space of rank greater than two is simply
connected.

The two-open argument is from May, *A Concise Course in Algebraic Topology*,
Chapter 2, §8. Chapter 3, §2 uses simple connectivity of finite Euclidean spheres
of dimension at least two in its universal-cover example. The formulation here
extends that finite-dimensional setting to arbitrary real normed spaces with
their original norm, without completeness or finite-dimensionality assumptions.
The underlying interfaces are the generic sphere homotopies, Mathlib's topology
APIs and Fundamental Groupoids' two-open simple-connectivity criterion. -/
theorem simplyConnectedSpace_unitSphere
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 2 < Module.rank ℝ E) :
    SimplyConnectedSpace (Metric.sphere (0 : E) 1) := by
  classical
  let : Nontrivial E :=
    (rank_pos_iff_nontrivial (R := ℝ) (M := E)).mp (lt_trans (by norm_num) h)
  obtain ⟨p⟩ := NormedSpace.sphere_nonempty_rclike (E := E) ℝ (show (0 : ℝ) ≤ 1 by norm_num)
  let U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1) :=
    ⟨{p}ᶜ, isOpen_compl_singleton⟩
  let V : TopologicalSpace.Opens (Metric.sphere (0 : E) 1) :=
    ⟨{-p}ᶜ, isOpen_compl_singleton⟩
  have hcover : U ⊔ V = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_of_forall
    intro x
    change x ≠ p ∨ x ≠ -p
    by_cases hx : x = p
    · exact Or.inr (hx ▸ ne_neg_of_mem_unit_sphere ℝ p)
    · exact Or.inl hx
  refine FundamentalGroup.simplyConnectedSpace_of_isOpenCover U V hcover ?_ ?_ ?_
  · let : ContractibleSpace ({p}ᶜ : Set (Metric.sphere (0 : E) 1)) :=
      contractibleSpace_sphere_compl_singleton p
    exact SimplyConnectedSpace.ofContractible _
  · let : ContractibleSpace ({-p}ᶜ : Set (Metric.sphere (0 : E) 1)) :=
      contractibleSpace_sphere_compl_singleton (-p)
    exact SimplyConnectedSpace.ofContractible _
  · exact isPathConnected_iff_pathConnectedSpace.mpr
      (pathConnectedSpace_sphere_compl_poles p (-p) h)
