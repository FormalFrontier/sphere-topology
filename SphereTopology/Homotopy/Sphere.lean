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
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Homotopies on real unit spheres

Normalizing a segment joins two non-antipodal unit-sphere maps. The same
construction gives a homotopy equivalence from the unit sphere to the subspace
of pairs of unit vectors which are not antipodal. Its forward map is the
diagonal and its inverse is the first projection; the homotopy fixes the
diagonal pointwise.

These results hold in any real normed vector space, including the zero space,
without finite-dimensionality or nonemptiness assumptions. Taking the ambient
space to be Euclidean `(n + 1)`-space recovers the statement for the usual
`n`-sphere.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  Problem (3), p. 20, asks for the diagonal homotopy equivalence for Euclidean
  spheres. The real-normed-space formulation here is a generalization.
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

end Metric.Sphere
