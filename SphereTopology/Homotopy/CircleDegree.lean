/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle
import SphereTopology.Homotopy.Sphere
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Degree of continuous circle self-maps

`Circle.degree` assigns an integer to every continuous self-map of the complex
unit circle. It applies the induced fundamental-group map to the positive
one-turn generator, returns the target basepoint to one along `Circle.path`,
and reads the integer coordinate using `Circle.fundamentalGroupEquivInt`.
No condition on the image of one is imposed.

`Circle.fundamentalGroupEquivInt_map` characterizes the induced endomorphism in
integer coordinates for every return path from `f 1` to `1`. The degree classifies
free homotopy classes of circle self-maps. Degree different from one is a
sufficient condition for a fixed point, not a necessary condition.

`Circle.degree_mul` makes degree additive for pointwise multiplication, in
contrast to multiplication of degrees under composition. Its multiset-product
corollary sums one contribution for every factor, retaining repeated factors
and including the empty product.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §7,
  p. 10, for degree, its independence of the return path, free homotopy
  classification, constants and signed power maps; Problem (2), p. 11,
  for the fixed-point consequence.
* The integer coordinates and positive generator are those of
  `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle`, following
  May's Chapter 1, §5.
  Mathlib's fundamental-groupoid, basepoint-transport, complex-circle and
  continuous-map group APIs supply the constructions used here.
-/

@[expose] public section

noncomputable section

namespace Circle

/-- The degree of a continuous circle self-map: the integer coordinate of the
image of the positive generator, after transport from `f 1` back to `1`.
This is the fundamental-group definition of May, Chapter 1, §7. -/
def degree (f : C(Circle, Circle)) : ℤ :=
  (fundamentalGroupEquivInt
    (FundamentalGroup.fundamentalGroupMulEquivOfPath (path (f 1) 1)
      (FundamentalGroup.map f 1
        (fundamentalGroupEquivInt.symm (Multiplicative.ofAdd 1))))).toAdd

/-- Evaluation of degree using the prescribed return path and positive generator. -/
theorem degree_def (f : C(Circle, Circle)) :
    degree f =
      (fundamentalGroupEquivInt
        (FundamentalGroup.fundamentalGroupMulEquivOfPath (path (f 1) 1)
          (FundamentalGroup.map f 1
            (fundamentalGroupEquivInt.symm (Multiplicative.ofAdd 1))))).toAdd := rfl

private theorem degree_transport_apply {X : Type*} [TopologicalSpace X]
    {x y : X} (a : Path x y) (γ : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath a γ =
      FundamentalGroup.fromPath
        ((Path.Homotopic.Quotient.mk a.symm).trans
          (γ.toPath.trans (Path.Homotopic.Quotient.mk a))) := rfl

private theorem degree_path_cancel {X : Type*} [TopologicalSpace X]
    {x y z : X} (a : Path.Homotopic.Quotient x y)
    (p : Path.Homotopic.Quotient x z) :
    a.trans (a.symm.trans p) = p := by
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]

private theorem degree_path_symm_cancel {X : Type*} [TopologicalSpace X]
    {x y z : X} (a : Path.Homotopic.Quotient x y)
    (p : Path.Homotopic.Quotient y z) :
    a.symm.trans (a.trans p) = p := by
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

-- The integer coordinate kills the conjugation relating two return paths.
private theorem degree_transport_independent {x : Circle} (a b : Path x 1)
    (γ : FundamentalGroup Circle x) :
    fundamentalGroupEquivInt (FundamentalGroup.fundamentalGroupMulEquivOfPath a γ) =
      fundamentalGroupEquivInt (FundamentalGroup.fundamentalGroupMulEquivOfPath b γ) := by
  let q : FundamentalGroup Circle 1 :=
    FundamentalGroup.fromPath ⟦b.symm.trans a⟧
  let r : FundamentalGroup Circle 1 :=
    FundamentalGroup.fromPath ⟦a.symm.trans b⟧
  have hqr : q * r = 1 := by
    change (Path.Homotopic.Quotient.mk (a.symm.trans b)).trans
      (Path.Homotopic.Quotient.mk (b.symm.trans a)) =
        Path.Homotopic.Quotient.refl 1
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc, degree_path_cancel,
      Path.Homotopic.Quotient.symm_trans]
  have hconj : FundamentalGroup.fundamentalGroupMulEquivOfPath a γ =
      q * FundamentalGroup.fundamentalGroupMulEquivOfPath b γ * r := by
    rw [degree_transport_apply, degree_transport_apply]
    change (Path.Homotopic.Quotient.mk a.symm).trans
        (γ.toPath.trans (Path.Homotopic.Quotient.mk a)) =
      (Path.Homotopic.Quotient.mk (a.symm.trans b)).trans
        (((Path.Homotopic.Quotient.mk b.symm).trans
          (γ.toPath.trans (Path.Homotopic.Quotient.mk b))).trans
          (Path.Homotopic.Quotient.mk (b.symm.trans a)))
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc, degree_path_cancel]
  rw [hconj, map_mul, map_mul]
  calc
    fundamentalGroupEquivInt q *
          fundamentalGroupEquivInt (FundamentalGroup.fundamentalGroupMulEquivOfPath b γ) *
          fundamentalGroupEquivInt r =
        fundamentalGroupEquivInt (FundamentalGroup.fundamentalGroupMulEquivOfPath b γ) *
          fundamentalGroupEquivInt (q * r) := by rw [map_mul]; ac_rfl
    _ = fundamentalGroupEquivInt
        (FundamentalGroup.fundamentalGroupMulEquivOfPath b γ) := by
      rw [hqr, map_one, mul_one]

private theorem degree_transport_trans {X : Type*} [TopologicalSpace X]
    {x y z : X} (a : Path x y) (b : Path y z) (γ : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (a.trans b) γ =
      FundamentalGroup.fundamentalGroupMulEquivOfPath b
        (FundamentalGroup.fundamentalGroupMulEquivOfPath a γ) := by
  simp only [degree_transport_apply, Path.trans_symm,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

private theorem degree_map_transport {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) {x y : X} (a : Path x y)
    (γ : FundamentalGroup X x) :
    FundamentalGroup.map f y (FundamentalGroup.fundamentalGroupMulEquivOfPath a γ) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (a.map f.continuous)
        (FundamentalGroup.map f x γ) := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    change Path.Homotopic.Quotient.mk ((a.symm.trans (γ.trans a)).map f.continuous) =
      Path.Homotopic.Quotient.mk
        ((a.map f.continuous).symm.trans ((γ.map f.continuous).trans (a.map f.continuous)))
    rw [Path.map_trans, Path.map_trans, Path.map_symm]

private theorem degree_transport_of_eq {x : Circle} (h : x = 1)
    (γ : FundamentalGroup Circle x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (path x 1) γ =
      FundamentalGroup.fromPath (γ.toPath.cast h.symm h.symm) := by
  subst x
  rw [path_self, degree_transport_apply]
  change (Path.Homotopic.Quotient.refl (1 : Circle)).trans
      (γ.toPath.trans (Path.Homotopic.Quotient.refl (1 : Circle))) =
    γ.toPath.cast rfl rfl
  simp only [Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.cast_rfl_rfl]

/-- For any return path, the induced fundamental-group map acts on integer
coordinates by multiplication by degree. This includes the return-path
independence in May, Chapter 1, §7, with the positive normalization of §5. -/
theorem fundamentalGroupEquivInt_map (f : C(Circle, Circle))
    (a : Path (f 1) 1) (n : ℤ) :
    fundamentalGroupEquivInt
        (FundamentalGroup.fundamentalGroupMulEquivOfPath a
          (FundamentalGroup.map f 1
            (fundamentalGroupEquivInt.symm (Multiplicative.ofAdd n)))) =
      Multiplicative.ofAdd (degree f * n) := by
  let A : Multiplicative ℤ →* Multiplicative ℤ :=
    fundamentalGroupEquivInt.toMonoidHom.comp
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath (path (f 1) 1)).toMonoidHom.comp
        ((FundamentalGroup.map f 1).comp fundamentalGroupEquivInt.symm.toMonoidHom))
  have hn : Multiplicative.ofAdd n = (Multiplicative.ofAdd (1 : ℤ)) ^ n := by
    rw [← ofAdd_zsmul]
    simp only [zsmul_eq_mul, Int.cast_id, mul_one]
  rw [degree_transport_independent a (path (f 1) 1)]
  change A (Multiplicative.ofAdd n) = Multiplicative.ofAdd (degree f * n)
  rw [hn, map_zpow, ← ofAdd_toAdd (A (Multiplicative.ofAdd 1)),
    ← ofAdd_zsmul]
  change Multiplicative.ofAdd (n • degree f) = Multiplicative.ofAdd (degree f * n)
  rw [zsmul_eq_mul, Int.cast_id, mul_comm]

private theorem degree_coordinate_map (f : C(Circle, Circle))
    (a : Path (f 1) 1) (γ : FundamentalGroup Circle 1) :
    fundamentalGroupEquivInt (FundamentalGroup.fundamentalGroupMulEquivOfPath a
      (FundamentalGroup.map f 1 γ)) =
        Multiplicative.ofAdd (degree f * (fundamentalGroupEquivInt γ).toAdd) := by
  simpa only [ofAdd_toAdd, MulEquiv.symm_apply_apply] using
    fundamentalGroupEquivInt_map f a (fundamentalGroupEquivInt γ).toAdd

/-- The identity circle map has degree one. -/
theorem degree_id : degree (ContinuousMap.id Circle) = 1 := by
  rw [degree_def, fundamentalGroupEquivInt_symm_apply,
    degree_transport_of_eq (show ContinuousMap.id Circle 1 = 1 from rfl)]
  change (fundamentalGroupEquivInt
    (FundamentalGroup.fromPath ⟦(loop 1).map continuous_id⟧)).toAdd = 1
  rw [Path.map_id, fundamentalGroupEquivInt_loop]
  rfl

/-- A constant circle map at any point has degree zero, as in May, Chapter 1, §7. -/
theorem degree_const (c : Circle) :
    degree (ContinuousMap.const Circle c) = 0 := by
  have hm : FundamentalGroup.map (ContinuousMap.const Circle c) 1
      (FundamentalGroup.fromPath ⟦loop 1⟧) =
        (1 : FundamentalGroup Circle ((ContinuousMap.const Circle c) 1)) := by
    change Path.Homotopic.Quotient.mk ((loop 1).map continuous_const) =
      Path.Homotopic.Quotient.mk (Path.refl c)
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    rfl
  rw [degree_def, fundamentalGroupEquivInt_symm_apply, hm]
  simp only [map_one]
  rfl

/-- Degree is multiplicative under composition of arbitrary circle self-maps. -/
theorem degree_comp (f g : C(Circle, Circle)) :
    degree (f.comp g) = degree f * degree g := by
  let a := path (g 1) 1
  let b := path (f 1) 1
  let γ := fundamentalGroupEquivInt.symm (Multiplicative.ofAdd 1)
  have hc := fundamentalGroupEquivInt_map (f.comp g) ((a.map f.continuous).trans b) 1
  have hg := fundamentalGroupEquivInt_map g a 1
  simp only [mul_one] at hc hg
  have hm : FundamentalGroup.map (f.comp g) 1 γ =
      FundamentalGroup.map f (g 1) (FundamentalGroup.map g 1 γ) := by
    change γ.toPath.map (f.comp g) = (γ.toPath.map g).map f
    exact Path.Homotopic.Quotient.map_comp
  rw [hm, degree_transport_trans, ← degree_map_transport, degree_coordinate_map, hg] at hc
  exact (congrArg Multiplicative.toAdd hc).symm

/-- The signed power map `z ↦ z ^ n` has degree `n`, including zero and negative
exponents, as in May, Chapter 1, §7. The power is pointwise on continuous maps. -/
theorem degree_zpow (n : ℤ) :
    degree ((ContinuousMap.id Circle) ^ n) = n := by
  let f : C(Circle, Circle) := (ContinuousMap.id Circle) ^ n
  have hf : f 1 = 1 := by
    simp only [f, ContinuousMap.zpow_apply, ContinuousMap.id_apply, one_zpow]
  have hl : ((loop 1).map f.continuous).cast hf.symm hf.symm = loop n := by
    apply Path.ext
    funext t
    change (loop 1 t) ^ n = loop n t
    rw [loop_apply, loop_apply, ← exp_intCast_mul]
    congr 1
    push_cast
    ring
  rw [degree_def, fundamentalGroupEquivInt_symm_apply, degree_transport_of_eq hf]
  change (fundamentalGroupEquivInt
    (FundamentalGroup.fromPath ⟦((loop 1).map f.continuous).cast hf.symm hf.symm⟧)).toAdd = n
  rw [hl, fundamentalGroupEquivInt_loop]
  rfl

private theorem degree_homotopy_transport {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} (H : f.Homotopy g)
    (x : X) (γ : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt x)
      (FundamentalGroup.map f x γ) = FundamentalGroup.map g x γ := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    have h := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H γ)
    have h' := congrArg (fun p ↦ (Path.Homotopic.Quotient.mk (H.evalAt x).symm).trans p) h
    change (Path.Homotopic.Quotient.mk (H.evalAt x).symm).trans
        ((Path.Homotopic.Quotient.mk (γ.map f.continuous)).trans
          (Path.Homotopic.Quotient.mk (H.evalAt x))) =
      Path.Homotopic.Quotient.mk (γ.map g.continuous)
    simpa only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc, degree_path_symm_cancel] using h'

/-- Degree is invariant under free homotopy, as in May, Chapter 1, §7. -/
theorem degree_eq_of_homotopic {f g : C(Circle, Circle)} (h : f.Homotopic g) :
    degree f = degree g := by
  obtain ⟨H⟩ := h
  have hf := fundamentalGroupEquivInt_map f ((H.evalAt 1).trans (path (g 1) 1)) 1
  rw [mul_one, degree_transport_trans, degree_homotopy_transport] at hf
  rw [degree_def]
  exact (congrArg Multiplicative.toAdd hf).symm

open scoped unitInterval

private theorem fundamentalGroup_transport_refl_cast
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    (γ : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath ((Path.refl y).cast h rfl) γ =
      FundamentalGroup.fromPath (γ.toPath.cast h.symm h.symm) := by
  cases h
  change (CategoryTheory.Iso.refl (FundamentalGroupoid.mk x)).conj γ =
    FundamentalGroup.fromPath (γ.toPath.cast rfl rfl)
  simp only [CategoryTheory.Iso.refl_conj, Path.Homotopic.Quotient.cast_rfl_rfl]

private theorem loop_one_surjective : Function.Surjective (loop 1) := by
  intro z
  obtain ⟨x, rfl⟩ := exp_surjective z
  have hπ : 0 < 2 * Real.pi := by positivity
  obtain ⟨y, hy, hxy⟩ := periodic_exp.exists_mem_Ico₀ hπ x
  let s : I := ⟨y / (2 * Real.pi),
    div_nonneg hy.1 hπ.le, (div_le_one hπ).mpr hy.2.le⟩
  refine ⟨s, ?_⟩
  rw [loop_apply]
  simp only [Int.cast_one, mul_one]
  change exp (2 * Real.pi * (y / (2 * Real.pi))) = exp x
  calc
    exp (2 * Real.pi * (y / (2 * Real.pi))) = exp y :=
      congrArg exp (mul_div_cancel₀ y hπ.ne')
    _ = exp x := hxy.symm

private theorem loop_one_injOn :
    Set.InjOn (loop 1) {s : I | (s : ℝ) < 1} := by
  intro s hs t ht h
  have hπ : 0 < 2 * Real.pi := by positivity
  have hang : 2 * Real.pi * (s : ℝ) = 2 * Real.pi * (t : ℝ) :=
    exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
      ⟨mul_nonneg hπ.le s.property.1,
        by simpa only [mul_one] using mul_lt_mul_of_pos_left hs hπ⟩
      ⟨mul_nonneg hπ.le t.property.1,
        by simpa only [mul_one] using mul_lt_mul_of_pos_left ht hπ⟩
      (by simpa only [loop_apply, Int.cast_one, mul_one] using h)
  exact Subtype.ext (mul_left_cancel₀ hπ.ne' hang)

-- The quotient of the interval identifies exactly its two endpoints.
private theorem loop_one_fibres {s t : I} (h : loop 1 s = loop 1 t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  rcases lt_or_eq_of_le s.property.2 with hs | hs
  · rcases lt_or_eq_of_le t.property.2 with ht | ht
    · exact Or.inl (loop_one_injOn hs ht h)
    · have ht' : t = 1 := Subtype.ext ht
      refine Or.inr (Or.inl ⟨loop_one_injOn hs (by norm_num) ?_, ht'⟩)
      simpa only [ht', (loop 1).source, (loop 1).target] using h
  · have hs' : s = 1 := Subtype.ext hs
    rcases lt_or_eq_of_le t.property.2 with ht | ht
    · refine Or.inr (Or.inr ⟨hs', loop_one_injOn ht (by norm_num) ?_⟩)
      simpa only [hs', (loop 1).source, (loop 1).target] using h.symm
    · exact Or.inl (hs'.trans (Subtype.ext ht).symm)

private theorem fundamentalGroupEquivInt_map_loop_one
    (f : C(Circle, Circle)) (hf : f 1 = 1) :
    fundamentalGroupEquivInt
        (FundamentalGroup.fromPath
          ⟦((loop 1).map f.continuous).cast hf.symm hf.symm⟧) =
      Multiplicative.ofAdd (degree f) := by
  have h := fundamentalGroupEquivInt_map f ((Path.refl 1).cast hf rfl) 1
  rw [fundamentalGroupEquivInt_symm_apply, fundamentalGroup_transport_refl_cast] at h
  change fundamentalGroupEquivInt
      (FundamentalGroup.fromPath
        ⟦((loop 1).map f.continuous).cast hf.symm hf.symm⟧) =
    Multiplicative.ofAdd (degree f * 1) at h
  simpa only [mul_one] using h

private theorem homotopic_of_degree_eq_of_map_one_eq_one
    (f g : C(Circle, Circle)) (hf : f 1 = 1) (hg : g 1 = 1)
    (h : degree f = degree g) : f.Homotopic g := by
  let p : Path (1 : Circle) 1 := ((loop 1).map f.continuous).cast hf.symm hf.symm
  let q : Path (1 : Circle) 1 := ((loop 1).map g.continuous).cast hg.symm hg.symm
  have hpq : FundamentalGroup.fromPath ⟦p⟧ = FundamentalGroup.fromPath ⟦q⟧ := by
    apply fundamentalGroupEquivInt.injective
    exact (fundamentalGroupEquivInt_map_loop_one f hf).trans
      ((congrArg Multiplicative.ofAdd h).trans
        (fundamentalGroupEquivInt_map_loop_one g hg).symm)
  obtain ⟨H⟩ := Path.Homotopic.Quotient.eq.mp hpq
  have hquot : Topology.IsQuotientMap (loop 1).toContinuousMap :=
    .of_surjective_continuous loop_one_surjective (loop 1).continuous
  let L (t : I) : C(I, Circle) :=
    ⟨fun s => H (t, s), (map_continuous H).comp (continuous_const.prodMk continuous_id)⟩
  have hL (t : I) : Function.FactorsThrough (L t) (loop 1).toContinuousMap := by
    intro s u hsu
    change H (t, s) = H (t, u)
    rcases loop_one_fibres hsu with hsu | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hsu]
    · exact (H.source t).trans (H.target t).symm
    · exact (H.target t).trans (H.source t).symm
  let K (t : I) : C(Circle, Circle) := hquot.lift (L t) (hL t)
  have hK (t s : I) : K t (loop 1 s) = H (t, s) :=
    ContinuousMap.congr_fun (hquot.lift_comp (L t) (hL t)) s
  refine ⟨{
    toFun := fun x => K x.1 x.2
    continuous_toFun := hquot.continuous_lift_prod_right ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · have heq : (fun x : I × I => K x.1 (loop 1 x.2)) = H :=
      funext fun x => hK x.1 x.2
    change Continuous (fun x : I × I => K x.1 (loop 1 x.2))
    rw [heq]
    exact map_continuous H
  · intro z
    obtain ⟨s, rfl⟩ := loop_one_surjective z
    rw [hK]
    exact H.map_zero_left s
  · intro z
    obtain ⟨s, rfl⟩ := loop_one_surjective z
    rw [hK]
    exact H.map_one_left s

-- A rotation of the target moves f(1) to one through an ordinary free homotopy.
private theorem homotopic_normalize (f : C(Circle, Circle)) :
    f.Homotopic (ContinuousMap.const Circle (f 1)⁻¹ * f) := by
  refine ⟨{
    toFun := fun x => path (f 1) 1 x.1 * (f 1)⁻¹ * f x.2
    continuous_toFun := by fun_prop
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro z
    simp only [(path (f 1) 1).source, mul_inv_cancel, one_mul]
  · intro z
    simp only [(path (f 1) 1).target, one_mul, ContinuousMap.mul_apply,
      ContinuousMap.const_apply]

/-- Two arbitrary continuous circle self-maps are freely homotopic exactly when
they have the same degree, as in May, Chapter 1, §7. -/
theorem homotopic_iff_degree_eq (f g : C(Circle, Circle)) :
    f.Homotopic g ↔ degree f = degree g := by
  constructor
  · exact degree_eq_of_homotopic
  · intro h
    let f₀ := ContinuousMap.const Circle (f 1)⁻¹ * f
    let g₀ := ContinuousMap.const Circle (g 1)⁻¹ * g
    have hf : f.Homotopic f₀ := homotopic_normalize f
    have hg : g.Homotopic g₀ := homotopic_normalize g
    have hf₀ : f₀ 1 = 1 := by simp only [f₀, ContinuousMap.mul_apply,
      ContinuousMap.const_apply, inv_mul_cancel]
    have hg₀ : g₀ 1 = 1 := by simp only [g₀, ContinuousMap.mul_apply,
      ContinuousMap.const_apply, inv_mul_cancel]
    have h₀ : degree f₀ = degree g₀ :=
      (degree_eq_of_homotopic hf).symm.trans (h.trans (degree_eq_of_homotopic hg))
    exact hf.trans ((homotopic_of_degree_eq_of_map_one_eq_one f₀ g₀ hf₀ hg₀ h₀).trans hg.symm)

/-- A continuous circle self-map of degree different from one has a fixed point.
This is May, Chapter 1, Problem (2); only sufficiency is asserted. -/
theorem exists_fixedPoint_of_degree_ne_one (f : C(Circle, Circle))
    (h : degree f ≠ 1) : ∃ z : Circle, f z = z := by
  by_contra hfixed
  have hne : ∀ z, f z ≠ z := fun z hz => hfixed ⟨z, hz⟩
  let antipodal : C(Circle, Circle) := ⟨fun z => -z, continuous_neg⟩
  have hnonantipodal : ∀ z, f z ≠ -(antipodal z) := by
    intro z hz
    apply hne z
    change f z = -(-z) at hz
    simpa only [neg_neg] using hz
  let H : f.Homotopy antipodal :=
    Metric.Sphere.homotopyOfNonAntipodal (E := ℂ) f antipodal hnonantipodal
  let p := path (-1) 1
  let R : antipodal.Homotopy (ContinuousMap.id Circle) := {
    toFun q := p q.1 * q.2
    continuous_toFun := (p.continuous.comp continuous_fst).mul continuous_snd
    map_zero_left z := by
      change p 0 * z = -z
      simp only [p, Path.source, neg_mul, one_mul]
    map_one_left z := by
      change p 1 * z = z
      simp only [p, Path.target, one_mul] }
  apply h
  exact (degree_eq_of_homotopic ⟨H.trans R⟩).trans degree_id

/-- Degree is additive under pointwise multiplication of arbitrary circle self-maps. -/
theorem degree_mul (f g : C(Circle, Circle)) :
    degree (f * g) = degree f + degree g := by
  have hf : f.Homotopic ((ContinuousMap.id Circle) ^ degree f) :=
    (homotopic_iff_degree_eq _ _).mpr (degree_zpow (degree f)).symm
  have hg : g.Homotopic ((ContinuousMap.id Circle) ^ degree g) :=
    (homotopic_iff_degree_eq _ _).mpr (degree_zpow (degree g)).symm
  let m : C(Circle × Circle, Circle) := ContinuousMap.fst * ContinuousMap.snd
  have h : (f * g).Homotopic
      (((ContinuousMap.id Circle) ^ degree f) *
        ((ContinuousMap.id Circle) ^ degree g)) :=
    (ContinuousMap.Homotopic.refl m).comp (hf.prodMk hg)
  calc
    degree (f * g) = degree (((ContinuousMap.id Circle) ^ degree f) *
        ((ContinuousMap.id Circle) ^ degree g)) := degree_eq_of_homotopic h
    _ = degree ((ContinuousMap.id Circle) ^ (degree f + degree g)) := by rw [zpow_add]
    _ = degree f + degree g := degree_zpow _

/-- The degree of a multiset product is the sum of the factors' degrees,
retaining repetitions and including the empty product. -/
theorem degree_multiset_prod (s : Multiset C(Circle, Circle)) :
    degree s.prod = (s.map degree).sum := by
  induction s using Multiset.induction_on with
  | empty =>
    simpa only [Multiset.prod_zero, Multiset.map_zero, Multiset.sum_zero,
      ContinuousMap.const_one] using degree_const (1 : Circle)
  | cons f s ih =>
    simp only [Multiset.prod_cons, degree_mul, Multiset.map_cons, Multiset.sum_cons, ih]

end Circle

end

end

/-!
# Circle degree examples

The square map tests degree on a nonidentity, nonconstant continuous self-map.
Its coefficient is computed from the transported positive loop and the integer
calculator. Identity and a constant at minus one give boundary computations.
The degree API computes composition and signed powers, distinguishes free homotopy
classes and supplies a fixed point for the square map. Rotation by minus one is
freely homotopic to identity, but is not based at one and has no fixed points.
-/

noncomputable section

namespace SphereTopologyTest

private theorem transport_path_of_eq {x : Circle} (h : x = 1)
    (γ : FundamentalGroup Circle x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (Circle.path x 1) γ =
      FundamentalGroup.fromPath (γ.toPath.cast h.symm h.symm) := by
  subst x
  rw [Circle.path_self]
  change (Path.Homotopic.Quotient.refl (1 : Circle)).trans
      (γ.toPath.trans (Path.Homotopic.Quotient.refl (1 : Circle))) =
    γ.toPath.cast rfl rfl
  simp only [Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.cast_rfl_rfl]

private def mapSquare : C(Circle, Circle) :=
  (ContinuousMap.id Circle) ^ (2 : ℕ)

private theorem mapSquare_fixed_one : mapSquare 1 = 1 := by
  simp only [mapSquare, ContinuousMap.pow_apply, ContinuousMap.id_apply, one_pow]

private theorem mapSquare_loop :
    ((Circle.loop 1).map mapSquare.continuous).cast
        mapSquare_fixed_one.symm mapSquare_fixed_one.symm = Circle.loop 2 := by
  apply Path.ext
  funext t
  change (Circle.loop 1 t) ^ (2 : ℕ) = Circle.loop 2 t
  rw [Circle.loop_apply, Circle.loop_apply, ← Circle.exp_natCast_mul]
  congr 1
  norm_num
  ring

private theorem mapSquare_degree : Circle.degree mapSquare = 2 := by
  rw [Circle.degree_def, Circle.fundamentalGroupEquivInt_symm_apply,
    transport_path_of_eq mapSquare_fixed_one]
  change (Circle.fundamentalGroupEquivInt
    (FundamentalGroup.fromPath
      ⟦((Circle.loop 1).map mapSquare.continuous).cast
        mapSquare_fixed_one.symm mapSquare_fixed_one.symm⟧)).toAdd = 2
  rw [mapSquare_loop, Circle.fundamentalGroupEquivInt_loop]
  rfl

private theorem mapSquare_degree_ne_one : Circle.degree mapSquare ≠ 1 := by
  rw [mapSquare_degree]
  norm_num

private theorem mapSquare_ne_id : mapSquare ≠ ContinuousMap.id Circle := by
  intro h
  have he := congrArg (fun f : C(Circle, Circle) ↦ f (-1)) h
  have hneg : (1 : Circle) = -1 := by
    simpa only [mapSquare, ContinuousMap.pow_apply, ContinuousMap.mul_apply,
      ContinuousMap.id_apply, pow_two, neg_mul_neg, one_mul] using he
  exact Circle.neg_ne_self (1 : Circle) hneg.symm

private theorem mapSquare_ne_const (c : Circle) :
    mapSquare ≠ ContinuousMap.const Circle c := by
  intro h
  have hc : c = 1 := by
    simpa only [mapSquare, ContinuousMap.pow_apply, ContinuousMap.id_apply,
      one_pow, ContinuousMap.const_apply] using
      (congrArg (fun f : C(Circle, Circle) ↦ f 1) h).symm
  have ht : mapSquare (Circle.exp (Real.pi / 2)) = 1 := by
    simpa only [ContinuousMap.const_apply, hc] using
      congrArg (fun f : C(Circle, Circle) ↦ f (Circle.exp (Real.pi / 2))) h
  apply Circle.exp_pi_ne_one
  calc
    Circle.exp Real.pi = (Circle.exp (Real.pi / 2)) ^ (2 : ℕ) := by
      rw [← Circle.exp_natCast_mul]
      congr 1
      norm_num
      ring
    _ = 1 := ht

private theorem identity_degree : Circle.degree (ContinuousMap.id Circle) = 1 := by
  rw [Circle.degree_def, Circle.fundamentalGroupEquivInt_symm_apply,
    transport_path_of_eq (show ContinuousMap.id Circle 1 = 1 from rfl)]
  change (Circle.fundamentalGroupEquivInt
    (FundamentalGroup.fromPath ⟦(Circle.loop 1).map continuous_id⟧)).toAdd = 1
  rw [Path.map_id, Circle.fundamentalGroupEquivInt_loop]
  rfl

private def constantNegOne : C(Circle, Circle) :=
  ContinuousMap.const Circle (-1)

private theorem constantNegOne_not_based : constantNegOne 1 ≠ 1 :=
  Circle.neg_ne_self (1 : Circle)

private theorem constantNegOne_degree : Circle.degree constantNegOne = 0 := by
  have hm : FundamentalGroup.map constantNegOne 1
      (FundamentalGroup.fromPath ⟦Circle.loop 1⟧) =
        (1 : FundamentalGroup Circle (constantNegOne 1)) := by
    change Path.Homotopic.Quotient.mk ((Circle.loop 1).map constantNegOne.continuous) =
      Path.Homotopic.Quotient.mk (Path.refl (-1))
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    rfl
  rw [Circle.degree_def, Circle.fundamentalGroupEquivInt_symm_apply, hm]
  simp only [map_one]
  rfl

private def rotation : C(Circle, Circle) :=
  -(ContinuousMap.id Circle)

private theorem rotation_not_based : rotation 1 ≠ 1 :=
  Circle.neg_ne_self (1 : Circle)

private theorem rotation_no_fixedPoint : ¬ ∃ z : Circle, rotation z = z := by
  rintro ⟨z, hz⟩
  exact Circle.neg_ne_self z hz

private theorem mapSquare_coordinate (a : Path (mapSquare 1) 1) :
    Circle.fundamentalGroupEquivInt
        (FundamentalGroup.fundamentalGroupMulEquivOfPath a
          (FundamentalGroup.map mapSquare 1
            (Circle.fundamentalGroupEquivInt.symm (Multiplicative.ofAdd (-3))))) =
      Multiplicative.ofAdd (-6) := by
  norm_num only [Circle.fundamentalGroupEquivInt_map, mapSquare_degree]

private theorem mapSquare_comp_degree :
    Circle.degree (mapSquare.comp mapSquare) = 4 := by
  norm_num only [Circle.degree_comp, mapSquare_degree]

private theorem inversion_degree :
    Circle.degree ((ContinuousMap.id Circle) ^ (-1 : ℤ)) = -1 :=
  Circle.degree_zpow (-1)

private theorem constantNegOne_homotopic_zpow_zero :
    constantNegOne.Homotopic ((ContinuousMap.id Circle) ^ (0 : ℤ)) := by
  apply (Circle.homotopic_iff_degree_eq _ _).mpr
  exact (Circle.degree_const (-1)).trans (Circle.degree_zpow 0).symm

private theorem mapSquare_not_homotopic_id :
    ¬ mapSquare.Homotopic (ContinuousMap.id Circle) := by
  intro h
  apply mapSquare_degree_ne_one
  exact ((Circle.homotopic_iff_degree_eq _ _).mp h).trans Circle.degree_id

private theorem mapSquare_has_fixedPoint : ∃ z : Circle, mapSquare z = z :=
  Circle.exists_fixedPoint_of_degree_ne_one mapSquare mapSquare_degree_ne_one

private def rotationHomotopy : rotation.Homotopy (ContinuousMap.id Circle) where
  toFun q := Circle.path (-1) 1 q.1 * q.2
  continuous_toFun :=
    ((Circle.path (-1) 1).continuous.comp continuous_fst).mul continuous_snd
  map_zero_left z := by
    change Circle.path (-1) 1 0 * z = -z
    rw [(Circle.path (-1) 1).source, neg_mul, one_mul]
  map_one_left z := by
    change Circle.path (-1) 1 1 * z = z
    rw [(Circle.path (-1) 1).target, one_mul]

private theorem degree_one_fixedPoint_examples :
    Circle.degree (ContinuousMap.id Circle) = 1 ∧
      (∃ z : Circle, ContinuousMap.id Circle z = z) ∧
      Circle.degree rotation = 1 ∧ ¬ ∃ z : Circle, rotation z = z := by
  refine ⟨Circle.degree_id, ⟨1, rfl⟩, ?_, rotation_no_fixedPoint⟩
  exact (Circle.degree_eq_of_homotopic ⟨rotationHomotopy⟩).trans Circle.degree_id

end SphereTopologyTest

end
