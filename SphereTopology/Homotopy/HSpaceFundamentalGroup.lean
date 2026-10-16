/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.HSpaces
import all Mathlib.Topology.Homotopy.HSpaces
public import Mathlib.Topology.Homotopy.Product
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Pointwise multiplication of loops in an H-space

Pointwise H-space multiplication gives a loop at the H-space unit. The endpoint
identification uses `HSpace.hmul_e_e`; no path between distinct basepoints is
chosen. The underlying path and its extensionality principle are Mathlib's
`Path` and `Path.ext`.

The pointwise product is based-homotopic to chronological concatenation. The
relative unit homotopies suffice: multiplication need not be associative or
commutative, and the unit laws need not hold as equalities. The two orders of
concatenation are homotopic, so the fundamental group at the unit is commutative.
Mathlib's fundamental-group multiplication reverses chronological concatenation;
thus the class of `loopMul p q` is `[q] * [p]`.

For continuous multiplication with a strict unit, `HSpace.loopMul_toHSpace`
identifies the construction for `IsTopologicalGroup.toHSpace` with `Path.mul`
and its canonical endpoint casts.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 1, Problem 3.
* `Mathlib.Topology.Homotopy.HSpaces` for H-spaces and their relative unit homotopies.
* `Mathlib.Topology.Path` for path products, continuous images, and endpoint casts.
* `Mathlib.Topology.Homotopy.Product` and
  `Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic` for product and concatenation homotopies.
-/

@[expose] public section

universe u

namespace HSpace

variable {X : Type u} [TopologicalSpace X] [HSpace X]

/-- Pointwise H-space multiplication of loops at the H-space unit. -/
def loopMul (p q : Path (HSpace.e : X) HSpace.e) :
    Path (HSpace.e : X) HSpace.e :=
  ((p.prod q).map HSpace.hmul.continuous).cast
    HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm

/-- Evaluation of pointwise loop multiplication is H-space multiplication. -/
@[simp]
theorem loopMul_apply (p q : Path (HSpace.e : X) HSpace.e) (t : unitInterval) :
    loopMul p q t = HSpace.hmul (p t, q t) := rfl

/-- Pointwise multiplication of two constant unit loops is the constant unit loop. -/
@[simp]
theorem loopMul_refl_refl :
    loopMul (Path.refl (HSpace.e : X)) (Path.refl (HSpace.e : X)) =
      Path.refl (HSpace.e : X) := by
  ext t
  simp only [loopMul_apply, Path.refl_apply, HSpace.hmul_e_e]

-- Restrict a homotopy fixed at the basepoint to a loop. The endpoint casts use
-- the equality at that basepoint supplied by the relative homotopy itself.
private noncomputable def homotopyRelAlongLoop {A : Type u} [TopologicalSpace A]
    {x : A} {f : C(A, A)}
    (F : f.HomotopyRel (ContinuousMap.id A) {x}) (p : Path x x) :
    Path.Homotopy
      ((p.map f.continuous).cast
        (F.fst_eq_snd (by simp)).symm (F.fst_eq_snd (by simp)).symm) p where
  toFun z := F (z.1, p z.2)
  continuous_toFun :=
    F.continuous.comp (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  map_zero_left t := F.apply_zero (p t)
  map_one_left t := F.apply_one (p t)
  prop' t s hs := by
    change F (t, p s) = f (p s)
    have hp : p s = x := by
      rcases hs with hs | hs
      · simpa only [hs] using p.source
      · rw [Set.mem_singleton_iff] at hs
        simpa only [hs] using p.target
    rw [hp]
    exact F.eq_fst t (by simp)

private theorem loopMul_refl_right_homotopic (p : Path (HSpace.e : X) HSpace.e) :
    Path.Homotopic (loopMul p (Path.refl HSpace.e)) p := by
  refine ⟨(homotopyRelAlongLoop HSpace.hmulE p).cast ?_ rfl⟩
  ext t
  rfl

private theorem loopMul_refl_left_homotopic (p : Path (HSpace.e : X) HSpace.e) :
    Path.Homotopic (loopMul (Path.refl HSpace.e) p) p := by
  refine ⟨(homotopyRelAlongLoop HSpace.eHmul p).cast ?_ rfl⟩
  ext t
  rfl

private theorem loopMul_homotopic
    {p p' q q' : Path (HSpace.e : X) HSpace.e}
    (hp : Path.Homotopic p p') (hq : Path.Homotopic q q') :
    Path.Homotopic (loopMul p q) (loopMul p' q') := by
  rcases hp with ⟨hp⟩
  rcases hq with ⟨hq⟩
  exact ⟨((Path.Homotopic.prodHomotopy hp hq).map HSpace.hmul).pathCast
    HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm⟩

-- Pointwise multiplication has strict interchange with simultaneous
-- concatenation, even though its unit laws hold only up to homotopy.
private theorem loopMul_trans (p q r s : Path (HSpace.e : X) HSpace.e) :
    loopMul (p.trans q) (r.trans s) = (loopMul p r).trans (loopMul q s) := by
  dsimp only [loopMul]
  rw [← Path.trans_prod_eq_prod_trans, Path.map_trans]
  exact Path.cast_trans _ _ HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm
    HSpace.hmul_e_e.symm

/-- Pointwise multiplication of loops at the H-space unit is based-homotopic
to chronological concatenation. This generalizes the topological-group comparison
in May, Chapter 1, Problem 3, using only the relative H-space unit laws. -/
theorem loopMul_homotopic_trans (p q : Path (HSpace.e : X) HSpace.e) :
    Path.Homotopic (loopMul p q) (p.trans q) := by
  -- In the product, traverse p in the first half and q in the second half.
  have h := loopMul_homotopic (Path.Homotopic.trans_refl p).symm
    (Path.Homotopic.refl_trans q).symm
  rw [loopMul_trans] at h
  exact h.trans ((loopMul_refl_right_homotopic p).hcomp
    (loopMul_refl_left_homotopic q))

private theorem loopMul_homotopic_trans_reverse
    (p q : Path (HSpace.e : X) HSpace.e) :
    Path.Homotopic (loopMul p q) (q.trans p) := by
  -- The other L-shaped detour traverses q first, without commuting hmul.
  have h := loopMul_homotopic (Path.Homotopic.refl_trans p).symm
    (Path.Homotopic.trans_refl q).symm
  rw [loopMul_trans] at h
  exact h.trans ((loopMul_refl_left_homotopic q).hcomp
    (loopMul_refl_right_homotopic p))

section StrictUnit

variable {M : Type u} [TopologicalSpace M] [MulOneClass M] [ContinuousMul M]

private theorem toHSpace_hmul_apply (x y : M) :
    @HSpace.hmul M _ (IsTopologicalGroup.toHSpace M) (x, y) = x * y := rfl

/-- For the H-space structure from continuous multiplication with a strict unit,
pointwise loop multiplication agrees with `Path.mul` after casting its endpoints. -/
theorem loopMul_toHSpace (p q : Path (1 : M) 1) :
    @loopMul M _ (IsTopologicalGroup.toHSpace M) p q =
      (p.mul q).cast (one_mul (1 : M)).symm (one_mul (1 : M)).symm := by
  apply DFunLike.ext _ _
  intro t
  exact (@loopMul_apply M _ (IsTopologicalGroup.toHSpace M) p q t).trans
    (toHSpace_hmul_apply (p t) (q t))

end StrictUnit

end HSpace

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X] [HSpace X]

/-- The class of the pointwise product is the reversed product of classes,
because fundamental-group multiplication reverses chronological concatenation. -/
theorem fromPath_loopMul (p q : Path (HSpace.e : X) HSpace.e) :
    (fromPath (Path.Homotopic.Quotient.mk (HSpace.loopMul p q)) :
      FundamentalGroup X (HSpace.e : X)) =
      fromPath (Path.Homotopic.Quotient.mk q) *
        fromPath (Path.Homotopic.Quotient.mk p) :=
  Path.Homotopic.Quotient.eq.mpr (HSpace.loopMul_homotopic_trans p q)

/-- The fundamental group at an H-space unit is commutative. This generalizes
the topological-group conclusion in May, Chapter 1, Problem 3. -/
theorem mul_comm (a b : FundamentalGroup X (HSpace.e : X)) : a * b = b * a := by
  induction a, b using Path.Homotopic.Quotient.ind₂ with
  | mk p q =>
    exact Path.Homotopic.Quotient.eq.mpr
      ((HSpace.loopMul_homotopic_trans_reverse p q).symm.trans
        (HSpace.loopMul_homotopic_trans p q))

/-- Commutativity of the existing fundamental-group multiplication at an H-space
unit; the group data is unchanged. -/
instance isMulCommutative : IsMulCommutative (FundamentalGroup X (HSpace.e : X)) :=
  IsMulCommutative.of_comm mul_comm

end FundamentalGroup

namespace Path

variable {M : Type u} [TopologicalSpace M] [MulOneClass M] [ContinuousMul M]

/-- Pointwise multiplication of loops at `1` is based-homotopic to chronological
concatenation. This is the comparison in May, Chapter 1, Problem 3, without an
associativity or inverse assumption. -/
theorem mul_homotopic_trans (p q : Path (1 : M) 1) :
    Homotopic ((p.mul q).cast (one_mul (1 : M)).symm (one_mul (1 : M)).symm)
      (p.trans q) := by
  simpa only [HSpace.loopMul_toHSpace] using
    (@HSpace.loopMul_homotopic_trans M _ (IsTopologicalGroup.toHSpace M) p q)

end Path

namespace FundamentalGroup

variable {M : Type u} [TopologicalSpace M] [MulOneClass M] [ContinuousMul M]

/-- Continuous multiplication with a strict unit makes the fundamental group at
`1` commutative, generalizing the topological-group conclusion in May, Chapter 1,
Problem 3. No associativity or inverse law is required; the existing group data is
unchanged. -/
instance isMulCommutative_one : IsMulCommutative (FundamentalGroup M (1 : M)) :=
  @FundamentalGroup.isMulCommutative M _ (IsTopologicalGroup.toHSpace M)

end FundamentalGroup
