/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Tactic.NormNum
import GroupTheory.Subgroup.IndexTwo
public import SphereTopology.Geometry.Projectivization
public import SphereTopology.Homotopy.Sphere
public import FundamentalGroupoids.Topology.Covering.Monodromy
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Two-element coordinates for real projective fundamental groups

For a real normed space `E` with `2 < Module.rank ℝ E`, a chosen unit vector over a
projective basepoint specifies a coordinate on its fundamental group with values
in `Multiplicative (ZMod 2)`. The construction uses the unit sphere for the given
norm, its scalar-action quotient covering, and simple connectivity of that sphere.
It applies to arbitrary universes and infinite rank as well as finite rank; no
inner product or completeness assumption is imposed.

The coordinate is normalized by the endpoint of a lifted loop: the identity
corresponds to returning to the chosen unit vector, and
`Multiplicative.ofAdd (1 : ZMod 2)` corresponds to reaching its antipode. The latter
is not the multiplicative identity, which is `Multiplicative.ofAdd (0 : ZMod 2)`.

## Implementation notes

Mathlib's quotient-covering equivalence takes values in the opposite of the real
unit-sphere group. We remove the opposite using `MulOpposite.opMulEquiv.symm`,
whose function is `unop`, without inverting the endpoint label. The two-element
dictionary is the inverse of `zmodMulEquivOfGenerator` with generator `-1`.
Fundamental Groupoids supplies the equivalence and represented-path endpoint laws.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, revised author edition,
  Chapter 3, §2, p. 22, for the finite Euclidean projective-space calculation.
  The formulation here extends it to real normed spaces with their original norm
  and cardinal rank greater than two, including infinite rank.
* Junyan Xu's covering-space monodromy formalization in
  `Mathlib.Topology.Homotopy.Lifting`, Mathlib's quotient-covering and explicit
  cyclic-generator equivalences, and its unit-sphere scalar action.
* `FundamentalGroupoids.Topology.Covering.Monodromy`, for the characteristic laws
  of the quotient-covering equivalence and endpoints of continuous lifts.
-/

@[expose] public section

universe u

namespace Projectivization

private theorem realUnitSphere_eq_one_or_neg_one (g : Metric.sphere (0 : ℝ) 1) :
    g = 1 ∨ g = -1 := by
  have hg : (g : ℝ) = -1 ∨ (g : ℝ) = 1 := by
    simpa only [Real.sphere_eq_pair (0 : ℝ) (r := 1) zero_le_one,
      zero_sub, zero_add, Set.mem_insert_iff, Set.mem_singleton_iff] using g.property
  rcases hg with hg | hg
  · exact Or.inr (Subtype.ext hg)
  · exact Or.inl (Subtype.ext hg)

private theorem realUnitSphere_neg_one_ne_one :
    (-1 : Metric.sphere (0 : ℝ) 1) ≠ 1 := by
  intro h
  have hreal : (-1 : ℝ) = 1 :=
    congrArg (fun g : Metric.sphere (0 : ℝ) 1 => (g : ℝ)) h
  norm_num at hreal

private theorem realUnitSphere_card : Nat.card (Metric.sphere (0 : ℝ) 1) = 2 := by
  apply (Nat.card_eq_two_iff' (1 : Metric.sphere (0 : ℝ) 1)).mpr
  refine ⟨(-1 : Metric.sphere (0 : ℝ) 1), realUnitSphere_neg_one_ne_one, ?_⟩
  intro g hg
  rcases realUnitSphere_eq_one_or_neg_one g with h | h
  · exact (hg h).elim
  · exact h

private theorem realUnitSphere_mem_zpowers_neg_one (g : Metric.sphere (0 : ℝ) 1) :
    g ∈ Subgroup.zpowers (-1 : Metric.sphere (0 : ℝ) 1) :=
  mem_zpowers_of_prime_card realUnitSphere_card realUnitSphere_neg_one_ne_one

/-- The fundamental group of real projective space, at a supplied basepoint and
chosen unit lift, in two-element coordinates.

This is the composition of Mathlib's quotient-covering equivalence, removal of
the opposite group by `unop`, and the inverse cyclic-generator equivalence sending
`-1` to `Multiplicative.ofAdd (1 : ZMod 2)`. Simple connectivity is supplied by
`simplyConnectedSpace_unitSphere hRank`; it is not an additional hypothesis.
The endpoint interface uses Fundamental Groupoids' monodromy characteristic laws.

For finite Euclidean spaces this is May, *A Concise Course in Algebraic Topology*,
Chapter 3, §2, p. 22. The formulation uses the original norm and extends to arbitrary
real normed spaces of cardinal rank greater than two, including infinite rank. -/
noncomputable def fundamentalGroupEquivZModTwo
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hRank : 2 < Module.rank ℝ E) (b : Projectivization ℝ E)
    (e : (Metric.Sphere.toProjectivization (E := E)) ⁻¹' {b}) :
    FundamentalGroup (Projectivization ℝ E) b ≃* Multiplicative (ZMod 2) := by
  letI : SimplyConnectedSpace (Metric.sphere (0 : E) 1) :=
    simplyConnectedSpace_unitSphere hRank
  exact
    (((Metric.Sphere.isQuotientCoveringMap_toProjectivization (E := E)).fundamentalGroupEquiv
      e).trans (MulOpposite.opMulEquiv :
        Metric.sphere (0 : ℝ) 1 ≃* (Metric.sphere (0 : ℝ) 1)ᵐᵒᵖ).symm).trans
      (zmodMulEquivOfGenerator (g := (-1 : Metric.sphere (0 : ℝ) 1))
        (by exact realUnitSphere_mem_zpowers_neg_one) (by exact realUnitSphere_card)).symm

/-- The two-element coordinate does not depend on the chosen unit lift of the
projective basepoint. The lift argument fixes the endpoint description, not a
sign choice in the resulting coordinate. -/
theorem fundamentalGroupEquivZModTwo_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hRank : 2 < Module.rank ℝ E) (b : Projectivization ℝ E)
    (e e' : (Metric.Sphere.toProjectivization (E := E)) ⁻¹' {b}) :
    fundamentalGroupEquivZModTwo hRank b e = fundamentalGroupEquivZModTwo hRank b e' := by
  let f := fundamentalGroupEquivZModTwo hRank b e
  let g := fundamentalGroupEquivZModTwo hRank b e'
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.ker_injective_of_card_eq_two (by simp [Nat.card_eq_fintype_card])
  exact (f.toMonoidHom.ker_eq_bot f.injective).trans
    (g.toMonoidHom.ker_eq_bot g.injective).symm

private theorem fundamentalGroupEquivZModTwo_apply_eq_iff_liftPath
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hRank : 2 < Module.rank ℝ E) (b : Projectivization ℝ E)
    (e : (Metric.Sphere.toProjectivization (E := E)) ⁻¹' {b}) (γ : Path b b)
    (z : Multiplicative (ZMod 2)) :
    fundamentalGroupEquivZModTwo hRank b e
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = z ↔
      (Metric.Sphere.isQuotientCoveringMap_toProjectivization (E := E)).isCoveringMap.liftPath
        γ.toContinuousMap e.1 (γ.source.trans e.2.symm) 1 =
          zmodMulEquivOfGenerator (g := (-1 : Metric.sphere (0 : ℝ) 1))
            realUnitSphere_mem_zpowers_neg_one realUnitSphere_card z • e.1 := by
  let : SimplyConnectedSpace (Metric.sphere (0 : E) 1) :=
    simplyConnectedSpace_unitSphere hRank
  let hp := Metric.Sphere.isQuotientCoveringMap_toProjectivization (E := E)
  have hmonodromy := hp.isCoveringMap.monodromy_mk_apply_eq_of_lift γ e
    (hp.isCoveringMap.liftPath γ.toContinuousMap e.1 (γ.source.trans e.2.symm))
    (hp.isCoveringMap.liftPath_lifts γ.toContinuousMap e.1 (γ.source.trans e.2.symm))
    (hp.isCoveringMap.liftPath_zero γ.toContinuousMap e.1 (γ.source.trans e.2.symm))
  unfold fundamentalGroupEquivZModTwo
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq,
    MulEquiv.symm_apply_eq]
  exact
    (hp.fundamentalGroupEquiv_apply_eq_iff e
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) _).trans
      (by rw [hmonodromy]; exact eq_comm)

/-- A loop has identity coordinate exactly when its covering lift starting at the
chosen unit vector returns to that vector. -/
theorem fundamentalGroupEquivZModTwo_apply_eq_one_iff
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hRank : 2 < Module.rank ℝ E) (b : Projectivization ℝ E)
    (e : (Metric.Sphere.toProjectivization (E := E)) ⁻¹' {b}) (γ : Path b b) :
    fundamentalGroupEquivZModTwo hRank b e
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = 1 ↔
      (Metric.Sphere.isQuotientCoveringMap_toProjectivization (E := E)).isCoveringMap.liftPath
        γ.toContinuousMap e.1 (γ.source.trans e.2.symm) 1 = e.1 := by
  simpa only [map_one, one_smul] using
    fundamentalGroupEquivZModTwo_apply_eq_iff_liftPath hRank b e γ 1

/-- A loop has coordinate `Multiplicative.ofAdd (1 : ZMod 2)` exactly when its
covering lift starting at the chosen unit vector ends at its antipode. -/
theorem fundamentalGroupEquivZModTwo_apply_eq_ofAdd_one_iff
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hRank : 2 < Module.rank ℝ E) (b : Projectivization ℝ E)
    (e : (Metric.Sphere.toProjectivization (E := E)) ⁻¹' {b}) (γ : Path b b) :
    fundamentalGroupEquivZModTwo hRank b e
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
          Multiplicative.ofAdd (1 : ZMod 2) ↔
      (Metric.Sphere.isQuotientCoveringMap_toProjectivization (E := E)).isCoveringMap.liftPath
        γ.toContinuousMap e.1 (γ.source.trans e.2.symm) 1 = -e.1 := by
  have hgenerator :
      zmodMulEquivOfGenerator (g := (-1 : Metric.sphere (0 : ℝ) 1))
          realUnitSphere_mem_zpowers_neg_one realUnitSphere_card
          (Multiplicative.ofAdd (1 : ZMod 2)) = (-1 : Metric.sphere (0 : ℝ) 1) := by
    simpa only [Int.cast_one, zpow_one] using
      (zmodMulEquivOfGenerator_apply_ofAdd_intCast
        (g := (-1 : Metric.sphere (0 : ℝ) 1))
        realUnitSphere_mem_zpowers_neg_one realUnitSphere_card (1 : ℤ))
  have hsmul : (-1 : Metric.sphere (0 : ℝ) 1) • e.1 = -e.1 := by
    apply Subtype.ext
    change ((-1 : Metric.sphere (0 : ℝ) 1) : ℝ) • (e.1 : E) = -(e.1 : E)
    simp
  simpa only [hgenerator, hsmul] using
    fundamentalGroupEquivZModTwo_apply_eq_iff_liftPath hRank b e γ
      (Multiplicative.ofAdd (1 : ZMod 2))

/-- The identity coordinate is characterized by the endpoint of any continuous
lift of the loop that starts at the chosen unit vector. -/
theorem fundamentalGroupEquivZModTwo_apply_eq_one_iff_of_lift
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hRank : 2 < Module.rank ℝ E) (b : Projectivization ℝ E)
    (e : (Metric.Sphere.toProjectivization (E := E)) ⁻¹' {b}) (γ : Path b b)
    (Γ : C(unitInterval, Metric.sphere (0 : E) 1))
    (hΓ : (Metric.Sphere.toProjectivization (E := E)) ∘ Γ = γ) (h0 : Γ 0 = e.1) :
    fundamentalGroupEquivZModTwo hRank b e
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = 1 ↔
      Γ 1 = e.1 := by
  have hLift : Γ =
      (Metric.Sphere.isQuotientCoveringMap_toProjectivization (E := E)).isCoveringMap.liftPath
        γ.toContinuousMap e.1 (γ.source.trans e.2.symm) :=
    (IsCoveringMap.eq_liftPath_iff'
      (Metric.Sphere.isQuotientCoveringMap_toProjectivization (E := E)).isCoveringMap
      (γ.source.trans e.2.symm)).mpr ⟨hΓ, h0⟩
  rw [fundamentalGroupEquivZModTwo_apply_eq_one_iff hRank b e γ, ← hLift]

/-- The coordinate `Multiplicative.ofAdd (1 : ZMod 2)` is characterized by the
antipodal endpoint of any continuous lift starting at the chosen unit vector. -/
theorem fundamentalGroupEquivZModTwo_apply_eq_ofAdd_one_iff_of_lift
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hRank : 2 < Module.rank ℝ E) (b : Projectivization ℝ E)
    (e : (Metric.Sphere.toProjectivization (E := E)) ⁻¹' {b}) (γ : Path b b)
    (Γ : C(unitInterval, Metric.sphere (0 : E) 1))
    (hΓ : (Metric.Sphere.toProjectivization (E := E)) ∘ Γ = γ) (h0 : Γ 0 = e.1) :
    fundamentalGroupEquivZModTwo hRank b e
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
          Multiplicative.ofAdd (1 : ZMod 2) ↔
      Γ 1 = -e.1 := by
  have hLift : Γ =
      (Metric.Sphere.isQuotientCoveringMap_toProjectivization (E := E)).isCoveringMap.liftPath
        γ.toContinuousMap e.1 (γ.source.trans e.2.symm) :=
    (IsCoveringMap.eq_liftPath_iff'
      (Metric.Sphere.isQuotientCoveringMap_toProjectivization (E := E)).isCoveringMap
      (γ.source.trans e.2.symm)).mpr ⟨hΓ, h0⟩
  rw [fundamentalGroupEquivZModTwo_apply_eq_ofAdd_one_iff hRank b e γ, ← hLift]

/-- Projecting a sphere path from the chosen unit vector to its antipode gives a
loop of coordinate `Multiplicative.ofAdd (1 : ZMod 2)`. The endpoint casts use the
supplied basepoint equality and invariance of the projection under negation. -/
theorem fundamentalGroupEquivZModTwo_map_path_neg
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hRank : 2 < Module.rank ℝ E) (b : Projectivization ℝ E)
    (e : (Metric.Sphere.toProjectivization (E := E)) ⁻¹' {b}) (Γ : Path e.1 (-e.1)) :
    fundamentalGroupEquivZModTwo hRank b e
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((Γ.map (Metric.Sphere.toProjectivization (E := E)).continuous).cast
            e.2.symm ((Metric.Sphere.toProjectivization_neg e.1).trans e.2).symm))) =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  exact
    (fundamentalGroupEquivZModTwo_apply_eq_ofAdd_one_iff_of_lift hRank b e
      ((Γ.map (Metric.Sphere.toProjectivization (E := E)).continuous).cast
        e.2.symm ((Metric.Sphere.toProjectivization_neg e.1).trans e.2).symm)
      Γ.toContinuousMap rfl Γ.source).mpr Γ.target

end Projectivization
