/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# Monodromy stabilizers and path components

For a covering map, the loops fixing a point of a fiber are exactly the image of the
fundamental group of the total space based at that point. Two points of a fiber lie in the
same monodromy orbit exactly when they are joined by a path in the total space.

These statements use Mathlib's covering maps, which need not be surjective. Unlike the
connected, locally path-connected setting of May's covering-space theory, no global
connectedness, local path-connectedness, or separation assumptions are needed here.

The monodromy and path-lifting constructions are those of Mathlib's prior formalization by
Junyan Xu in `Mathlib.Topology.Homotopy.Lifting`. In particular, the point stabilizer below
is not the kernel of the permutation representation for a general covering map. For quotient
coverings, Mathlib's `IsQuotientCoveringMap.monodromy_eq_id_iff` identifies these conditions,
and `IsQuotientCoveringMap.ker_monodromyPerm` already computes that kernel.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §§2–4,
  especially the monodromy discussion on p. 25.
* Junyan Xu, `Mathlib.Topology.Homotopy.Lifting`, for covering-space monodromy and lifting.
-/

@[expose] public section

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

namespace IsCoveringMap

variable (cov : IsCoveringMap p) {x : X}

set_option backward.isDefEq.respectTransparency.types false in
/-- A loop fixes a point of the fiber under monodromy if and only if it belongs to the image
of the fundamental group of the total space based at that point. This is the point-stabilizer
formulation of the covering-space correspondence in May, Chapter 3, §§2–4, without global
connectedness or local path-connectedness assumptions. No regularity of the covering is assumed. -/
theorem monodromy_eq_self_iff_mem_range (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    cov.monodromy γ e = e ↔
      γ ∈ (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.2).range := by
  constructor
  · intro h
    refine ⟨(cov.liftPathQuotient γ e).cast rfl (congrArg Subtype.val h.symm), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_cast,
      cov.map_liftPathQuotient]
    simp
  · rintro ⟨Γ, rfl⟩
    apply cov.monodromy_eq_of_map_eq Γ
    rw [FundamentalGroup.mapOfEq_apply]
    simp

/-- Two points of a fiber lie in the same monodromy orbit if and only if they are joined by a
path in the total space. This is the orbit formulation of the covering-space correspondence in
May, Chapter 3, §§2–4. If the total space is path-connected, this equivalence yields transitivity;
the equivalence itself needs no such assumption. -/
theorem exists_monodromy_eq_iff_joined (e e' : p ⁻¹' {x}) :
    (∃ γ : FundamentalGroup X x, cov.monodromy γ e = e') ↔ Joined e.1 e'.1 := by
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨Γ⟩ := cov.liftPathQuotient γ e
    exact ⟨Γ⟩
  · rintro ⟨Γ⟩
    let γ := (Path.Homotopic.Quotient.mk Γ).map ⟨p, cov.continuous⟩
    refine ⟨γ.cast e.2.symm e'.2.symm, cov.monodromy_eq_of_map_eq (.mk Γ) ?_⟩
    exact ((γ.cast_cast e.2.symm e'.2.symm e.2 e'.2).trans γ.cast_rfl_rfl).symm

end IsCoveringMap

namespace IsQuotientCoveringMap

variable {G : Type*} [Group G] [MulAction G E] (hp : IsQuotientCoveringMap p G) {x : X}

/-- For a quotient covering, fixing one point of a fiber under monodromy is equivalent to
acting trivially on the whole fiber. Thus the kernel of the monodromy representation is the
preimage of any point stabilizer. Combined with
`IsCoveringMap.monodromy_eq_self_iff_mem_range`, this recovers
`IsQuotientCoveringMap.ker_monodromyPerm`. -/
theorem ker_monodromyPerm_eq_comap_stabilizer (e : p ⁻¹' {x}) :
    (hp.isCoveringMap.monodromyPerm x).ker =
      (MulAction.stabilizer (Equiv.Perm (p ⁻¹' {x})) e).comap
        (hp.isCoveringMap.monodromyPerm x) := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  simpa only [DFunLike.ext'_iff, IsCoveringMap.coe_monodromyPerm, Equiv.Perm.coe_one,
    Equiv.Perm.smul_def] using hp.monodromy_eq_id_iff e (γ := γ)

end IsQuotientCoveringMap
