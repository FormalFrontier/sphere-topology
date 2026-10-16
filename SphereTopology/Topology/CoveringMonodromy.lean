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

Continuous maps over a common base intertwine monodromy. The proof generalizes the
lifted-path-class argument of Mathlib's `IsQuotientCoveringMap.monodromy_toPermFiber`;
`IsQuotientCoveringMap.monodromy_naturality_toPermFiber` recovers its quotient-action
formula. Over a path-connected base, continuous maps out of a covering space are determined
by their values on one whole fiber when the target projection is separated and locally
injective. This uniqueness requires no local path connectedness.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §§2–4,
  especially the monodromy discussion on p. 25.
* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §7, p. 29,
  for uniqueness of maps of covering spaces from their restrictions to a fiber.
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

section Maps

universe u v w

variable {E : Type u} {E' : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : E → B} {q : E' → B}

namespace IsCoveringMap

/-- Monodromy is natural for continuous maps between covering spaces over the same base.
This uses the lifted homotopy class of a path, without connectivity hypotheses. -/
theorem monodromy_naturality (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (f : C(E, E')) (hf : q ∘ f = p) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    covq.monodromy γ ⟨f e, (congr_fun hf e).trans e.2⟩ =
      ⟨f (covp.monodromy γ e),
        (congr_fun hf (covp.monodromy γ e)).trans (covp.monodromy γ e).2⟩ := by
  let Γ := covp.liftPathQuotient γ e
  let p' : C(E, B) := ⟨p, covp.continuous⟩
  let q' : C(E', B) := ⟨q, covq.continuous⟩
  have hcomp : q'.comp f = p' := ContinuousMap.ext fun z ↦ congr_fun hf z
  apply covq.monodromy_eq_of_map_eq (Γ.map f)
  rw [← Path.Homotopic.Quotient.map_comp]
  convert covp.map_liftPathQuotient γ e using 2
  · exact congr_fun hf e
  · exact congr_fun hf (covp.monodromy γ e)
  · grind

/-- Continuous maps over a path-connected base from a covering space to a separated,
locally injective map agree everywhere if they agree on one whole fiber. Every path component
of the source meets that fiber, and uniqueness of lifts applies on each component. No local
path connectedness, total-space connectedness, nonemptiness, or surjectivity is required. -/
theorem eq_of_comp_eq_of_eqOn_fiber (covp : IsCoveringMap p) (hsep : IsSeparatedMap q)
    (hinj : IsLocallyInjective q) [PathConnectedSpace B] (f g : C(E, E'))
    (hf : q ∘ f = p) (hg : q ∘ g = p) (b : B)
    (h : ∀ e : p ⁻¹' {b}, f e = g e) : f = g := by
  ext e
  obtain ⟨a, ha⟩ := covp.comp_subtypeVal_pathComponent_surjective e b
  exact hsep.eqOn_of_comp_eqOn hinj isPathConnected_pathComponent.isConnected.isPreconnected
    f.continuous.continuousOn g.continuous.continuousOn
    (fun z _ ↦ congr_fun (hf.trans hg.symm) z) a.property (h ⟨a, ha⟩)
    (mem_pathComponent_self e)

end IsCoveringMap

end Maps

namespace IsQuotientCoveringMap

variable {G : Type*} [Group G] [MulAction G E] (hp : IsQuotientCoveringMap p G) {x : X}

/-- Naturality for the continuous action defining a quotient covering recovers the
`IsQuotientCoveringMap.monodromy_toPermFiber` formula. Thus the naturality statement for
arbitrary covering maps specializes to the quotient-covering commutation law. -/
theorem monodromy_naturality_toPermFiber {y : X} (γ : Path.Homotopic.Quotient x y)
    (g : G) (e : p ⁻¹' {x}) :
    hp.isCoveringMap.monodromy γ (hp.toPermFiber x g e) =
      hp.toPermFiber y g (hp.isCoveringMap.monodromy γ e) := by
  exact hp.isCoveringMap.monodromy_naturality hp.isCoveringMap
    ⟨fun z ↦ g • z, hp.toContinuousConstSMul.continuous_const_smul g⟩
    (funext fun _ ↦ hp.map_smul g) γ e

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
