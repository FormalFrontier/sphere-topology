/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.CircleBouquet
public import Mathlib.Topology.Defs.Induced
import Mathlib.Logic.Equiv.Set

/-!
# Topology of circle-bouquet relabelings

The map `CircleBouquet.relabel` is a closed embedding exactly when its label
function is injective, and a quotient map exactly when its label function is
surjective. The closed-embedding proof factors through the image subfamily;
the quotient proof uses the final topology of the circle inclusions. Retractions
detect collisions and omitted labels using a point distinct from the common point.
Source and target ambient universes and label universes are independent; empty
and infinite label families are included.

## References

* The bouquet, its inclusions and retractions are those of
  `SphereTopology.Homotopy.CircleBouquet`.
* Mathlib supplies the topological colimit, map and homeomorphism APIs.
-/

@[expose] public section

universe u v u' w

namespace CircleBouquet

private theorem injective_of_injective_relabel {I : Type v} {J : Type w}
    (σ : I → J) (h : Function.Injective (relabel.{u, v, u', w} σ)) :
    Function.Injective σ := by
  intro i j hij
  by_contra hne
  have hp : inclusion.{u, v} i (-1) = inclusion.{u, v} j (-1) := h (by
    simp only [relabel_inclusion_apply, hij])
  have hr := congrArg (retraction.{u, v} i) hp
  have hi : retraction.{u, v} i (inclusion.{u, v} i (-1)) = (-1 : Circle) :=
    congrArg (fun f : C(Circle, Circle) ↦ f (-1)) (retraction_inclusion.{u, v} i)
  have hj : retraction.{u, v} i (inclusion.{u, v} j (-1)) = (1 : Circle) :=
    congrArg (fun f : C(Circle, Circle) ↦ f (-1))
      (retraction_inclusion_of_ne.{u, v} i j (Ne.symm hne))
  exact Circle.neg_ne_self (1 : Circle) (hi.symm.trans (hr.trans hj))

/-- The inverse of a bijective relabeling is the original inverse relabeling,
including when the ambient universes differ. -/
private noncomputable def relabelHomeomorph {I : Type v} {J : Type w} (e : I ≃ J) :
    space.{u, v} I ≃ₜ space.{u', w} J where
  toFun := relabel.{u, v, u', w} e
  invFun := relabel.{u', w, u, v} e.symm
  left_inv x := by
    have h : (relabel.{u', w, u, v} e.symm).comp (relabel.{u, v, u', w} e) =
        ContinuousMap.id (space.{u, v} I) := by
      rw [← relabel_comp, Equiv.symm_comp_self, relabel_id]
    exact congrArg (fun f : C(space.{u, v} I, space.{u, v} I) ↦ f x) h
  right_inv x := by
    have h : (relabel.{u, v, u', w} e).comp (relabel.{u', w, u, v} e.symm) =
        ContinuousMap.id (space.{u', w} J) := by
      rw [← relabel_comp, Equiv.self_comp_symm, relabel_id]
    exact congrArg (fun f : C(space.{u', w} J, space.{u', w} J) ↦ f x) h
  continuous_toFun := (relabel.{u, v, u', w} e).continuous
  continuous_invFun := (relabel.{u', w, u, v} e.symm).continuous

private theorem subfamilyInclusion_comp_relabel {I : Type v} {J : Type w}
    (S : Set J) (σ : I → S) :
    (subfamilyInclusion.{u', w} S).comp (relabel.{u, v, u', w} σ) =
      relabel.{u, v, u', w} (fun i ↦ (σ i).1) := by
  apply ContinuousMap.ext
  intro x
  exact congrFun (CircleBouquet.funext
    (f := (subfamilyInclusion.{u', w} S).comp (relabel.{u, v, u', w} σ))
    (g := relabel.{u, v, u', w} (fun i ↦ (σ i).1))
    (by
      intro i z
      simp only [ContinuousMap.comp_apply, relabel_inclusion_apply]
      exact congrArg (fun f : C(Circle, space.{u', w} J) ↦ f z)
        (subfamilyInclusion_inclusion.{u', w} S (σ i)))
    (by simp only [ContinuousMap.comp_apply, relabel_basepoint,
      subfamilyInclusion_basepoint])) x

private theorem relabel_eq_subfamilyInclusion_comp {I : Type v} {J : Type w}
    (σ : I → J) (hσ : Function.Injective σ) :
    relabel.{u, v, u', w} σ =
      (subfamilyInclusion.{u', w} (Set.range σ)).comp
        (relabel.{u, v, u', w} (Equiv.ofInjective σ hσ)) := by
  simpa only [Equiv.ofInjective_apply] using
    (subfamilyInclusion_comp_relabel.{u, v, u', w}
      (Set.range σ) (Equiv.ofInjective σ hσ)).symm

/-- Relabeling is a closed embedding exactly when the label function is injective. -/
theorem isClosedEmbedding_relabel_iff {I : Type v} {J : Type w} (σ : I → J) :
    Topology.IsClosedEmbedding (relabel.{u, v, u', w} σ) ↔ Function.Injective σ := by
  constructor
  · intro h
    exact injective_of_injective_relabel.{u, v, u', w} σ h.injective
  · intro hσ
    rw [relabel_eq_subfamilyInclusion_comp.{u, v, u', w} σ hσ]
    exact (isClosedEmbedding_subfamilyInclusion.{u', w} (Set.range σ)).comp
      (relabelHomeomorph.{u, v, u', w} (Equiv.ofInjective σ hσ)).isClosedEmbedding

/-- Relabeling hits every point exactly when it hits every circle label. The common
point is hit even when the label family is empty. -/
theorem surjective_relabel_iff {I : Type v} {J : Type w} (σ : I → J) :
    Function.Surjective (relabel.{u, v, u', w} σ) ↔ Function.Surjective σ := by
  classical
  constructor
  · intro h j
    by_contra hj
    have hσ (i : I) : σ i ≠ j := fun he ↦ hj ⟨i, he⟩
    have hconstant :
        (fun x : space.{u, v} I ↦ retraction.{u', w} j (relabel.{u, v, u', w} σ x)) =
          fun _ ↦ (1 : Circle) := by
      apply CircleBouquet.funext.{u, v}
      · intro i z
        rw [relabel_inclusion_apply]
        exact congrArg (fun k : C(Circle, Circle) ↦ k z)
          (retraction_inclusion_of_ne.{u', w} j (σ i) (hσ i))
      · simp only [relabel_basepoint, retraction_basepoint]
    obtain ⟨x, hx⟩ := h (inclusion.{u', w} j (-1))
    have hneg : retraction.{u', w} j (inclusion.{u', w} j (-1)) = (-1 : Circle) :=
      congrArg (fun k : C(Circle, Circle) ↦ k (-1)) (retraction_inclusion.{u', w} j)
    exact Circle.neg_ne_self (1 : Circle)
      (hneg.symm.trans ((congrArg (retraction.{u', w} j) hx.symm).trans
        (congrFun hconstant x)))
  · intro hσ y
    rcases eq_basepoint_or_exists_inclusion.{u', w} y with rfl | ⟨j, z, rfl⟩
    · exact ⟨basepoint.{u, v} I, relabel_basepoint.{u, v, u', w} σ⟩
    · obtain ⟨i, rfl⟩ := hσ j
      exact ⟨inclusion.{u, v} i z, relabel_inclusion_apply.{u, v, u', w} σ i z⟩

/-- Relabeling is a quotient map exactly when the label function is surjective. -/
theorem isQuotientMap_relabel_iff {I : Type v} {J : Type w} (σ : I → J) :
    Topology.IsQuotientMap (relabel.{u, v, u', w} σ) ↔ Function.Surjective σ := by
  constructor
  · intro h
    exact (surjective_relabel_iff.{u, v, u', w} σ).1 h.surjective
  · intro hσ
    refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen ?_,
      (surjective_relabel_iff.{u, v, u', w} σ).2 hσ⟩
    intro V
    constructor
    · intro hV
      apply (isOpen_iff.{u', w} V).2
      intro j
      obtain ⟨i, rfl⟩ := hσ j
      have he : inclusion.{u, v} i ⁻¹' (relabel.{u, v, u', w} σ ⁻¹' V) =
          inclusion.{u', w} (σ i) ⁻¹' V := by
        ext z
        simp only [Set.mem_preimage, relabel_inclusion_apply]
      rw [← he]
      exact hV.preimage (inclusion.{u, v} i).continuous
    · intro hV
      exact hV.preimage (relabel.{u, v, u', w} σ).continuous

end CircleBouquet
