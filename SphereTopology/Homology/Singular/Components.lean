/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Nonbasepoint path components and the degree-zero augmentation

For a space `X`, coefficients `R`, and a point `x : X`, the coproduct of copies
of `R` over the path components other than that of `x` maps to ordinary `H₀`.
Its generator at `c` is the difference of the `c` and basepoint-component
injections under Mathlib's `TopCat.singularHomology₀Iso`. This morphism is
exhibited as a kernel of the total augmentation, using `KernelFork.ofι` rather
than a separately chosen kernel object. No nonzero-coefficient, finiteness or
path-connectedness assumption is made.

The construction uses Mathlib's all-simplex singular homology with categorical
coefficients. It generalizes the integral nonbasepoint-component calculation;
it does not identify this model with based-relative or primed reduced homology,
normalized chains with tensor coefficients, or compactly generated weak Hausdorff
models.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapters 13 and 15, for
  the integral nonbasepoint-component description and comparison of homology
  theories. The model comparisons listed above are not supplied here.
* Joël Riou's Mathlib formalization of simplicial and singular homology in
  degree zero supplies the path-component coproduct and augmentation used here.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits AlgebraicTopology

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  [Preadditive C] [CategoryWithHomology C]

/-- The nonbasepoint-component generators of the augmentation kernel: the
summand at `c` maps to `[c] - [x]` in ordinary degree-zero homology. -/
noncomputable def singularHomologyZeroComponentInclusion
    (X : TopCat.{w}) (R : C) (x : X) :
    (∐ (fun _ : {c : ZerothHomotopy X // c ≠ .mk x} ↦ R)) ⟶
      ((singularHomologyFunctor C 0).obj R).obj X :=
  Sigma.desc (fun c ↦
    (Sigma.ι (fun _ : ZerothHomotopy X ↦ R) c.val -
      Sigma.ι (fun _ : ZerothHomotopy X ↦ R) (.mk x)) ≫
        (X.singularHomology₀Iso R).inv)

/-- Each generator has the sign nonbasepoint component minus basepoint
component. This equation determines the component inclusion by `Sigma.hom_ext`. -/
@[reassoc]
theorem ι_singularHomologyZeroComponentInclusion
    (X : TopCat.{w}) (R : C) (x : X)
    (c : {c : ZerothHomotopy X // c ≠ .mk x}) :
    Sigma.ι (fun _ : {c : ZerothHomotopy X // c ≠ .mk x} ↦ R) c ≫
        singularHomologyZeroComponentInclusion X R x =
      (Sigma.ι (fun _ : ZerothHomotopy X ↦ R) c.val -
        Sigma.ι (fun _ : ZerothHomotopy X ↦ R) (.mk x)) ≫
          (X.singularHomology₀Iso R).inv := by
  exact Sigma.ι_desc _ _

/-- Every component difference is annihilated by the total augmentation. -/
@[reassoc (attr := simp)]
theorem singularHomologyZeroComponentInclusion_augmentation
    (X : TopCat.{w}) (R : C) (x : X) :
    singularHomologyZeroComponentInclusion X R x ≫ X.singularHomology₀ε R = 0 := by
  apply Sigma.hom_ext
  intro c
  rw [ι_singularHomologyZeroComponentInclusion_assoc,
    ← singularHomology₀Iso_sigma_desc_id X R]
  simp only [Iso.inv_hom_id_assoc, Preadditive.sub_comp, Sigma.ι_desc,
    sub_self, comp_zero]

/-- The coproduct over nonbasepoint path components is a kernel of the total
augmentation. Thus the standard kernel-fork lifting and uniqueness APIs apply.
This is the categorical-coefficient form of the integral component calculation
in May, *A Concise Course in Algebraic Topology*, Chapters 13 and 15. -/
noncomputable def singularHomologyZeroComponentInclusionIsKernel
    (X : TopCat.{w}) (R : C) (x : X) :
    IsLimit (KernelFork.ofι (singularHomologyZeroComponentInclusion X R x)
      (singularHomologyZeroComponentInclusion_augmentation X R x)) := by
  classical
  let b : ZerothHomotopy X := .mk x
  let j : PUnit.{w + 1} → ZerothHomotopy X := fun _ ↦ b
  let e : ((Set.range j)ᶜ : Set _) ≃ {c : ZerothHomotopy X // c ≠ b} :=
    Equiv.subtypeEquivRight (fun c ↦ by simp [j])
  -- Use the existing complement-coproduct projection, reindexed by `c ≠ b`.
  let p : (∐ (fun _ : ZerothHomotopy X ↦ R)) ⟶
      ∐ (fun _ : {c : ZerothHomotopy X // c ≠ b} ↦ R) :=
    (sigmaConstCokernelCofork R j).π ≫
      (Sigma.reindex e (fun _ : {c : ZerothHomotopy X // c ≠ b} ↦ R)).hom
  have hp (c : ZerothHomotopy X) (hc : c ≠ b) :
      Sigma.ι (fun _ : ZerothHomotopy X ↦ R) c ≫ p =
        Sigma.ι (fun _ : {c : ZerothHomotopy X // c ≠ b} ↦ R) ⟨c, hc⟩ := by
    dsimp only [p]
    rw [ι_sigmaConstCokernelCofork_π_assoc R j c (by simpa [j, eq_comm] using hc)]
    exact Sigma.ι_reindex_hom e (fun _ : {c : ZerothHomotopy X // c ≠ b} ↦ R) _
  have hpb : Sigma.ι (fun _ : ZerothHomotopy X ↦ R) b ≫ p = 0 := by
    change Sigma.ι (fun _ : ZerothHomotopy X ↦ R) (j PUnit.unit) ≫
      (sigmaConstCokernelCofork R j).π ≫ _ = 0
    simp
  let ρ := (X.singularHomology₀Iso R).hom ≫ p
  let σ := Sigma.ι (fun _ : ZerothHomotopy X ↦ R) b ≫
    (X.singularHomology₀Iso R).inv
  have hδρ : singularHomologyZeroComponentInclusion X R x ≫ ρ = 𝟙 _ := by
    apply Sigma.hom_ext
    intro c
    rw [ι_singularHomologyZeroComponentInclusion_assoc]
    change (Sigma.ι (fun _ : ZerothHomotopy X ↦ R) c.val -
      Sigma.ι (fun _ : ZerothHomotopy X ↦ R) b) ≫
        (X.singularHomology₀Iso R).inv ≫ ((X.singularHomology₀Iso R).hom ≫ p) = _
    rw [Iso.inv_hom_id_assoc, Preadditive.sub_comp, hp c.val c.property, hpb,
      sub_zero, Category.comp_id]
  have hpδ : p ≫ singularHomologyZeroComponentInclusion X R x =
      (X.singularHomology₀Iso R).inv -
        Sigma.desc (fun _ : ZerothHomotopy X ↦ 𝟙 R) ≫ σ := by
    apply Sigma.hom_ext
    intro c
    rw [Preadditive.comp_sub, Sigma.ι_desc_assoc, Category.id_comp,
      ← Category.assoc (Sigma.ι _ c) p]
    by_cases hc : c = b
    · subst c
      rw [hpb, zero_comp]
      simp [σ]
    · rw [hp c hc, ι_singularHomologyZeroComponentInclusion]
      simp only [Preadditive.sub_comp, σ, b]
  have hρδ : ρ ≫ singularHomologyZeroComponentInclusion X R x =
      𝟙 _ - X.singularHomology₀ε R ≫ σ := by
    dsimp only [ρ]
    rw [Category.assoc, hpδ, Preadditive.comp_sub, Iso.hom_inv_id,
      ← Category.assoc, singularHomology₀Iso_sigma_desc_id]
  -- The two splitting identities give the standard kernel-fork lift and uniqueness.
  exact KernelFork.IsLimit.ofι _ _ (fun g _ ↦ g ≫ ρ)
    (fun g hg ↦ by
      rw [Category.assoc, hρδ, Preadditive.comp_sub, Category.comp_id,
        ← Category.assoc, hg, zero_comp, sub_zero])
    (fun g _ m hm ↦ by rw [← hm, Category.assoc, hδρ, Category.comp_id])

end TopCat
