/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.OpenEmbedding
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# Original-domain and universe-transport API

Conjugating component maps by homeomorphisms gives the same canonical descent
with transported points. The characteristic maps below have the original
factor domains. Choosing Mathlib's `TopCat.uliftFunctorObjHomeo` gives the
caller contract for three independent factor/index universes, without a
smallness witness or equality of universes.

The universe-lifting functor and its homeomorphisms are Mathlib constructions
by Joël Riou. No new space or bundled family map is defined here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u v w

namespace TopCat

variable {I : Type v} {X0 : I → TopCat.{u}} {Y0 : I → TopCat.{w}}
  {X : I → TopCat.{max u v}} {Y : I → TopCat.{max w v}}
  (a0 : ∀ i, X0 i) (b0 : ∀ i, Y0 i) (f0 : ∀ i, C(X0 i, Y0 i))
  (hf0 : ∀ i, f0 i (a0 i) = b0 i)
  (eX : ∀ i, X0 i ≃ₜ X i) (eY : ∀ i, Y0 i ≃ₜ Y i)

set_option quotPrecheck false in
local notation "aa" => (fun i ↦ eX i (a0 i))
set_option quotPrecheck false in
local notation "bb" => (fun i ↦ eY i (b0 i))
set_option quotPrecheck false in
local notation "cf" => (fun i ↦ (eY i : C(Y0 i, Y i)).comp
  ((f0 i).comp ((eX i).symm : C(X i, X0 i))))
set_option quotPrecheck false in
local notation "hp" => (fun i ↦ by
  change eY i (f0 i ((eX i).symm (eX i (a0 i)))) = eY i (b0 i)
  rw [Homeomorph.symm_apply_apply, hf0 i])
set_option quotPrecheck false in
local notation "PX" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "PY" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "α" => (fun i ↦ (TopCat.const (aa i) : PX ⟶ X i))
set_option quotPrecheck false in
local notation "β" => (fun i ↦ (TopCat.const (bb i) : PY ⟶ Y i))
set_option quotPrecheck false in
local notation "WX" => (widePushout PX X α : TopCat)
set_option quotPrecheck false in
local notation "hx" => WidePushout.head α PUnit.unit
set_option quotPrecheck false in
local notation "hy" => WidePushout.head β PUnit.unit
set_option quotPrecheck false in
local notation "F" => widePushoutDesc α (ContinuousMap.const PX hy)
  (fun i ↦ (WidePushout.ι β i).hom.comp (cf i))
  (widePushoutDesc_point_condition aa bb cf hp)

/-- The characteristic inclusions of both original domains preserve their points. -/
theorem widePushout_point_conjugate_ι_point (i : I) :
    WidePushout.ι α i (eX i (a0 i)) = hx ∧
      WidePushout.ι β i (eY i (b0 i)) = hy :=
  ⟨widePushout_point_ι_point aa i, widePushout_point_ι_point bb i⟩

/-- The factor equation is stated on the original, unlifted source domain. -/
theorem widePushoutDesc_point_conjugate_ι (i : I) (x : X0 i) :
    F (WidePushout.ι α i (eX i x)) = WidePushout.ι β i (eY i (f0 i x)) := by
  calc
    _ = WidePushout.ι β i (cf i (eX i x)) :=
      widePushoutDesc_point_ι aa bb cf hp i (eX i x)
    _ = _ := by
      change WidePushout.ι β i (eY i (f0 i ((eX i).symm (eX i x)))) = _
      rw [Homeomorph.symm_apply_apply]

/-- Open embeddings are preserved by conjugation before canonical descent. -/
theorem isOpenEmbedding_widePushoutDesc_point_conjugate
    (E0 : ∀ i, Topology.IsOpenEmbedding (f0 i)) : Topology.IsOpenEmbedding F :=
  isOpenEmbedding_widePushoutDesc_point aa bb cf hp
    (fun i ↦ (eY i).isOpenEmbedding.comp
      ((E0 i).comp (eX i).symm.isOpenEmbedding))

/-- The arbitrary-subset image formula can be read entirely on the original
factor domains, not only on their transported copies. -/
theorem preimage_image_widePushoutDesc_point_conjugate
    (hreflect0 : ∀ i x, f0 i x = b0 i → x = a0 i) (S : Set WX) (i : I) :
    ((WidePushout.ι β i).hom.comp (eY i : C(Y0 i, Y i))) ⁻¹' (F '' S) =
      f0 i '' (((WidePushout.ι α i).hom.comp (eX i : C(X0 i, X i))) ⁻¹' S) := by
  have hreflect : ∀ i x, cf i x = bb i → x = aa i := by
    intro k x hfx
    change eY k (f0 k ((eX k).symm x)) = eY k (b0 k) at hfx
    have hxa := hreflect0 k ((eX k).symm x) ((eY k).injective hfx)
    simpa only [Homeomorph.apply_symm_apply] using congrArg (eX k) hxa
  ext y
  change eY i y ∈ WidePushout.ι β i ⁻¹' (F '' S) ↔ _
  rw [preimage_image_widePushoutDesc_point aa bb cf hp hreflect S i]
  constructor
  · rintro ⟨x, hxS, he⟩
    refine ⟨(eX i).symm x, ?_, ?_⟩
    · change WidePushout.ι α i x ∈ S at hxS
      change WidePushout.ι α i (eX i ((eX i).symm x)) ∈ S
      rw [Homeomorph.apply_symm_apply]
      exact hxS
    · apply (eY i).injective
      exact he
  · rintro ⟨x, hxS, rfl⟩
    refine ⟨eX i x, hxS, ?_⟩
    change eY i (f0 i ((eX i).symm (eX i x))) = eY i (f0 i x)
    rw [Homeomorph.symm_apply_apply]

/-- Independently sized original factors are lifted only by the index universe.
The displayed descent is the existing one, with the canonical transported points
and conjugated maps; the caller supplies no smallness or universe equality. -/
theorem isOpenEmbedding_widePushoutDesc_point_ulift
    (E0 : ∀ i, Topology.IsOpenEmbedding (f0 i)) :
    let XL : I → TopCat.{max u v} := fun i ↦ uliftFunctor.{v, u}.obj (X0 i)
    let YL : I → TopCat.{max w v} := fun i ↦ uliftFunctor.{v, w}.obj (Y0 i)
    let ex : ∀ i, X0 i ≃ₜ XL i := fun i ↦ (X0 i).uliftFunctorObjHomeo
    let ey : ∀ i, Y0 i ≃ₜ YL i := fun i ↦ (Y0 i).uliftFunctorObjHomeo
    let al := fun i ↦ ex i (a0 i)
    let bl := fun i ↦ ey i (b0 i)
    let fl : ∀ i, C(XL i, YL i) := fun i ↦ (ey i : C(Y0 i, YL i)).comp
      ((f0 i).comp ((ex i).symm : C(XL i, X0 i)))
    let pl : ∀ i, fl i (al i) = bl i := fun i ↦ by
      change ey i (f0 i ((ex i).symm (ex i (a0 i)))) = ey i (b0 i)
      rw [Homeomorph.symm_apply_apply, hf0 i]
    let sl := fun i ↦ (TopCat.const (al i) : TopCat.of PUnit ⟶ XL i)
    let tl := fun i ↦ (TopCat.const (bl i) : TopCat.of PUnit ⟶ YL i)
    Topology.IsOpenEmbedding
      (widePushoutDesc sl
        (ContinuousMap.const (TopCat.of PUnit) (WidePushout.head tl PUnit.unit))
        (fun i ↦ (WidePushout.ι tl i).hom.comp (fl i))
        (widePushoutDesc_point_condition al bl fl pl)) := by
  dsimp only
  exact isOpenEmbedding_widePushoutDesc_point_conjugate
    (X := fun i ↦ uliftFunctor.{v, u}.obj (X0 i))
    (Y := fun i ↦ uliftFunctor.{v, w}.obj (Y0 i)) a0 b0 f0 hf0
    (fun i ↦ (X0 i).uliftFunctorObjHomeo)
    (fun i ↦ (Y0 i).uliftFunctorObjHomeo) E0

end TopCat
