/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout.PointMap
public import SphereTopology.Topology.WidePushout.Compactness

/-!
# Open embeddings of point-attached wide pushouts

Component open embeddings induce an open embedding of the existing categorical
wide pushouts. The factor-preimage formula holds for every subset of the source,
not just the whole source. Point reflection prevents new head or cross-factor
collisions; Mathlib's final topology then makes every open image open.

No separation, finiteness or nonempty-index assumption is used. The source and
target diagram universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u v w

namespace TopCat

variable {I : Type v} {X : I → TopCat.{max u v}} {Y : I → TopCat.{max w v}}
  (a : ∀ i, X i) (b : ∀ i, Y i) (f : ∀ i, C(X i, Y i))
  (hf : ∀ i, f i (a i) = b i)

set_option quotPrecheck false in
local notation "PX" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "PY" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "α" => (fun i ↦ (TopCat.const (a i) : PX ⟶ X i))
set_option quotPrecheck false in
local notation "β" => (fun i ↦ (TopCat.const (b i) : PY ⟶ Y i))
set_option quotPrecheck false in
local notation "WX" => (widePushout PX X α : TopCat)
set_option quotPrecheck false in
local notation "hx" => WidePushout.head α PUnit.unit
set_option quotPrecheck false in
local notation "hy" => WidePushout.head β PUnit.unit
set_option quotPrecheck false in
local notation "F" => widePushoutDesc α (ContinuousMap.const PX hy)
  (fun i ↦ (WidePushout.ι β i).hom.comp (f i))
  (widePushoutDesc_point_condition a b f hf)

/-- An image contains the common head precisely when its source set does. -/
theorem mem_image_widePushoutDesc_point_head
    (hreflect : ∀ i x, f i x = b i → x = a i) (S : Set WX) :
    hy ∈ F '' S ↔ hx ∈ S := by
  constructor
  · rintro ⟨q, hq, he⟩
    obtain ⟨_ | i, t, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan PX X α) q
    · cases t
      change hx ∈ S at hq
      exact hq
    · change WidePushout.ι α i t ∈ S at hq
      change F (WidePushout.ι α i t) = hy at he
      have ht : f i t = b i := (widePushout_point_ι_eq_head_iff b i (f i t)).1
        ((widePushoutDesc_point_ι a b f hf i t).symm.trans he)
      have hta : t = a i := hreflect i t ht
      subst t
      exact (widePushout_point_ι_point a i) ▸ hq
  · intro h
    exact ⟨hx, h, widePushoutDesc_point_head a b f hf PUnit.unit⟩

/-- The factor preimage of the image of any subset is its component image. -/
theorem preimage_image_widePushoutDesc_point
    (hreflect : ∀ i x, f i x = b i → x = a i) (S : Set WX) (i : I) :
    WidePushout.ι β i ⁻¹' (F '' S) = f i '' (WidePushout.ι α i ⁻¹' S) := by
  ext y
  constructor
  · rintro ⟨q, hq, he⟩
    obtain ⟨_ | k, t, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan PX X α) q
    · cases t
      change hx ∈ S at hq
      change F hx = WidePushout.ι β i y at he
      have hyb : y = b i := (widePushout_point_ι_eq_head_iff b i y).1
        (he.symm.trans (widePushoutDesc_point_head a b f hf PUnit.unit))
      refine ⟨a i, ?_, (hf i).trans hyb.symm⟩
      change WidePushout.ι α i (a i) ∈ S
      rw [widePushout_point_ι_point a i]
      exact hq
    · change WidePushout.ι α k t ∈ S at hq
      change F (WidePushout.ι α k t) = WidePushout.ι β i y at he
      have he' : WidePushout.ι β k (f k t) = WidePushout.ι β i y :=
        (widePushoutDesc_point_ι a b f hf k t).symm.trans he
      by_cases hkt : f k t = b k
      · have hta : t = a k := hreflect k t hkt
        have hyb : y = b i := (widePushout_point_ι_eq_head_iff b i y).1 (by
          calc
            WidePushout.ι β i y = WidePushout.ι β k (f k t) := he'.symm
            _ = hy := by
              rw [hkt]
              exact widePushout_point_ι_point b k)
        refine ⟨a i, ?_, (hf i).trans hyb.symm⟩
        change WidePushout.ι α i (a i) ∈ S
        rw [widePushout_point_ι_point a i]
        rw [hta, widePushout_point_ι_point a k] at hq
        exact hq
      · have hki : k = i := congrArg Sigma.fst
          ((widePushout_point_ι_eq_ι_iff_of_ne b hkt).1 he')
        subst k
        exact ⟨t, hq, (isEmbedding_widePushout_point_ι Y b i).injective he'⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨WidePushout.ι α i t, ht, widePushoutDesc_point_ι a b f hf i t⟩

/-- Component injections give an injective descent, even for an empty family. -/
theorem injective_widePushoutDesc_point
    (hinj : ∀ i, Function.Injective (f i)) : Function.Injective F := by
  have hreflect : ∀ i x, f i x = b i → x = a i :=
    fun i _ hfx ↦ hinj i (hfx.trans (hf i).symm)
  intro q r hqr
  have hr : F q ∈ F '' ({r} : Set WX) := ⟨r, mem_singleton r, hqr.symm⟩
  obtain ⟨_ | i, t, rfl⟩ :=
    Concrete.colimit_exists_rep (WidePushoutShape.wideSpan PX X α) q
  · cases t
    change hx = r
    change F hx ∈ F '' ({r} : Set WX) at hr
    have hh : hy ∈ F '' ({r} : Set WX) :=
      (congrArg (fun y ↦ y ∈ F '' ({r} : Set WX))
        (widePushoutDesc_point_head a b f hf PUnit.unit)).mp hr
    exact mem_singleton_iff.1
      ((mem_image_widePushoutDesc_point_head a b f hf hreflect {r}).1 hh)
  · change WidePushout.ι α i t = r
    change F (WidePushout.ι α i t) ∈ F '' ({r} : Set WX) at hr
    have hY : WidePushout.ι β i (f i t) ∈ F '' ({r} : Set WX) :=
      (congrArg (fun y ↦ y ∈ F '' ({r} : Set WX))
        (widePushoutDesc_point_ι a b f hf i t)).mp hr
    have ht : f i t ∈ f i '' (WidePushout.ι α i ⁻¹' ({r} : Set WX)) := by
      rw [← preimage_image_widePushoutDesc_point a b f hf hreflect {r} i]
      exact hY
    rcases ht with ⟨s, hs, hst⟩
    have hst' : s = t := hinj i hst
    subst s
    exact mem_singleton_iff.1 hs

/-- Point reflection and component open maps make every open image open. -/
theorem isOpenMap_widePushoutDesc_point
    (hreflect : ∀ i x, f i x = b i → x = a i)
    (hopen : ∀ i, IsOpenMap (f i)) : IsOpenMap F := by
  intro S hS
  apply (isOpen_widePushout_iff β (F '' S)).2
  refine ⟨isOpen_discrete _, ?_⟩
  intro i
  rw [preimage_image_widePushoutDesc_point a b f hf hreflect S i]
  exact hopen i _ (hS.preimage (WidePushout.ι α i).hom.continuous)

/-- Point-preserving component open embeddings induce an open embedding of the
canonical categorical point-wide-pushouts, without separation assumptions. -/
theorem isOpenEmbedding_widePushoutDesc_point
    (E : ∀ i, Topology.IsOpenEmbedding (f i)) : Topology.IsOpenEmbedding F :=
  .of_continuous_injective_isOpenMap (F).continuous
    (injective_widePushoutDesc_point a b f hf (fun i ↦ (E i).injective))
    (isOpenMap_widePushoutDesc_point a b f hf
      (fun i _ hfx ↦ (E i).injective (hfx.trans (hf i).symm))
      (fun i ↦ (E i).isOpenMap))

/-- The factor preimage of the full range is the component range, requiring only
point preservation. -/
theorem preimage_range_widePushoutDesc_point (i : I) :
    WidePushout.ι β i ⁻¹' range F = range (f i) := by
  ext y
  constructor
  · intro h
    by_cases hyb : y = b i
    · exact ⟨a i, (hf i).trans hyb.symm⟩
    · rw [range_widePushoutDesc_point a b f hf] at h
      rcases h with h | h
      · exact (hyb ((widePushout_point_ι_eq_head_iff b i y).1
          (mem_singleton_iff.1 h))).elim
      · rcases mem_iUnion.1 h with ⟨k, z, ⟨x, rfl⟩, he⟩
        have hik : i = k := congrArg Sigma.fst
          ((widePushout_point_ι_eq_ι_iff_of_ne b hyb).1 he.symm)
        subst k
        exact ⟨x, (isEmbedding_widePushout_point_ι Y b i).injective he⟩
  · rintro ⟨x, rfl⟩
    exact ⟨WidePushout.ι α i x, widePushoutDesc_point_ι a b f hf i x⟩

end TopCat
