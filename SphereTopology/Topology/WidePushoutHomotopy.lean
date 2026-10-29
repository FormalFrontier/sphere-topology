/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.WidePushout
public import Mathlib.Topology.Homotopy.Basic

/-!
# Parametrized continuity and homotopy descent for wide pushouts

A supplied topological colimit has its characteristic continuity property after
product with a parameter space `P`, for maps to `Y`, whenever
`LocallyCompactPair P Y` holds. In particular, local compactness of `P` suffices;
no separation condition on `Y` or local compactness of the diagram is needed.
The parameter, target, diagram and indexing universes are independent.

`TopCat.widePushoutProdDesc` descends compatible jointly continuous families.
Its head and factor equations, uniqueness, fixed-parameter agreement with
`TopCat.widePushoutDesc`, and parameter-precomposition law give its universal
property. `TopCat.widePushoutHomotopy` glues canonical interval homotopies
whose restrictions agree on the attaching space at every time. The common
point need not remain fixed when the attaching space is a point.

## References

* Mathlib's topological-colimit API by Patrick Massot, Kim Morrison, Mario
  Carneiro and Andrew Yang, and its concrete-colimit API, supply finality and
  representatives.
* Reid Barton's compact-open formalization supplies individual-map currying;
  Mathlib's evaluation and locally compact pair APIs supply joint evaluation.
* Shing Tak Lam's homotopy formalization supplies the interval convention and
  the `ContinuousMap.HomotopyLike` interface.
* The free-path-space transposition used in the homotopy extension property
  motivates putting the parameter inside the continuous mapping space.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe j k d p q y u v

namespace TopCat

/-- The characteristic continuity criterion for a supplied topological colimit,
with an independent product parameter and target. The pair hypothesis is used
only to evaluate continuous maps from the parameter space. -/
theorem continuous_prod_iff_of_isColimit {J : Type j} [Category.{k} J]
    {F : J ⥤ TopCat.{d}} (c : Cocone F) (hc : IsColimit c)
    {P : Type p} {Y : Type y} [TopologicalSpace P] [TopologicalSpace Y]
    [LocallyCompactPair P Y] (a : P × c.pt → Y) :
    Continuous a ↔ ∀ i, Continuous (fun z : P × F.obj i ↦ a (z.1, c.ι.app i z.2)) := by
  constructor
  · intro ha i
    exact ha.comp (continuous_fst.prodMk ((c.ι.app i).hom.continuous.comp continuous_snd))
  · intro ha
    have hs (x : c.pt) : Continuous (fun t : P ↦ a (t, x)) := by
      obtain ⟨i, z, rfl⟩ := Concrete.isColimit_exists_rep F hc x
      exact (ha i).comp (continuous_id.prodMk continuous_const)
    let b : c.pt → C(P, Y) := fun x ↦ ⟨fun t ↦ a (t, x), hs x⟩
    have hb : Continuous b := by
      apply (continuous_iff_of_isColimit c hc b).2
      intro i
      exact ContinuousMap.continuous_of_continuous_uncurry _ ((ha i).comp continuous_swap)
    exact (hb.comp continuous_snd).eval continuous_fst

/-- The ordinary colimit continuity criterion is recovered from the
product-parameter criterion by using a one-point parameter. -/
theorem continuous_iff_of_isColimit_unit {J : Type j} [Category.{k} J]
    {F : J ⥤ TopCat.{d}} (c : Cocone F) (hc : IsColimit c)
    {Y : Type y} [TopologicalSpace Y] (a : c.pt → Y) :
    Continuous a ↔ ∀ i, Continuous (a ∘ c.ι.app i) := by
  have hunit : Continuous (fun z : PUnit.{1} × c.pt ↦ a z.2) ↔ Continuous a :=
    ⟨fun h ↦ h.comp ((continuous_const (y := PUnit.unit)).prodMk continuous_id),
      fun h ↦ h.comp continuous_snd⟩
  rw [← hunit, continuous_prod_iff_of_isColimit c hc]
  constructor
  · intro h i
    exact (h i).comp ((continuous_const (y := PUnit.unit)).prodMk continuous_id)
  · intro h i
    exact (h i).comp continuous_snd

variable {I : Type v} {B : TopCat.{max u v}} {X : I → TopCat.{max u v}}
  (f : ∀ i, B ⟶ X i)

/-- Joint continuity out of a product with a wide pushout is checked on the
head and every factor. Retaining the head also covers the empty index. -/
theorem continuous_prod_widePushout_iff {P : Type p} {Y : Type y}
    [TopologicalSpace P] [TopologicalSpace Y] [LocallyCompactPair P Y]
    (a : P × (widePushout B X f : TopCat.{max u v}) → Y) :
    Continuous a ↔
      Continuous (fun z : P × B ↦ a (z.1, WidePushout.head f z.2)) ∧
      ∀ i, Continuous (fun z : P × X i ↦ a (z.1, WidePushout.ι f i z.2)) := by
  refine (continuous_prod_iff_of_isColimit
    (colimit.cocone (WidePushoutShape.wideSpan B X f)) (colimit.isColimit _) a).trans ?_
  constructor
  · intro h
    exact ⟨h none, fun i ↦ h (some i)⟩
  · rintro ⟨hB, hX⟩ (_ | i)
    · exact hB
    · exact hX i

/-- Functions on a product with a wide pushout are determined by their values
on the head and every factor, with no topology on the parameter or target. -/
theorem widePushout_prod_funext {P : Type p} {Y : Sort y}
    {a b : P × (widePushout B X f : TopCat.{max u v}) → Y}
    (hB : ∀ t x, a (t, WidePushout.head f x) = b (t, WidePushout.head f x))
    (hX : ∀ i t x, a (t, WidePushout.ι f i x) = b (t, WidePushout.ι f i x)) : a = b := by
  funext ⟨t, x⟩
  exact congrFun (widePushout_funext f
    (g := fun z ↦ a (t, z)) (h := fun z ↦ b (t, z)) (hB t) (fun i ↦ hX i t)) x

section ProductDescent

variable {P : Type p} {Y : Type y} [TopologicalSpace P] [TopologicalSpace Y]
  [LocallyCompactPair P Y]
  (g : C(P × B, Y)) (h : ∀ i, C(P × X i, Y))
  (w : ∀ i t b, h i (t, f i b) = g (t, b))

/-- Descend compatible jointly continuous families through a wide pushout.
The parameter and target universes are independent of the diagram universe. -/
def widePushoutProdDesc : C(P × (widePushout B X f : TopCat.{max u v}), Y) where
  toFun z := widePushoutDesc f (g.curry z.1) (fun i ↦ (h i).curry z.1)
    (fun i b ↦ w i z.1 b) z.2
  continuous_toFun := by
    apply (continuous_prod_widePushout_iff f _).2
    constructor
    · exact g.continuous.congr (fun z ↦
        (widePushoutDesc_head f (g.curry z.1) (fun i ↦ (h i).curry z.1)
          (fun i b ↦ w i z.1 b) z.2).symm)
    · intro i
      exact (h i).continuous.congr (fun z ↦
        (widePushoutDesc_ι f (g.curry z.1) (fun i ↦ (h i).curry z.1)
          (fun i b ↦ w i z.1 b) i z.2).symm)

/-- Product descent restricts to the prescribed family on the head. -/
@[simp] theorem widePushoutProdDesc_head (t : P) (b : B) :
    widePushoutProdDesc f g h w (t, WidePushout.head f b) = g (t, b) :=
  widePushoutDesc_head f (g.curry t) (fun i ↦ (h i).curry t) (fun i b ↦ w i t b) b

/-- Product descent restricts to the prescribed family on every factor. -/
@[simp] theorem widePushoutProdDesc_ι (i : I) (t : P) (x : X i) :
    widePushoutProdDesc f g h w (t, WidePushout.ι f i x) = h i (t, x) :=
  widePushoutDesc_ι f (g.curry t) (fun i ↦ (h i).curry t) (fun i b ↦ w i t b) i x

/-- The head and factor equations uniquely characterize product descent. -/
theorem widePushoutProdDesc_unique
    (a : C(P × (widePushout B X f : TopCat.{max u v}), Y))
    (hB : ∀ t b, a (t, WidePushout.head f b) = g (t, b))
    (hX : ∀ i t x, a (t, WidePushout.ι f i x) = h i (t, x)) :
    a = widePushoutProdDesc f g h w := by
  apply DFunLike.coe_injective
  apply widePushout_prod_funext f
  · intro t b
    exact (hB t b).trans (widePushoutProdDesc_head f g h w t b).symm
  · intro i t x
    exact (hX i t x).trans (widePushoutProdDesc_ι f g h w i t x).symm

/-- At each fixed parameter, product descent is the existing continuous descent
of the head and factor slices. -/
theorem widePushoutProdDesc_curry (t : P) :
    (widePushoutProdDesc f g h w).curry t =
      widePushoutDesc f (g.curry t) (fun i ↦ (h i).curry t) (fun i b ↦ w i t b) := by
  ext x
  rfl

/-- Restricting or reparametrizing a descended family is descent of the
reparametrized head and factor families. -/
theorem widePushoutProdDesc_comp_prodMap {Q : Type q} [TopologicalSpace Q]
    [LocallyCompactPair Q Y] (a : C(Q, P)) :
    (widePushoutProdDesc f g h w).comp (a.prodMap (ContinuousMap.id _)) =
      widePushoutProdDesc f (g.comp (a.prodMap (ContinuousMap.id B)))
        (fun i ↦ (h i).comp (a.prodMap (ContinuousMap.id (X i))))
        (fun i t b ↦ w i (a t) b) := by
  apply widePushoutProdDesc_unique
  · intro t b
    exact widePushoutProdDesc_head f g h w (a t) b
  · intro i t x
    exact widePushoutProdDesc_ι f g h w i (a t) x

end ProductDescent

section Homotopy

variable {Y : Type y} [TopologicalSpace Y]
  {a₀ a₁ : C((widePushout B X f : TopCat.{max u v}), Y)}
  {HB : Type*} [FunLike HB (unitInterval × B) Y]
  [ContinuousMap.HomotopyLike HB (a₀.comp (WidePushout.head f).hom)
    (a₁.comp (WidePushout.head f).hom)]
  {HX : I → Type*} [∀ i, FunLike (HX i) (unitInterval × X i) Y]
  [∀ i, ContinuousMap.HomotopyLike (HX i) (a₀.comp (WidePushout.ι f i).hom)
    (a₁.comp (WidePushout.ι f i).hom)]
  (g : HB) (h : ∀ i, HX i) (w : ∀ i t b, h i (t, f i b) = g (t, b))

/-- Glue homotopies agreeing on the attaching space at every time.
No pointwise fixing or separation hypothesis is imposed. -/
def widePushoutHomotopy : ContinuousMap.Homotopy a₀ a₁ :=
  let d := widePushoutProdDesc f (⟨g, map_continuous g⟩ : C(unitInterval × B, Y))
    (fun i ↦ ⟨h i, map_continuous (h i)⟩) w
  { toContinuousMap := d
    map_zero_left := by
      intro x
      apply congrFun (widePushout_funext f (g := fun x ↦ d (0, x)) (h := a₀) ?_ ?_) x
      · intro b
        exact (widePushoutProdDesc_head f _ _ w 0 b).trans
          (ContinuousMap.HomotopyLike.map_zero_left g b)
      · intro i z
        exact (widePushoutProdDesc_ι f _ _ w i 0 z).trans
          (ContinuousMap.HomotopyLike.map_zero_left (h i) z)
    map_one_left := by
      intro x
      apply congrFun (widePushout_funext f (g := fun x ↦ d (1, x)) (h := a₁) ?_ ?_) x
      · intro b
        exact (widePushoutProdDesc_head f _ _ w 1 b).trans
          (ContinuousMap.HomotopyLike.map_one_left g b)
      · intro i z
        exact (widePushoutProdDesc_ι f _ _ w i 1 z).trans
          (ContinuousMap.HomotopyLike.map_one_left (h i) z) }

/-- Glued homotopies have the prescribed restriction to the head at all times. -/
@[simp] theorem widePushoutHomotopy_head (t : unitInterval) (b : B) :
    widePushoutHomotopy f g h w (t, WidePushout.head f b) = g (t, b) :=
  widePushoutProdDesc_head f (⟨g, map_continuous g⟩ : C(unitInterval × B, Y))
    (fun i ↦ ⟨h i, map_continuous (h i)⟩) w t b

/-- Glued homotopies have the prescribed restriction to every factor at all times. -/
@[simp] theorem widePushoutHomotopy_ι (i : I) (t : unitInterval) (x : X i) :
    widePushoutHomotopy f g h w (t, WidePushout.ι f i x) = h i (t, x) :=
  widePushoutProdDesc_ι f (⟨g, map_continuous g⟩ : C(unitInterval × B, Y))
    (fun i ↦ ⟨h i, map_continuous (h i)⟩) w i t x

/-- The all-time head and factor equations uniquely characterize the glued homotopy. -/
theorem widePushoutHomotopy_unique (H : ContinuousMap.Homotopy a₀ a₁)
    (hB : ∀ t b, H (t, WidePushout.head f b) = g (t, b))
    (hX : ∀ i t x, H (t, WidePushout.ι f i x) = h i (t, x)) :
    H = widePushoutHomotopy f g h w := by
  apply DFunLike.coe_injective
  apply widePushout_prod_funext f
  · intro t b
    exact (hB t b).trans (widePushoutHomotopy_head f g h w t b).symm
  · intro i t x
    exact (hX i t x).trans (widePushoutHomotopy_ι f g h w i t x).symm

end Homotopy

end TopCat
