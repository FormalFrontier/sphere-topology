/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homotopy.CircleBouquet.FundamentalGroup
public import FundamentalGroupoids.FundamentalGroup.DiskAttachment.Quotient
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Image

/-!
# Fundamental groups of indexed circle-bouquet presentations

Signed lists determine paths in the original complex-circle bouquet. The empty
list gives the constant path, and a singleton gives exactly its signed circle
path. Longer lists use Mathlib's binary half-and-half concatenation, traversing
the tail before the head, in agreement with fundamental-group multiplication
`p * q = q.trans p`. For `[a, b, c]`, the letters `c`, `b`, and `a` receive the
first quarter, second quarter, and final half of the time interval.

The period-one circle map of each list pulls back along `Circle.loop 1` to its
specified path at every time, including both endpoints. Its positive class is
the image of the ordered free-group word under the bouquet generator equivalence.
List families retain these unreduced clocks. Abstract free-group relators use
`FreeGroup.toWord`, with decidable equality chosen internally.

One closed complex disk is attached for each relator index, including duplicate
and trivial relators. The boundary clocks and attaching classes identify the
fundamental group with the quotient by the normal closure of the relators.
`listPresentationEquiv_mk` and `presentationEquiv_mk` characterize these
isomorphisms on every free-group word using the original bouquet inclusion.
Both label and relator index types may be empty.

For a group `G`, all elements of the kernel of `FreeGroup.prod` index the
canonical attachment. `canonicalFundamentalGroupEquiv` identifies `G` with its
fundamental group, and `canonicalFundamentalGroupEquiv_apply` sends each element
to the positive class of its included circle.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–8,
  for disk attachments and presentations of fundamental groups.
* Sphere Topology's positive circle-bouquet generator equivalence;
  Fundamental Groupoids' complex-circle normalization, based loop naturality,
  and disk-attachment quotient equivalence; Mathlib's path extension,
  additive-circle gluing, free groups, normal closures, and quotient groups.
-/

@[expose] public section

noncomputable section

universe u v w z

namespace CircleBouquet.Presentation

/-- The included positive complex-circle path, with both endpoints at the common point. -/
def positivePath {I : Type v} (i : I) :
    Path (CircleBouquet.basepoint.{u, v} I) (CircleBouquet.basepoint.{u, v} I) :=
  ((Circle.loop 1).map (CircleBouquet.inclusion.{u, v} i).continuous).cast
    (CircleBouquet.inclusion_basepoint.{u, v} i).symm
    (CircleBouquet.inclusion_basepoint.{u, v} i).symm

/-- A positive letter follows its included circle path; a negative letter reverses it. -/
def letterPath {I : Type v} (s : I × Bool) :
    Path (CircleBouquet.basepoint.{u, v} I) (CircleBouquet.basepoint.{u, v} I) :=
  if s.2 then positivePath.{u, v} s.1 else (positivePath.{u, v} s.1).symm

/-- The unreduced signed-list path, with an exact singleton case and a tail-first clock. -/
def wordPath {I : Type v} : List (I × Bool) →
    Path (CircleBouquet.basepoint.{u, v} I) (CircleBouquet.basepoint.{u, v} I)
  | [] => Path.refl (CircleBouquet.basepoint.{u, v} I)
  | [s] => letterPath.{u, v} s
  | s :: t :: tail => (wordPath (t :: tail)).trans (letterPath.{u, v} s)

/-- A positively signed letter is its original positive path. -/
@[simp] theorem letterPath_true {I : Type v} (i : I) :
    letterPath.{u, v} (i, true) = positivePath.{u, v} i := rfl

/-- A negatively signed letter reverses its original positive path. -/
@[simp] theorem letterPath_false {I : Type v} (i : I) :
    letterPath.{u, v} (i, false) = (positivePath.{u, v} i).symm := rfl

/-- The empty word has the constant path. -/
@[simp] theorem wordPath_nil (I : Type v) :
    wordPath.{u, v} ([] : List (I × Bool)) =
      Path.refl (CircleBouquet.basepoint.{u, v} I) := rfl

/-- A singleton uses exactly its signed path, with no added pause. -/
@[simp] theorem wordPath_singleton {I : Type v} (s : I × Bool) :
    wordPath.{u, v} [s] = letterPath.{u, v} s := rfl

/-- For a nonempty tail the specified path traverses the tail before the head. -/
@[simp] theorem wordPath_cons_cons {I : Type v} (s t : I × Bool)
    (tail : List (I × Bool)) :
    wordPath.{u, v} (s :: t :: tail) =
      (wordPath.{u, v} (t :: tail)).trans (letterPath.{u, v} s) := rfl

/-- The circle map glued from the specified signed-list path using period one. -/
def wordCircle {I : Type v} (l : List (I × Bool)) :
    C(Circle, CircleBouquet.space.{u, v} I) :=
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let p := wordPath.{u, v} l
  let q : C(AddCircle (1 : ℝ), CircleBouquet.space.{u, v} I) :=
    ⟨AddCircle.liftIco 1 0 p.extend,
      AddCircle.liftIco_zero_continuous
        (p.extend_zero.trans p.extend_one.symm) p.extend.continuous.continuousOn⟩
  q.comp ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm :
    C(Circle, AddCircle (1 : ℝ)))

/-- The glued map takes the original complex point one to the bouquet's common point. -/
theorem wordCircle_one {I : Type v} (l : List (I × Bool)) :
    wordCircle.{u, v} l 1 = CircleBouquet.basepoint.{u, v} I := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let p := wordPath.{u, v} l
  let h := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have h0 : h 0 = 1 :=
    (AddCircle.homeomorphCircle_apply one_ne_zero 0).trans AddCircle.toCircle_zero
  have hs : h.symm 1 = (0 : AddCircle (1 : ℝ)) := by
    rw [← h0, h.symm_apply_apply]
  change AddCircle.liftIco (1 : ℝ) 0 p.extend (h.symm 1) =
    CircleBouquet.basepoint.{u, v} I
  rw [hs]
  have hq := AddCircle.liftIco_zero_coe_apply (p := (1 : ℝ)) (f := p.extend)
    (x := (0 : ℝ)) (show (0 : ℝ) ∈ Set.Ico 0 1 from ⟨le_rfl, zero_lt_one⟩)
  simpa only [AddCircle.coe_zero, Path.extend_zero] using hq

/-- The free-group relators read from the prescribed lists, without altering their clocks. -/
def listRelators {I : Type v} {R : Type w} (L : R → List (I × Bool)) : R → FreeGroup I :=
  fun r => FreeGroup.mk (L r)

/-- A canonical reduced word for an abstract free-group element, with no equality premise. -/
def wordOf {I : Type v} (g : FreeGroup I) : List (I × Bool) := by
  classical
  exact g.toWord

/-- The word family used only when the input relators are abstract free-group elements. -/
def canonicalWords {I : Type v} {R : Type w} (ρ : R → FreeGroup I) :
    R → List (I × Bool) :=
  fun r => wordOf (ρ r)

/-- Reading the fixed canonical word in the free group recovers the given element. -/
@[simp] theorem mk_wordOf {I : Type v} (g : FreeGroup I) :
    FreeGroup.mk (wordOf g) = g := by
  classical
  exact FreeGroup.mk_toWord

/-- The canonical-word family reads back to the original abstract relator family. -/
@[simp] theorem listRelators_canonicalWords {I : Type v} {R : Type w}
    (ρ : R → FreeGroup I) : listRelators (canonicalWords ρ) = ρ := by
  funext r
  exact mk_wordOf (ρ r)

/-- One original-circle attaching map for each member of the prescribed index family. -/
def attachingMaps {I : Type v} {R : Type w} (L : R → List (I × Bool)) :
    R → C(Circle, CircleBouquet.space.{u, v} I) :=
  fun r => wordCircle.{u, v} (L r)

/-- Every member of the attaching family is based at the original bouquet point. -/
theorem attachingMaps_one {I : Type v} {R : Type w} (L : R → List (I × Bool)) (r : R) :
    attachingMaps.{u, v, w} L r 1 = CircleBouquet.basepoint.{u, v} I :=
  wordCircle_one.{u, v} (L r)

/-- The space obtained by attaching one closed complex disk per prescribed relator index. -/
def spaceOfLists {I : Type v} {R : Type w} (L : R → List (I × Bool)) :
    TopCat.{max u v w} :=
  TopCat.diskAttachment (attachingMaps.{u, v, w} L)

/-- The original-space inclusion into the indexed disk attachment. -/
def inclusionOfLists {I : Type v} {R : Type w} (L : R → List (I × Bool)) :
    C(CircleBouquet.space.{u, v} I, spaceOfLists.{u, v, w} L) :=
  TopCat.diskAttachmentInclusion (attachingMaps.{u, v, w} L)

/-- The image of the original bouquet point in the disk attachment. -/
def basepointOfLists {I : Type v} {R : Type w} (L : R → List (I × Bool)) :
    spaceOfLists.{u, v, w} L :=
  inclusionOfLists.{u, v, w} L (CircleBouquet.basepoint.{u, v} I)

/-- The positive attaching classes computed from the constructed circle maps. -/
def attachingClasses {I : Type v} {R : Type w} (L : R → List (I × Bool)) :
    R → FundamentalGroup (CircleBouquet.space.{u, v} I) (CircleBouquet.basepoint.{u, v} I) :=
  fun r => FundamentalGroup.mapOfEq (attachingMaps.{u, v, w} L r)
    (attachingMaps_one.{u, v, w} L r) (FundamentalGroup.fromPath ⟦Circle.loop 1⟧)

/-- The existing disk-attachment quotient equivalence for the constructed attaching classes. -/
def attachingClassQuotientEquiv {I : Type v} {R : Type w} (L : R → List (I × Bool)) :
    (FundamentalGroup (CircleBouquet.space.{u, v} I) (CircleBouquet.basepoint.{u, v} I) ⧸
      Subgroup.normalClosure (Set.range (attachingClasses.{u, v, w} L))) ≃*
        FundamentalGroup (spaceOfLists.{u, v, w} L) (basepointOfLists.{u, v, w} L) :=
  FundamentalGroup.diskAttachmentFundamentalGroupQuotientEquiv
    (attachingMaps.{u, v, w} L) (CircleBouquet.basepoint.{u, v} I)
    (attachingMaps_one.{u, v, w} L)

/-- The attaching family for abstract relators, using the canonical word clock explicitly. -/
def abstractAttachingMaps {I : Type v} {R : Type w} (ρ : R → FreeGroup I) :
    R → C(Circle, CircleBouquet.space.{u, v} I) :=
  attachingMaps.{u, v, w} (canonicalWords ρ)

/-- Abstract-relator attaching maps also take one to the original bouquet point. -/
theorem abstractAttachingMaps_one {I : Type v} {R : Type w} (ρ : R → FreeGroup I) (r : R) :
    abstractAttachingMaps.{u, v, w} ρ r 1 = CircleBouquet.basepoint.{u, v} I :=
  attachingMaps_one.{u, v, w} (canonicalWords ρ) r

/-- The fixed disk-attachment space for an abstract indexed relator family. -/
def spaceOfRelators {I : Type v} {R : Type w} (ρ : R → FreeGroup I) :
    TopCat.{max u v w} :=
  spaceOfLists.{u, v, w} (canonicalWords ρ)

/-- The fixed basepoint of the space for an abstract indexed relator family. -/
def basepointOfRelators {I : Type v} {R : Type w} (ρ : R → FreeGroup I) :
    spaceOfRelators.{u, v, w} ρ :=
  basepointOfLists.{u, v, w} (canonicalWords ρ)

/-! ## The kernel presentation of an arbitrary group -/

section

variable (G : Type z) [Group G]

/-- Relator indices for the canonical presentation: every element of the kernel of `prod`. -/
abbrev KernelRelators : Type z := ↥((FreeGroup.prod : FreeGroup G →* G).ker)

/-- The canonical relator family includes every kernel element as a free-group word. -/
def kernelRelatorFamily : KernelRelators G → FreeGroup G :=
  fun r => r.val

/-- The canonical space uses the kernel presentation, with no chosen presentation input. -/
def canonicalSpace : TopCat.{max u z} :=
  spaceOfRelators.{u, z, z} (kernelRelatorFamily G)

/-- The basepoint of the kernel-presentation space. -/
def canonicalBasepoint : canonicalSpace.{u, z} G :=
  basepointOfRelators.{u, z, z} (kernelRelatorFamily G)

/-- The stock kernel-quotient isomorphism, with the explicit section `FreeGroup.of`. -/
def kernelQuotientEquiv :
    (FreeGroup G ⧸ (FreeGroup.prod : FreeGroup G →* G).ker) ≃* G :=
  QuotientGroup.quotientKerEquivOfRightInverse (FreeGroup.prod : FreeGroup G →* G)
    FreeGroup.of (fun g => FreeGroup.prod.of (x := g))

end

/-! ## Circle and disk-boundary clocks -/

/-- The positive included path follows the complex-circle exponential at every time. -/
theorem positivePath_apply {I : Type v} (i : I) (t : unitInterval) :
    positivePath.{u, v} i t =
      CircleBouquet.inclusion.{u, v} i (Circle.exp (2 * Real.pi * (t : ℝ))) := by
  change CircleBouquet.inclusion.{u, v} i (Circle.loop 1 t) = _
  simp only [Circle.loop_apply, Int.cast_one, mul_one]

/-- Pullback along the positive circle loop recovers the entire prescribed list path. -/
theorem wordCircle_loop {I : Type v} (l : List (I × Bool)) (t : unitInterval) :
    wordCircle.{u, v} l (Circle.loop 1 t) = wordPath.{u, v} l t := by
  by_cases ht : (t : ℝ) < 1
  · let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
    let p := wordPath.{u, v} l
    let h := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
    have hs : h.symm (Circle.loop 1 t) = ((t : ℝ) : AddCircle (1 : ℝ)) := by
      have hh : h (AddCircle.loop 1 1 t) = Circle.loop 1 t :=
        AddCircle.homeomorphCircle_loop one_ne_zero 1 t
      rw [← hh, h.symm_apply_apply]
      simp only [AddCircle.loop_apply, Int.cast_one, mul_one, one_mul]
    change AddCircle.liftIco (1 : ℝ) 0 p.extend (h.symm (Circle.loop 1 t)) = p t
    rw [hs]
    exact (AddCircle.liftIco_zero_coe_apply (p := (1 : ℝ)) (f := p.extend)
      (x := (t : ℝ)) ⟨t.property.1, ht⟩).trans (p.extend_extends' t)
  · have ht1 : t = 1 :=
      Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
    subst t
    rw [(Circle.loop 1).target, wordCircle_one, (wordPath.{u, v} l).target]

/-- The circle map of an abstract word retains the path of its chosen word. -/
theorem wordCircle_wordOf_loop {I : Type v} (g : FreeGroup I) (t : unitInterval) :
    wordCircle.{u, v} (wordOf g) (Circle.loop 1 t) = wordPath.{u, v} (wordOf g) t := by
  exact wordCircle_loop.{u, v} (wordOf g) t

/-- Each prescribed-list attaching map has its specified signed-list clock. -/
theorem attachingMaps_loop {I : Type v} {R : Type w}
    (L : R → List (I × Bool)) (r : R) (t : unitInterval) :
    attachingMaps.{u, v, w} L r (Circle.loop 1 t) = wordPath.{u, v} (L r) t := by
  exact wordCircle_loop.{u, v} (L r) t

/-- Each abstract-relator attaching map has the clock of its chosen word. -/
theorem abstractAttachingMaps_loop {I : Type v} {R : Type w}
    (ρ : R → FreeGroup I) (r : R) (t : unitInterval) :
    abstractAttachingMaps.{u, v, w} ρ r (Circle.loop 1 t) =
      wordPath.{u, v} (wordOf (ρ r)) t := by
  exact attachingMaps_loop.{u, v, w} (canonicalWords ρ) r t

/-- The boundary of every indexed disk traverses the prescribed list path after inclusion. -/
theorem diskAttachmentDisk_attachingMaps_loop {I : Type v} {R : Type w}
    (L : R → List (I × Bool)) (r : R) (t : unitInterval) :
    TopCat.diskAttachmentDisk (attachingMaps.{u, v, w} L) r
        (TopCat.diskBoundary (Circle.loop 1 t)) =
      inclusionOfLists.{u, v, w} L (wordPath.{u, v} (L r) t) := by
  exact (TopCat.diskAttachmentDisk_boundary (attachingMaps.{u, v, w} L) r
    (Circle.loop 1 t)).trans
      (congrArg (inclusionOfLists.{u, v, w} L) (attachingMaps_loop.{u, v, w} L r t))

/-- The boundary clock for an abstract relator uses its chosen word without alteration. -/
theorem diskAttachmentDisk_abstractAttachingMaps_loop {I : Type v} {R : Type w}
    (ρ : R → FreeGroup I) (r : R) (t : unitInterval) :
    TopCat.diskAttachmentDisk (abstractAttachingMaps.{u, v, w} ρ) r
        (TopCat.diskBoundary (Circle.loop 1 t)) =
      inclusionOfLists.{u, v, w} (canonicalWords ρ)
        (wordPath.{u, v} (wordOf (ρ r)) t) := by
  exact diskAttachmentDisk_attachingMaps_loop.{u, v, w} (canonicalWords ρ) r t

/-! ## Homotopy classes of signed words -/

/-- The included positive path represents the positive bouquet generator. -/
theorem fromPath_positivePath {I : Type v} (i : I) :
    FundamentalGroup.fromPath ⟦positivePath.{u, v} i⟧ =
      CircleBouquet.positiveGenerator.{u, v} i := by
  exact (CircleBouquet.positiveGenerator_eq_loop.{u, v} i).symm

/-- A signed path represents the image of its signed singleton word. -/
theorem fromPath_letterPath {I : Type v} (s : I × Bool) :
    FundamentalGroup.fromPath ⟦letterPath.{u, v} s⟧ =
      CircleBouquet.generatorEquiv.{u, v} I (FreeGroup.mk [s]) := by
  rcases s with ⟨i, b⟩
  cases b with
  | false =>
      have hnegative : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := by
        rw [FreeGroup.of, FreeGroup.inv_mk]
        rfl
      change FundamentalGroup.fromPath ⟦(positivePath.{u, v} i).symm⟧ =
        CircleBouquet.generatorEquiv.{u, v} I (FreeGroup.mk [(i, false)])
      rw [hnegative, map_inv, CircleBouquet.generatorEquiv_of]
      change (FundamentalGroup.fromPath ⟦positivePath.{u, v} i⟧)⁻¹ =
        (CircleBouquet.positiveGenerator.{u, v} i)⁻¹
      rw [fromPath_positivePath]
  | true =>
      change FundamentalGroup.fromPath ⟦positivePath.{u, v} i⟧ =
        CircleBouquet.generatorEquiv.{u, v} I (FreeGroup.of i)
      rw [CircleBouquet.generatorEquiv_of, fromPath_positivePath]

/-- The tail-first signed-word path represents its ordered free-group word. -/
theorem fromPath_wordPath {I : Type v} (l : List (I × Bool)) :
    FundamentalGroup.fromPath ⟦wordPath.{u, v} l⟧ =
      CircleBouquet.generatorEquiv.{u, v} I (FreeGroup.mk l) := by
  induction l with
  | nil =>
      change (1 : FundamentalGroup (CircleBouquet.space.{u, v} I)
        (CircleBouquet.basepoint.{u, v} I)) =
          CircleBouquet.generatorEquiv.{u, v} I (1 : FreeGroup I)
      exact (map_one (CircleBouquet.generatorEquiv.{u, v} I)).symm
  | cons s tail ih =>
      cases tail with
      | nil =>
          exact fromPath_letterPath.{u, v} s
      | cons t tail =>
          change FundamentalGroup.fromPath ⟦letterPath.{u, v} s⟧ *
              FundamentalGroup.fromPath ⟦wordPath.{u, v} (t :: tail)⟧ =
            CircleBouquet.generatorEquiv.{u, v} I (FreeGroup.mk (s :: t :: tail))
          rw [fromPath_letterPath, ih]
          exact (map_mul (CircleBouquet.generatorEquiv.{u, v} I)
            (FreeGroup.mk [s]) (FreeGroup.mk (t :: tail))).symm

/-- The canonical reduced word represents the given abstract free-group element. -/
theorem fromPath_wordOf {I : Type v} (g : FreeGroup I) :
    FundamentalGroup.fromPath ⟦wordPath.{u, v} (wordOf g)⟧ =
      CircleBouquet.generatorEquiv.{u, v} I g := by
  simpa only [mk_wordOf] using (fromPath_wordPath.{u, v} (wordOf g))

/-- Every signed list represents its image under the positive bouquet generator map. -/
theorem wordClass (I : Type v) :
    ∀ l : List (I × Bool), FundamentalGroup.fromPath ⟦wordPath.{u, v} l⟧ =
      CircleBouquet.generatorMap.{u, v} I (FreeGroup.mk l) := by
  intro l
  exact (fromPath_wordPath.{u, v} l).trans
    (DFunLike.congr_fun (CircleBouquet.generatorEquiv_toMonoidHom.{u, v} I)
      (FreeGroup.mk l))

/-- The canonical word represents the image of its abstract free-group element. -/
theorem abstractWordClass (I : Type v) :
    ∀ g : FreeGroup I, FundamentalGroup.fromPath ⟦wordPath.{u, v} (wordOf g)⟧ =
      CircleBouquet.generatorMap.{u, v} I g := by
  intro g
  exact (fromPath_wordOf.{u, v} g).trans
    (DFunLike.congr_fun (CircleBouquet.generatorEquiv_toMonoidHom.{u, v} I) g)

/-! ## Presentation and group-realization equivalences -/

/-- The positive class of a glued word circle is the class of its entire specified path. -/
theorem mapOfEq_wordCircle {I : Type v} (l : List (I × Bool)) :
    FundamentalGroup.mapOfEq (wordCircle.{u, v} l) (wordCircle_one.{u, v} l)
        (FundamentalGroup.fromPath ⟦Circle.loop 1⟧) =
      FundamentalGroup.fromPath ⟦wordPath.{u, v} l⟧ := by
  rw [FundamentalGroup.mapOfEq_fromPath]
  apply congrArg (fun p : Path (CircleBouquet.basepoint.{u, v} I)
    (CircleBouquet.basepoint.{u, v} I) => FundamentalGroup.fromPath ⟦p⟧)
  ext t
  exact wordCircle_loop.{u, v} l t

/-- Each positive attaching class is the image of its prescribed unreduced list relator. -/
theorem attachingClasses_eq_generatorEquiv {I : Type v} {R : Type w}
    (L : R → List (I × Bool)) (r : R) :
    attachingClasses.{u, v, w} L r =
      CircleBouquet.generatorEquiv.{u, v} I (FreeGroup.mk (L r)) := by
  exact (mapOfEq_wordCircle.{u, v} (L r)).trans (fromPath_wordPath.{u, v} (L r))

/-- Each positive abstract attaching class is the image of the given relator, without inversion. -/
theorem mapOfEq_abstractAttachingMaps {I : Type v} {R : Type w}
    (ρ : R → FreeGroup I) (r : R) :
    FundamentalGroup.mapOfEq (abstractAttachingMaps.{u, v, w} ρ r)
        (abstractAttachingMaps_one.{u, v, w} ρ r)
        (FundamentalGroup.fromPath ⟦Circle.loop 1⟧) =
      CircleBouquet.generatorEquiv.{u, v} I (ρ r) := by
  exact (mapOfEq_wordCircle.{u, v} (wordOf (ρ r))).trans
    (fromPath_wordOf.{u, v} (ρ r))

/-- The list-presentation quotient is identified with the fundamental group of its
indexed disk attachment. The isomorphism is induced by the original bouquet inclusion;
see May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–8. -/
def listPresentationEquiv {I : Type v} {R : Type w} (L : R → List (I × Bool)) :
    (FreeGroup I ⧸ Subgroup.normalClosure (Set.range (listRelators L))) ≃*
      FundamentalGroup (spaceOfLists.{u, v, w} L) (basepointOfLists.{u, v, w} L) :=
  (QuotientGroup.congr
    (Subgroup.normalClosure (Set.range (listRelators L)))
    (Subgroup.normalClosure (Set.range (attachingClasses.{u, v, w} L)))
    (CircleBouquet.generatorEquiv.{u, v} I) (by
      rw [CircleBouquet.generatorEquiv_toMonoidHom,
        Subgroup.map_normalClosure _ _ (CircleBouquet.generatorMap_bijective.{u, v} I).surjective,
        ← Set.range_comp']
      apply congrArg Subgroup.normalClosure
      apply congrArg Set.range
      funext r
      exact (DFunLike.congr_fun (CircleBouquet.generatorEquiv_toMonoidHom.{u, v} I)
        (FreeGroup.mk (L r))).symm.trans
          (attachingClasses_eq_generatorEquiv.{u, v, w} L r).symm)).trans
    (attachingClassQuotientEquiv.{u, v, w} L)

/-- On every original free-group word, the list-presentation equivalence is the
original-inclusion homomorphism applied to the positive bouquet generator map. -/
theorem listPresentationEquiv_mk {I : Type v} {R : Type w}
    (L : R → List (I × Bool)) (g : FreeGroup I) :
    listPresentationEquiv.{u, v, w} L
        (QuotientGroup.mk' (Subgroup.normalClosure (Set.range (listRelators L))) g) =
      FundamentalGroup.map (inclusionOfLists.{u, v, w} L)
        (CircleBouquet.basepoint.{u, v} I) (CircleBouquet.generatorMap.{u, v} I g) := by
  rw [listPresentationEquiv, MulEquiv.coe_trans, Function.comp_apply,
    QuotientGroup.congr_mk']
  exact Eq.trans
    (FundamentalGroup.diskAttachmentFundamentalGroupQuotientEquiv_mk
      (attachingMaps.{u, v, w} L) (CircleBouquet.basepoint.{u, v} I)
      (attachingMaps_one.{u, v, w} L) (CircleBouquet.generatorEquiv.{u, v} I g))
    (congrArg (FundamentalGroup.map (inclusionOfLists.{u, v, w} L)
      (CircleBouquet.basepoint.{u, v} I))
        (DFunLike.congr_fun (CircleBouquet.generatorEquiv_toMonoidHom.{u, v} I) g))

/-- The quotient by the given abstract relators is identified with the fundamental group
of their fixed canonical-word disk attachment; see May, *A Concise Course in Algebraic
Topology*, Chapter 2, §§6–8. -/
def presentationEquiv {I : Type v} {R : Type w} (ρ : R → FreeGroup I) :
    (FreeGroup I ⧸ Subgroup.normalClosure (Set.range ρ)) ≃*
      FundamentalGroup (spaceOfRelators.{u, v, w} ρ) (basepointOfRelators.{u, v, w} ρ) := by
  have hrel : listRelators (canonicalWords ρ) = ρ :=
    listRelators_canonicalWords ρ
  exact (QuotientGroup.quotientMulEquivOfEq
    (congrArg (fun f : R → FreeGroup I => Subgroup.normalClosure (Set.range f))
      hrel.symm)).trans (listPresentationEquiv.{u, v, w} (canonicalWords ρ))

/-- On every original free-group word, the abstract-presentation equivalence is the
original-inclusion homomorphism applied to the positive bouquet generator map. -/
theorem presentationEquiv_mk {I : Type v} {R : Type w}
    (ρ : R → FreeGroup I) (g : FreeGroup I) :
    presentationEquiv.{u, v, w} ρ
        (QuotientGroup.mk' (Subgroup.normalClosure (Set.range ρ)) g) =
      FundamentalGroup.map (inclusionOfLists.{u, v, w} (canonicalWords ρ))
        (CircleBouquet.basepoint.{u, v} I) (CircleBouquet.generatorMap.{u, v} I g) := by
  change listPresentationEquiv.{u, v, w} (canonicalWords ρ)
    (QuotientGroup.mk' (Subgroup.normalClosure
      (Set.range (listRelators (canonicalWords ρ)))) g) = _
  exact listPresentationEquiv_mk.{u, v, w} (canonicalWords ρ) g

/-- Including every kernel element as a relator generates exactly the canonical kernel. -/
theorem normalClosure_kernelRelatorFamily (G : Type z) [Group G] :
    Subgroup.normalClosure (Set.range (kernelRelatorFamily G)) =
      (FreeGroup.prod : FreeGroup G →* G).ker := by
  have hrange : Set.range (kernelRelatorFamily G) =
      ((FreeGroup.prod : FreeGroup G →* G).ker : Set (FreeGroup G)) :=
    Subtype.range_val
  rw [hrange, Subgroup.normalClosure_eq_self]

/-- Every group is identified with the fundamental group of its canonical kernel-presentation
space. The isomorphism sends each group element to its included positive circle class;
see May, *A Concise Course in Algebraic Topology*, Chapter 2, §8. -/
def canonicalFundamentalGroupEquiv (G : Type z) [Group G] :
    G ≃* FundamentalGroup (canonicalSpace.{u, z} G) (canonicalBasepoint.{u, z} G) :=
  (kernelQuotientEquiv G).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (normalClosure_kernelRelatorFamily G).symm).trans
      (presentationEquiv.{u, z, z} (kernelRelatorFamily G)))

/-- Each element corresponds to the positive class of its original included circle,
followed through the original bouquet inclusion into the canonical attachment. -/
theorem canonicalFundamentalGroupEquiv_apply (G : Type z) [Group G] (g : G) :
    canonicalFundamentalGroupEquiv.{u, z} G g =
      FundamentalGroup.map
        (inclusionOfLists.{u, z, z} (canonicalWords (kernelRelatorFamily G)))
        (CircleBouquet.basepoint.{u, z} G) (CircleBouquet.positiveGenerator.{u, z} g) := by
  change presentationEquiv.{u, z, z} (kernelRelatorFamily G)
    (QuotientGroup.mk' (Subgroup.normalClosure (Set.range (kernelRelatorFamily G)))
      (FreeGroup.of g)) = _
  simpa only [CircleBouquet.generatorMap_of] using
    (presentationEquiv_mk.{u, z, z} (kernelRelatorFamily G) (FreeGroup.of g))

end CircleBouquet.Presentation

end
