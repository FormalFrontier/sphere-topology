/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import SphereTopology.Topology.CoveringEquivalence
public import SphereTopology.Topology.CoveringMonodromy
public import SphereTopology.Topology.DeckGroup

/-!
# Deck transformations and monodromy

Restriction to a point fiber gives a homomorphism from the deck group to the centralizer
of monodromy in the permutation group of that fiber. No connectivity hypotheses are needed
for this homomorphism. If the base is path connected, restriction to the whole fiber is
faithful, even when the total space is disconnected or empty. Local path connectedness is
not needed for faithfulness.

If the total space is locally path connected and the base is path connected, restriction
is a multiplicative equivalence `IsCoveringMap.deckMonodromyEquiv`. A commuting permutation
extends by based lifting on each open path component, and whole-fiber uniqueness makes the
extensions for a permutation and its inverse into inverse maps. The total space may be
empty; no point of it or surjectivity of the covering is assumed.

For path-connected, locally path-connected total space,
`IsCoveringMap.deckMonodromyEquivOfPathConnected` uses the fiber over the image of a supplied
point, with no connectedness assumption on the base. Both equivalences have the same
canonical restriction homomorphism as their forward map. These formulations generalize
the connected, locally path-connected setting of May, Chapter 3, §7.

The target is a subgroup of the permutation group of the point fiber, not a group structure
on that fiber. This centralizer is distinct from a point stabilizer or the kernel of the
monodromy representation, both of which are subgroups of the fundamental group.

The fiber action is the existing `deck.instMulActionFiber`; both deck transformations and
permutations multiply by composition, so restriction involves no inversion.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §7, p. 29,
  for restriction of maps of covering spaces to a fiber and its inverse.
* Mathlib's based lifting criterion and the open-path-component gluing argument.
* Mathlib's deck group (Kim Morrison), covering-space monodromy and lifting (Junyan Xu),
  and restriction of group actions to invariant subsets.
* The covering-space fiber action and monodromy naturality in this library.
-/

@[expose] public section

universe u v w

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B} (cov : IsCoveringMap p)

/-- Deck transformations intertwine monodromy along every homotopy class of paths.
This is naturality for their continuous maps over the base. -/
theorem monodromy_deck_smul {x y : B} (γ : Path.Homotopic.Quotient x y)
    (g : deck p) (e : p ⁻¹' {x}) :
    cov.monodromy γ (g • e) = g • cov.monodromy γ e := by
  apply Subtype.ext
  exact congrArg Subtype.val (cov.monodromy_naturality cov
    ⟨fun z ↦ g • z, (g : E ≃ₜ E).continuous⟩ (deck.comp_eq g) γ e)

/-- The permutation induced by a deck transformation commutes with every monodromy
permutation on the fiber. -/
theorem commute_monodromyPerm_deck (b : B) (γ : FundamentalGroup B b) (g : deck p) :
    Commute (cov.monodromyPerm b γ)
      (MulAction.toPermHom (deck p) (p ⁻¹' {b}) g) := by
  ext e
  exact congrArg Subtype.val (cov.monodromy_deck_smul γ g e)

/-- Restriction of deck transformations to a fiber, with codomain the centralizer of
monodromy. This is the forward map in the covering-space comparison of May, Chapter 3,
§7, p. 29, without connectedness, local path connectedness, or surjectivity assumptions. -/
noncomputable def deckMonodromyHom (b : B) :
    deck p →* Subgroup.centralizer (Set.range (cov.monodromyPerm b)) :=
  (MulAction.toPermHom (deck p) (p ⁻¹' {b})).codRestrict _ fun g ↦ by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨γ, rfl⟩
    exact (cov.commute_monodromyPerm_deck b γ g).eq

/-- Restriction acts by the original deck transformation on the underlying total-space
coordinate. -/
@[simp] theorem deckMonodromyHom_apply_coe (b : B) (g : deck p) (e : p ⁻¹' {b}) :
    ((cov.deckMonodromyHom b g).val e).val = g • e.val :=
  rfl

include cov

/-- Deck transformations of a cover over a path-connected base are equal if their actions
agree on a whole fiber. This is the uniqueness part of restriction to a fiber in May,
Chapter 3, §7, p. 29; the total space need not be connected, locally path connected, or
nonempty. -/
theorem deck_ext [PathConnectedSpace B] (b : B) {g h : deck p}
    (he : ∀ e : p ⁻¹' {b}, g • e.val = h • e.val) : g = h := by
  have heq := cov.eq_of_comp_eq_of_eqOn_fiber cov.isSeparatedMap
    cov.isLocalHomeomorph.isLocallyInjective
    (⟨fun z ↦ g • z, (g : E ≃ₜ E).continuous⟩ : C(E, E))
    ⟨fun z ↦ h • z, (h : E ≃ₜ E).continuous⟩ (deck.comp_eq g) (deck.comp_eq h) b he
  apply eq_of_smul_eq_smul (α := E)
  intro e
  exact congrArg (fun f : C(E, E) ↦ f e) heq

/-- Restriction to the monodromy centralizer is injective over a path-connected base.
No local path connectedness of either space is required. -/
theorem deckMonodromyHom_injective [PathConnectedSpace B] (b : B) :
    Function.Injective (cov.deckMonodromyHom b) := by
  intro g h heq
  apply cov.deck_ext b
  intro e
  simpa only [deckMonodromyHom_apply_coe] using
    congrArg (fun α : Subgroup.centralizer (Set.range (cov.monodromyPerm b)) ↦
      (α.val e).val) heq

section Extension

variable {b : B}

private theorem centralizer_monodromy_apply
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b)))
    (γ : FundamentalGroup B b) (e : p ⁻¹' {b}) :
    cov.monodromy γ (α.val e) = α.val (cov.monodromy γ e) :=
  congrArg (fun σ : Equiv.Perm (p ⁻¹' {b}) ↦ σ e)
    ((Subgroup.mem_centralizer_iff.mp α.property) _ ⟨γ, rfl⟩)

private theorem centralizer_range_le
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) (e : p ⁻¹' {b}) :
    (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.property).range ≤
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ (α.val e).property).range := by
  intro γ hγ
  apply (cov.monodromy_eq_self_iff_mem_range (α.val e) γ).mp
  rw [cov.centralizer_monodromy_apply α γ e,
    (cov.monodromy_eq_self_iff_mem_range e γ).mpr hγ]

private theorem exists_based_monodromy_lift
    {A : Type w} [TopologicalSpace A] [PathConnectedSpace A]
    [LocallyPathConnectedSpace A] (i : C(A, E)) (a₀ : A) (ha : p (i a₀) = b)
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) :
    ∃ F : C(A, E), F a₀ = (α.val ⟨i a₀, ha⟩).val ∧ p ∘ F = p ∘ i := by
  subst b
  let e : p ⁻¹' {p (i a₀)} := ⟨i a₀, rfl⟩
  have hπ : (FundamentalGroup.map ((⟨p, cov.continuous⟩ : C(E, B)).comp i) a₀).range ≤
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ (α.val e).property).range := by
    apply le_trans _ (cov.centralizer_range_le α e)
    rintro _ ⟨γ, rfl⟩
    refine ⟨FundamentalGroup.map i a₀ γ, ?_⟩
    change FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ rfl
      (FundamentalGroup.map i a₀ γ) = _
    simp only [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  exact (cov.existsUnique_continuousMap_lifts_of_range_le
    (f := (⟨p, cov.continuous⟩ : C(E, B)).comp i) (a₀ := a₀) (e₀ := (α.val e).val)
    (show p (α.val e).val = p (i a₀) from (α.val e).property) hπ).exists

private theorem based_monodromy_lift_fiber
    {A : Type w} [TopologicalSpace A] [PathConnectedSpace A]
    (i F : C(A, E)) (hF : p ∘ F = p ∘ i) (a₀ : A) (ha₀ : p (i a₀) = b)
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b)))
    (h₀ : F a₀ = (α.val ⟨i a₀, ha₀⟩).val) (a : A) (ha : p (i a) = b) :
    F a = (α.val ⟨i a, ha⟩).val := by
  let δ := PathConnectedSpace.somePath a₀ a
  let γ : FundamentalGroup B b :=
    (((Path.Homotopic.Quotient.mk δ).map i).map ⟨p, cov.continuous⟩).cast ha₀.symm ha.symm
  have hi : cov.monodromy γ ⟨i a₀, ha₀⟩ = ⟨i a, ha⟩ :=
    cov.monodromy_eq_of_map_eq ((Path.Homotopic.Quotient.mk δ).map i) (by
      change ((Path.Homotopic.Quotient.mk δ).map i).map ⟨p, cov.continuous⟩ =
        Path.Homotopic.Quotient.cast γ ha₀ ha
      simp only [γ, Path.Homotopic.Quotient.cast_cast,
        Path.Homotopic.Quotient.cast_rfl_rfl])
  have hcomp : (⟨p, cov.continuous⟩ : C(E, B)).comp F =
      (⟨p, cov.continuous⟩ : C(E, B)).comp i := ContinuousMap.ext (congr_fun hF)
  have hFa₀ : p (F a₀) = b := (congr_fun hF a₀).trans ha₀
  have hFa : p (F a) = b := (congr_fun hF a).trans ha
  have map_loop_eq (f g : C(A, B)) (hfg : f = g)
      (hx : f a₀ = b) (hy : f a = b) (hx' : g a₀ = b) (hy' : g a = b) :
      ((Path.Homotopic.Quotient.mk δ).map f).cast hx.symm hy.symm =
        ((Path.Homotopic.Quotient.mk δ).map g).cast hx'.symm hy'.symm := by
    subst g
    rfl
  have hloop : (((Path.Homotopic.Quotient.mk δ).map F).map
      ⟨p, cov.continuous⟩).cast hFa₀.symm hFa.symm = γ := by
    simp only [γ, ← Path.Homotopic.Quotient.map_comp]
    exact map_loop_eq _ _ hcomp hFa₀ hFa ha₀ ha
  have hFF : cov.monodromy γ ⟨F a₀, hFa₀⟩ = ⟨F a, hFa⟩ := by
    rw [← hloop]
    apply cov.monodromy_eq_of_map_eq ((Path.Homotopic.Quotient.mk δ).map F)
    change ((Path.Homotopic.Quotient.mk δ).map F).map ⟨p, cov.continuous⟩ =
      ((((Path.Homotopic.Quotient.mk δ).map F).map ⟨p, cov.continuous⟩).cast
        hFa₀.symm hFa.symm).cast hFa₀ hFa
    simp only [Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]
  have hbase : (⟨F a₀, hFa₀⟩ : p ⁻¹' {b}) = α.val ⟨i a₀, ha₀⟩ := Subtype.ext h₀
  rw [hbase, cov.centralizer_monodromy_apply α, hi] at hFF
  exact (congrArg Subtype.val hFF).symm

private theorem exists_pathComponent_monodromy_lift [PathConnectedSpace B]
    [LocallyPathConnectedSpace E]
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) (x : E) :
    ∃ F : C(pathComponent x, E), p ∘ F = p ∘ Subtype.val ∧
      ∀ (e : p ⁻¹' {b}) (he : e.val ∈ pathComponent x), F ⟨e.val, he⟩ = (α.val e).val := by
  let : PathConnectedSpace (pathComponent x) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent
  let : LocallyPathConnectedSpace (pathComponent x) :=
    (IsOpen.pathComponent x).locallyPathConnectedSpace
  obtain ⟨a₀, ha₀⟩ := cov.comp_subtypeVal_pathComponent_surjective x b
  let i : C(pathComponent x, E) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨F, h₀, hF⟩ := cov.exists_based_monodromy_lift i a₀ ha₀ α
  refine ⟨F, hF, fun e he ↦ ?_⟩
  exact cov.based_monodromy_lift_fiber i F hF a₀ ha₀ α h₀ ⟨e.val, he⟩ e.property

/-- A permutation commuting with monodromy extends to a continuous map over the base.
The total space may be disconnected or empty; the construction glues based lifts on its
open path components. This is the map-extension step in May, Chapter 3 §7, p. 29. -/
private theorem exists_continuousMap_monodromy_extension [PathConnectedSpace B]
    [LocallyPathConnectedSpace E]
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) :
    ∃ F : C(E, E), p ∘ F = p ∧ ∀ e : p ⁻¹' {b}, F e.val = (α.val e).val := by
  classical
  let Components := {s : Set E // ∃ x : E, s = pathComponent x}
  let component (x : E) : Components := ⟨pathComponent x, x, rfl⟩
  have hlifts (s : Components) :
      ∃ F : C(s.val, E), p ∘ F = p ∘ Subtype.val ∧
        ∀ (e : p ⁻¹' {b}) (he : e.val ∈ s.val), F ⟨e.val, he⟩ = (α.val e).val := by
    rcases s with ⟨s, x, rfl⟩
    exact cov.exists_pathComponent_monodromy_lift α x
  choose lifts hlifts_proj hlifts_fiber using hlifts
  let extend (s : Components) (x : E) : E :=
    if hx : x ∈ s.val then lifts s ⟨x, hx⟩ else x
  let F (x : E) : E := extend (component x) x
  have hcomponent (s : Components) (y : s.val) : component y.val = s := by
    apply Subtype.ext
    obtain ⟨x, hx⟩ := s.property
    change pathComponent y.val = s.val
    exact (pathComponent_congr (hx ▸ y.property)).trans hx.symm
  have hrestrict (s : Components) (y : s.val) : F y.val = lifts s y := by
    change extend (component y.val) y.val = lifts s y
    rw [hcomponent s y]
    simp only [extend, dite_eq_left y.property]
  have hcont : Continuous F := by
    apply continuous_of_continuousOn_iUnion_of_isOpen (s := fun s : Components ↦ s.val)
    · intro s
      rw [continuousOn_iff_continuous_domRestrict]
      convert (lifts s).continuous using 1
      funext y
      exact hrestrict s y
    · rintro ⟨s, x, rfl⟩
      exact IsOpen.pathComponent x
    · apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_iUnion.mpr ⟨component x, mem_pathComponent_self x⟩
  refine ⟨⟨F, hcont⟩, funext fun x ↦ ?_, fun e ↦ ?_⟩
  · change p (F x) = p x
    rw [hrestrict (component x) ⟨x, mem_pathComponent_self x⟩]
    exact congr_fun (hlifts_proj (component x)) ⟨x, mem_pathComponent_self x⟩
  · change F e.val = (α.val e).val
    rw [hrestrict (component e.val) ⟨e.val, mem_pathComponent_self e.val⟩]
    exact hlifts_fiber (component e.val) e (mem_pathComponent_self e.val)

/-- A permutation of a fiber commuting with monodromy extends to a deck transformation.
This is the extension part of May, Chapter 3 §7, p. 29, allowing disconnected or empty total
spaces. Only the base is path connected, and local path connectedness is needed only of
the total space. No surjectivity or inhabitance of a fiber is assumed. -/
private theorem exists_deck_monodromy_extension [PathConnectedSpace B] [LocallyPathConnectedSpace E]
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) :
    ∃ g : deck p, ∀ e : p ⁻¹' {b}, g • e.val = (α.val e).val := by
  obtain ⟨F, hFp, hF⟩ := cov.exists_continuousMap_monodromy_extension α
  obtain ⟨G, hGp, hG⟩ := cov.exists_continuousMap_monodromy_extension (α⁻¹)
  have hGF : G.comp F = ContinuousMap.id E := by
    refine cov.eq_of_comp_eq_of_eqOn_fiber cov.isSeparatedMap
      cov.isLocalHomeomorph.isLocallyInjective (G.comp F) (ContinuousMap.id E) ?_ rfl b ?_
    · change p ∘ (G ∘ F) = p
      rw [← Function.comp_assoc, hGp, hFp]
    · intro e
      change G (F e.val) = e.val
      rw [hF e, hG (α.val e)]
      exact congrArg Subtype.val (α.val.symm_apply_apply e)
  have hFG : F.comp G = ContinuousMap.id E := by
    refine cov.eq_of_comp_eq_of_eqOn_fiber cov.isSeparatedMap
      cov.isLocalHomeomorph.isLocallyInjective (F.comp G) (ContinuousMap.id E) ?_ rfl b ?_
    · change p ∘ (F ∘ G) = p
      rw [← Function.comp_assoc, hFp, hGp]
    · intro e
      change F (G e.val) = e.val
      rw [hG e, hF ((α⁻¹).val e)]
      exact congrArg Subtype.val (α.val.apply_symm_apply e)
  let g : E ≃ₜ E :=
    { toFun := F
      invFun := G
      left_inv := fun x ↦ DFunLike.congr_fun hGF x
      right_inv := fun x ↦ DFunLike.congr_fun hFG x
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
  exact ⟨⟨g, hFp⟩, hF⟩

end Extension

section PathConnectedExtension

private theorem mapOfEq_range_eq_of_centralizer {b : B}
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) (e : p ⁻¹' {b}) :
    (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.2).range =
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ (α.val e).2).range := by
  ext γ
  rw [← cov.monodromy_eq_self_iff_mem_range e γ,
    ← cov.monodromy_eq_self_iff_mem_range (α.val e) γ,
    centralizer_monodromy_apply cov α γ e]
  exact ⟨congrArg α.val, fun h ↦ α.val.injective h⟩

private theorem exists_deck_smul_eq_basepoint
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm (p e₀)))) :
    ∃ g : deck p, g • e₀ = (α.val ⟨e₀, rfl⟩).val := by
  let e' := α.val ⟨e₀, rfl⟩
  have hmap : FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ (show p e₀ = p e₀ from rfl) =
      FundamentalGroup.map ⟨p, cov.continuous⟩ e₀ := by
    ext γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      Path.Homotopic.Quotient.cast_rfl_rfl]
  have hπ : (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range =
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e'.2).range := by
    rw [← hmap]
    exact mapOfEq_range_eq_of_centralizer cov α ⟨e₀, rfl⟩
  let H := cov.homeomorphOfRangeEq cov e₀ e'.val e'.2.symm hπ
  have hH : p ∘ H = p := funext fun e ↦
    cov.homeomorphOfRangeEq_apply_proj cov e₀ e'.val e'.2.symm hπ e
  refine ⟨⟨H, hH⟩, ?_⟩
  exact cov.homeomorphOfRangeEq_apply_basepoint cov e₀ e'.val e'.2.symm hπ

/-- A permutation commuting with monodromy on an occupied fiber of a covering with
path-connected, locally path-connected total space extends to a deck transformation on that
whole fiber. This is the extension part of May, Chapter 3 §7, p. 29, with no connectedness or
local path connectedness assumption on the base and no surjectivity assumption on the cover.
The explicit point specifies the occupied fiber. -/
private theorem exists_deck_smul_eq_of_pathConnected
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm (p e₀)))) :
    ∃ g : deck p, ∀ e : p ⁻¹' {p e₀}, g • e.val = (α.val e).val := by
  obtain ⟨g, hg⟩ := cov.exists_deck_smul_eq_basepoint e₀ α
  refine ⟨g, fun e ↦ ?_⟩
  let ebase : p ⁻¹' {p e₀} := ⟨e₀, rfl⟩
  obtain ⟨γ, hγ⟩ := (cov.exists_monodromy_eq_iff_joined ebase e).mpr
    (PathConnectedSpace.joined e₀ e.val)
  have hg' : (g • ebase : p ⁻¹' {p e₀}) = α.val ebase := Subtype.ext hg
  have he : (g • e : p ⁻¹' {p e₀}) = α.val e := by
    calc
      g • e = g • cov.monodromy γ ebase := by rw [hγ]
      _ = cov.monodromy γ (g • ebase) :=
        (cov.monodromy_deck_smul γ g ebase).symm
      _ = cov.monodromy γ (α.val ebase) := by rw [hg']
      _ = α.val (cov.monodromy γ ebase) := centralizer_monodromy_apply cov α γ ebase
      _ = α.val e := by rw [hγ]
  exact congrArg Subtype.val he

end PathConnectedExtension

/-- Restriction identifies the deck group with the centralizer of monodromy on a fiber
when the base is path connected and the total space is locally path connected. This is the
restriction comparison of May, Chapter 3, §7, p. 29, generalized to disconnected or empty
total spaces. No surjectivity or nonemptiness is assumed. -/
noncomputable def deckMonodromyEquiv [PathConnectedSpace B] [LocallyPathConnectedSpace E]
    (b : B) : deck p ≃* Subgroup.centralizer (Set.range (cov.monodromyPerm b)) :=
  MulEquiv.ofBijective (cov.deckMonodromyHom b) ⟨cov.deckMonodromyHom_injective b, by
    intro α
    obtain ⟨g, hg⟩ := cov.exists_deck_monodromy_extension α
    exact ⟨g, Subtype.ext (Equiv.ext fun e ↦ Subtype.ext (hg e))⟩⟩

/-- The forward homomorphism of the comparison is restriction to the fiber. -/
@[simp] theorem deckMonodromyEquiv_toMonoidHom [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] (b : B) :
    (cov.deckMonodromyEquiv b).toMonoidHom = cov.deckMonodromyHom b :=
  rfl

/-- The comparison applies the original deck transformation to each fiber coordinate. -/
@[simp] theorem deckMonodromyEquiv_apply_coe [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] (b : B) (g : deck p) (e : p ⁻¹' {b}) :
    ((cov.deckMonodromyEquiv b g).val e).val = g • e.val :=
  rfl

/-- The inverse comparison extends the given permutation on every point of the fiber. -/
@[simp] theorem deckMonodromyEquiv_symm_smul [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] (b : B)
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) (e : p ⁻¹' {b}) :
    (cov.deckMonodromyEquiv b).symm α • e.val = (α.val e).val := by
  rw [← cov.deckMonodromyEquiv_apply_coe b, MulEquiv.apply_symm_apply]

/-- For path-connected, locally path-connected total space, restriction identifies the
deck group with the monodromy centralizer on the fiber containing a specified point.
This is the occupied-fiber form of May, Chapter 3, §7, p. 29. The base need not be path
connected or locally path connected, and the covering need not be surjective. -/
noncomputable def deckMonodromyEquivOfPathConnected [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) :
    deck p ≃* Subgroup.centralizer (Set.range (cov.monodromyPerm (p e₀))) :=
  MulEquiv.ofBijective (cov.deckMonodromyHom (p e₀)) ⟨by
    intro g h hgh
    apply (deck.evalEmbedding cov.isSeparatedMap
      cov.isLocalHomeomorph.isLocallyInjective e₀).injective
    apply Subtype.ext
    exact congrArg (fun α ↦ (α.val ⟨e₀, rfl⟩).val) hgh, by
    intro α
    obtain ⟨g, hg⟩ := cov.exists_deck_smul_eq_of_pathConnected e₀ α
    exact ⟨g, Subtype.ext (Equiv.ext fun e ↦ Subtype.ext (hg e))⟩⟩

/-- The occupied-fiber comparison has the same restriction homomorphism. -/
@[simp] theorem deckMonodromyEquivOfPathConnected_toMonoidHom [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) :
    (cov.deckMonodromyEquivOfPathConnected e₀).toMonoidHom = cov.deckMonodromyHom (p e₀) :=
  rfl

/-- The occupied-fiber comparison applies the deck transformation to each coordinate. -/
@[simp] theorem deckMonodromyEquivOfPathConnected_apply_coe [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) (g : deck p) (e : p ⁻¹' {p e₀}) :
    ((cov.deckMonodromyEquivOfPathConnected e₀ g).val e).val = g • e.val :=
  rfl

/-- The inverse occupied-fiber comparison extends the permutation on the whole fiber. -/
@[simp] theorem deckMonodromyEquivOfPathConnected_symm_smul [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E)
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm (p e₀))))
    (e : p ⁻¹' {p e₀}) :
    (cov.deckMonodromyEquivOfPathConnected e₀).symm α • e.val = (α.val e).val := by
  rw [← cov.deckMonodromyEquivOfPathConnected_apply_coe e₀, MulEquiv.apply_symm_apply]

/-- Where both constructions apply, they are equal as multiplicative equivalence data:
their forward maps are the same canonical restriction. -/
theorem deckMonodromyEquiv_eq_of_pathConnected [PathConnectedSpace B] [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) :
    cov.deckMonodromyEquiv (p e₀) = cov.deckMonodromyEquivOfPathConnected e₀ := by
  apply MulEquiv.ext
  intro g
  rfl

end IsCoveringMap
