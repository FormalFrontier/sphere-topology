/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.CoveringMonodromy
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.ZMultiples

/-!
# Examples for covering-space monodromy

The quotient `ℝ → AddCircle (1 : ℝ)` has distinct points in its zero fiber joined by a path
in `ℝ`. Its monodromy therefore has a moving loop, outside the image of the fundamental
group of `ℝ`. The covering map and the discreteness of the integer-period subgroup are
provided by Mathlib's prior formalizations in `Mathlib.Topology.Covering.AddCircle` and
`Mathlib.Topology.Instances.ZMultiples`.

The discrete two-point trivial covering `Bool × Unit → Unit` has two distinct monodromy
orbits. Thus a connected base, even a point, does not by itself imply transitivity.
-/

@[expose] public section

/-- The period-one real quotient has a moving monodromy element, which does not come from a
loop in the total space based at its starting point. -/
private theorem realCircle_exists_moving_monodromy :
    ∃ (e e' : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0})
      (γ : FundamentalGroup (AddCircle (1 : ℝ)) 0),
      e ≠ e' ∧ (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromy γ e = e' ∧
        γ ∉ (FundamentalGroup.mapOfEq
          ⟨((↑) : ℝ → AddCircle (1 : ℝ)), (AddCircle.isCoveringMap_coe (1 : ℝ)).continuous⟩
          e.2).range := by
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let e : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0} := ⟨0, AddCircle.coe_zero _⟩
  let e' : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0} := ⟨1, AddCircle.coe_period _⟩
  have hne : e ≠ e' := by
    intro h
    exact zero_ne_one (congrArg Subtype.val h)
  obtain ⟨γ, hγ⟩ := (cov.exists_monodromy_eq_iff_joined e e').mpr
    (PathConnectedSpace.joined _ _)
  refine ⟨e, e', γ, hne, hγ, ?_⟩
  intro hmem
  have hfix := (cov.monodromy_eq_self_iff_mem_range e γ).mpr hmem
  exact hne (hfix.symm.trans hγ)

/-- A two-point discrete fiber over a point need not be a single monodromy orbit. -/
private theorem discreteCover_exists_distinct_monodromy_orbits :
    ∃ e e' : (Prod.snd : Bool × Unit → Unit) ⁻¹' {()},
      ¬ ∃ γ : FundamentalGroup Unit (),
        (IsCoveringMap.of_discreteTopology (Prod.snd : Bool × Unit → Unit)).monodromy γ e = e' := by
  let cov := IsCoveringMap.of_discreteTopology (Prod.snd : Bool × Unit → Unit)
  let e : (Prod.snd : Bool × Unit → Unit) ⁻¹' {()} := ⟨(false, ()), rfl⟩
  let e' : (Prod.snd : Bool × Unit → Unit) ⁻¹' {()} := ⟨(true, ()), rfl⟩
  refine ⟨e, e', ?_⟩
  intro h
  obtain ⟨Γ⟩ := (cov.exists_monodromy_eq_iff_joined e e').mp h
  have heq := cov.const_of_comp Γ.continuous (fun _ _ ↦ Subsingleton.elim _ _) 0 1
  have hbad : false = true := congrArg Prod.fst (Γ.source.symm.trans (heq.trans Γ.target))
  cases hbad
