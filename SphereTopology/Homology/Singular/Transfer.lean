/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Topology.SingularLifts
public import SimplicialObjects.FiniteFiberTransfer
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Singular transfer for finite-fiber covering maps

A covering map with finite point fibers gives a transfer on the all-simplex
singular chain complex, with a coefficient object in a preadditive category
with the requisite coproducts. Applying homology gives the ordinary singular
homology transfer. The spaces need not be connected, locally connected or
nonempty, and the covering need not be surjective or have constant degree.

The construction uses evaluation of singular lifts and the finite-fiber
simplicial transfer. These are Mathlib's singular chain and homology objects;
no normalized-chain, tensor-coefficient, CGWH, negative-degree, reduced,
relative or deck-equivariant comparison is made.

## References

May, *A Concise Course in Algebraic Topology*, revised edition, §16, Problem 3,
motivates the covering transfer and its sheet identity. Mathlib supplies the
singular chain and homology functors; Simplicial Objects supplies the
equifibered finite-fiber transfer specialized here.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe w v u

namespace IsCoveringMap

variable {X Y : TopCat.{w}} {p : Y ⟶ X}

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Transfer on singular chains for a covering map with finite point fibers.
The coefficient is an arbitrary object, with no constant-sheet assumption. -/
noncomputable def singularChainComplexTransfer (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) :
    ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ⟶
      ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj Y :=
  SSet.chainComplexTransfer (TopCat.toSSet.map p) hp.toSSet_map_equifibered
    (fun s => by
      let := hf (X.toSSetObjEquiv (op ⦋0⦌) s default)
      exact hp.finite_singularLift (op ⦋0⦌) s default) R

/-- Each component is the finite-fiber coproduct transfer. -/
theorem singularChainComplexTransfer_f (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (n : ℕ) :
    (hp.singularChainComplexTransfer hf R).f n =
      sigmaConstTransfer ((TopCat.toSSet.map p).app (op ⦋n⦌))
        (fun s => by
          let := hf (X.toSSetObjEquiv (op ⦋n⦌) s default)
          exact hp.finite_singularLift (op ⦋n⦌) s default) R :=
  rfl

/-- A singular simplex transfers to the sum of all of its lifts. -/
theorem summandι_singularChainComplexTransfer_f (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C)
    {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) s ≫
        (hp.singularChainComplexTransfer hf R).f n =
      ∑ᶠ t : {t : (TopCat.toSSet.obj Y) _⦋n⦌ // (TopCat.toSSet.map p).app _ t = s},
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) t.val := by
  rw [singularChainComplexTransfer_f]
  exact ι_sigmaConstTransfer _ _ _ _

/-- Transfer followed by pushforward multiplies singular chains by the sheet
number, as in May, §16, Problem 3. Finiteness is required separately from the
cardinality equality. -/
theorem singularChainComplexTransfer_comp_map (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (d : ℕ)
    (hd : ∀ x : X, Nat.card {y : Y // p y = x} = d) :
    hp.singularChainComplexTransfer hf R ≫
        ((AlgebraicTopology.singularChainComplexFunctor C).obj R).map p =
      d • 𝟙 (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X) := by
  apply SSet.chainComplexTransfer_comp_map (TopCat.toSSet.map p)
    hp.toSSet_map_equifibered
    (fun s => by
      let := hf (X.toSSetObjEquiv (op ⦋0⦌) s default)
      exact hp.finite_singularLift (op ⦋0⦌) s default) R d
  intro s
  exact (Nat.card_congr (hp.singularLiftEquiv (op ⦋0⦌) s default)).trans
    (hd (X.toSSetObjEquiv (op ⦋0⦌) s default))

variable [CategoryWithHomology C]

/-- The ordinary singular homology transfer induced by the chain transfer. -/
noncomputable def singularHomologyTransfer (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (q : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor C q).obj R).obj X ⟶
      ((AlgebraicTopology.singularHomologyFunctor C q).obj R).obj Y :=
  SSet.homologyTransfer (TopCat.toSSet.map p) hp.toSSet_map_equifibered
    (fun s => by
      let := hf (X.toSSetObjEquiv (op ⦋0⦌) s default)
      exact hp.finite_singularLift (op ⦋0⦌) s default) R q

/-- The homology transfer is the image of the chain transfer under homology. -/
theorem singularHomologyTransfer_eq_map (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (q : ℕ) :
    hp.singularHomologyTransfer hf R q =
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) q).map
        (hp.singularChainComplexTransfer hf R) :=
  rfl

/-- Transfer followed by pushforward multiplies ordinary singular homology by
the sheet number, in every nonnegative degree, as in May, §16, Problem 3. -/
theorem singularHomologyTransfer_comp_map (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (d q : ℕ)
    (hd : ∀ x : X, Nat.card {y : Y // p y = x} = d) :
    hp.singularHomologyTransfer hf R q ≫
        ((AlgebraicTopology.singularHomologyFunctor C q).obj R).map p =
      d • 𝟙 (((AlgebraicTopology.singularHomologyFunctor C q).obj R).obj X) := by
  apply SSet.homologyTransfer_comp_map (TopCat.toSSet.map p)
    hp.toSSet_map_equifibered
    (fun s => by
      let := hf (X.toSSetObjEquiv (op ⦋0⦌) s default)
      exact hp.finite_singularLift (op ⦋0⦌) s default) R d q
  intro s
  exact (Nat.card_congr (hp.singularLiftEquiv (op ⦋0⦌) s default)).trans
    (hd (X.toSSetObjEquiv (op ⦋0⦌) s default))

end IsCoveringMap
