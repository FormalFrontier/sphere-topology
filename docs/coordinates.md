# Integral coordinates for all-simplex chains

The canonical home is released
[`SimplicialObjects.ChainCoordinates`](https://github.com/FormalFrontier/simplicial-objects/blob/143f667bdeb0aeccd02e6475781d5c456f00c95b/SimplicialObjects/ChainCoordinates.lean),
publicly imported by `SphereTopology.Homology.Singular.SmallChains`.
The four names remain in `AlgebraicTopology`; existing Sphere imports expose
those same declarations, not aliases or separate Sphere definitions.

The declarations below use `open CategoryTheory`, `open scoped Simplicial`,
`universe u` and `namespace AlgebraicTopology`, as in that source.

## Coefficients and degreewise coordinates

```lean
abbrev integerCoefficients : ModuleCat.{u} ℤ :=
  (ModuleCat.uliftFunctor.{u} ℤ).obj (ModuleCat.of ℤ ℤ)

noncomputable def chainGroupIsoFinsupp (X : SSet.{u}) (n : ℕ) :
    (X.chainComplex integerCoefficients).X n ≅
      ModuleCat.of ℤ (X _⦋n⦌ →₀ ℤ)
```

The coefficient carrier is `ULift.{u} ℤ`, with the module structure supplied by
`ModuleCat.uliftFunctor`, not a new or arbitrarily selected integer module.
The source first identifies Mathlib's simplicial-chain coproduct with the
finitely supported lifted coefficients using
`X.isColimitChainComplexXCofan integerCoefficients n` and
`ModuleCat.finsuppCoconeIsColimit ℤ (ULift ℤ) (X _⦋n⦌)`.
It then removes the coefficient lift by
`Finsupp.mapRange.linearEquiv (ULift.moduleEquiv (R := ℤ) (M := ℤ))`.
The target has the canonical integer module structure on
`X _⦋n⦌ →₀ ℤ`; the simplex carrier and universe are unchanged.
There is no finiteness, nonemptiness, topology, compactness or separation
hypothesis on the simplicial set. Singular simplicial sets are one application,
not an extra restriction in the coordinate API.

## Characteristic laws

```lean
theorem ι_chainGroupIsoFinsupp_hom (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex (R := integerCoefficients) x ≫ (chainGroupIsoFinsupp X n).hom =
      ModuleCat.ofHom ((Finsupp.lsingle x).comp ULift.moduleEquiv.toLinearMap)

theorem chainGroupIsoFinsupp_hom_ι (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌) :
    (chainGroupIsoFinsupp X n).hom.hom
        ((X.ιChainComplex (R := integerCoefficients) x).hom (ULift.up (1 : ℤ))) =
      Finsupp.single x 1
```

The first law is an equality of module morphisms on each simplex summand; it
computes every lifted integer coefficient, not only one. The second, registered
`@[simp]` in the released source, computes the unit basis chain. Both use the
same coefficient provider as the degreewise isomorphism.

## Scope and compatibility

These coordinates use **all** simplices, including degenerate simplices.
They identify one module in each degree. The four declarations do not construct
a chain isomorphism, natural isomorphism, normalized-chain comparison, or
homology isomorphism. In particular, a nonzero singular chain, even a cycle,
does not establish a nonzero class in `H₁` without showing it is not a boundary.
Sphere's separate boundary, small-inclusion and subdivision lemmas remain in
Sphere; they are not additional declarations of the coordinate dependency.
The generic coordinate statement retains arbitrary `SSet.{u}`, and Sphere's
singular models, categorical-coefficient component interfaces and covering
transfer retain their own universes, providers and hypotheses.

Use a Sphere release that re-exports the coordinate dependency together with
its matching Simplicial Objects pin. A legacy Sphere release defining the same
four names cannot be co-imported with the new canonical coordinate module.
Existing downstream pins do not update automatically, and arbitrary release
pairs are not promised compatible.

## References and credit

J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 16, gives
mathematical background. Mathlib's simplicial-chain coproducts by Joël Riou and
Andrew Yang and module-category colimits by Kim Morrison and Joël Riou supply
the cofans; Mathlib supplies the lifted module and linear-equivalence APIs.
Formal Frontier Agents, including Prism, supplied the coordinate formalization,
originally used in Sphere and now maintained in Simplicial Objects.
See [credits](CREDITS.md) and the dependency's module references.
