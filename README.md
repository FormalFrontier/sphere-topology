# Sphere Topology

A reusable Lean library for circle fundamental groups, continuous fields on
spheres, covering-space lifts of singular simplices, and integral singular
homology. It develops finite-support subdivision and cover-small chains, ordinary
and nonnegative reduced Mayer–Vietoris sequences, and explicit circle and
standard two-sphere computations. Their antipodal sign obstruction gives a
continuous-field hairy-ball theorem for the unit two-sphere. Import the
aggregate `SphereTopology` or the focused modules listed below; no source
research repository is needed to use the library.

Authors: Formal Frontier Agents.

Original project contributions are licensed [Apache-2.0](LICENSE); see
[credits and provenance](docs/CREDITS.md). See the [API reference](docs/API.md) and [guide](docs/README.md) for the
constructions and conventions.

## Headline results

The subdivision, Mayer–Vietoris and sphere computations below use integer
coefficients; singular chains have finite support. The zeroth augmentation
criterion and nonbasepoint-component presentation also permit categorical
coefficient objects. The homology computations
use the unit spheres in `EuclideanSpace ℝ (Fin 2)` and
`EuclideanSpace ℝ (Fin 3)`. The fundamental-group calculator uses Mathlib's real
additive circle and complex unit circle.

- **Normalized circle fundamental group.** For every real `T ≠ 0`,
  [`AddCircle.fundamentalGroupEquivInt`](SphereTopology/Homotopy/Circle.lean)
  identifies `π₁(AddCircle T, 0)` with `Multiplicative ℤ`. The projected segment
  `t ↦ T*n*t mod T` has coordinate `n`, and any lift starting at zero ends at
  `T` times the computed integer. The signed-period homeomorphism to the complex
  unit `Circle` agrees with its counterclockwise-normalized calculator, also
  when `T < 0`. `Circle.exp` uses radians, so its lifted endpoint is `2π*n`.
  The zero-period quotient has trivial fundamental group and is excluded from
  the integer equivalence, not from the covering-map construction.

- **Continuous hairy-ball theorem for S².** Every bundled continuous
  field `V : C(sphere2, E3)` pointwise orthogonal to the radius vanishes
  somewhere: [`sphere2_exists_zero_of_orthogonal_field`](SphereTopology/Homotopy/HairyBallSphere2.lean#L26).
  On the unit sphere in **any** real inner-product space, a nowhere-zero
  continuous radius-orthogonal field yields an explicit identity-to-antipodal
  homotopy, without a finite-dimensional assumption:
  [`Metric.Sphere.homotopyAntipodalOfNowhereZeroOrthogonal`](SphereTopology/Homotopy/TangentField.lean#L94).
  Only the zero theorem specializes to the three-dimensional model.
- **Circle/S² homology and antipodal sign.** Ordered east/west punctures on the
  circle and north/south punctures on S² yield `H̃₁(S¹; ℤ) ≅ ℤ` and
  `H̃₂(S²; ℤ) ≅ ℤ`:
  [`reducedSingularHomologyOneSphereOneIntegerIso`](SphereTopology/Homology/Singular/Circle.lean),
  [`reducedSingularHomologyTwoSphereTwoIntegerIso`](SphereTopology/Homology/Singular/Sphere.lean).
  The circle's two-point basis is upper minus lower (`false` minus `true`);
  the sphere deformation fixes its equator and the equator-to-circle
  homeomorphism uses ordered coordinates `(x,y)`. Cover-swap naturality gives
  `-id` on ordinary and positive-degree reduced integral `H₂` for the
  antipodal map, hence multiplication by `-1` in the fixed `ℤ` coordinate and
  nonhomotopy to identity:
  [`integralSingularHomologyMap_sphere2Antipodal_two`](SphereTopology/Homology/Singular/SphereAntipodal.lean).
- **Covering-space lifts of singular simplices.** For `p : Y ⟶ X` between
  spaces in a common ambient universe and `IsCoveringMap p`, evaluation at
  **any** point of a simplex identifies its lift fiber under
  `TopCat.toSSet.map p` with the corresponding point fiber:
  [`IsCoveringMap.singularLiftEquiv`](SphereTopology/Topology/SingularLifts.lean).
  Restriction is bijective for **every** simplex operator, including faces
  that omit vertex zero and degeneracies:
  `IsCoveringMap.bijective_singularLiftRestrict`. There are no nonemptiness,
  connectedness, local connectedness, surjectivity or finite-sheet assumptions
  on the base or total space. A finite point fiber gives finitely many lifts.
  The induced singular simplicial map is equifibered:
  `IsCoveringMap.toSSet_map_equifibered` makes every naturality square a
  pullback. The continuous-map version allows independent universes and a simply
  connected, locally path connected domain; finite nonempty real standard
  simplices have the required domain instances.
- **Subdivision and cover-small chains.** Signed barycentric subdivision `Sd`
  and its support-preserving prism `H` obey `∂H + H∂ = id − Sd`:
  [`singularHomotopy_boundary`](SphereTopology/Homology/Singular/Subdivision.lean#L1598).
  The iterated prism is a *telescoping sum* of degree-raising maps, not iteration
  of a degree-raising function. For an open cover, inclusion of finite-support
  chains small in some cover member is a quasi-isomorphism:
  [`quasiIso_smallSingularChainInclusion`](SphereTopology/Homology/Singular/SmallChains.lean#L524).
  The ambient and cover-index universes may differ; empty cases are permitted
  where the stated cover hypotheses allow them. Continuous maps and cover
  refinements have compatible chain maps.
- **Ordered integral Mayer–Vietoris.** For two opens covering a space, the
  first chain map is `(c,−c)`, followed by addition. Connecting maps satisfy
  all three successive exactness positions, ordered-cover naturality and the
  minus sign under cover swap:
  [`twoOpenMayerVietoris_exact_intersection`](SphereTopology/Homology/Singular/MayerVietoris.lean#L1087),
  [`twoOpenMayerVietorisδ_naturality_induced`](SphereTopology/Homology/Singular/MayerVietoris.lean#L1073),
  [`twoOpenMayerVietorisδ_swap_eq_neg`](SphereTopology/Homology/Singular/MayerVietoris.lean#L858).
  The connecting morphism lands in small-chain intersection homology, with an
  explicit comparison to homology of the intersection as an open subspace. The general minus-identity criterion additionally requires the
  transported-intersection identity and a monic connecting map.
- **Nonbasepoint path components.** Given `x : X`, the coproduct of a coefficient
  object `R` over `{c : ZerothHomotopy X // c ≠ .mk x}` maps to `H₀(X; R)` by
  component minus basepoint-component injections:
  [`singularHomologyZeroComponentInclusion`](SphereTopology/Homology/Singular/Components.lean).
  This uses Mathlib's independent space/category universes, coproducts,
  preadditivity and `CategoryWithHomology`, with no nonzero-coefficient,
  path-connectedness or finiteness assumption. Its kernel universal property gives
  the integral comparison
  [`reducedSingularHomologyZeroComponentsIso`](SphereTopology/Homology/Singular/Reduced.lean).
  The three-point presentation has inverse generators `[1]−[0]`
  and `[2]−[0]`; basepoint `true` on the two-point space recovers the existing
  false-minus-true basis.
- **Nonnegative reduced homology.** Degree zero is the augmentation kernel;
  positive degrees agree with ordinary homology. It is homotopy invariant,
  vanishes for contractible **nonempty** spaces, and `H̃₀(∅)=0` does not
  assert a degree-minus-one theory:
  [`reducedSingularHomologyFunctor`](SphereTopology/Homology/Singular/Reduced.lean),
  [`isZero_reducedSingularHomologyZero_empty`](SphereTopology/Homology/Singular/Reduced.lean).
  The two-point transposition acts by `-1` in the upper-minus-lower basis.
  For every two-open cover, the reduced difference/sum sequence is exact at
  `H̃₀(U) ⊕ H̃₀(V)`; the sum is epic when `U ∩ V` is nonempty:
  [`twoOpenReducedMayerVietoris_exact_biprodZero`](SphereTopology/Homology/Singular/ReducedMayerVietoris.lean),
  [`twoOpenReducedMayerVietorisFromBiprodZero_epi`](SphereTopology/Homology/Singular/ReducedMayerVietoris.lean).
  Disjoint nonempty opens can instead have zero reduced homology on each open
  and nonzero ambient reduced `H̃₀`, so epimorphy is not unconditional.
  The reduced low-degree Mayer–Vietoris boundary is an isomorphism if **both**
  `H̃₀` and `H̃₁` vanish on **each** open, with naturality and cover-swap sign:
  [`twoOpenReducedMayerVietorisIsoOfAcyclicOpens`](SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L739).

- **Path connectedness from degree-zero homology.** In a preadditive category
  with the requisite small coproducts and homology, the total augmentation
  `H₀(X; R) ⟶ R` is invertible exactly when `X` is path connected, provided
  the coefficient object `R` is nonzero:
  [`isIso_singularHomology₀ε_iff_pathConnectedSpace`](SphereTopology/Homology/Singular/Connectedness.lean).
  Nonemptiness of `X` is part of the conclusion, not an assumption. For
  **nonempty** `X`, integral reduced `H₀` vanishes exactly when `X` is path
  connected:
  [`isZero_reducedSingularHomologyZero_iff_pathConnectedSpace`](SphereTopology/Homology/Singular/Connectedness.lean).
  The empty space still has zero reduced `H₀`; with zero coefficients the
  augmentation can also be invertible on disconnected spaces.

## Modules and client conventions

| Module beneath `SphereTopology` | Public role |
| --- | --- |
| `Homotopy.Circle` | Signed-period integer loops, normalized fundamental-group coordinates, lifted endpoints and complex-circle agreement. |
| `Homotopy.TangentField`, `Homotopy.HairyBallSphere2` | Generic normalization/homotopy and the standard S² continuous-field zero theorem. |
| `Topology.StdSimplex`, `Topology.SingularLifts` | Finite-simplex domain instances, evaluation equivalences, restriction bijections and equifibered singular maps for covering spaces. |
| `Homology.Singular.Subdivision`, `SmallChains` | Integral subdivision, prism equations, small-chain quasi-isomorphism, maps and refinements. |
| `Homology.Singular.MayerVietoris` | Ordinary ordered two-open sequence, comparison, exactness and naturality. |
| `Homology.Singular.Components` | Categorical-coefficient nonbasepoint-component inclusion and augmentation-kernel statement. |
| `Homology.Singular.Reduced`, `ReducedMayerVietoris` | Nonnegative reduced homology, integral component comparison, two-point sign, reduced degree-zero tail and connecting map. |
| `Homology.Singular.Connectedness` | Total-augmentation and nonempty integral reduced-zero criteria for path connectedness. |
| `Homology.Singular.Circle`, `Sphere`, `SphereAntipodal` | Fixed models, integer coordinates and antipodal obstruction. |

The covering-space interfaces concern topological and simplicial lift fibers;
they do not construct additional chain or homology maps. A simply connected
simplex domain does not impose connectedness assumptions on the base space.

The subdivision and small-chain boundary is the alternating face sum, not an
arbitrary-coefficient chain theory. The component leaf instead reuses Mathlib's
categorical-coefficient singular `H₀`. Its augmentation-kernel/all-simplex model
generalizes the integral calculation in J. P. May's *A Concise Course in Algebraic
Topology*, Chapters 13 and 15, using Joël Riou's Mathlib formalization. It does not
supply based-relative or primed reduced-homology comparisons, normalized-chain/
tensor-coefficient comparisons, or CGWH/k-ification correspondences.
Open-cover small-chain interfaces allow independently universed
cover indices; ordered Mayer–Vietoris naturality compares spaces in a common
ambient universe. No global nonemptiness assumption is implicit for covers.
The reduced low-degree target uses the open-intersection comparison. The
library does not compute all homology groups of all spheres or prove an
arbitrary-sphere, characteristic-two, smooth tangent-bundle or general-degree
hairy-ball theorem.

Four explicitly `noncomputable` definitions—
`Convexity.StdSimplex.subdivideSimplex`, `Convexity.StdSimplex.homotopySimplex`,
`AlgebraicTopology.singularSubdivisionIterate` and
`AlgebraicTopology.singularHomotopyIterate`—expose equations rather than
executable extraction. The removed four compiler-generated partial companions
narrow the runtime interface; no external runtime-client equivalence is
promised. `Convexity.StdSimplex.exists_mem_support_of_mem_support_sum` no longer
needs `[DecidableEq α]`; explicit positional or named-class callers may need
to adjust even though ordinary use preserves the result.

`TopCat.openSingularSetIso` and
`AlgebraicTopology.twoOpenReducedMayerVietorisδZero` are public interfaces
with private implementation helpers: ordinary imports support their public
lemmas, not unfolding or diagnostic `import all` as a promised client API.
`TopCat.path_endpoints_eq_of_totallyDisconnected` is public. The
`@[simp↓]` registration of
`Convexity.StdSimplex.affineAugmentation_subdivide_zero` is part of the
current interface; restricted simplifier clients sometimes need to disable
`subdivideSimplex_zero` and `affineAugmentation_single`. The accompanying
regressions do not promise every custom downstream simp set behaves alike.

## Pinned build and use

Use Git, elan, dependency-network access and the committed manifest: Lean
`leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and eight resolved
transitive packages. Mathlib is the sole direct dependency; no other Formal
Frontier library is needed. Routine use does not require `lake update`.
Fetch the matching precompiled mathlib cache **successfully before building**;
repeat after changing pins or replacing `.lake`:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake -Kjobs=2 --wfail build
lake env lean -DwarningAsError=true SphereTopologyTest/PublicAPIClient.lean
```

Both `SphereTopology` and `SphereTopologyTest` are default Lake roots. All
test/audit modules are explicit test roots; the production aggregate
imports no tests. Focused builds can use the module names in the table.
For another Lake project, pin an independently reviewed exact revision at
`https://github.com/FormalFrontier/sphere-topology.git` and retain matching
Lean/mathlib pins.
Ordinary imports need neither private research notes nor implementation-body
unfolding, for example:

```lean
module
import SphereTopology

open CategoryTheory
open scoped RealInnerProductSpace
open SphereTopology

private theorem field_has_zero (V : C(sphere2, E3))
    (hOrth : ∀ p, inner ℝ p.1 (V p) = 0) : ∃ p, V p = 0 :=
  sphere2_exists_zero_of_orthogonal_field V hOrth

private noncomputable def sphere_homology :
    TopCat.reducedSingularHomology sphere2 2 ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularHomologyTwoSphereTwoIntegerIso
```

## Source, rights and credit

The mathematical motivation is Charles A. Weibel, *The K-book: An Introduction
to Algebraic K-theory*, complete-book build dated August 29, 2013, Example
I.1.2.2. The book passage rules out **two independent tangent fields**; this
library proves a **stronger one-field** zero theorem for continuous orthogonal
fields on the literal S². It does not certify the source's algebraic kernel,
unimodular-row or completion statements, and asserts no full book coverage.
See [formalization.yaml](formalization.yaml) for the public bibliographic
record and [credits](docs/CREDITS.md) for the distinct mathematical authors,
research/production reconciliations, interface and documentation contributions.
No book assets, third-party source excerpts or mathlib implementation are
bundled; dependency and book authors retain their own rights and notices.
