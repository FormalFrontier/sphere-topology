# Sphere Topology

A reusable Lean library for continuous fields on spheres and integral singular
homology. It develops finite-support subdivision and cover-small chains, ordinary
and nonnegative reduced Mayer–Vietoris sequences, and explicit circle and
standard two-sphere computations. Their antipodal sign obstruction gives a
continuous-field hairy-ball theorem for the literal unit two-sphere. Import the
aggregate `SphereTopology` or the focused modules listed below; no source
research repository is needed to use the library.

Authors: Formal Frontier Agents.

Original project contributions are licensed [Apache-2.0](LICENSE); see
[credits and provenance](docs/CREDITS.md). The [API reference](docs/API.md) and
[its guide](docs/README.md) distinguish retained native output from subsequent
source inspection. The bibliographic source motivates this independent library;
source-specific algebraic consequences and full source coverage are separate.

## Headline results

All chain and homology constructions below use integer coefficients; a singular
chain has finite support. The literal circle and two-sphere are unit spheres in
`EuclideanSpace ℝ (Fin 2)` and `EuclideanSpace ℝ (Fin 3)`, respectively.

- **Continuous hairy-ball theorem for the literal S².** Every bundled continuous
  field `V : C(sphere2, E3)` pointwise orthogonal to the radius vanishes
  somewhere: [`sphere2_exists_zero_of_orthogonal_field`](SphereTopology/Homotopy/HairyBallSphere2.lean#L26).
  On the unit sphere in **any** real inner-product space, a nowhere-zero
  continuous radius-orthogonal field yields an explicit identity-to-antipodal
  homotopy, without a finite-dimensional assumption:
  [`Metric.Sphere.homotopyAntipodalOfNowhereZeroOrthogonal`](SphereTopology/Homotopy/TangentField.lean#L94).
  Only the zero theorem specializes to the literal three-dimensional model.
- **Circle/S² homology and antipodal sign.** Ordered east/west punctures on the
  circle and north/south punctures on S² yield `H̃₁(S¹; ℤ) ≅ ℤ` and
  `H̃₂(S²; ℤ) ≅ ℤ`:
  [`reducedSingularHomologyOneSphereOneIntegerIso`](SphereTopology/Homology/Singular/Circle.lean),
  [`reducedSingularHomologyTwoSphereTwoIntegerIso`](SphereTopology/Homology/Singular/Sphere.lean).
  The circle's two-point basis is upper minus lower (`false` minus `true`);
  the sphere deformation fixes its equator and the equator-to-circle
  homeomorphism uses ordered coordinates `(x,y)`. Cover-swap naturality gives
  `-id` on ordinary and positive-degree reduced integral `H₂` for the literal
  antipodal map, hence multiplication by `-1` in the fixed `ℤ` coordinate and
  nonhomotopy to identity:
  [`integralSingularHomologyMap_sphere2Antipodal_two`](SphereTopology/Homology/Singular/SphereAntipodal.lean).
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
  [`twoOpenMayerVietoris_exact_intersection`](SphereTopology/Homology/Singular/MayerVietoris.lean#L1011),
  [`twoOpenMayerVietorisδ_naturality_induced`](SphereTopology/Homology/Singular/MayerVietoris.lean#L997),
  [`twoOpenMayerVietorisδ_swap_eq_neg`](SphereTopology/Homology/Singular/MayerVietoris.lean#L858).
  The native connection uses small-chain intersection homology, with an explicit
  comparison to the literal intersection; the two are not claimed definitionally
  equal. The general minus-identity criterion additionally requires the
  transported-intersection identity and a monic connecting map.
- **Nonnegative reduced homology.** Degree zero is the augmentation kernel;
  positive degrees agree with ordinary homology. It is homotopy invariant,
  vanishes for native contractible **nonempty** spaces, and `H̃₀(∅)=0` does not
  assert a degree-minus-one theory:
  [`reducedSingularHomologyFunctor`](SphereTopology/Homology/Singular/Reduced.lean),
  [`isZero_reducedSingularHomologyZero_empty`](SphereTopology/Homology/Singular/Reduced.lean).
  The two-point transposition acts by `-1` in the upper-minus-lower basis.
  The reduced low-degree Mayer–Vietoris boundary is an isomorphism if **both**
  `H̃₀` and `H̃₁` vanish on **each** open, with naturality and cover-swap sign:
  [`twoOpenReducedMayerVietorisIsoOfAcyclicOpens`](SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L392).

## Modules and client conventions

| Module beneath `SphereTopology` | Public role |
| --- | --- |
| `Homotopy.TangentField`, `Homotopy.HairyBallSphere2` | Generic normalization/homotopy and the literal S² continuous-field zero theorem. |
| `Homology.Singular.Subdivision`, `SmallChains` | Integral subdivision, prism equations, small-chain quasi-isomorphism, maps and refinements. |
| `Homology.Singular.MayerVietoris` | Ordinary ordered two-open sequence, comparison, exactness and naturality. |
| `Homology.Singular.Reduced`, `ReducedMayerVietoris` | Nonnegative reduced homology, two-point sign and low-degree connecting map. |
| `Homology.Singular.Circle`, `Sphere`, `SphereAntipodal` | Fixed models, integer coordinates and literal antipodal obstruction. |

The source boundary is the alternating face sum, not an arbitrary-coefficient
chain theory. Open-cover small-chain interfaces allow independently universed
cover indices; ordered Mayer–Vietoris naturality compares spaces in a common
ambient universe. No global nonemptiness assumption is implicit for covers.
The reduced low-degree target uses the literal-intersection comparison. The
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
21 test/audit modules are explicit test roots; the production aggregate
imports no tests. Focused builds can use the module names in the table.
For another Lake project, pin an independently reviewed exact revision at
`https://github.com/FormalFrontier/sphere-topology.git` and retain matching
Lean/mathlib pins. Access to that distribution repository requires
private-project authorization until public visibility is separately decided.
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

The project's previous accepted release has a successful pinned ordinary
build and complete transitive axiom audit of all 32 modules and 1,083 logical
declarations, including private/test declarations and reached dependencies;
only `propext`, `Classical.choice` and `Quot.sound` occur. These are historical
checks of the released mathematics, not proof of a later source-coverage claim.
An ordinary compilation checks proofs; separate exhaustive stored-proof replay
is not a release condition. API display counts do not substitute for that audit.

One historical matching-cache, clean-project run of the 32 project modules
took 56.61 seconds across 3,029 total Lake jobs in a 23 GiB runtime. Its
largest-child RSS was 1,694,824 KiB—not aggregate peak, an enforced memory
cap, or a measured minimum. A separate incremental build in an 8 GiB service
reported 1.4 GiB peak; this is a different workload, not a cold-build or
portability promise. The command above records settings, not a measured cap on
concurrent Lean processes or aggregate memory.

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
