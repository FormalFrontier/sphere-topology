# Sphere Topology

Lean topology and integral singular homology: circle fundamental groups and
map degree, continuous fields on spheres, covering-space lifts and finite-fiber
transfers, subdivision, cover-small chains and Mayer–Vietoris. Explicit circle
and two-sphere computations give a continuous hairy-ball theorem for S².

See the [mathematical guide](docs/guide.md) for full hypotheses, formulas,
examples and conventions, the [API reference](docs/API.md) for a bounded display
selection, and [credits](docs/CREDITS.md) for mathematical and formalization origins.

## Headline results

- **H-space fundamental groups commute.**
  [`FundamentalGroup.mul_comm`](SphereTopology/Homotopy/HSpaceFundamentalGroup.lean)
  applies at the unit of any H-space, using only its two relative unit
  homotopies. No associativity, commutativity or strict unit laws for the
  multiplication are assumed. Continuous multiplication with a strict unit
  also gives `Path.mul_homotopic_trans`, without associativity or inverses.
- **Normalized circle fundamental groups and degree.** For real `T ≠ 0`,
  [`AddCircle.fundamentalGroupEquivInt`](SphereTopology/Homotopy/Circle.lean)
  identifies `π₁(AddCircle T, 0)` with `Multiplicative ℤ`, including signed
  periods, lifted endpoints and agreement with the complex unit circle.
  [`Circle.degree`](SphereTopology/Homotopy/CircleDegree.lean) classifies free
  homotopy of arbitrary continuous circle self-maps. Composition multiplies
  degree, `z ↦ z^n` has degree `n : ℤ`, and degree different from `1` is a
  sufficient, not necessary, fixed-point condition. No based-map premise is needed.
- **Quotient presentations of topological wide pushouts.**
  [`TopCat.widePushoutHomeomorph`](SphereTopology/Topology/WidePushout.lean)
  identifies the quotient of `B ⊕ Σ i, X i` by `b ∼ (i, f i b)` with the
  categorical wide pushout of arbitrary continuous maps `f i : B ⟶ X i`,
  preserving the head and every factor. Continuity and descent have an
  independent target universe; empty and singleton families need no separation,
  compactness or homotopy assumptions.
- **Parametrized continuity and homotopy gluing.**
  [`TopCat.continuous_prod_iff_of_isColimit`](SphereTopology/Topology/WidePushoutHomotopy.lean)
  checks joint continuity on the legs of any supplied topological colimit under
  Mathlib's `LocallyCompactPair P Y` hypothesis; a locally compact parameter
  suffices, with no separation condition on the target. Parameter and target
  universes are independent. Compatible families on a wide pushout's head and
  every factor descend continuously, with computation, uniqueness, fixed-parameter
  and reparametrization laws. Compatible interval homotopies glue at all times,
  without requiring the common point to stay fixed.
- **Point-relative equivalences and contractions.**
  [`TopCat.widePushoutPointHomotopyEquiv`](SphereTopology/Topology/WidePushoutPointHomotopy.lean)
  descends point-preserving factor maps and supplied relative inverse homotopies.
  Inverse point preservation follows from the forward maps and left relative
  homotopies. The chosen relative witnesses compute on the head and every factor.
  Supplied contractions fixing the attaching points contract the wide pushout,
  including an empty index family. This is stronger data than ordinary factor
  contractibility; countably many endpoint-zero intervals give a nontrivial client.
- **Factor retractions and embeddings for point-wide-pushouts.**
  [`TopCat.widePushoutPointRetraction`](SphereTopology/Topology/WidePushoutRetraction.lean)
  retracts the categorical wide pushout of arbitrary chosen-point spaces onto
  any selected factor. It fixes that factor, collapses every other factor to
  the chosen point and computes the head; each factor inclusion is an embedding.
  Index and space universes are independent, with no separation or finiteness
  hypotheses. The circle-bouquet retractions specialize this construction.
- **Compact subsets meet finitely many pointed factors.**
  [`finite_widePushoutPointSupport`](SphereTopology/Topology/WidePushout/Compactness.lean)
  applies to arbitrary indexed T₁ spaces attached at chosen points. A compact
  subset of their categorical wide pushout meets only finitely many factors
  away from the common point. The support API characterizes coverings by the
  common point plus factor ranges; every continuous map from a compact domain,
  including a path, has such a finite-factor covering. There is no Hausdorff,
  compact-factor, countability or finite-index assumption.
- **Subfamily retractions and continuous factorization.**
  [`TopCat.widePushoutPointSubfamilyRetraction`](SphereTopology/Topology/WidePushout/Subfamily.lean)
  retracts onto any subfamily, with an embedding inclusion whose range includes
  the common point. A continuous map factors through that inclusion exactly
  when its support lies in the subfamily, without separation or compactness
  assumptions. For T₁ factors, every compact-domain map factors through a finite
  subfamily. The circle-bouquet application retains the endpoints of based loops,
  including included positive original-circle loops.
- **Strict finite-stage factorization of compact homotopies.**
  [`TopCat.exists_finite_widePushout_point_subfamily_homotopyRel`](SphereTopology/Topology/WidePushout/SubfamilyHomotopy.lean)
  factors a prescribed compact-image relative homotopy in a point-wide-pushout
  of T₁ factors through a finite subfamily containing any prescribed finite
  set. Recovery holds at every pair of parameters, including both endpoint
  maps and arbitrary relative subsets. Compact domains suffice, without source
  separation, factor compactness or countability. At a fixed subfamily,
  existence of a relative or path homotopy is reflected without T₁ or compactness.
  [`CircleBouquet.loop_homotopic_iff_exists_finite_subfamily`](SphereTopology/Homotopy/CircleBouquet.lean)
  gives finite-stage detection for based loops in arbitrary circle bouquets;
  the stronger homotopy theorem recovers a supplied based homotopy itself.
- **Arbitrary-index circle bouquets.**
  [`CircleBouquet.space`](SphereTopology/Homotopy/CircleBouquet.lean) is the wide
  pushout of based complex circles, with a common point even for the empty
  family and independent index/ambient universes. Inclusions, descent and
  extensionality give its universal property; retractions detect the positive
  generators as nonidentity. Bijectivity of `generatorMap` and identification
  of the fundamental group with `FreeGroup I` are not proved.
- **Continuous hairy-ball theorem for S².**
  [`sphere2_exists_zero_of_orthogonal_field`](SphereTopology/Homotopy/HairyBallSphere2.lean)
  says every `V : C(sphere2, E3)` pointwise orthogonal to the radius has a zero.
  In any real inner-product space, a nowhere-zero continuous orthogonal field
  on the metric unit sphere gives an explicit identity-to-antipodal homotopy
  ([`TangentField`](SphereTopology/Homotopy/TangentField.lean)), without finite
  dimensionality. Only the zero theorem specializes to Euclidean three-space.
- **Circle/S² homology and antipodal sign.** Ordered punctures give
  `H̃₁(S¹; ℤ) ≅ ℤ` and `H̃₂(S²; ℤ) ≅ ℤ`, in the unit-sphere models in
  `EuclideanSpace ℝ (Fin 2)` and `EuclideanSpace ℝ (Fin 3)`
  ([`Circle`](SphereTopology/Homology/Singular/Circle.lean),
  [`Sphere`](SphereTopology/Homology/Singular/Sphere.lean)). The circle basis is
  upper minus lower; the equator coordinate is ordered `(x,y)`.
  [`SphereAntipodal`](SphereTopology/Homology/Singular/SphereAntipodal.lean)
  computes `-id` on ordinary and reduced integral `H₂`, hence multiplication
  by `-1` in the fixed integer coordinate and nonhomotopy to identity.
- **Covering-space lifts of simplices.** For a covering `p : Y ⟶ X`,
  [`IsCoveringMap.singularLiftEquiv`](SphereTopology/Topology/SingularLifts.lean)
  identifies the lift fiber of a singular simplex with a point fiber by
  evaluation at any point. Restriction is bijective for every simplex
  operator, including degeneracies and faces omitting vertex zero. There are
  no nonemptiness, connectedness, local connectedness, surjectivity or finite-
  sheet assumptions on the base or total space. The singular map is equifibered.
- **Finite-fiber covering transfer.** For `p : Y ⟶ X`, `IsCoveringMap p` and
  finite point fibers,
  [`singularChainComplexTransfer`](SphereTopology/Homology/Singular/Transfer.lean)
  uses coefficient objects in any preadditive category with coproducts indexed
  in the space universe; object and morphism universes are independent.
  Ordinary homology adds only `CategoryWithHomology` and uses `q : ℕ`.
  A simplex maps to the sum of its lifts. Transfer then pushforward is
  `d • id` if every point fiber has cardinality `d`; finiteness is a separate
  premise. No constant degree, nonemptiness, surjectivity or connectedness is
  needed for the construction.
- **Subdivision and cover-small chains.** Integral signed subdivision `Sd`
  and its support-preserving prism `H` satisfy `∂H + H∂ = id − Sd`
  ([`Subdivision`](SphereTopology/Homology/Singular/Subdivision.lean)). For an
  open cover, inclusion of finite-support chains small in a cover member is a
  quasi-isomorphism
  ([`SmallChains`](SphereTopology/Homology/Singular/SmallChains.lean)). Space
  and cover-index universes may differ; no global nonemptiness is assumed.
  Cover-respecting continuous maps and refinements induce compatible chain maps.
- **Ordered ordinary and reduced Mayer–Vietoris.** Two opens covering a space
  give difference `(c,−c)` followed by sum, all three successive ordinary
  exactness positions, ordered-cover naturality and cover-swap minus sign
  ([`MayerVietoris`](SphereTopology/Homology/Singular/MayerVietoris.lean)).
  The reduced low-degree boundary uses open-intersection homology and is an
  isomorphism when both `H̃₀` and `H̃₁` vanish on each open. The reduced
  degree-zero sequence is exact at the biproduct for every two-open cover;
  its final map is epic when the intersection is nonempty, not unconditionally
  ([`ReducedMayerVietoris`](SphereTopology/Homology/Singular/ReducedMayerVietoris.lean)).
- **Components and path connectedness.**
  [`Components`](SphereTopology/Homology/Singular/Components.lean) presents the
  augmentation kernel by nonbasepoint path components, with categorical
  coefficients. In a preadditive category with the requisite coproducts and
  homology, `H₀(X; R) ⟶ R` is invertible exactly when `X` is path connected
  if `R` is nonzero; nonemptiness is a conclusion
  ([`Connectedness`](SphereTopology/Homology/Singular/Connectedness.lean)).
  For nonempty `X`, integral `H̃₀(X)=0` is equivalent to path connectedness.
  Reduced homology is nonnegative, with augmentation kernel in degree zero,
  ordinary homology in positive degrees and `H̃₀(∅)=0`; no degree-minus-one
  convention is asserted. Contractible-space premises include nonemptiness.
- **Covering foundations from Fundamental Groupoids.** The dependency supplies
  based unique lifting, monodromy, maps of covers, deck actions and based
  equal-image equivalences; Sphere re-exports the five deprecated covering
  module paths below. The [guide](docs/guide.md#headline-results) gives the
  distinct connectedness and local path connectedness hypotheses for each
  result. These are not a general classification of coverings.

## Using the library

```toml
[[require]]
name = "sphere-topology"
git = "https://github.com/FormalFrontier/sphere-topology.git"
rev = "main"
```

GitHub `main` contains published releases; Lake records the resolved commit in
`lake-manifest.json`. To select a fixed release, use its full commit instead.
Import `SphereTopology` or a focused module from the table. For example, the
following interfaces are also used by the library's existing clients:

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

## Building

The toolchain and dependency graph are pinned in `lean-toolchain` and
`lake-manifest.json`: Lean `v4.34.0-rc2`, Mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, Simplicial Objects
`143f667bdeb0aeccd02e6475781d5c456f00c95b` and Fundamental Groupoids
`7a3b69c5c2a88044db6e2f664790913d709ae20b`.
Fetch the matching precompiled Mathlib cache successfully before building:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake -Kjobs=2 --wfail build
lake env lean -DwarningAsError=true SphereTopologyTest/PublicAPIClient.lean
```

`SphereTopology` and `SphereTopologyTest` are default Lake libraries; the
production aggregate imports no tests. Routine use does not need `lake update`.

## Contents

| Module beneath `SphereTopology` | Public role |
| --- | --- |
| `Homotopy.Circle` | Signed-period integer loops, normalized fundamental-group coordinates, lifted endpoints and complex-circle agreement. |
| `Homotopy.CircleBouquet` | Arbitrary-index circle bouquet, inclusions and descent, positive-generator homomorphism, circle retractions and generator nonidentity; no free-group identification. |
| `Homotopy.CircleDegree` | Integer degree of unbased circle self-maps, composition and signed powers, free homotopy classification and a sufficient fixed-point condition. |
| `Homotopy.HSpaceFundamentalGroup` | Pointwise H-space loop multiplication, based comparison with concatenation, quotient comparison and commutativity at the unit. |
| `Homotopy.TangentField`, `Homotopy.HairyBallSphere2` | Generic normalization/homotopy and the standard S² continuous-field zero theorem. |
| `Topology.CoveringLifting` | Deprecated public re-export of `FundamentalGroupoids.Topology.Covering.Lifting`. Based unique lifting iff fundamental-group image containment, using Mathlib's sufficient criterion. |
| `Topology.StdSimplex`, `Topology.SingularLifts` | Finite-simplex domain instances, evaluation equivalences, restriction bijections and equifibered singular maps for covering spaces. |
| `Topology.WidePushoutRetraction` | Selected-factor retractions, head and every-factor equations, and embeddings for arbitrary point-wide-pushouts. |
| `Topology.WidePushout` | Head- and factor-preserving quotient homeomorphism for arbitrary wide pushouts, final-topology continuity, independent-target descent and empty/singleton/point boundary results. |
| `Topology.WidePushoutHomotopy` | Product-parameter continuity for supplied colimits, compatible wide-pushout family descent and interval-homotopy gluing, with independent parameter and target universes. |
| `Topology.WidePushoutPointHomotopy` | Point-preserving factor equivalences with singleton-relative inverse witnesses, head and factor equations, and contractions fixing the common point. |
| `Topology.WidePushout.Compactness` | Support away from chosen points, common-point covering characterization, finite support of compact subsets for T₁ factors and compact-domain finite-factor coverings. |
| `Topology.WidePushout.Subfamily` | Arbitrary-subfamily inclusions and retractions, embeddings and exact ranges, supported-map factorization and uniqueness, nested-subfamily compatibility, and finite-subfamily factorization for compact domains and T₁ factors. |
| `Topology.WidePushout.SubfamilyHomotopy` | Support criterion and object-level recovery for relative homotopies, strict compact-image finite-stage factorization with prescribed finite initial data, and fixed-stage reflection without separation assumptions. |
| `Topology.CoveringMonodromy` | Deprecated public re-export of `FundamentalGroupoids.Topology.Covering.Monodromy`. Point stabilizers, path-component orbits, monodromy naturality and canonical equivariant fiber restriction with identity/composition laws; whole-fiber uniqueness over a path-connected base; quotient-action and permutation-kernel bridges. |
| `Topology.CoveringEquivalence` | Deprecated public re-export of `FundamentalGroupoids.Topology.Covering.Equivalence`. Surjectivity for nonempty source and path-connected target; based homeomorphism over a fixed base from equal images, with both totals path connected and only source locally path connected. |
| `Topology.DeckMonodromy` | Deprecated public re-export of `FundamentalGroupoids.Topology.Covering.DeckMonodromy`. Equivalences between continuous maps of covers and equivariant fiber maps with locally path-connected source and either path-connected base or path-connected source at a supplied point; deck-centralizer restriction, path-connected-base faithfulness and the corresponding deck-group equivalences. |
| `Topology.DeckGroup` | Deprecated public re-export of `FundamentalGroupoids.Topology.Covering.DeckGroup`. Point-fiber deck actions, evaluation embeddings and fixed-point rigidity for separated, locally injective maps with preconnected total space. |
| `Homology.Singular.Transfer` | Finite-point-fiber covering transfer on all-simplex singular chains and ordinary homology, lift-sum and sheet formulas. |
| `Homology.Singular.Subdivision`, `SmallChains` | Integral subdivision, prism equations, small-chain quasi-isomorphism, maps and refinements. |
| `Homology.Singular.MayerVietoris` | Ordinary ordered two-open sequence, comparison, exactness and naturality. |
| `Homology.Singular.Components` | Categorical-coefficient nonbasepoint-component inclusion and augmentation-kernel statement. |
| `Homology.Singular.Reduced`, `ReducedMayerVietoris` | Nonnegative reduced homology, integral component comparison, two-point sign, reduced degree-zero tail and connecting map. |
| `Homology.Singular.Connectedness` | Total-augmentation and nonempty integral reduced-zero criteria for path connectedness. |
| `Homology.Singular.Circle`, `Sphere`, `SphereAntipodal` | Fixed models, integer coordinates and antipodal obstruction. |

## Conventions and limitations

Integral coordinates are supplied by released
[`SimplicialObjects.ChainCoordinates`](https://github.com/FormalFrontier/simplicial-objects/blob/143f667bdeb0aeccd02e6475781d5c456f00c95b/SimplicialObjects/ChainCoordinates.lean).
The four `AlgebraicTopology` names are re-exported by `SmallChains` without
renaming. For `X : SSet.{u}`, coefficients are `(ModuleCat.uliftFunctor.{u} ℤ).obj
(ModuleCat.of ℤ ℤ)`. The degree-`n` coordinate module is
`ModuleCat.of ℤ (X _⦋n⦌ →₀ ℤ)`, on all simplices, including degenerate ones.
This is degreewise, not a chain or natural isomorphism; no normalized-chain
comparison or nonzero-homology consequence follows from a nonzero chain.
See the [coordinate guide](docs/coordinates.md) for full types, providers and
source origins, and the [mathematical guide](docs/guide.md) for all other
scope and compatibility qualifications.

## References

- J. Peter May, *A Concise Course in Algebraic Topology*: Chapters 1–3 and
  13–16; exact sections and conventions are in the guide and module references.
- Charles A. Weibel, *The K-book*, Example I.1.2.2: sphere-field motivation.
  Its two-independent-field obstruction is distinct from the stronger one-field
  zero theorem here; no algebraic kernel, row-completion or whole-book claim is made.
- Mathlib, [Simplicial Objects](https://github.com/FormalFrontier/simplicial-objects)
  and [Fundamental Groupoids](https://github.com/FormalFrontier/fundamental-groupoids).

## Credits and license

Authors: Formal Frontier Agents. Project Lean and documentation are AI-authored.
Mathematical sources, Mathlib contributors and original project, Prism and
Orrery contributions retain their distinct credit in [CREDITS.md](docs/CREDITS.md).
Licensed under [Apache-2.0](LICENSE); dependency and book authors retain their
own rights and notices. No book assets or excerpts are bundled.
