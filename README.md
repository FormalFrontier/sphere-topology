# Sphere Topology

A reusable Lean library for circle fundamental groups, continuous fields on
spheres, covering spaces, and integral singular homology. Its covering-space
interfaces give based lifting, deck actions on fibers, monodromy-centralizer
comparisons, based equivalences, and lifts of singular simplices. It develops
finite-support subdivision and cover-small chains, ordinary and nonnegative reduced
Mayer–Vietoris sequences, and explicit circle and standard two-sphere
computations. Their antipodal sign obstruction gives a continuous-field
hairy-ball theorem for the unit two-sphere. Import the aggregate
`SphereTopology` or the focused modules listed below; no source research
repository is needed to use the library.

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

- **H-space fundamental groups are commutative.** At the unit of any H-space,
  [`HSpace.loopMul_homotopic_trans`](SphereTopology/Homotopy/HSpaceFundamentalGroup.lean)
  compares pointwise loop multiplication with chronological concatenation using
  only the two relative unit homotopies. No associativity, commutativity or strict
  unit laws for the H-space multiplication are assumed.
  `FundamentalGroup.fromPath_loopMul` gives the class `[q] * [p]`, and
  `FundamentalGroup.mul_comm` proves commutativity for arbitrary classes. The
  `IsMulCommutative` instance preserves the existing fundamental-group data.
  For continuous multiplication with a strict unit,
  `Path.mul_homotopic_trans` gives the comparison using `Path.mul`; no
  associativity or inverse law is needed.

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
- **Based covering-map lifting criterion.** A continuous map from a path
  connected, locally path connected domain has a unique lift with a prescribed
  value exactly when its fundamental-group image lies in that of the covering
  map:
  [`IsCoveringMap.existsUnique_continuousMap_lifts_iff_range_le`](SphereTopology/Topology/CoveringLifting.lean).
  The three spaces have independent universes; neither global surjectivity nor
  connectedness or local path connectedness of the base or total space is required.
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
- **Deck transformations on fibers.** For any map `p : E → B` with a topology
  on `E`, Mathlib's `deck p` acts on each point fiber `p ⁻¹' {b}`. If `p` is
  separated and locally injective and `E` is preconnected, evaluation at a
  specified `e : E` embeds the deck group into `p ⁻¹' {p e}`, and a deck
  transformation fixing a point is the identity:
  [`deck.evalEmbedding`, `deck.eq_one_of_smul_eq`](SphereTopology/Topology/DeckGroup.lean).
  The generic interfaces need no topology on `B` or continuity of `p`.
  Covering maps supply separation and local injectivity; no Hausdorff total
  space, base connectedness/local path connectedness, surjectivity, or
  transitivity of the deck action is assumed. General lift uniqueness is reused
  from Mathlib's `IsSeparatedMap.eq_of_comp_eq` and `IsCoveringMap.eq_of_comp_eq`,
  not redefined.
- **Deck groups as monodromy centralizers.** For any covering `p : E → B`,
  restriction to the point fiber gives
  [`IsCoveringMap.deckMonodromyHom`](SphereTopology/Topology/DeckMonodromy.lean),
  a homomorphism into the centralizer of the monodromy image in
  `Equiv.Perm (p ⁻¹' {b})`. With path-connected base it is faithful, without
  local path connectedness or total-space connectedness. If in addition `E`
  is locally path connected, `IsCoveringMap.deckMonodromyEquiv` is a
  multiplicative equivalence for every `b : B`; disconnected and empty total
  spaces are allowed, with no nonemptiness or surjectivity premise.
  Alternatively, with path-connected, locally path-connected `E` and a
  specified `e : E`, `IsCoveringMap.deckMonodromyEquivOfPathConnected` uses the
  fiber over `p e` without connectedness or local path connectedness of `B`.
  Both constructions restrict the original deck action, their inverse extends
  the permutation on the whole fiber, and they agree wherever both apply.
  The centralizer is a subgroup of the fiber's permutation group, distinct
  from a point stabilizer or the monodromy kernel in the fundamental group.
- **Covering-space monodromy and based equivalences.** For any covering map,
  the stabilizer of a point in a fiber is the image of the fundamental group
  based at that point, and two fiber points share a monodromy orbit exactly
  when they are joined in the total space:
  [`IsCoveringMap.monodromy_eq_self_iff_mem_range`](SphereTopology/Topology/CoveringMonodromy.lean),
  `IsCoveringMap.exists_monodromy_eq_iff_joined`. These need no global
  connectedness or local path connectedness. For quotient coverings,
  `IsQuotientCoveringMap.ker_monodromyPerm_eq_comap_stabilizer` identifies the
  permutation kernel with the preimage of any point stabilizer; no such kernel
  identification is asserted for arbitrary covers.
  A continuous map over a fixed common base between covers is surjective
  when its source is nonempty and its target total space is path connected:
  [`IsCoveringMap.surjective_of_comp_eq`](SphereTopology/Topology/CoveringEquivalence.lean).
  When both total spaces are path connected and only the source is locally
  path connected, equality of their based fundamental-group images constructs
  `IsCoveringMap.homeomorphOfRangeEq`, a homeomorphism over that base. The second
  image is transported along the inverse of the chosen projection equality.
  The total spaces and base have three independent universes; no global base
  connectedness, local path connectedness or surjectivity of the covers is
  required. Four chosen-point and projection laws, and
  `IsCoveringMap.homeomorphOfRangeEq_eq_iff`, characterize the construction and
  its inverse. This is the based equal-image case, not a general classification
  of coverings or a classification by bare homeomorphism of total spaces.
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
| `Homotopy.HSpaceFundamentalGroup` | Pointwise H-space loop multiplication, based comparison with concatenation, quotient comparison and commutativity at the unit. |
| `Homotopy.TangentField`, `Homotopy.HairyBallSphere2` | Generic normalization/homotopy and the standard S² continuous-field zero theorem. |
| `Topology.CoveringLifting` | Based unique lifting iff fundamental-group image containment, using Mathlib's sufficient criterion. |
| `Topology.StdSimplex`, `Topology.SingularLifts` | Finite-simplex domain instances, evaluation equivalences, restriction bijections and equifibered singular maps for covering spaces. |
| `Topology.CoveringMonodromy` | Point stabilizers, path-component orbits, naturality for continuous maps of covers and whole-fiber uniqueness over a path-connected base; quotient-action and permutation-kernel bridges. |
| `Topology.CoveringEquivalence` | Surjectivity for nonempty source and path-connected target; based homeomorphism over a fixed base from equal images, with both totals path connected and only source locally path connected. |
| `Topology.DeckMonodromy` | Restriction to the monodromy centralizer; whole-fiber faithfulness for path-connected base; equivalences with locally path-connected total space and either path-connected base or path-connected total space at a specified point. |
| `Topology.DeckGroup` | Point-fiber deck actions, evaluation embeddings and fixed-point rigidity for separated, locally injective maps with preconnected total space. |
| `Homology.Singular.Subdivision`, `SmallChains` | Integral subdivision, prism equations, small-chain quasi-isomorphism, maps and refinements. |
| `Homology.Singular.MayerVietoris` | Ordinary ordered two-open sequence, comparison, exactness and naturality. |
| `Homology.Singular.Components` | Categorical-coefficient nonbasepoint-component inclusion and augmentation-kernel statement. |
| `Homology.Singular.Reduced`, `ReducedMayerVietoris` | Nonnegative reduced homology, integral component comparison, two-point sign, reduced degree-zero tail and connecting map. |
| `Homology.Singular.Connectedness` | Total-augmentation and nonempty integral reduced-zero criteria for path connectedness. |
| `Homology.Singular.Circle`, `Sphere`, `SphereAntipodal` | Fixed models, integer coordinates and antipodal obstruction. |

The singular-lift interfaces concern topological and simplicial lift fibers;
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

The sphere-field motivation is Charles A. Weibel, *The K-book: An Introduction
to Algebraic K-theory*, complete-book build dated August 29, 2013, Example
I.1.2.2. The book passage rules out **two independent tangent fields**; this
library proves a **stronger one-field** zero theorem for continuous orthogonal
fields on the literal S². It does not certify the source's algebraic kernel,
unimodular-row or completion statements, and asserts no full book coverage.
See [formalization.yaml](formalization.yaml) for the public bibliographic
record and [credits](docs/CREDITS.md) for the distinct mathematical authors,
research/production reconciliations, interface and documentation contributions.

The based covering-lift criterion follows J. P. May, *A Concise Course in
Algebraic Topology*, Chapter 3 §7, printed pp. 28–29 (PDF pp. 36–37), and reuses
Mathlib's lifting formalization, especially Junyan Xu's approach. The
covering-map fixed-point corollary specializes uniqueness of maps of covers
there, printed p. 29 (PDF p. 37), by comparing a deck transformation with the
identity. The deck interfaces reuse Mathlib's deck group formalized by Kim
Morrison and sharp separated-map uniqueness formalized by Junyan Xu. This is
not a claim of a separately stated fixed-point theorem or complete coverage of
May's text. The restriction-to-fiber comparison with the monodromy centralizer
follows the deck-automorphism comparison in the same section, using based
lifting and open path components to allow disconnected or empty total spaces.

No book assets, third-party source excerpts or mathlib implementation are
bundled; dependency and book authors retain their own rights and notices.
