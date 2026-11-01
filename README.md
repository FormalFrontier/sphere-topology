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
  [`AddCircle.fundamentalGroupEquivInt`](https://github.com/FormalFrontier/fundamental-groupoids/blob/main/FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Circle.lean)
  is supplied by Fundamental Groupoids and identifies `π₁(AddCircle T, 0)`
  with `Multiplicative ℤ`, including signed periods, lifted endpoints and
  agreement with the complex unit circle.
  [`Circle.degree`](SphereTopology/Homotopy/CircleDegree.lean) classifies free
  homotopy of arbitrary continuous circle self-maps. Composition multiplies
  degree, while pointwise multiplication adds it, including multiset products
  with repeated factors. The map `z ↦ z^n` has degree `n : ℤ`, and degree different
  from `1` is a sufficient, not necessary, fixed-point condition. No based-map
  premise is needed.
- **Disk boundary degree and non-retraction.** Every continuous map
  `G : C(Metric.closedBall (0 : ℂ) 1, Circle)` has boundary restriction of
  degree zero, so that restriction is not the identity on `Circle`
  ([`Disk`](SphereTopology/Homotopy/Disk.lean)). The boundary map is the
  coordinate-preserving inclusion of the complex unit circle into the closed
  unit disk; no basedness premise is imposed. This is not a theorem about
  arbitrary-dimensional disks or an extension converse.
- **Forward intersections with spheres.** In a real inner-product affine space,
  [`Sphere.rayInter`](SphereTopology/Geometry/ForwardRay.lean) continues from
  `q` through a distinct closed-ball point `x` to the sphere, with parameter
  at least one even when `q` is outside the ball. For a closed-ball start,
  positive sphere-intersection parameters are characterized by the upper root,
  and a boundary second point is fixed, including the diagonal. The total
  parameter and point formulas are jointly continuous on the whole off-diagonal;
  boundary starts agree with Mathlib's `Sphere.secondInter` when `x` is in the
  closed ball. No finite-dimensionality, completeness or global radius-sign
  assumption is needed.
- **Continuous ray maps and boundary-only strict retractions.** In a real
  inner-product affine torsor,
  [`Sphere.rayInterMap`](SphereTopology/Geometry/ForwardRayMap.lean) turns an
  ambient-valued continuous map `f` on a closed ball, with `f x ≠ x` at every
  point, into a continuous map to its sphere. If boundary points have images
  in the closed ball, composition with the boundary inclusion is exactly the
  identity. No image condition is imposed on interior points; a fixed-point-free
  continuous closed-ball selfmap is a specialization.
  Vector and point universes are independent, and radii are arbitrary real
  numbers, with no finite-dimensionality, completeness or nontriviality premise.
  This generalizes the boundary-fixing construction in May's closed-disk
  argument (Chapter 1, §6), not a fixed-point theorem in this generality.
- **Generic stereographic geometry.** For
  `E : Type u` with `[NormedAddCommGroup E]` and `[InnerProductSpace ℝ E]`,
  let `S := Metric.sphere (0 : E) 1` be the canonical sphere subtype,
  `p q : S`, `H := (ℝ ∙ (p : E))ᗮ` and
  `σ := stereographic (norm_eq_of_mem_sphere p)`.
  [`stereographicHomeomorph p`](SphereTopology/Geometry/Stereographic.lean)
  identifies `({p}ᶜ : Set S)` with `H`; for `hpq : p ≠ q`,
  `stereographicOverlapHomeomorph p q hpq` identifies
  `({p}ᶜ ∩ {q}ᶜ : Set S)` with `H \ {σ q}`.
  These retain Mathlib's factor-2 stereographic map: the excluded pole is
  `+p`, and the one-pole inverse sends `0` to `-p`. The overlap target deletes
  zero exactly when `q = -p`.
- **Last-axis one-point compactification coordinates.**
  [`EuclideanSpace.onePointHomeomorphSphere`](SphereTopology/Geometry/OnePointSphere.lean)
  identifies `OnePoint (EuclideanSpace ℝ (Fin n))` with the unit sphere in
  `EuclideanSpace ℝ (Fin (n+1))`, for every `n`, including zero. Infinity maps
  to the last unit vector and finite zero to its antipode. Finite coordinates
  have denominator `‖x‖²+4`, and the off-pole inverse has coordinates
  `2*p_i/(1-p_last)`. The underlying append-zero-last linear isometry also
  applies over `RCLike` scalars; only the sphere homeomorphism is real.
- **Finite generalized loops and based sphere-map classes.** For every `n : ℕ`,
  [`GenLoop.sphereHomeomorph`](SphereTopology/Homotopy/HomotopyGroup/Sphere.lean)
  gives a homeomorphism from `GenLoop (Fin n) X x` to
  `{F : C(Sⁿ, X) // F (EuclideanSpace.northPoint n) = x}`, where `Sⁿ` is the
  unit sphere in `EuclideanSpace ℝ (Fin (n+1))`.
  `HomotopyGroup.equivSphereClasses` gives a natural set equivalence from
  `HomotopyGroup (Fin n) X x` to the existing `ZerothHomotopy` of this subtype.
  Inverse representatives precompose with
  [`Cube.collapseToSphere`](SphereTopology/Geometry/CubeSphere.lean).
  Constants and based postcomposition are preserved, including between targets
  in independent universes. Equality of sphere-map components is exactly
  homotopy relative to the singleton last-axis north pole. Targets require only
  a topology and a chosen point, with no separation, local compactness or
  well-pointedness hypothesis.
- **Positive-dimensional sphere pinch and folding.** For `d = n + 1 > 0`,
  [`Metric.Sphere.pinch n`](SphereTopology/Geometry/SpherePinch.lean) maps the
  existing last-axis unit sphere `Sᵈ` to its two-factor point-wide-pushout.
  Its cube pullback traverses the left factor before the right factor in
  coordinate zero; the two closed-half formulas agree at the separating slice,
  and fixed quarter-point witnesses give distinct non-head values.
  `surjective_pinch` and `isQuotientMap_pinch` show that it is surjective and a
  quotient map for the topology of that categorical target. `pinch_eq_head_iff`
  identifies its head fiber with the equator where ambient coordinate zero
  vanishes; `pinch_eq_pinch_iff` says that two points have the same image exactly
  when they are equal or both lie on that equator.
  [`Metric.Sphere.pinchFold`](SphereTopology/Homotopy/HomotopyGroup/SpherePinchFold.lean)
  is jointly continuous on the ordinary compact-open based-map subtype and
  preserves simultaneous paths of its factors, for arbitrary topological targets.
  Its identity/constant folds in opposite orders differ at the left quarter-point,
  including for the circle.
  [`pinch_fold_class`](SphereTopology/Homotopy/HomotopyGroup/SpherePinch.lean)
  compares folding based maps `F, G` with the existing homotopy-group
  multiplication: writing `J` for the inverse sphere-class comparison, the
  result is `J(G) * J(F)`, including in dimension one. Each original factor
  retraction composed with the pinch is homotopic to the identity relative to
  the north pole. `pinch_fold_homotopicRel_assoc` gives associativity of folding
  three arbitrary based maps up to north-pole-relative homotopy for every `d > 0`;
  its original three-inclusion specialization, `pinch_homotopicRel_coassoc`,
  gives coassociativity into the three-factor point-wide-pushout. The two
  iterated maps are not equal: `pinch_coassoc_nondegenerate` exhibits their
  different values at the same cube time `3/8`, and three distinct non-head
  inclusion values of the left nesting. For `d = n + 2 ≥ 2`,
  `pinch_fold_homotopicRel_swap` gives a north-pole-relative homotopy when the
  two arbitrary based factor maps are interchanged. Its original-inclusion specialization,
  `pinch_homotopicRel_swap`, identifies the pinch up to that relative homotopy
  with the original categorical factor swap after the pinch. Raw folding and
  based postcomposition allow independently universed targets with only a
  topology. No dimension-one cocommutativity, zero-sphere pinch, orientation,
  full cogroup structure or new group operation on sphere-map components is
  asserted.
- **Based coordinate reflections and coinverses.** For every positive sphere
  dimension `d = n + 1`, including S¹, and every pre-last axis `i : Fin (n + 1)`,
  [`coordinateReflection`](SphereTopology/Geometry/SphereCoordinateReflection.lean)
  negates exactly ambient coordinate `i.castSucc` and fixes the last-axis north
  pole. It is involutive, differs from the identity, and is uniquely determined
  by its cube pullback: reversing axis `i` of the original collapse. For an
  arbitrary based map to a topological space,
  [`coordinateReflection_precomp_class`](SphereTopology/Homotopy/HomotopyGroup/SphereCoordinateReflection.lean)
  identifies precomposition by this reflection with the existing homotopy-group
  inverse. Folding the pinch with reflection and identity in either order is
  homotopic to the north constant relative to the north pole, for every such
  axis; neither folded map is equal to that constant. These results do not
  require commutativity and do not assert S¹ cocommutativity or a full cogroup
  structure.
- **Topology of real normed unit spheres.** The topology-only APIs in
  [`Homotopy.Sphere`](SphereTopology/Homotopy/Sphere.lean) are stated for
  `E : Type u` with `[NormedAddCommGroup E] [NormedSpace ℝ E]`, using its
  original norm and `S := Metric.sphere (0 : E) 1`.
  `contractibleSpace_sphere_compl_singleton p` gives
  `ContractibleSpace ({p}ᶜ : Set S)` without a rank premise; simple connectivity
  follows from Mathlib's `SimplyConnectedSpace.ofContractible`.
  `pathConnectedSpace_sphere_compl_poles p q h` gives
  `PathConnectedSpace ({p}ᶜ ∩ {q}ᶜ : Set S)` for all `p,q`, including equal
  poles, when `h : 2 < Module.rank ℝ E` (cardinal rank).
  `simplyConnectedSpace_unitSphere h` gives `SimplyConnectedSpace S` under the
  same rank bound, including the usual `Sⁿ` for `n ≥ 2` and infinite-dimensional
  spaces. No completeness, finite-dimensionality, supplied pole for the whole
  sphere, ambient connectivity or overlap-nonemptiness assumption is needed.
  These statements generalize May's finite Euclidean sphere setting; the
  orthogonal-coordinate charts above still require an inner product.
- **Canonical antipodal quotient covering.** For `E : Type w` with
  `[NormedAddCommGroup E] [NormedSpace ℝ E]`,
  [`Metric.Sphere.isQuotientCoveringMap_toProjectivization`](SphereTopology/Geometry/Projectivization.lean)
  makes the canonical continuous map
  `Metric.Sphere.toProjectivization : C(Metric.sphere (0 : E) 1, Projectivization ℝ E)`
  a quotient covering for the scalar action of `Metric.sphere (0 : ℝ) 1`,
  whose elements act by identity and negation. The sphere uses the original norm;
  the target has the quotient topology from nonzero vectors. No inner product,
  dimension, completeness, local compactness, nonemptiness, nontriviality or
  freeness hypothesis is required. This includes the zero space's empty-to-empty
  map and the two-point-to-one-point map for `E = ℝ`.
- **Real projective fundamental groups and lifted endpoints.** For a real
  normed space `E` with `2 < Module.rank ℝ E`,
  [`Projectivization.fundamentalGroupEquivZModTwo`](SphereTopology/Homotopy/Projectivization.lean)
  identifies `π₁(Projectivization ℝ E, b)` with `Multiplicative (ZMod 2)`.
  A chosen unit lift over the supplied basepoint fixes the lift description,
  but not the resulting coordinate. The identity means returning to that lift;
  `Multiplicative.ofAdd (1 : ZMod 2)` means reaching its antipode. The sphere
  uses the given norm, with no inner-product, finite-dimensionality or
  completeness assumption, including infinite cardinal rank.
- **Boundary-only fixed points on complex closed balls.** A continuous map
  `F : C(Metric.closedBall c r, ℂ)`, with `c : ℂ` and `0 ≤ r`, has a fixed
  point if its sphere-boundary images lie in that ball
  ([`Complex.exists_fixedPoint_closedBall_of_boundary_mapsTo`](SphereTopology/Homotopy/Disk.lean)).
  No image bound is imposed on interior points, and no ambient extension is
  assumed. The continuous self-map case retains the API
  [`Complex.exists_fixedPoint_closedBall`](SphereTopology/Homotopy/Disk.lean).
  This includes the radius-zero singleton and generalizes May's closed unit
  disk self-map theorem (Chapter 1, §6, p. 10); it is not a higher-dimensional
  fixed-point theorem.
- **Quotient presentations of topological wide pushouts.**
  [`TopCat.widePushoutHomeomorph`](SphereTopology/Topology/WidePushout.lean)
  identifies the quotient of `B ⊕ Σ i, X i` by `b ∼ (i, f i b)` with the
  categorical wide pushout of arbitrary continuous maps `f i : B ⟶ X i`,
  preserving the head and every factor. Continuity and descent have an
  independent target universe; empty and singleton families need no separation,
  compactness or homotopy assumptions.
- **Embeddings, closed maps and neighborhoods of point-wide-pushouts.**
  [`TopCat.isEmbedding_widePushoutDesc_point`](SphereTopology/Topology/WidePushout/OpenEmbedding.lean)
  promotes point-preserving component embeddings to an embedding of the
  canonical wide pushouts; open or closed component embeddings give an open or
  closed embedding, respectively. Point reflection and component open or closed
  maps also suffice for the corresponding map property. The index may be
  arbitrary or empty, and source and target universes are independent, with no
  separation assumptions. The [ULift caller](SphereTopology/Topology/WidePushout/PointLift.lean)
  accommodates smaller original factors. For a given function relabeling factors
  with finite label fibers, the [closed-map criterion](SphereTopology/Topology/WidePushout/ClosedMap.lean)
  assumes closed component maps, point reflection, and the head and factor equations.
  The function is closed exactly when each omitted target factor has a closed chosen-point
  singleton, with no continuity or separation assumption. Closed rays based at zero give a proper
  closed embedding that is not open. For open neighborhoods of the attaching points,
  [`TopCat.widePushoutPointNeighborhoodHomeomorph`](SphereTopology/Topology/WidePushout/OpenNeighborhood.lean)
  identifies their wide pushout with its open range in the ordinary subtype topology.
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
- **Factor retractions and separation of point-wide-pushouts.**
  [`TopCat.widePushoutPointRetraction`](SphereTopology/Topology/WidePushoutRetraction.lean)
  retracts the categorical wide pushout of arbitrary chosen-point spaces onto
  any selected factor, and each factor inclusion is an embedding. The
  [retractions jointly distinguish points](SphereTopology/Topology/WidePushout/Separation.lean),
  without separation or finiteness assumptions, even for the empty index family.
  The pushout is T₀, T₁ or Hausdorff exactly when every factor has that property;
  factorwise inheritance is available by instance inference. Index and space
  universes are independent. No embedding into the product is asserted.
  The circle-bouquet retractions specialize this construction.
- **Compact subsets meet finitely many pointed factors.**
  [`finite_widePushoutPointSupport`](SphereTopology/Topology/WidePushout/Compactness.lean)
  applies to arbitrary indexed T₁ spaces attached at chosen points. A compact
  subset of their categorical wide pushout meets only finitely many factors
  away from the common point. The support API characterizes coverings by the
  common point plus factor ranges; every continuous map from a compact domain,
  including a path, has such a finite-factor covering. There is no Hausdorff,
  compact-factor, countability or finite-index assumption.
- **Charts around a common subset.**
  [`TopCat.widePushoutPointChart`](SphereTopology/Topology/WidePushout/Chart.lean)
  adjoins one factor to a subset containing the common point. Distinct charts
  intersect in that subset, and the subset together with the charts covers the
  pushout, including an empty family. Factorwise path connectedness of its
  inverse images makes the common subset path connected; a chart then needs
  path connectedness only of its own whole factor. An open common subset gives
  open charts, with no separation assumptions.
- **Fundamental groups of factor-plus-core charts.**
  [`TopCat.widePushoutPointChartFundamentalGroupDesc`](SphereTopology/Topology/WidePushout/FundamentalGroup.lean)
  glues homomorphisms on an arbitrary path-connected open neighborhood of the
  common point and its charts, assuming path connectedness of each whole
  factor. Only agreement on the core is required. The inclusion-induced
  core and chart restrictions characterize the result, for arbitrary target
  groups in an independent universe, empty index families and coincident
  charts. If each original factor's core-preimage inclusion induces the trivial
  fundamental-group map, the factor inclusion-induced coproduct map `q` is split
  injective. The specified splitting extends factor homomorphisms to arbitrary
  independently universed monoid targets. These hypotheses alone do not imply
  surjectivity of `q` or uniqueness of these extensions. Under just the path-connected
  core and whole-factor hypotheses,
  [`TopCat.widePushoutPointChartFundamentalGroupColimitEquiv`](SphereTopology/Topology/WidePushout/FundamentalGroupColimit.lean)
  identifies the raw group colimit of the core-to-chart star with the ambient
  fundamental group. Both directions preserve every core and chart inclusion
  map, including for an empty index family; no core-preimage nullity is needed.
  With the split-injectivity hypotheses above,
  [`FundamentalGroupKernel`](SphereTopology/Topology/WidePushout/FundamentalGroupKernel.lean)
  identifies the kernel of the ambient-to-original-factor-coproduct retraction
  `ρ` with the ambient algebraic normal closure of `⋃ i, γᵢ(ker pᵢ)`.
  Here `γᵢ` is induced by chart inclusion; `pᵢ` comes from restricting the
  ambient factor collapse to that chart and then applying the inverse ULift
  homeomorphism to the original factor. Consequently, `q` is surjective exactly
  when `ker pᵢ ≤ ker γᵢ` for every chart. Under this condition, `q` and the specified
  `ρ` form a multiplicative equivalence, and these extensions are unique
  for arbitrary independently universed monoid targets. For the inclusion family
  into the ambient fundamental group, this condition is also necessary for
  uniqueness: when it fails, the identity and `q.comp ρ` agree on all original-factor
  restrictions but differ. No simply connected core, path-connected core preimages
  or chart–factor homotopy equivalences are required.
  Index and space universes are independent, and an empty family retains its point
  head. No vanishing of these chart defects or free-product computation from
  ordinary contractibility of chosen factor neighborhoods is asserted.
- **Subfamily retractions and continuous factorization.**
  [`TopCat.widePushoutPointSubfamilyRetraction`](SphereTopology/Topology/WidePushout/Subfamily.lean)
  retracts onto any subfamily, with an embedding inclusion whose range includes
  the common point. This inclusion is closed exactly when the chosen-point
  singleton in every omitted factor is closed; retained factors need no separation
  hypothesis. A continuous map factors through that inclusion exactly
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
  generators as nonidentity.
  [`CircleBouquet.generatorEquiv`](SphereTopology/Homotopy/CircleBouquet/FundamentalGroup.lean)
  identifies its fundamental group with `FreeGroup I`, sending each free generator
  to the included counterclockwise circle class. `CircleBouquet.lift` gives the
  unique extension of arbitrary generator values to a homomorphism into any
  group, in an independent target universe. Distinct included positive generators
  do not commute. The inverse equivalence is noncomputable; no geometric
  word-extraction algorithm is asserted.
  The continuous map `CircleBouquet.relabel σ` realizes arbitrary relabelings,
  preserving the original positive generators and commuting with `FreeGroup.map σ`.
  Source and target ambient and label universes are independent, including empty
  or infinite families and noninjective label maps. The universal property is
  natural under precomposition by this map through `CircleBouquet.lift_comp_relabel`.
  Its [topological criteria](SphereTopology/Homotopy/CircleBouquet/Topology.lean)
  characterize closed embeddings exactly by injective label maps and quotient
  maps exactly by surjective label maps. Relabeling is a
  [closed map exactly when every label fiber is finite](SphereTopology/Homotopy/CircleBouquet/ClosedMap.lean);
  the bouquet has the weak/final topology, not the Hawaiian-earring subspace topology.
  The induced fundamental-group homomorphism is injective or surjective exactly
  when the label map has the corresponding property. Its kernel is the normal
  closure of the differences `positiveGenerator i * (positiveGenerator k)⁻¹`
  for equal labels `σ i = σ k`, by `CircleBouquet.ker_mapOfEq_relabel`; no
  surjectivity assumption is needed.
- **Diagonal equivalence for non-antipodal pairs.** In any real normed vector
  space, [`Metric.Sphere.diagonalHomotopyEquiv`](SphereTopology/Homotopy/Sphere.lean)
  has the diagonal as its forward map and first projection as its inverse.
  Normalized affine interpolation stays in the non-antipodal-pair subspace and
  fixes the diagonal. No finite-dimensionality or nonemptiness hypothesis is needed.
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
`8c837e82648939ced56a8d7ee005d6f582204b1e`, and Group Theory
`9c060da75c15b9930292aec1d7655c2a44885842`. The manifest also includes
Homological Algebra `1ecd25213926138278dbd661bd516de9135d944a`.
Fetch the matching precompiled Mathlib cache successfully before building:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake -Kjobs=2 --wfail build
lake env lean -DwarningAsError=true SphereTopologyTest/PublicAPIClient.lean
```

`SphereTopology` and `SphereTopologyTest` are default Lake libraries; the
production aggregate imports no tests. The private coordinate, zero-period and
circle H-space checks are in
[`SphereTopologyTest.CircleHSpace`](SphereTopologyTest/CircleHSpace.lean).
The historical `SphereTopologyTest.CircleFundamentalGroup` and
`SphereTopologyTest.HSpaceFundamentalGroup` imports publicly re-export this
verification module. Routine use does not need `lake update`.

## Contents

| Module beneath `SphereTopology` | Public role |
| --- | --- |
| `Geometry.ForwardRay` | Total upper-root ray parameter and affine intersection point, sphere membership and positive-parameter characterization, boundary identities, joint off-diagonal continuity and agreement with Mathlib's boundary-start construction. |
| `Geometry.ForwardRayMap` | Sphere-valued continuous ray maps for inclusion-avoiding ambient-valued maps on closed balls in real inner-product affine torsors; boundary-only closed-ball images give a strict boundary retraction, with the closed-ball selfmap specialization, independent vector/point universes and arbitrary real radii. |
| [`Geometry.Projectivization`](SphereTopology/Geometry/Projectivization.lean) | Canonical real unit-sphere projection for the given norm, quotient-map and equal-or-antipodal fiber criteria, negation law, and quotient covering for the scalar action of `Metric.sphere (0 : ℝ) 1`. |
| [`Geometry.Stereographic`](SphereTopology/Geometry/Stereographic.lean) | Inner-product-space stereographic homeomorphisms to an orthogonal complement and its arbitrary-point puncture, with forward/inverse coercion laws and inverse-zero antipode. |
| [`Geometry.OnePointSphere`](SphereTopology/Geometry/OnePointSphere.lean) | Append-zero-last hyperplane isometry over real or complex scalars, and real one-point compactification coordinates with the last-axis north pole, finite-point formulas, off-pole inverse and zero/infinity laws, including zero dimension. |
| [`Geometry.CubeSphere`](SphereTopology/Geometry/CubeSphere.lean) | `Cube.onePointBoundaryComplHomeomorphSphere` uses increasing coordinates in their original order to identify the one-point compactification of the finite cube boundary complement with the last-axis unit sphere; `Cube.collapseToSphere` sends exactly the cube boundary to north, including the empty boundary in dimension zero; a pre-last ambient coordinate vanishes exactly on the boundary or its corresponding midpoint slice. |
| [`Geometry.SpherePinch`](SphereTopology/Geometry/SpherePinch.lean) | Positive-dimensional pinch to the existing two-factor point-wide-pushout, cube pullback and uniqueness, surjectivity and quotient topology, equatorial head fiber and equal-or-equatorial fiber criterion, closed-half and midpoint formulas, non-head quarter witnesses, raw folding and independently universed postcomposition; three distinct non-head values and unequal iterated three-factor folds. |
| [`Geometry.SphereCoordinateReflection`](SphereTopology/Geometry/SphereCoordinateReflection.lean) | North-fixing involutive reflection in every pre-last coordinate of each positive-dimensional sphere, original cube-reversal characteristic and uniqueness, generalized-loop comparison, and nonconstant reflection/identity folds, including S¹. |
| `Homotopy.Circle` | Deprecated public re-export of `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle`: signed-period integer loops, normalized fundamental-group coordinates, lifted endpoints and complex-circle agreement. |
| `Homotopy.CircleBouquet` | Arbitrary-index circle bouquet, inclusions and descent, final-topology open and closed tests, closed subfamily inclusions, finite-label-fiber closedness of relabeling, positive-generator homomorphism, circle retractions and generator nonidentity. The [closed-map criterion](SphereTopology/Homotopy/CircleBouquet/ClosedMap.lean) characterizes closed relabelings exactly by finite label fibers, using Mathlib's circle topology and the local point-wide-pushout criterion. |
| [`Homotopy.CircleBouquet.Topology`](SphereTopology/Homotopy/CircleBouquet/Topology.lean) | Relabeling is a closed embedding exactly for injective label maps, and a quotient map exactly for surjective label maps, with independent source and target ambient and label universes. |
| [`Homotopy.CircleBouquet.FundamentalGroup`](SphereTopology/Homotopy/CircleBouquet/FundamentalGroup.lean) | Free-group identification preserving the included positive classes, universal property for group targets in independent universes, relabeling kernels as normal closures of equal-label generator differences, and noncommuting distinct generators, including arbitrary or empty index families. |
| `Homotopy.CircleDegree` | Integer degree of unbased circle self-maps, composition and signed powers, free homotopy classification and a sufficient fixed-point condition. |
| `Homotopy.Disk` | Degree-zero boundary restrictions and non-retraction for the complex closed unit disk; boundary-only fixed points for complex-valued maps on closed balls of nonnegative radius, with the continuous self-map specialization. |
| `Homotopy.HSpaceFundamentalGroup` | Pointwise H-space loop multiplication, based comparison with concatenation, quotient comparison and commutativity at the unit. |
| [`Homotopy.HomotopyGroup.Sphere`](SphereTopology/Homotopy/HomotopyGroup/Sphere.lean) | Finite generalized-loop homeomorphism to fixed-north-pole sphere maps, natural set equivalence of homotopy classes with existing path components, representative and inverse formulas, constants, based postcomposition and singleton-relative homotopy. |
| [`Homotopy.HomotopyGroup.SpherePinch`](SphereTopology/Homotopy/HomotopyGroup/SpherePinch.lean) | Fold-class comparison with existing multiplication in the order `J(G) * J(F)`, both original retraction counits, associativity of folding and original three-factor coassociativity for positive-dimensional spheres; folded-map interchange and original-factor-swap cocommutativity in dimensions at least two, all relative to the last-axis north pole. |
| [`Homotopy.HomotopyGroup.SpherePinchFold`](SphereTopology/Homotopy/HomotopyGroup/SpherePinchFold.lean) | Jointly continuous raw folding on the compact-open north-based sphere-map subtype, closed-half formulas, agreement with coordinate-zero concatenation, preservation of simultaneous paths, and identity/constant order separation for every positive sphere dimension. |
| [`Homotopy.HomotopyGroup.SphereCoordinateReflection`](SphereTopology/Homotopy/HomotopyGroup/SphereCoordinateReflection.lean) | Precomposition by every pre-last coordinate reflection represents the existing homotopy-group inverse for arbitrary based targets; both reflection/identity pinch folds are nullhomotopic relative to north in every positive dimension, including S¹. |
| [`Homotopy.Projectivization`](SphereTopology/Homotopy/Projectivization.lean) | Real projective fundamental-group coordinates in `Multiplicative (ZMod 2)` under `2 < Module.rank ℝ E`, independent of the chosen unit lift, with covering-lift endpoint and projected antipodal-path laws. |
| `Homotopy.Sphere` | Real-normed-space normalization, non-antipodal interpolation and diagonal equivalence; one-pole contractibility, two-pole path connectedness and whole-sphere simple connectivity, the last two under `2 < Module.rank ℝ E`. |
| `Homotopy.TangentField`, `Homotopy.HairyBallSphere2` | Orthogonal-field homotopies and the standard S² continuous-field zero theorem; normalization is re-exported from `Homotopy.Sphere`. |
| `Topology.CoveringLifting` | Deprecated public re-export of `FundamentalGroupoids.Topology.Covering.Lifting`. Based unique lifting iff fundamental-group image containment, using Mathlib's sufficient criterion. |
| [`Topology.Projectivization`](SphereTopology/Topology/Projectivization.lean) | Quotient topology from nonzero vectors of a module over any division ring, assuming only a topology on the module; quotient-maker and continuity APIs, with no scalar topology or action-continuity premise. |
| `Topology.StdSimplex`, `Topology.SingularLifts` | Finite-simplex domain instances, evaluation equivalences, restriction bijections and equifibered singular maps for covering spaces. |
| `Topology.WidePushoutRetraction` | Selected-factor retractions, head and every-factor equations, and embeddings for arbitrary point-wide-pushouts. |
| `Topology.WidePushout.Separation` | Joint injectivity of factor retractions, including empty families; canonical T₀/T₁/T₂ inheritance and factorwise iff/reflection via factor embeddings. |
| `Topology.WidePushout` | Head- and factor-preserving quotient homeomorphism for arbitrary wide pushouts, final-topology continuity, independent-target descent and empty/singleton/point boundary results. |
| [`Topology.WidePushout.PointMap`](SphereTopology/Topology/WidePushout/PointMap.lean) | Point-preserving descent, characteristic equations, identity/composition, final topology and the head-retaining range union. |
| [`Topology.WidePushout.OpenEmbedding`](SphereTopology/Topology/WidePushout/OpenEmbedding.lean) | Structural image/injectivity identities, componentwise embeddings, and open/closed map and embedding criteria at their natural hypotheses. The [finite-label-fiber closed-map engine](SphereTopology/Topology/WidePushout/ClosedMap.lean) gives the sharp omitted-singleton criterion for given functions with closed components, point reflection and head/leg equations, without continuity or separation assumptions; it uses Mathlib's colimit topology and local `PointMap` and `Compactness` APIs. |
| [`Topology.WidePushout.OpenNeighborhood`](SphereTopology/Topology/WidePushout/OpenNeighborhood.lean) | Arbitrary-subset neighborhoods, local factor pullbacks and the ordinary open-subtype neighborhood homeomorphism. |
| [`Topology.WidePushout.PointLift`](SphereTopology/Topology/WidePushout/PointLift.lean) | Original-domain conjugation and the independent factor/index universe ULift caller. |
| `Topology.WidePushoutHomotopy` | Product-parameter continuity for supplied colimits, compatible wide-pushout family descent and interval-homotopy gluing, with independent parameter and target universes. |
| `Topology.WidePushoutPointHomotopy` | Point-preserving factor equivalences with singleton-relative inverse witnesses, head and factor equations, and contractions fixing the common point. |
| `Topology.WidePushout.Compactness` | Support away from chosen points, common-point covering characterization, finite support of compact subsets for T₁ factors and compact-domain finite-factor coverings. |
| `Topology.WidePushout.Chart` | Factor-plus-subset charts, exact inverse images and intersections, an empty-family-compatible cover, factorwise path connectedness, and openness for an open common subset containing the head. |
| `Topology.WidePushout.FundamentalGroup` | Open-neighborhood charts, common-overlap fundamental-group descent and extensionality; inclusion-induced coproduct map, conditional split injection and monoid-target extensions. |
| `Topology.WidePushout.FundamentalGroupColimit` | Core-to-chart fundamental-group star, ambient inclusion cocone, its colimit universal property and raw-colimit multiplicative equivalence preserving every leg in both directions; path-connected core and whole factors suffice. |
| [`Topology.WidePushout.FundamentalGroupKernel`](SphereTopology/Topology/WidePushout/FundamentalGroupKernel.lean) | Normal-closure kernel of the original-factor-coproduct retraction, exact original-factor generation criterion, specified multiplicative equivalence, monoid-target extension uniqueness and its sharp ambient self-target criterion; independent universes and empty families. |
| `Topology.WidePushout.Subfamily` | Arbitrary-subfamily inclusions and retractions, embeddings and exact ranges, closed-embedding criterion on omitted chosen points, supported-map factorization and uniqueness, nested-subfamily compatibility, and finite-subfamily factorization for compact domains and T₁ factors. |
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

The cube–sphere comparisons use ordinary compact-open mapping spaces and the
induced topology on the fixed-pole subtypes, not May's compactly generated
mapping-space convention. The finite sphere is locally compact Hausdorff,
supplying the source hypotheses for the relative-homotopy comparison; targets
need no separation or local compactness. In dimension zero, north has value `x`
and south may have any value `z : X`.
The separate compactification point at infinity remains present: the unique
cube point collapses to south, so the zero-dimensional cube collapse misses north.

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

- J. Peter May, *A Concise Course in Algebraic Topology*: Chapters 1–3, 8–9
  and 13–16. The cube–sphere comparisons use Chapter 8, §§1–2, pp. 57–58,
  and Chapter 9, §1, p. 65; other exact sections and conventions are in the
  guide and module references.
- Charles A. Weibel, *The K-book*, Example I.1.2.2: sphere-field motivation.
  Its two-independent-field obstruction is distinct from the stronger one-field
  zero theorem here; no algebraic kernel, row-completion or whole-book claim is made.
- Mathlib, [Simplicial Objects](https://github.com/FormalFrontier/simplicial-objects),
  [Fundamental Groupoids](https://github.com/FormalFrontier/fundamental-groupoids)
  and [Group Theory](https://github.com/FormalFrontier/group-theory).

## Credits and license

Authors: Formal Frontier Agents. Project Lean and documentation are AI-authored.
Mathematical sources, Mathlib contributors and original project, Prism and
Orrery contributions retain their distinct credit in [CREDITS.md](docs/CREDITS.md).
The generic stereographic API reuses Heather Macbeth's Mathlib sphere charts
and follows the library's earlier sphere/circle chart constructions. The normed
sphere topology APIs build on the existing generic sphere homotopies, Mathlib's
topology and linear algebra, and Fundamental Groupoids' two-open criterion.
The cube–sphere comparisons reuse Mathlib's generalized-loop APIs and
Fundamental Groupoids' one-point loop and path-component comparisons.
Licensed under [Apache-2.0](LICENSE); dependency and book authors retain their
own rights and notices. No book assets or excerpts are bundled.
