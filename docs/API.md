# API reference

This reference contains 567 native display sites in ten mathematical library leaves.
Import `SphereTopology` for the library; the 21 test/audit modules are separate.
All 32 shipped module records are retained, including 22 empty display records.
The ordinary build checks proofs; the complete axiom audit separately covers private declarations.
Native display-site counts are not a complete kernel-declaration census.

Headers below reuse native doc-gen4 display signatures, not complete declarations
with proof bodies. Five explicitly labeled headers are corrected by source
inspection at `f66621f5ff0d90bad849d4f7fcef3c7b96720d55`: four noncomputable
modifiers and one removed DecidableEq binder. Other native header tokens remain
unchanged. Source links follow the current source; retained native lines are historical.
Native pretty-printing uses each source namespace, notation and type inference;
consult the linked source for suppressed inferred types and universe conventions.
These displayed fragments are not promised to elaborate alone in a fresh namespace.
Source links are relative to this same checkout.

The historical native provenance and separate current source inspection are in [api-manifest.json](api-manifest.json).
See [generation instructions](README.md) and the [library overview](../README.md).
Where no source docstring exists, a separately authored **API note** is labeled explicitly.

## SphereTopology.Homology.Singular.Circle

Scope: mathematical library leaf.

### SphereTopology.E2

```lean
abbrev SphereTopology.E2 : Type
```

The real Euclidean plane, with coordinates indexed by `0` and `1`.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L35) (retained native site: line 35).

### SphereTopology.eastVector

```lean
def SphereTopology.eastVector : E2
```

The vector `(1, 0)` in the Euclidean plane.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L38) (retained native site: line 38).

### SphereTopology.eastVector_norm

```lean
theorem SphereTopology.eastVector_norm : ‖eastVector‖ = 1
```

**API note (not a source docstring):** The coordinate vector (1,0) has norm one in the Euclidean plane. This supplies the unit-circle membership proof for the east pole.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L41) (retained native site: line 41).

### SphereTopology.eastPoint

```lean
def SphereTopology.eastPoint : ↑(Metric.sphere 0 1)
```

The east pole `(1, 0)`, bundled as a point of the metric unit circle.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L44) (retained native site: line 44).

### SphereTopology.eastPoint_first

```lean
theorem SphereTopology.eastPoint_first : (↑eastPoint).ofLp 0 = 1
```

**API note (not a source docstring):** The east pole has coordinate zero equal to one. The native display uses ofLp for Euclidean coordinate evaluation.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L50) (retained native site: line 50).

### SphereTopology.eastPoint_second

```lean
theorem SphereTopology.eastPoint_second : (↑eastPoint).ofLp 1 = 0
```

**API note (not a source docstring):** The east pole has coordinate one equal to zero. Coordinates are indexed by Fin 2, starting at zero.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L53) (retained native site: line 53).

### SphereTopology.westPoint

```lean
noncomputable def SphereTopology.westPoint : ↑(Metric.sphere 0 1)
```

The west pole `(-1, 0)`, defined as the antipode of `eastPoint`.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L56) (retained native site: line 56).

### SphereTopology.northVector

```lean
def SphereTopology.northVector : E2
```

The vector `(0, 1)` in the Euclidean plane.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L58) (retained native site: line 58).

### SphereTopology.northPoint

```lean
def SphereTopology.northPoint : ↑(Metric.sphere 0 1)
```

The north pole `(0, 1)`, bundled as a point of the metric unit circle.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L60) (retained native site: line 60).

### SphereTopology.southPoint

```lean
noncomputable def SphereTopology.southPoint : ↑(Metric.sphere 0 1)
```

The south pole `(0, -1)`, defined as the antipode of `northPoint`.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L64) (retained native site: line 64).

### SphereTopology.eastPoint_ne_westPoint

```lean
theorem SphereTopology.eastPoint_ne_westPoint : eastPoint ≠ westPoint
```

**API note (not a source docstring):** The east and west poles of the literal real unit circle are distinct. This ensures their complements cover the circle.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L67) (retained native site: line 67).

### SphereTopology.sphere1

```lean
abbrev SphereTopology.sphere1 : TopCat
```

The literal metric unit circle in `E2`, viewed as an object of `TopCat`.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L72) (retained native site: line 72).

### SphereTopology.circleEastPunctured

```lean
def SphereTopology.circleEastPunctured : TopologicalSpace.Opens ↑sphere1
```

The complement of the east pole, first in the ordered east/west open cover.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L75) (retained native site: line 75).

### SphereTopology.circleWestPunctured

```lean
def SphereTopology.circleWestPunctured : TopologicalSpace.Opens ↑sphere1
```

The complement of the west pole, second in the ordered east/west open cover.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L79) (retained native site: line 79).

### SphereTopology.circlePunctured_join

```lean
theorem SphereTopology.circlePunctured_join : circleEastPunctured ⊔ circleWestPunctured = ⊤
```

**API note (not a source docstring):** The complement of the east pole and the complement of the west pole cover the entire circle, in that order. The opens lattice join is their union.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L83) (retained native site: line 83).

### SphereTopology.euclideanLineHomeomorphReal

```lean
noncomputable def SphereTopology.euclideanLineHomeomorphReal : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ
```

Identify the one-coordinate Euclidean space with `ℝ` by its unique coordinate.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L91) (retained native site: line 91).

### SphereTopology.circleEastPuncturedHomeomorph

```lean
noncomputable def SphereTopology.circleEastPuncturedHomeomorph : ↑((TopologicalSpace.Opens.toTopCat sphere1).obj circleEastPunctured) ≃ₜ ℝ
```

The east-pole stereographic chart, followed by the identification of
one-dimensional Euclidean space with `ℝ`. Its domain omits the east pole.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L96) (retained native site: line 96).

### SphereTopology.circleWestPuncturedHomeomorph

```lean
noncomputable def SphereTopology.circleWestPuncturedHomeomorph : ↑((TopologicalSpace.Opens.toTopCat sphere1).obj circleWestPunctured) ≃ₜ ℝ
```

The west-pole stereographic chart, followed by the identification of
one-dimensional Euclidean space with `ℝ`. Its domain omits the west pole.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L107) (retained native site: line 107).

### SphereTopology.circlePunctureIntersection

```lean
abbrev SphereTopology.circlePunctureIntersection : Type
```

The circle with both east and west poles removed, as the subtype underlying
the intersection of the two punctured opens.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L118) (retained native site: line 118).

### SphereTopology.circle_eq_east_or_west_of_second_eq_zero

```lean
theorem SphereTopology.circle_eq_east_or_west_of_second_eq_zero (p : ↑(Metric.sphere 0 1)) (hp : (↑p).ofLp 1 = 0) : p = eastPoint ∨ p = westPoint
```

**API note (not a source docstring):** A point of the literal unit circle whose second coordinate is zero is one of the east and west poles. The unit-norm hypothesis comes from the sphere subtype; the result is not a claim about arbitrary plane vectors.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L124) (retained native site: line 124).

### SphereTopology.circlePunctureIntersection_second_ne_zero

```lean
theorem SphereTopology.circlePunctureIntersection_second_ne_zero (p : circlePunctureIntersection) : (↑↑p).ofLp 1 ≠ 0
```

**API note (not a source docstring):** Removing both horizontal poles forces the second coordinate of every remaining circle point to be nonzero. This is the boundary fact used to split the intersection into its upper and lower components.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L143) (retained native site: line 143).

### SphereTopology.circlePunctureIntersectionComponent

```lean
noncomputable def SphereTopology.circlePunctureIntersectionComponent (p : circlePunctureIntersection) : Bool
```

The pinned component order: `false` is the upper semicircle and `true` is
the lower semicircle.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L150) (retained native site: line 150).

### SphereTopology.circlePunctureIntersectionComponent_eq_false_iff

```lean
theorem SphereTopology.circlePunctureIntersectionComponent_eq_false_iff (p : circlePunctureIntersection) : circlePunctureIntersectionComponent p = false ↔ 0 < (↑↑p).ofLp 1
```

**API note (not a source docstring):** On the twice-punctured circle, component false means that the second coordinate is strictly positive: the upper component.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L155) (retained native site: line 155).

### SphereTopology.circlePunctureIntersectionComponent_eq_true_iff

```lean
theorem SphereTopology.circlePunctureIntersectionComponent_eq_true_iff (p : circlePunctureIntersection) : circlePunctureIntersectionComponent p = true ↔ (↑↑p).ofLp 1 < 0
```

**API note (not a source docstring):** On the twice-punctured circle, component true means that the second coordinate is strictly negative: the lower component. The exclusion of both poles rules out the zero-coordinate boundary.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L160) (retained native site: line 160).

### SphereTopology.continuous_circlePunctureIntersectionComponent

```lean
theorem SphereTopology.continuous_circlePunctureIntersectionComponent : Continuous circlePunctureIntersectionComponent
```

**API note (not a source docstring):** The upper/lower component selector is continuous to the discrete Boolean two-point space. Its two fibers are open in the twice-punctured circle; it is not asserted continuous on the whole circle.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L170) (retained native site: line 170).

### SphereTopology.circlePunctureIntersectionToTwoPoint

```lean
noncomputable def SphereTopology.circlePunctureIntersectionToTwoPoint : C(circlePunctureIntersection, ↑TopCat.twoPointSpace)
```

The continuous component map to the discrete two-point space: upper points
map to `false`, and lower points map to `true`.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L191) (retained native site: line 191).

### SphereTopology.circlePunctureIntersectionRepresentative

```lean
noncomputable def SphereTopology.circlePunctureIntersectionRepresentative : Bool → circlePunctureIntersection
```

Choose the north pole for `false` and the south pole for `true`, each with
its proof of membership in the twice-punctured circle.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L198) (retained native site: line 198).

### SphereTopology.circlePunctureIntersectionFromTwoPoint

```lean
noncomputable def SphereTopology.circlePunctureIntersectionFromTwoPoint : C(↑TopCat.twoPointSpace, circlePunctureIntersection)
```

The continuous choice of north/south representatives, inverse to the
component map up to the radial homotopy.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L214) (retained native site: line 214).

### SphereTopology.circlePunctureIntersectionComponent_representative

```lean
theorem SphereTopology.circlePunctureIntersectionComponent_representative (b : Bool) : circlePunctureIntersectionComponent (circlePunctureIntersectionRepresentative b) = b
```

**API note (not a source docstring):** Selecting the component of the chosen north/south representative returns the original Boolean label. This is the exact right-inverse law of the component map.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L220) (retained native site: line 220).

### SphereTopology.circlePunctureIntersectionRepresentative_false_second

```lean
theorem SphereTopology.circlePunctureIntersectionRepresentative_false_second : (↑↑(circlePunctureIntersectionRepresentative false)).ofLp 1 = 1
```

**API note (not a source docstring):** The representative of the upper component false is the north pole and has second coordinate one.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L227) (retained native site: line 227).

### SphereTopology.circlePunctureIntersectionRepresentative_true_second

```lean
theorem SphereTopology.circlePunctureIntersectionRepresentative_true_second : (↑↑(circlePunctureIntersectionRepresentative true)).ofLp 1 = -1
```

**API note (not a source docstring):** The representative of the lower component true is the south pole and has second coordinate minus one.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L231) (retained native site: line 231).

### SphereTopology.circlePunctureIntersectionLinearVector

```lean
noncomputable def SphereTopology.circlePunctureIntersectionLinearVector (t : ↑unitInterval) (p : circlePunctureIntersection) : E2
```

Interpolate linearly from the chosen component representative at `t = 0`
to `p` at `t = 1`, before normalization. The second coordinate stays nonzero.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L235) (retained native site: line 235).

### SphereTopology.circlePunctureIntersectionLinearVector_second_pos_of_component_false

```lean
theorem SphereTopology.circlePunctureIntersectionLinearVector_second_pos_of_component_false (t : ↑unitInterval) (p : circlePunctureIntersection) (hp : circlePunctureIntersectionComponent p = false) : 0 < (circlePunctureIntersectionLinearVector t p).ofLp 1
```

**API note (not a source docstring):** For an upper-component point, the unnormalized segment from its north representative to the point has positive second coordinate at every time in the closed unit interval, including both endpoints.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L244) (retained native site: line 244).

### SphereTopology.circlePunctureIntersectionLinearVector_second_neg_of_component_true

```lean
theorem SphereTopology.circlePunctureIntersectionLinearVector_second_neg_of_component_true (t : ↑unitInterval) (p : circlePunctureIntersection) (hp : circlePunctureIntersectionComponent p = true) : (circlePunctureIntersectionLinearVector t p).ofLp 1 < 0
```

**API note (not a source docstring):** For a lower-component point, the unnormalized segment from its south representative to the point has negative second coordinate at every time in the closed unit interval.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L260) (retained native site: line 260).

### SphereTopology.circlePunctureIntersectionLinearVector_second_ne_zero

```lean
theorem SphereTopology.circlePunctureIntersectionLinearVector_second_ne_zero (t : ↑unitInterval) (p : circlePunctureIntersection) : (circlePunctureIntersectionLinearVector t p).ofLp 1 ≠ 0
```

**API note (not a source docstring):** The interpolating vector never has zero second coordinate, since the segment stays in the selected upper or lower component. The time parameter is restricted to the unit interval.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L277) (retained native site: line 277).

### SphereTopology.circlePunctureIntersectionLinearVector_ne_zero

```lean
theorem SphereTopology.circlePunctureIntersectionLinearVector_ne_zero (t : ↑unitInterval) (p : circlePunctureIntersection) : circlePunctureIntersectionLinearVector t p ≠ 0
```

**API note (not a source docstring):** The interpolating vector is nonzero at every allowed time. This justifies division by its norm in the radial homotopy.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L286) (retained native site: line 286).

### SphereTopology.circlePunctureIntersectionRadialVector

```lean
noncomputable def SphereTopology.circlePunctureIntersectionRadialVector (t : ↑unitInterval) (p : circlePunctureIntersection) : E2
```

Normalize the nonzero interpolating vector to norm one. This retains its
upper/lower component because normalization uses a positive scalar.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L293) (retained native site: line 293).

### SphereTopology.circlePunctureIntersectionRadialVector_norm

```lean
theorem SphereTopology.circlePunctureIntersectionRadialVector_norm (t : ↑unitInterval) (p : circlePunctureIntersection) : ‖circlePunctureIntersectionRadialVector t p‖ = 1
```

**API note (not a source docstring):** The radial normalization of the nonzero interpolating vector has norm one, so it defines a point of the unit circle.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L300) (retained native site: line 300).

### SphereTopology.circlePunctureIntersectionRadialVector_second_ne_zero

```lean
theorem SphereTopology.circlePunctureIntersectionRadialVector_second_ne_zero (t : ↑unitInterval) (p : circlePunctureIntersection) : (circlePunctureIntersectionRadialVector t p).ofLp 1 ≠ 0
```

**API note (not a source docstring):** Radial normalization retains a nonzero second coordinate, so it does not hit either removed horizontal pole.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L308) (retained native site: line 308).

### SphereTopology.circlePunctureIntersectionRadialPoint

```lean
noncomputable def SphereTopology.circlePunctureIntersectionRadialPoint (t : ↑unitInterval) (p : circlePunctureIntersection) : circlePunctureIntersection
```

The normalized interpolating vector as a point of the twice-punctured circle;
its nonzero second coordinate excludes both removed poles.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L316) (retained native site: line 316).

### SphereTopology.continuous_circlePunctureIntersectionLinearVector

```lean
theorem SphereTopology.continuous_circlePunctureIntersectionLinearVector : Continuous fun (q : ↑unitInterval × circlePunctureIntersection) => circlePunctureIntersectionLinearVector q.1 q.2
```

**API note (not a source docstring):** The unnormalized interpolation is jointly continuous in time and in the twice-punctured circle point. This is stronger than continuity for each fixed point separately.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L332) (retained native site: line 332).

### SphereTopology.continuous_circlePunctureIntersectionRadialPoint

```lean
theorem SphereTopology.continuous_circlePunctureIntersectionRadialPoint : Continuous fun (q : ↑unitInterval × circlePunctureIntersection) => circlePunctureIntersectionRadialPoint q.1 q.2
```

**API note (not a source docstring):** The normalized interpolation is jointly continuous as a map into the twice-punctured circle. Nonvanishing of the interpolating vector makes the inverse norm continuous.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L346) (retained native site: line 346).

### SphereTopology.circlePunctureIntersectionRadialHomotopyMap

```lean
noncomputable def SphereTopology.circlePunctureIntersectionRadialHomotopyMap : C(↑unitInterval × circlePunctureIntersection, circlePunctureIntersection)
```

Bundle the radial interpolation as a jointly continuous map of time and
point. Time zero selects the component representative; time one returns the point.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L356) (retained native site: line 356).

### SphereTopology.circlePunctureIntersectionRadialPoint_zero

```lean
theorem SphereTopology.circlePunctureIntersectionRadialPoint_zero (p : circlePunctureIntersection) : circlePunctureIntersectionRadialPoint 0 p = circlePunctureIntersectionRepresentative (circlePunctureIntersectionComponent p)
```

**API note (not a source docstring):** At time zero the radial homotopy returns the selected north/south representative of the point's component, not the original point in general.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L363) (retained native site: line 363).

### SphereTopology.circlePunctureIntersectionRadialPoint_one

```lean
theorem SphereTopology.circlePunctureIntersectionRadialPoint_one (p : circlePunctureIntersection) : circlePunctureIntersectionRadialPoint 1 p = p
```

**API note (not a source docstring):** At time one the radial homotopy is the identity on the twice-punctured circle.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L374) (retained native site: line 374).

### SphereTopology.circlePunctureIntersectionRadialHomotopy

```lean
noncomputable def SphereTopology.circlePunctureIntersectionRadialHomotopy : (circlePunctureIntersectionFromTwoPoint.comp circlePunctureIntersectionToTwoPoint).Homotopy (ContinuousMap.id circlePunctureIntersection)
```

The homotopy from the component-representative composite to the identity,
using normalized straight-line interpolation within each component.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L384) (retained native site: line 384).

### SphereTopology.circlePunctureIntersectionHomotopyEquiv

```lean
noncomputable def SphereTopology.circlePunctureIntersectionHomotopyEquiv : ContinuousMap.HomotopyEquiv circlePunctureIntersection ↑TopCat.twoPointSpace
```

The homotopy equivalence with the two-point space given by the component map
and north/south representatives, ordered as `false`/`true`.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L394) (retained native site: line 394).

### SphereTopology.circlePunctureIntersectionHomotopyEquivULift

```lean
noncomputable def SphereTopology.circlePunctureIntersectionHomotopyEquivULift : ContinuousMap.HomotopyEquiv (ULift.{u_1, 0} circlePunctureIntersection) (ULift.{u_2, 0} ↑TopCat.twoPointSpace)
```

Transport the component homotopy equivalence to `ULift` on both sides via
the canonical `ULift` homeomorphisms, without changing the component order.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L411) (retained native site: line 411).

### SphereTopology.circleEastPunctured_contractibleSpace

```lean
theorem SphereTopology.circleEastPunctured_contractibleSpace : ContractibleSpace ↑((TopologicalSpace.Opens.toTopCat sphere1).obj circleEastPunctured)
```

**API note (not a source docstring):** The circle with its east pole removed is contractible, by its stereographic homeomorphism with the real line. This theorem supplies the class value rather than declaring a new global instance.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L419) (retained native site: line 419).

### SphereTopology.circleWestPunctured_contractibleSpace

```lean
theorem SphereTopology.circleWestPunctured_contractibleSpace : ContractibleSpace ↑((TopologicalSpace.Opens.toTopCat sphere1).obj circleWestPunctured)
```

**API note (not a source docstring):** The circle with its west pole removed is contractible, by its stereographic homeomorphism with the real line. This is a theorem-valued class witness, not a claim that the whole circle contracts.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L424) (retained native site: line 424).

### SphereTopology.isZero_reducedSingularHomology_circleEastPunctured

```lean
theorem SphereTopology.isZero_reducedSingularHomology_circleEastPunctured (n : ℕ) : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat sphere1).obj circleEastPunctured).reducedSingularHomology n)
```

**API note (not a source docstring):** Every nonnegative reduced integral singular homology object of the east-punctured circle is zero. The natural-number degree includes reduced degree zero; no degree minus one is represented.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L429) (retained native site: line 429).

### SphereTopology.isZero_reducedSingularHomology_circleWestPunctured

```lean
theorem SphereTopology.isZero_reducedSingularHomology_circleWestPunctured (n : ℕ) : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat sphere1).obj circleWestPunctured).reducedSingularHomology n)
```

**API note (not a source docstring):** Every nonnegative reduced integral singular homology object of the west-punctured circle is zero, using contractibility of that open.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L435) (retained native site: line 435).

### SphereTopology.reducedSingularHomologyOneSphereOneIntegerIso

```lean
noncomputable def SphereTopology.reducedSingularHomologyOneSphereOneIntegerIso : sphere1.reducedSingularHomology 1 ≅ ↧ℤ
```

Identify the circle's first reduced integral singular homology with `ℤ`.
The coordinate uses the east/west ordered Mayer--Vietoris connecting map and
the two-point basis `[false] - [true]`, with `false` the upper component.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L441) (retained native site: line 441).

### SphereTopology.reducedSingularHomologyOneSphereOneIntegerIso_hom

```lean
theorem SphereTopology.reducedSingularHomologyOneSphereOneIntegerIso_hom : reducedSingularHomologyOneSphereOneIntegerIso.hom = CategoryTheory.CategoryStruct.comp (AlgebraicTopology.twoOpenReducedMayerVietorisδZero circleEastPunctured circleWestPunctured circlePunctured_join) (CategoryTheory.CategoryStruct.comp (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv circlePunctureIntersectionHomotopyEquiv 0).hom TopCat.reducedSingularHomologyZeroTwoPointIntegerIso.hom)
```

**API note (not a source docstring):** The chosen H-tilde-one circle coordinate is the ordered east/west reduced connecting morphism followed by the upper/lower two-point homotopy equivalence and its fixed integer coordinate. The formula identifies the chosen map, not merely an unspecified isomorphism with the integers.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L456) (retained native site: line 456).

### SphereTopology.circlePunctured_join_reversed

```lean
theorem SphereTopology.circlePunctured_join_reversed : circleWestPunctured ⊔ circleEastPunctured = ⊤
```

**API note (not a source docstring):** The west/east ordering of the same two punctured opens also covers the circle. This changes the order of the Mayer--Vietoris input, not the underlying union.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L465) (retained native site: line 465).

### SphereTopology.circlePunctureIntersectionReversed

```lean
abbrev SphereTopology.circlePunctureIntersectionReversed : Type
```

The same literal intersection with the puncture order reversed.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L470) (retained native site: line 470).

### SphereTopology.circlePunctureIntersectionSwapHomeomorph

```lean
def SphereTopology.circlePunctureIntersectionSwapHomeomorph : circlePunctureIntersectionReversed ≃ₜ circlePunctureIntersection
```

The sign-free identity homeomorphism between the two meet orderings.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L475) (retained native site: line 475).

### SphereTopology.circlePunctureIntersectionReversedHomotopyEquiv

```lean
noncomputable def SphereTopology.circlePunctureIntersectionReversedHomotopyEquiv : ContinuousMap.HomotopyEquiv circlePunctureIntersectionReversed ↑TopCat.twoPointSpace
```

The upper/lower equivalence for the reversed ordered cover.  It uses the
same Boolean order, so `false` is still upper and `true` is still lower.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L483) (retained native site: line 483).

### SphereTopology.circlePunctureIntersectionReversedComponent_eq_false_iff

```lean
theorem SphereTopology.circlePunctureIntersectionReversedComponent_eq_false_iff (p : circlePunctureIntersectionReversed) : circlePunctureIntersectionComponent (circlePunctureIntersectionSwapHomeomorph p) = false ↔ 0 < (↑↑p).ofLp 1
```

**API note (not a source docstring):** After the sign-free identification from the reversed meet ordering, label false still denotes a strictly positive second coordinate. Swapping cover order does not relabel the geometric upper component.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L490) (retained native site: line 490).

### SphereTopology.circlePunctureIntersectionReversedComponent_eq_true_iff

```lean
theorem SphereTopology.circlePunctureIntersectionReversedComponent_eq_true_iff (p : circlePunctureIntersectionReversed) : circlePunctureIntersectionComponent (circlePunctureIntersectionSwapHomeomorph p) = true ↔ (↑↑p).ofLp 1 < 0
```

**API note (not a source docstring):** After the sign-free identification from the reversed meet ordering, label true still denotes a strictly negative second coordinate. The lower component keeps its Boolean label.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L497) (retained native site: line 497).

### SphereTopology.reducedSingularHomologyOneSphereOneIntegerIsoReversed

```lean
noncomputable def SphereTopology.reducedSingularHomologyOneSphereOneIntegerIsoReversed : sphere1.reducedSingularHomology 1 ≅ ↧ℤ
```

The reversed-cover circle computation, retained as an order/sign client.
Its coordinate still means upper minus lower; the accepted ordered-cover swap
theorem below records the negation of the connecting morphism.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L504) (retained native site: line 504).

### SphereTopology.reducedSingularHomologyOneSphereOneIntegerIsoReversed_hom

```lean
theorem SphereTopology.reducedSingularHomologyOneSphereOneIntegerIsoReversed_hom : reducedSingularHomologyOneSphereOneIntegerIsoReversed.hom = CategoryTheory.CategoryStruct.comp (AlgebraicTopology.twoOpenReducedMayerVietorisδZero circleWestPunctured circleEastPunctured circlePunctured_join_reversed) (CategoryTheory.CategoryStruct.comp (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv circlePunctureIntersectionReversedHomotopyEquiv 0).hom TopCat.reducedSingularHomologyZeroTwoPointIntegerIso.hom)
```

**API note (not a source docstring):** The reversed coordinate map uses the west/east connecting morphism, the same upper/lower component labels, and the fixed two-point integer coordinate. Its construction is displayed separately from the original ordered coordinate.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L519) (retained native site: line 519).

### SphereTopology.circleReducedMayerVietoris_swap_eq_neg

```lean
theorem SphereTopology.circleReducedMayerVietoris_swap_eq_neg : CategoryTheory.CategoryStruct.comp (AlgebraicTopology.twoOpenReducedMayerVietorisδZero circleEastPunctured circleWestPunctured circlePunctured_join) (TopCat.reducedSingularHomologyMap (AlgebraicTopology.twoOpenIntersectionSwapMap circleEastPunctured circleWestPunctured) 0) = -AlgebraicTopology.twoOpenReducedMayerVietorisδZero circleWestPunctured circleEastPunctured circlePunctured_join_reversed
```

**API note (not a source docstring):** Transporting the east/west reduced connecting morphism along the sign-free intersection swap gives the negative of the west/east connecting morphism. The minus sign belongs to ordered Mayer--Vietoris, not to a relabeling of upper and lower components.

[Source](../SphereTopology/Homology/Singular/Circle.lean#L528) (retained native site: line 528).

## SphereTopology.Homology.Singular.MayerVietoris

Scope: mathematical library leaf.

### TopCat.openSingularSet

```lean
noncomputable def TopCat.openSingularSet {X : TopCat} (U : TopologicalSpace.Opens ↑X) : (toSSet.obj X).Subcomplex
```

The simplicial subset of singular simplices of `X` whose image is contained
in the open subset `U`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L44) (retained native site: line 44).

### TopCat.mem_openSingularSet_iff

```lean
theorem TopCat.mem_openSingularSet_iff {X : TopCat} (U : TopologicalSpace.Opens ↑X) {n : SimplexCategoryᵒᵖ} (x : (toSSet.obj X).obj n) : x ∈ (openSingularSet U).obj n ↔ Set.range ⇑((X.toSSetObjEquiv n) x) ⊆ ↑U
```

Membership in `openSingularSet U` means exactly that the range of the
singular simplex is contained in `U`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L50) (retained native site: line 50).

### TopCat.openSingularSetMap

```lean
noncomputable def TopCat.openSingularSetMap {X Y : TopCat} (f : X ⟶ Y) (U : TopologicalSpace.Opens ↑X) (W : TopologicalSpace.Opens ↑Y) (h : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑W) : (openSingularSet U).toSSet ⟶ (openSingularSet W).toSSet
```

The map on ambient open-singular subcomplexes induced by a map of spaces
which sends one open subset into another.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L71) (retained native site: line 71).

### TopCat.openSingularSetMap_comp_inclusion

```lean
theorem TopCat.openSingularSetMap_comp_inclusion {X Y : TopCat} (f : X ⟶ Y) (U : TopologicalSpace.Opens ↑X) (W : TopologicalSpace.Opens ↑Y) (h : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑W) : CategoryTheory.CategoryStruct.comp (openSingularSetMap f U W h) (openSingularSet W).ι = CategoryTheory.CategoryStruct.comp (openSingularSet U).ι (toSSet.map f)
```

**API note (not a source docstring):** For a continuous map sending U into W, mapping the ambient open-singular subcomplex and then including it in the target singular set equals inclusion followed by the full singular-set map. This compatibility does not require a cover.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L84) (retained native site: line 84).

### TopCat.openSingularSetMap_comp_inclusion_assoc

```lean
theorem TopCat.openSingularSetMap_comp_inclusion_assoc {X Y : TopCat} (f : X ⟶ Y) (U : TopologicalSpace.Opens ↑X) (W : TopologicalSpace.Opens ↑Y) (h : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑W) {Z : SSet} (h✝ : toSSet.obj Y ⟶ Z) : CategoryTheory.CategoryStruct.comp (openSingularSetMap f U W h) (CategoryTheory.CategoryStruct.comp (openSingularSet W).ι h✝) = CategoryTheory.CategoryStruct.comp (openSingularSet U).ι (CategoryTheory.CategoryStruct.comp (toSSet.map f) h✝)
```

**API note (not a source docstring):** Generated reassoc form of openSingularSetMap_comp_inclusion: the same inclusion/naturality identity after an arbitrary simplicial map out of the target singular set. The MapsTo hypothesis is retained.

Generated `reassoc` declaration from `TopCat.openSingularSetMap_comp_inclusion`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L84) (retained native site: line 84).

### TopCat.openSingularSetInfMap

```lean
noncomputable def TopCat.openSingularSetInfMap {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : (openSingularSet U ⊓ openSingularSet V).toSSet ⟶ (openSingularSet U' ⊓ openSingularSet V').toSSet
```

The induced map on intersections of two ambient open-singular
subcomplexes.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L90) (retained native site: line 90).

### TopCat.openSingularSetSupMap

```lean
noncomputable def TopCat.openSingularSetSupMap {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : (openSingularSet U ⊔ openSingularSet V).toSSet ⟶ (openSingularSet U' ⊔ openSingularSet V').toSSet
```

The induced map on unions of two ambient open-singular subcomplexes.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L105) (retained native site: line 105).

### TopCat.openSingularSetInfMap_comp_left

```lean
theorem TopCat.openSingularSetInfMap_comp_left {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : CategoryTheory.CategoryStruct.comp (openSingularSetInfMap f U V U' V' hU hV) (SSet.Subcomplex.homOfLE ⋯) = CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) (openSingularSetMap f U U' hU)
```

**API note (not a source docstring):** The induced map between intersections of ambient open-singular subcomplexes commutes with projection to the first member. The underlying continuous map must send U into U' and V into V'; no cover hypothesis is used.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L119) (retained native site: line 119).

### TopCat.openSingularSetInfMap_comp_left_assoc

```lean
theorem TopCat.openSingularSetInfMap_comp_left_assoc {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') {Z : SSet} (h : (openSingularSet U').toSSet ⟶ Z) : CategoryTheory.CategoryStruct.comp (openSingularSetInfMap f U V U' V' hU hV) (CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) h) = CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) (CategoryTheory.CategoryStruct.comp (openSingularSetMap f U U' hU) h)
```

**API note (not a source docstring):** Generated reassociated left-intersection compatibility, with arbitrary postcomposition from the target U' open-singular subcomplex to a simplicial set Z.

Generated `reassoc` declaration from `TopCat.openSingularSetInfMap_comp_left`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L119) (retained native site: line 119).

### TopCat.openSingularSetInfMap_comp_right

```lean
theorem TopCat.openSingularSetInfMap_comp_right {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : CategoryTheory.CategoryStruct.comp (openSingularSetInfMap f U V U' V' hU hV) (SSet.Subcomplex.homOfLE ⋯) = CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) (openSingularSetMap f V V' hV)
```

**API note (not a source docstring):** The induced map between intersections of ambient open-singular subcomplexes commutes with projection to the second member V'. Both MapsTo hypotheses are explicit, without assuming the opens cover.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L128) (retained native site: line 128).

### TopCat.openSingularSetInfMap_comp_right_assoc

```lean
theorem TopCat.openSingularSetInfMap_comp_right_assoc {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') {Z : SSet} (h : (openSingularSet V').toSSet ⟶ Z) : CategoryTheory.CategoryStruct.comp (openSingularSetInfMap f U V U' V' hU hV) (CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) h) = CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) (CategoryTheory.CategoryStruct.comp (openSingularSetMap f V V' hV) h)
```

**API note (not a source docstring):** Generated reassoc form of the right-intersection compatibility, followed by any simplicial map from the target V' open-singular subcomplex to Z.

Generated `reassoc` declaration from `TopCat.openSingularSetInfMap_comp_right`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L128) (retained native site: line 128).

### TopCat.openSingularSetMap_comp_supLeft

```lean
theorem TopCat.openSingularSetMap_comp_supLeft {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : CategoryTheory.CategoryStruct.comp (openSingularSetMap f U U' hU) (SSet.Subcomplex.homOfLE ⋯) = CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) (openSingularSetSupMap f U V U' V' hU hV)
```

**API note (not a source docstring):** Mapping the first ambient open-singular subcomplex and then including it in the target union agrees with including in the source union and applying the induced union map. The ordered first member is U, and the pair need not cover.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L137) (retained native site: line 137).

### TopCat.openSingularSetMap_comp_supLeft_assoc

```lean
theorem TopCat.openSingularSetMap_comp_supLeft_assoc {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') {Z : SSet} (h : (openSingularSet U' ⊔ openSingularSet V').toSSet ⟶ Z) : CategoryTheory.CategoryStruct.comp (openSingularSetMap f U U' hU) (CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) h) = CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) (CategoryTheory.CategoryStruct.comp (openSingularSetSupMap f U V U' V' hU hV) h)
```

**API note (not a source docstring):** Generated reassociated first-member/union naturality identity, after an arbitrary map from the target union of open-singular subcomplexes to Z.

Generated `reassoc` declaration from `TopCat.openSingularSetMap_comp_supLeft`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L137) (retained native site: line 137).

### TopCat.openSingularSetMap_comp_supRight

```lean
theorem TopCat.openSingularSetMap_comp_supRight {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : CategoryTheory.CategoryStruct.comp (openSingularSetMap f V V' hV) (SSet.Subcomplex.homOfLE ⋯) = CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) (openSingularSetSupMap f U V U' V' hU hV)
```

**API note (not a source docstring):** Mapping the second ambient open-singular subcomplex and then including it in the target union agrees with inclusion followed by the induced union map. The second member is V, with no cover assumption.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L146) (retained native site: line 146).

### TopCat.openSingularSetMap_comp_supRight_assoc

```lean
theorem TopCat.openSingularSetMap_comp_supRight_assoc {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') {Z : SSet} (h : (openSingularSet U' ⊔ openSingularSet V').toSSet ⟶ Z) : CategoryTheory.CategoryStruct.comp (openSingularSetMap f V V' hV) (CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) h) = CategoryTheory.CategoryStruct.comp (SSet.Subcomplex.homOfLE ⋯) (CategoryTheory.CategoryStruct.comp (openSingularSetSupMap f U V U' V' hU hV) h)
```

**API note (not a source docstring):** Generated reassoc form of the second-member/union naturality identity, retaining the ordered MapsTo hypotheses and allowing arbitrary postcomposition from the target union.

Generated `reassoc` declaration from `TopCat.openSingularSetMap_comp_supRight`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L146) (retained native site: line 146).

### TopCat.openSingularSetIso

```lean
noncomputable def TopCat.openSingularSetIso {X : TopCat} (U : TopologicalSpace.Opens ↑X) : toSSet.obj ((TopologicalSpace.Opens.toTopCat X).obj U) ≅ (openSingularSet U).toSSet
```

Singular simplices of the open subspace `U` identify with singular
simplices of `X` whose image is contained in `U`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L168) (retained native site: line 168).

### TopCat.twoOpenCover

```lean
def TopCat.twoOpenCover {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : Bool → TopologicalSpace.Opens ↑X
```

The ordered two-member family `(U,V)`.  The Boolean value `false` indexes
`U`, and `true` indexes `V`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L188) (retained native site: line 188).

### TopCat.isOpenCover_twoOpenCover

```lean
theorem TopCat.isOpenCover_twoOpenCover {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (hUV : U ⊔ V = ⊤) : TopologicalSpace.IsOpenCover (twoOpenCover U V)
```

The ordered family `(U,V)` covers exactly when `U ⊔ V = ⊤`.

Formal boundary: the displayed theorem supplies the stated implication; the retained native prose above is not evidence of a separate converse.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L193) (retained native site: line 193).

### TopCat.openSingularSet_inf

```lean
theorem TopCat.openSingularSet_inf {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : openSingularSet U ⊓ openSingularSet V = openSingularSet (U ⊓ V)
```

Intersecting the ambient singular subcomplexes agrees with taking the
singular subcomplex of the intersection.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L202) (retained native site: line 202).

### TopCat.openSingularSet_sup

```lean
theorem TopCat.openSingularSet_sup {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : openSingularSet U ⊔ openSingularSet V = smallSingularSet (twoOpenCover U V)
```

The union of the two ambient singular subcomplexes is the accepted
cover-small singular set for the ordered family `(U,V)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L213) (retained native site: line 213).

### TopCat.openMap

```lean
def TopCat.openMap {X Y : TopCat} (f : X ⟶ Y) (U : TopologicalSpace.Opens ↑X) (W : TopologicalSpace.Opens ↑Y) (h : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑W) : (TopologicalSpace.Opens.toTopCat X).obj U ⟶ (TopologicalSpace.Opens.toTopCat Y).obj W
```

A continuous map restricted to a map between open subspaces.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L231) (retained native site: line 231).

### TopCat.openMap_comp_inclusion

```lean
theorem TopCat.openMap_comp_inclusion {X Y : TopCat} (f : X ⟶ Y) (U : TopologicalSpace.Opens ↑X) (W : TopologicalSpace.Opens ↑Y) (h : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑W) : CategoryTheory.CategoryStruct.comp (openMap f U W h) W.inclusion' = CategoryTheory.CategoryStruct.comp U.inclusion' f
```

**API note (not a source docstring):** Restricting a continuous map to U with values in W and then including W into Y is the original map after including U into X. The supplied MapsTo proof provides the restriction.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L237) (retained native site: line 237).

### TopCat.openMap_comp_inclusion_assoc

```lean
theorem TopCat.openMap_comp_inclusion_assoc {X Y : TopCat} (f : X ⟶ Y) (U : TopologicalSpace.Opens ↑X) (W : TopologicalSpace.Opens ↑Y) (h : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑W) {Z : TopCat} (h✝ : Y ⟶ Z) : CategoryTheory.CategoryStruct.comp (openMap f U W h) (CategoryTheory.CategoryStruct.comp W.inclusion' h✝) = CategoryTheory.CategoryStruct.comp U.inclusion' (CategoryTheory.CategoryStruct.comp f h✝)
```

**API note (not a source docstring):** Generated reassociated restriction/inclusion formula: the same equality remains true after any continuous map from Y to Z. No cover condition is added.

Generated `reassoc` declaration from `TopCat.openMap_comp_inclusion`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L237) (retained native site: line 237).

### TopCat.mapsTo_twoOpenCover

```lean
theorem TopCat.mapsTo_twoOpenCover {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') (i : Bool) : ∃ (j : Bool), Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑(twoOpenCover U V i) ↑(twoOpenCover U' V' j)
```

A map respecting `U` and `V` respects the corresponding ordered Boolean
covers without changing the index.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L242) (retained native site: line 242).

### AlgebraicTopology.openSingularChainIso

```lean
noncomputable def AlgebraicTopology.openSingularChainIso {X : TopCat} (U : TopologicalSpace.Opens ↑X) : (TopCat.toSSet.obj ((TopologicalSpace.Opens.toTopCat X).obj U)).chainComplex integerCoefficients ≅ (TopCat.openSingularSet U).toSSet.chainComplex integerCoefficients
```

The chain isomorphism identifying ordinary singular chains of an open
subspace with the corresponding simplicial subcomplex in the ambient space.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L258) (retained native site: line 258).

### AlgebraicTopology.isPushout_chainComplexMap

```lean
theorem AlgebraicTopology.isPushout_chainComplexMap {W X Y Z : SSet} {f : W ⟶ X} {g : W ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z} (h : CategoryTheory.IsPushout f g i j) : CategoryTheory.IsPushout (SSet.chainComplexMap f integerCoefficients) (SSet.chainComplexMap g integerCoefficients) (SSet.chainComplexMap i integerCoefficients) (SSet.chainComplexMap j integerCoefficients)
```

Integer simplicial chains preserve pushout squares of simplicial sets.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L283) (retained native site: line 283).

### AlgebraicTopology.mono_chainComplexMap_subcomplex

```lean
theorem AlgebraicTopology.mono_chainComplexMap_subcomplex {X : SSet} {A B : X.Subcomplex} (h : A ≤ B) : CategoryTheory.Mono (SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) integerCoefficients)
```

An inclusion of simplicial subcomplexes induces a monomorphism on integer
chain complexes.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L296) (retained native site: line 296).

### AlgebraicTopology.subcomplex_inter_union_isPushout

```lean
theorem AlgebraicTopology.subcomplex_inter_union_isPushout {X : SSet} (A B : X.Subcomplex) : CategoryTheory.IsPushout (SSet.Subcomplex.homOfLE ⋯) (SSet.Subcomplex.homOfLE ⋯) (SSet.Subcomplex.homOfLE ⋯) (SSet.Subcomplex.homOfLE ⋯)
```

The pushout square formed by the intersection and union of two simplicial
subcomplexes.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L307) (retained native site: line 307).

### AlgebraicTopology.subcomplexUnionShortComplex

```lean
noncomputable def AlgebraicTopology.subcomplexUnionShortComplex {X : SSet} (A B : X.Subcomplex) : CategoryTheory.ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)
```

The ordered difference/sum short complex of integer chains associated to
two simplicial subcomplexes.  Its first map is `(c,-c)` and its second map is
addition.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L319) (retained native site: line 319).

### AlgebraicTopology.subcomplexUnionShortExact

```lean
theorem AlgebraicTopology.subcomplexUnionShortExact {X : SSet} (A B : X.Subcomplex) : (subcomplexUnionShortComplex A B).ShortExact
```

The difference/sum chain complex for two simplicial subcomplexes is short
exact.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L326) (retained native site: line 326).

### AlgebraicTopology.subcomplexInfSwapChainIso

```lean
noncomputable def AlgebraicTopology.subcomplexInfSwapChainIso {X : SSet} (A B : X.Subcomplex) : (A ⊓ B).toSSet.chainComplex integerCoefficients ≅ (B ⊓ A).toSSet.chainComplex integerCoefficients
```

Swapping the two intersection factors at chain level.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L351) (retained native site: line 351).

### AlgebraicTopology.subcomplexSupSwapChainIso

```lean
noncomputable def AlgebraicTopology.subcomplexSupSwapChainIso {X : SSet} (A B : X.Subcomplex) : (A ⊔ B).toSSet.chainComplex integerCoefficients ≅ (B ⊔ A).toSSet.chainComplex integerCoefficients
```

Swapping the two union factors at chain level.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L358) (retained native site: line 358).

### AlgebraicTopology.subcomplexUnionSwapIso

```lean
noncomputable def AlgebraicTopology.subcomplexUnionSwapIso {X : SSet} (A B : X.Subcomplex) : subcomplexUnionShortComplex A B ≅ subcomplexUnionShortComplex B A
```

Swapping the two members of the ordered difference/sum sequence.  The
intersection term is multiplied by `-1`, the middle term is braided, and the
union term is merely transported across commutativity of union.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L365) (retained native site: line 365).

### AlgebraicTopology.subcomplexUnionδ

```lean
noncomputable def AlgebraicTopology.subcomplexUnionδ {X : SSet} (A B : X.Subcomplex) (n : ℕ) : (A ⊔ B).toSSet.homology integerCoefficients (n + 1) ⟶ (A ⊓ B).toSSet.homology integerCoefficients n
```

The connecting map of the union short exact sequence, from degree `n+1`
to degree `n`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L389) (retained native site: line 389).

### AlgebraicTopology.subcomplexUnion_exact₁

```lean
theorem AlgebraicTopology.subcomplexUnion_exact₁ {X : SSet} (A B : X.Subcomplex) (n : ℕ) : { X₁ := (A ⊔ B).toSSet.homology integerCoefficients (n + 1), X₂ := (A ⊓ B).toSSet.homology integerCoefficients n, X₃ := HomologicalComplex.homology (subcomplexUnionShortComplex A B).X₂ n, f := subcomplexUnionδ A B n, g := HomologicalComplex.homologyMap (subcomplexUnionShortComplex A B).f n, zero := ⋯ }.Exact
```

Exactness at the intersection term after the connecting map.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L396) (retained native site: line 396).

### AlgebraicTopology.subcomplexUnion_exact₂

```lean
theorem AlgebraicTopology.subcomplexUnion_exact₂ {X : SSet} (A B : X.Subcomplex) (n : ℕ) : { X₁ := HomologicalComplex.homology (subcomplexUnionShortComplex A B).X₁ n, X₂ := HomologicalComplex.homology (subcomplexUnionShortComplex A B).X₂ n, X₃ := HomologicalComplex.homology (subcomplexUnionShortComplex A B).X₃ n, f := HomologicalComplex.homologyMap (subcomplexUnionShortComplex A B).f n, g := HomologicalComplex.homologyMap (subcomplexUnionShortComplex A B).g n, zero := ⋯ }.Exact
```

Exactness at the direct-sum chain-complex homology term.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L404) (retained native site: line 404).

### AlgebraicTopology.subcomplexUnion_exact₃

```lean
theorem AlgebraicTopology.subcomplexUnion_exact₃ {X : SSet} (A B : X.Subcomplex) (n : ℕ) : { X₁ := HomologicalComplex.homology (subcomplexUnionShortComplex A B).X₂ (n + 1), X₂ := HomologicalComplex.homology (subcomplexUnionShortComplex A B).X₃ (n + 1), X₃ := (A ⊓ B).toSSet.homology integerCoefficients n, f := HomologicalComplex.homologyMap (subcomplexUnionShortComplex A B).g (n + 1), g := subcomplexUnionδ A B n, zero := ⋯ }.Exact
```

Exactness at the union term before the connecting map.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L415) (retained native site: line 415).

### AlgebraicTopology.subcomplexUnionδ_swap

```lean
theorem AlgebraicTopology.subcomplexUnionδ_swap {X : SSet} (A B : X.Subcomplex) (n : ℕ) : CategoryTheory.CategoryStruct.comp (subcomplexUnionδ A B n) (HomologicalComplex.homologyMap (subcomplexInfSwapChainIso A B).hom n) = -CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (subcomplexSupSwapChainIso A B).hom (n + 1)) (subcomplexUnionδ B A n)
```

Swapping the ordered pair multiplies the connecting morphism by `-1`,
after the canonical transports across commutativity of intersection and union.
This records the sign convention independently of any topological client.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L423) (retained native site: line 423).

### AlgebraicTopology.integralSingularChains

```lean
noncomputable abbrev AlgebraicTopology.integralSingularChains (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ
```

The integral singular chain complex of a topological space.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L442) (retained native site: line 442).

### AlgebraicTopology.integralSingularChainMap

```lean
noncomputable def AlgebraicTopology.integralSingularChainMap {X Y : TopCat} (f : X ⟶ Y) : integralSingularChains X ⟶ integralSingularChains Y
```

The integral singular chain map induced by a continuous map.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L446) (retained native site: line 446).

### AlgebraicTopology.twoOpenIntersectionToLeft

```lean
def AlgebraicTopology.twoOpenIntersectionToLeft {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : (TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V) ⟶ (TopologicalSpace.Opens.toTopCat X).obj U
```

Inclusion of `U ∩ V` into the first open set.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L451) (retained native site: line 451).

### AlgebraicTopology.twoOpenIntersectionToRight

```lean
def AlgebraicTopology.twoOpenIntersectionToRight {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : (TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V) ⟶ (TopologicalSpace.Opens.toTopCat X).obj V
```

Inclusion of `U ∩ V` into the second open set.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L456) (retained native site: line 456).

### AlgebraicTopology.twoOpenIntersectionToLeft_comp

```lean
theorem AlgebraicTopology.twoOpenIntersectionToLeft_comp {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : CategoryTheory.CategoryStruct.comp (twoOpenIntersectionToLeft U V) U.inclusion' = (U ⊓ V).inclusion'
```

**API note (not a source docstring):** The literal inclusion of U intersect V into U followed by the inclusion of U into X is the direct inclusion of the intersection into X. This identity is independent of whether U and V cover X.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L461) (retained native site: line 461).

### AlgebraicTopology.twoOpenIntersectionToLeft_comp_assoc

```lean
theorem AlgebraicTopology.twoOpenIntersectionToLeft_comp_assoc {X : TopCat} (U V : TopologicalSpace.Opens ↑X) {Z : TopCat} (h : X ⟶ Z) : CategoryTheory.CategoryStruct.comp (twoOpenIntersectionToLeft U V) (CategoryTheory.CategoryStruct.comp U.inclusion' h) = CategoryTheory.CategoryStruct.comp (U ⊓ V).inclusion' h
```

**API note (not a source docstring):** Generated reassoc form of the first intersection-inclusion identity, with an arbitrary continuous map from X to Z after the inclusion.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenIntersectionToLeft_comp`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L461) (retained native site: line 461).

### AlgebraicTopology.twoOpenIntersectionToRight_comp

```lean
theorem AlgebraicTopology.twoOpenIntersectionToRight_comp {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : CategoryTheory.CategoryStruct.comp (twoOpenIntersectionToRight U V) V.inclusion' = (U ⊓ V).inclusion'
```

**API note (not a source docstring):** The literal inclusion of U intersect V into V followed by the inclusion of V into X is the direct inclusion of the intersection into X. There is no cover hypothesis.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L467) (retained native site: line 467).

### AlgebraicTopology.twoOpenIntersectionToRight_comp_assoc

```lean
theorem AlgebraicTopology.twoOpenIntersectionToRight_comp_assoc {X : TopCat} (U V : TopologicalSpace.Opens ↑X) {Z : TopCat} (h : X ⟶ Z) : CategoryTheory.CategoryStruct.comp (twoOpenIntersectionToRight U V) (CategoryTheory.CategoryStruct.comp V.inclusion' h) = CategoryTheory.CategoryStruct.comp (U ⊓ V).inclusion' h
```

**API note (not a source docstring):** Generated reassociated second intersection-inclusion formula, followed by an arbitrary continuous map from X to Z.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenIntersectionToRight_comp`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L467) (retained native site: line 467).

### AlgebraicTopology.twoOpenDifferenceChainMap

```lean
noncomputable def AlgebraicTopology.twoOpenDifferenceChainMap {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V)) ⟶ integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj U) ⊞ integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj V)
```

The ordered chain difference `c ↦ (c,-c)` induced by the two
intersection inclusions.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L473) (retained native site: line 473).

### AlgebraicTopology.twoOpenSumChainMap

```lean
noncomputable def AlgebraicTopology.twoOpenSumChainMap {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj U) ⊞ integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj V) ⟶ integralSingularChains X
```

The ordered chain sum induced by the inclusions of `U` and `V` into `X`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L483) (retained native site: line 483).

### AlgebraicTopology.twoOpenDifference_comp_sum

```lean
theorem AlgebraicTopology.twoOpenDifference_comp_sum {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : CategoryTheory.CategoryStruct.comp (twoOpenDifferenceChainMap U V) (twoOpenSumChainMap U V) = 0
```

The ordered difference followed by the sum is zero.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L491) (retained native site: line 491).

### AlgebraicTopology.twoOpenDifference_comp_sum_assoc

```lean
theorem AlgebraicTopology.twoOpenDifference_comp_sum_assoc {X : TopCat} (U V : TopologicalSpace.Opens ↑X) {Z : ChainComplex (ModuleCat ℤ) ℕ} (h : integralSingularChains X ⟶ Z) : CategoryTheory.CategoryStruct.comp (twoOpenDifferenceChainMap U V) (CategoryTheory.CategoryStruct.comp (twoOpenSumChainMap U V) h) = CategoryTheory.CategoryStruct.comp 0 h
```

The ordered difference followed by the sum is zero.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenDifference_comp_sum`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L492) (retained native site: line 492).

### AlgebraicTopology.twoOpenIntersectionMap

```lean
def AlgebraicTopology.twoOpenIntersectionMap {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : (TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V) ⟶ (TopologicalSpace.Opens.toTopCat Y).obj (U' ⊓ V')
```

The map of intersection subspaces induced by a map respecting an ordered
pair of opens.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L501) (retained native site: line 500).

### AlgebraicTopology.twoOpenBiprodChainMap

```lean
noncomputable def AlgebraicTopology.twoOpenBiprodChainMap {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj U) ⊞ integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj V) ⟶ integralSingularChains ((TopologicalSpace.Opens.toTopCat Y).obj U') ⊞ integralSingularChains ((TopologicalSpace.Opens.toTopCat Y).obj V')
```

The direct-sum chain map induced by a map respecting the ordered pair.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L510) (retained native site: line 509).

### AlgebraicTopology.twoOpenSmallChainMap

```lean
noncomputable def AlgebraicTopology.twoOpenSmallChainMap {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : smallSingularChainComplex (TopCat.twoOpenCover U V) ⟶ smallSingularChainComplex (TopCat.twoOpenCover U' V')
```

The cover-small chain map induced by a map respecting the ordered pair.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L522) (retained native site: line 521).

### AlgebraicTopology.twoOpenAmbientShortComplex

```lean
noncomputable abbrev AlgebraicTopology.twoOpenAmbientShortComplex {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : CategoryTheory.ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)
```

The chain-level difference/sum sequence inside the singular set of `X`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L531) (retained native site: line 530).

### AlgebraicTopology.twoOpenAmbientShortComplexMap

```lean
noncomputable def AlgebraicTopology.twoOpenAmbientShortComplexMap {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : twoOpenAmbientShortComplex U V ⟶ twoOpenAmbientShortComplex U' V'
```

Naturality of the ambient difference/sum short complex for maps respecting
ordered pairs of opens.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L535) (retained native site: line 534).

### AlgebraicTopology.twoOpenIntersectionChainIso

```lean
noncomputable def AlgebraicTopology.twoOpenIntersectionChainIso {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V)) ≅ (twoOpenAmbientShortComplex U V).X₁
```

Ordinary chains on `U ∩ V` identify with the first term of the ambient
difference/sum sequence.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L574) (retained native site: line 573).

### AlgebraicTopology.twoOpenBiprodChainIso

```lean
noncomputable def AlgebraicTopology.twoOpenBiprodChainIso {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj U) ⊞ integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj V) ≅ (twoOpenAmbientShortComplex U V).X₂
```

The direct sum of ordinary chains on `U` and `V` identifies with the
middle term of the ambient difference/sum sequence.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L583) (retained native site: line 582).

### AlgebraicTopology.twoOpenUnionChainIso

```lean
noncomputable def AlgebraicTopology.twoOpenUnionChainIso {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : (twoOpenAmbientShortComplex U V).X₃ ≅ smallSingularChainComplex (TopCat.twoOpenCover U V)
```

The last ambient term identifies with chains small in the ordered cover
`(U,V)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L591) (retained native site: line 590).

### AlgebraicTopology.twoOpenSmallShortComplex

```lean
noncomputable def AlgebraicTopology.twoOpenSmallShortComplex {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : CategoryTheory.ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)
```

The ordinary-chain / cover-small-chain short complex for the ordered pair
`(U,V)`.  Its first map uses the convention `(c,-c)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L599) (retained native site: line 598).

### AlgebraicTopology.twoOpenSmallToAmbientIso

```lean
noncomputable def AlgebraicTopology.twoOpenSmallToAmbientIso {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : twoOpenSmallShortComplex U V ≅ twoOpenAmbientShortComplex U V
```

The ordinary/open-chain short complex identified with its ambient
subcomplex model.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L613) (retained native site: line 612).

### AlgebraicTopology.twoOpenSmallShortExact

```lean
theorem AlgebraicTopology.twoOpenSmallShortExact {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : (twoOpenSmallShortComplex U V).ShortExact
```

The ordinary-chain / cover-small-chain sequence is short exact.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L622) (retained native site: line 621).

### AlgebraicTopology.twoOpenSmallShortComplexSwapIso

```lean
noncomputable def AlgebraicTopology.twoOpenSmallShortComplexSwapIso {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : twoOpenSmallShortComplex U V ≅ twoOpenSmallShortComplex V U
```

Swapping the two opens in the cover-small short complex.  The first
component includes the sign forced by the convention `c ↦ (c,-c)`, the middle
component braids the two summands, and the last component reindexes the same
cover-small chains.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L630) (retained native site: line 629).

### AlgebraicTopology.twoOpenIntersectionSwapChainIso

```lean
noncomputable def AlgebraicTopology.twoOpenIntersectionSwapChainIso {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : (twoOpenSmallShortComplex U V).X₁ ≅ (twoOpenSmallShortComplex V U).X₁
```

The sign-free transport between the intersection-chain terms when the
ordered pair is swapped.  The minus sign removes the sign already present in
the first component of `twoOpenSmallShortComplexSwapIso`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L642) (retained native site: line 641).

### AlgebraicTopology.twoOpenCoverSwapChainIso

```lean
noncomputable def AlgebraicTopology.twoOpenCoverSwapChainIso {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : (twoOpenSmallShortComplex U V).X₃ ≅ (twoOpenSmallShortComplex V U).X₃
```

Reindexing the same cover-small chains after swapping the two opens.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L651) (retained native site: line 650).

### AlgebraicTopology.twoOpenCoverSwapChainIso_comp_inclusion

```lean
theorem AlgebraicTopology.twoOpenCoverSwapChainIso_comp_inclusion {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : CategoryTheory.CategoryStruct.comp (twoOpenCoverSwapChainIso U V).hom (smallSingularChainInclusion (TopCat.twoOpenCover V U)) = smallSingularChainInclusion (TopCat.twoOpenCover U V)
```

Swapping the two entries only reindexes cover-small chains: after inclusion
in all singular chains, the swap map is the identity.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L657) (retained native site: line 656).

### AlgebraicTopology.twoOpenCoverSwapChainIso_comp_inclusion_assoc

```lean
theorem AlgebraicTopology.twoOpenCoverSwapChainIso_comp_inclusion_assoc {X : TopCat} (U V : TopologicalSpace.Opens ↑X) {Z : ChainComplex (ModuleCat ℤ) ℕ} (h : ((singularChainComplexFunctor (ModuleCat ℤ)).obj integerCoefficients).obj X ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (twoOpenCoverSwapChainIso U V).hom (smallSingularChainInclusion (TopCat.twoOpenCover V U))) h = CategoryTheory.CategoryStruct.comp (smallSingularChainInclusion (TopCat.twoOpenCover U V)) h
```

Swapping the two entries only reindexes cover-small chains: after inclusion
in all singular chains, the swap map is the identity.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenCoverSwapChainIso_comp_inclusion`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L659) (retained native site: line 658).

### AlgebraicTopology.twoOpenSmallShortComplexMap

```lean
noncomputable def AlgebraicTopology.twoOpenSmallShortComplexMap {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : twoOpenSmallShortComplex U V ⟶ twoOpenSmallShortComplex U' V'
```

The natural map between the short exact chain sequences associated to a
continuous map respecting ordered pairs of opens.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L685) (retained native site: line 684).

### AlgebraicTopology.twoOpenSmallShortComplexMap_comp_inclusion

```lean
theorem AlgebraicTopology.twoOpenSmallShortComplexMap_comp_inclusion {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : CategoryTheory.CategoryStruct.comp (twoOpenSmallShortComplexMap f U V U' V' hU hV).τ₃ (smallSingularChainInclusion (TopCat.twoOpenCover U' V')) = CategoryTheory.CategoryStruct.comp (smallSingularChainInclusion (TopCat.twoOpenCover U V)) (integralSingularChainMap f)
```

The last component of the natural map of short complexes agrees, after
cover-small inclusion, with the ordinary singular chain map induced by `f`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L709) (retained native site: line 708).

### AlgebraicTopology.twoOpenSmallShortComplexMap_comp_inclusion_assoc

```lean
theorem AlgebraicTopology.twoOpenSmallShortComplexMap_comp_inclusion_assoc {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') {Z : ChainComplex (ModuleCat ℤ) ℕ} (h : ((singularChainComplexFunctor (ModuleCat ℤ)).obj integerCoefficients).obj Y ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (twoOpenSmallShortComplexMap f U V U' V' hU hV).τ₃ (smallSingularChainInclusion (TopCat.twoOpenCover U' V'))) h = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (smallSingularChainInclusion (TopCat.twoOpenCover U V)) (integralSingularChainMap f)) h
```

The last component of the natural map of short complexes agrees, after
cover-small inclusion, with the ordinary singular chain map induced by `f`.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenSmallShortComplexMap_comp_inclusion`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L711) (retained native site: line 710).

### AlgebraicTopology.integralSingularHomology

```lean
noncomputable abbrev AlgebraicTopology.integralSingularHomology (X : TopCat) (n : ℕ) : ModuleCat ℤ
```

Integral singular homology in degree `n`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L740) (retained native site: line 739).

### AlgebraicTopology.smallSingularHomologyIso

```lean
noncomputable def AlgebraicTopology.smallSingularHomologyIso {X : TopCat} {ι : Type u_1} (W : ι → TopologicalSpace.Opens ↑X) (hW : TopologicalSpace.IsOpenCover W) (n : ℕ) : HomologicalComplex.homology (smallSingularChainComplex W) n ≅ integralSingularHomology X n
```

A cover-small homology group is canonically isomorphic to ordinary
singular homology when the family is an open cover.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L745) (retained native site: line 744).

### AlgebraicTopology.twoOpenSpaceHomologyIso

```lean
noncomputable def AlgebraicTopology.twoOpenSpaceHomologyIso {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₃ n ≅ integralSingularHomology X n
```

The last term of the two-open short complex has ordinary singular
homology, via the accepted cover-small quasi-isomorphism.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L754) (retained native site: line 753).

### AlgebraicTopology.twoOpenMiddleHomologyIso

```lean
noncomputable def AlgebraicTopology.twoOpenMiddleHomologyIso {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (n : ℕ) : HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₂ n ≅ integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj U) n ⊞ integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj V) n
```

The middle homology term is canonically the direct sum
`Hₙ(U;ℤ) ⊕ Hₙ(V;ℤ)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L764) (retained native site: line 763).

### AlgebraicTopology.twoOpenMayerVietorisδ

```lean
noncomputable def AlgebraicTopology.twoOpenMayerVietorisδ {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : integralSingularHomology X (n + 1) ⟶ HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n
```

The ordinary Mayer--Vietoris connecting morphism for the ordered cover
`(U,V)`, with the chain convention `c ↦ (c,-c)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L782) (retained native site: line 781).

### AlgebraicTopology.twoOpenMayerVietorisSwapSpaceMap

```lean
noncomputable def AlgebraicTopology.twoOpenMayerVietorisSwapSpaceMap {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ) : integralSingularHomology X n ⟶ integralSingularHomology X n
```

The ordinary homology self-map induced by reindexing the ordered cover
`(U,V)` as `(V,U)`.  It conjugates the cover-small swap map by the accepted
cover-small/ordinary homology isomorphisms.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L791) (retained native site: line 790).

### AlgebraicTopology.twoOpenMayerVietorisSwapSpaceMap_eq_id

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisSwapSpaceMap_eq_id {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ) : twoOpenMayerVietorisSwapSpaceMap U V hUV hVU n = CategoryTheory.CategoryStruct.id (integralSingularHomology X n)
```

Reindexing the two-member cover induces the identity on ordinary singular
homology of the ambient space.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L801) (retained native site: line 800).

### AlgebraicTopology.twoOpenMayerVietorisδ_swap

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisδ_swap {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ) : CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisδ U V hUV n) (HomologicalComplex.homologyMap (twoOpenIntersectionSwapChainIso U V).hom n) = -CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisSwapSpaceMap U V hUV hVU (n + 1)) (twoOpenMayerVietorisδ V U hVU n)
```

Swapping the ordered cover changes the ordinary Mayer--Vietoris
connecting morphism by `-1`, after the sign-free transport of the intersection
term and the canonical cover reindexing on the space term.  Thus the sign from
the chain convention `c ↦ (c,-c)` remains visible over `ℤ`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L821) (retained native site: line 820).

### AlgebraicTopology.twoOpenMayerVietorisδ_swap_eq_neg

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisδ_swap_eq_neg {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ) : CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisδ U V hUV n) (HomologicalComplex.homologyMap (twoOpenIntersectionSwapChainIso U V).hom n) = -twoOpenMayerVietorisδ V U hVU n
```

In the ordinary formulation, where reindexing the cover acts identically
on `H(X;ℤ)`, swapping `U` and `V` negates the connecting morphism.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L856) (retained native site: line 855).

### AlgebraicTopology.twoOpenMayerVietorisToSpace

```lean
noncomputable def AlgebraicTopology.twoOpenMayerVietorisToSpace {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₂ n ⟶ integralSingularHomology X n
```

The map from the middle homology term to ordinary homology of `X`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L868) (retained native site: line 867).

### AlgebraicTopology.twoOpenMayerVietorisFromIntersection

```lean
noncomputable def AlgebraicTopology.twoOpenMayerVietorisFromIntersection {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (n : ℕ) : HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n ⟶ integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj U) n ⊞ integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj V) n
```

The difference map on homology, displayed with target
`Hₙ(U) ⊕ Hₙ(V)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L876) (retained native site: line 875).

### AlgebraicTopology.twoOpenMayerVietorisFromBiprod

```lean
noncomputable def AlgebraicTopology.twoOpenMayerVietorisFromBiprod {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj U) n ⊞ integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj V) n ⟶ integralSingularHomology X n
```

The sum map on homology, displayed with source
`Hₙ(U) ⊕ Hₙ(V)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L886) (retained native site: line 885).

### AlgebraicTopology.twoOpenMayerVietorisδ_comp

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisδ_comp {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisδ U V hUV n) (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n) = 0
```

**API note (not a source docstring):** For the open cover U union V = X, the connecting map from H_(n+1)(X;Z) to the intersection homology followed by the short complex's ordered difference map on H_n is zero. This uses the fixed (c,-c) convention and is a consecutive-map identity, not an exactness assertion by itself.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L896) (retained native site: line 895).

### AlgebraicTopology.twoOpenMayerVietorisδ_comp_assoc

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisδ_comp_assoc {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) {Z : ModuleCat ℤ} (h : HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₂ n ⟶ Z) : CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisδ U V hUV n) (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n) h) = CategoryTheory.CategoryStruct.comp 0 h
```

**API note (not a source docstring):** Generated reassoc form of the connecting-then-difference zero identity, followed by an arbitrary morphism from the middle homology object to Z. The displayed right side is the zero morphism composed with that outgoing map.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenMayerVietorisδ_comp`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L896) (retained native site: line 895).

### AlgebraicTopology.twoOpenMayerVietoris_comp_toSpace

```lean
theorem AlgebraicTopology.twoOpenMayerVietoris_comp_toSpace {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n) (twoOpenMayerVietorisToSpace U V hUV n) = 0
```

**API note (not a source docstring):** For a two-open cover, the homology map of the ordered difference followed by the map from the middle homology object to ordinary H_n(X;Z) is zero. The middle object is still presented as homology of the chain biproduct.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L904) (retained native site: line 903).

### AlgebraicTopology.twoOpenMayerVietoris_comp_toSpace_assoc

```lean
theorem AlgebraicTopology.twoOpenMayerVietoris_comp_toSpace_assoc {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) {Z : ModuleCat ℤ} (h : integralSingularHomology X n ⟶ Z) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n) (CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisToSpace U V hUV n) h) = CategoryTheory.CategoryStruct.comp 0 h
```

**API note (not a source docstring):** Generated reassociated difference-then-space zero identity, after any integer-module morphism from H_n(X;Z). The open-cover hypothesis and degree n are unchanged.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenMayerVietoris_comp_toSpace`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L904) (retained native site: line 903).

### AlgebraicTopology.twoOpenMayerVietoris_toSpace_comp_δ

```lean
theorem AlgebraicTopology.twoOpenMayerVietoris_toSpace_comp_δ {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisToSpace U V hUV (n + 1)) (twoOpenMayerVietorisδ U V hUV n) = 0
```

**API note (not a source docstring):** For the open cover U union V = X, the map from the middle homology object in degree n+1 to ordinary H_(n+1)(X;Z), followed by the connecting morphism into intersection H_n, is zero. This records consecutive-map vanishing with the degree shift explicit.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L916) (retained native site: line 915).

### AlgebraicTopology.twoOpenMayerVietoris_toSpace_comp_δ_assoc

```lean
theorem AlgebraicTopology.twoOpenMayerVietoris_toSpace_comp_δ_assoc {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) {Z : ModuleCat ℤ} (h : HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n ⟶ Z) : CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisToSpace U V hUV (n + 1)) (CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisδ U V hUV n) h) = CategoryTheory.CategoryStruct.comp 0 h
```

**API note (not a source docstring):** Generated reassoc form of the space-then-connecting zero identity, followed by any morphism out of the intersection homology object in degree n. The right side retains the zero-map postcomposition expression.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenMayerVietoris_toSpace_comp_δ`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L916) (retained native site: line 915).

### AlgebraicTopology.twoOpenMayerVietorisIntersectionMap

```lean
noncomputable def AlgebraicTopology.twoOpenMayerVietorisIntersectionMap {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') (n : ℕ) : HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n ⟶ HomologicalComplex.homology (twoOpenSmallShortComplex U' V').X₁ n
```

The map on the intersection homology term induced by a continuous map
respecting ordered pairs.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L929) (retained native site: line 928).

### AlgebraicTopology.twoOpenMayerVietorisSpaceMap

```lean
noncomputable def AlgebraicTopology.twoOpenMayerVietorisSpaceMap {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) (n : ℕ) : integralSingularHomology X n ⟶ integralSingularHomology Y n
```

The ordinary-space homology map obtained naturally from the two-open
short complexes.  It is defined by conjugating the cover-small map by the
accepted cover-small/ordinary homology isomorphisms.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L939) (retained native site: line 938).

### AlgebraicTopology.twoOpenMayerVietorisSpaceMap_eq

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisSpaceMap_eq {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) (n : ℕ) : twoOpenMayerVietorisSpaceMap f U V U' V' hU hV hUV hU'V' n = HomologicalComplex.homologyMap (integralSingularChainMap f) n
```

The space map used in Mayer--Vietoris naturality is the ordinary singular
homology map induced by the underlying continuous map.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L952) (retained native site: line 951).

### AlgebraicTopology.twoOpenMayerVietorisδ_naturality

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisδ_naturality {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) (n : ℕ) : CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisδ U V hUV n) (twoOpenMayerVietorisIntersectionMap f U V U' V' hU hV n) = CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisSpaceMap f U V U' V' hU hV hUV hU'V' (n + 1)) (twoOpenMayerVietorisδ U' V' hU'V' n)
```

Naturality of the ordinary two-open Mayer--Vietoris connecting
morphism.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L978) (retained native site: line 977).

### AlgebraicTopology.twoOpenMayerVietorisδ_naturality_induced

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisδ_naturality_induced {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) (n : ℕ) : CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisδ U V hUV n) (twoOpenMayerVietorisIntersectionMap f U V U' V' hU hV n) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (integralSingularChainMap f) (n + 1)) (twoOpenMayerVietorisδ U' V' hU'V' n)
```

Naturality of the connecting morphism with the standard ordinary singular
homology map of the underlying continuous map displayed explicitly.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L995) (retained native site: line 994).

### AlgebraicTopology.twoOpenMayerVietoris_exact_intersection

```lean
theorem AlgebraicTopology.twoOpenMayerVietoris_exact_intersection {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : { X₁ := integralSingularHomology X (n + 1), X₂ := HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n, X₃ := HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₂ n, f := twoOpenMayerVietorisδ U V hUV n, g := HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n, zero := ⋯ }.Exact
```

Exactness at `Hₙ(U∩V)` in the ordinary Mayer--Vietoris sequence.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1010) (retained native site: line 1009).

### AlgebraicTopology.twoOpenMayerVietoris_exact_middle

```lean
theorem AlgebraicTopology.twoOpenMayerVietoris_exact_middle {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : { X₁ := HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n, X₂ := HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₂ n, X₃ := integralSingularHomology X n, f := HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n, g := twoOpenMayerVietorisToSpace U V hUV n, zero := ⋯ }.Exact
```

Exactness at the middle term in the ordinary Mayer--Vietoris sequence.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1043) (retained native site: line 1042).

### AlgebraicTopology.twoOpenMayerVietoris_exact_space

```lean
theorem AlgebraicTopology.twoOpenMayerVietoris_exact_space {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : { X₁ := HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₂ (n + 1), X₂ := integralSingularHomology X (n + 1), X₃ := HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n, f := twoOpenMayerVietorisToSpace U V hUV (n + 1), g := twoOpenMayerVietorisδ U V hUV n, zero := ⋯ }.Exact
```

Exactness at `Hₙ₊₁(X)` before the connecting morphism.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1080) (retained native site: line 1079).

### AlgebraicTopology.twoOpenMayerVietoris_exact_at_intersection

```lean
theorem AlgebraicTopology.twoOpenMayerVietoris_exact_at_intersection {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : { X₁ := integralSingularHomology X (n + 1), X₂ := HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n, X₃ := integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj U) n ⊞ integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj V) n, f := twoOpenMayerVietorisδ U V hUV n, g := twoOpenMayerVietorisFromIntersection U V n, zero := ⋯ }.Exact
```

Exactness at `Hₙ(U∩V)` with the middle term displayed as
`Hₙ(U) ⊕ Hₙ(V)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1118) (retained native site: line 1117).

### AlgebraicTopology.twoOpenMayerVietoris_exact_at_biprod

```lean
theorem AlgebraicTopology.twoOpenMayerVietoris_exact_at_biprod {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : { X₁ := HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n, X₂ := integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj U) n ⊞ integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj V) n, X₃ := integralSingularHomology X n, f := twoOpenMayerVietorisFromIntersection U V n, g := twoOpenMayerVietorisFromBiprod U V hUV n, zero := ⋯ }.Exact
```

Exactness at `Hₙ(U) ⊕ Hₙ(V)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1151) (retained native site: line 1150).

### AlgebraicTopology.twoOpenMayerVietoris_exact_at_space

```lean
theorem AlgebraicTopology.twoOpenMayerVietoris_exact_at_space {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) : { X₁ := integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj U) (n + 1) ⊞ integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj V) (n + 1), X₂ := integralSingularHomology X (n + 1), X₃ := HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n, f := twoOpenMayerVietorisFromBiprod U V hUV (n + 1), g := twoOpenMayerVietorisδ U V hUV n, zero := ⋯ }.Exact
```

Exactness at `Hₙ₊₁(X)` with the preceding term displayed as
`Hₙ₊₁(U) ⊕ Hₙ₊₁(V)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1181) (retained native site: line 1180).

### AlgebraicTopology.twoOpenSmallShortComplex_f_fst

```lean
theorem AlgebraicTopology.twoOpenSmallShortComplex_f_fst {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : CategoryTheory.CategoryStruct.comp (twoOpenSmallShortComplex U V).f CategoryTheory.Limits.biprod.fst = integralSingularChainMap (twoOpenIntersectionToLeft U V)
```

The left projection of the first map in the two-open small short complex
is induced by the literal inclusion `U ∩ V → U`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1239) (retained native site: line 1238).

### AlgebraicTopology.twoOpenSmallShortComplex_f_snd

```lean
theorem AlgebraicTopology.twoOpenSmallShortComplex_f_snd {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : CategoryTheory.CategoryStruct.comp (twoOpenSmallShortComplex U V).f CategoryTheory.Limits.biprod.snd = -integralSingularChainMap (twoOpenIntersectionToRight U V)
```

The right projection of the first map in the two-open small short complex
is minus the map induced by the literal inclusion `U ∩ V → V`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1277) (retained native site: line 1276).

### AlgebraicTopology.twoOpenSmallShortComplex_f_eq_difference

```lean
theorem AlgebraicTopology.twoOpenSmallShortComplex_f_eq_difference {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : (twoOpenSmallShortComplex U V).f = twoOpenDifferenceChainMap U V
```

The first map of the two-open small short complex is the accepted ordered
difference map `c ↦ (c,-c)`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1317) (retained native site: line 1316).

### AlgebraicTopology.twoOpenIntersectionHomologyIso

```lean
noncomputable def AlgebraicTopology.twoOpenIntersectionHomologyIso {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (n : ℕ) : integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V)) n ≅ HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ n
```

The homology of the literal open intersection is canonically the first
homology object of the accepted two-open small short complex.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1328) (retained native site: line 1327).

### AlgebraicTopology.twoOpenMayerVietorisFromIntersection_fst

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisFromIntersection_fst {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (n : ℕ) : CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisFromIntersection U V n) CategoryTheory.Limits.biprod.fst = CategoryTheory.CategoryStruct.comp (twoOpenIntersectionHomologyIso U V n).inv (HomologicalComplex.homologyMap (integralSingularChainMap (twoOpenIntersectionToLeft U V)) n)
```

The left projection of the displayed ordinary difference map is induced
by `U ∩ V → U`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1336) (retained native site: line 1335).

### AlgebraicTopology.twoOpenMayerVietorisFromIntersection_snd

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisFromIntersection_snd {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (n : ℕ) : CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisFromIntersection U V n) CategoryTheory.Limits.biprod.snd = CategoryTheory.CategoryStruct.comp (twoOpenIntersectionHomologyIso U V n).inv (-HomologicalComplex.homologyMap (integralSingularChainMap (twoOpenIntersectionToRight U V)) n)
```

The right projection of the displayed ordinary difference map is minus
the map induced by `U ∩ V → V`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1352) (retained native site: line 1350).

### AlgebraicTopology.integralSingularChainMap_twoOpenIntersectionMap

```lean
theorem AlgebraicTopology.integralSingularChainMap_twoOpenIntersectionMap {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') : integralSingularChainMap (twoOpenIntersectionMap f U V U' V' hU hV) = (twoOpenSmallShortComplexMap f U V U' V' hU hV).τ₁
```

The first component of the accepted map of two-open small short complexes
is the chain map induced by the literal map of open intersections.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1384) (retained native site: line 1381).

### AlgebraicTopology.twoOpenMayerVietorisIntersectionMap_eq

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisIntersectionMap_eq {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') (n : ℕ) : twoOpenMayerVietorisIntersectionMap f U V U' V' hU hV n = HomologicalComplex.homologyMap (integralSingularChainMap (twoOpenIntersectionMap f U V U' V' hU hV)) n
```

The accepted map on the intersection homology term is the ordinary
homology map induced by the literal open-intersection map.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1416) (retained native site: line 1413).

### AlgebraicTopology.twoOpenIntersectionHomologyIso_naturality

```lean
theorem AlgebraicTopology.twoOpenIntersectionHomologyIso_naturality {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') (n : ℕ) : CategoryTheory.CategoryStruct.comp (twoOpenIntersectionHomologyIso U V n).hom (twoOpenMayerVietorisIntersectionMap f U V U' V' hU hV n) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (integralSingularChainMap (twoOpenIntersectionMap f U V U' V' hU hV)) n) (twoOpenIntersectionHomologyIso U' V' n).hom
```

Naturality of the literal-intersection identification.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1429) (retained native site: line 1426).

### AlgebraicTopology.twoOpenIntersectionHomologyIso_naturality_assoc

```lean
theorem AlgebraicTopology.twoOpenIntersectionHomologyIso_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') (n : ℕ) {Z : ModuleCat ℤ} (h : HomologicalComplex.homology (twoOpenSmallShortComplex U' V').X₁ n ⟶ Z) : CategoryTheory.CategoryStruct.comp (twoOpenIntersectionHomologyIso U V n).hom (CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisIntersectionMap f U V U' V' hU hV n) h) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (integralSingularChainMap (twoOpenIntersectionMap f U V U' V' hU hV)) n) (CategoryTheory.CategoryStruct.comp (twoOpenIntersectionHomologyIso U' V' n).hom h)
```

Naturality of the literal-intersection identification.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenIntersectionHomologyIso_naturality`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1430) (retained native site: line 1427).

### AlgebraicTopology.twoOpenIntersectionSwapMap

```lean
def AlgebraicTopology.twoOpenIntersectionSwapMap {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : (TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V) ⟶ (TopologicalSpace.Opens.toTopCat X).obj (V ⊓ U)
```

The sign-free map from the literal intersection `U ∩ V` to the literal
intersection `V ∩ U`.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1444) (retained native site: line 1441).

### AlgebraicTopology.integralSingularChainMap_twoOpenIntersectionSwapMap

```lean
theorem AlgebraicTopology.integralSingularChainMap_twoOpenIntersectionSwapMap {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : integralSingularChainMap (twoOpenIntersectionSwapMap U V) = (twoOpenIntersectionSwapChainIso U V).hom
```

The chain map induced by the sign-free literal-intersection swap is the
accepted intersection swap chain isomorphism.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1467) (retained native site: line 1464).

### AlgebraicTopology.integralSingularHomologyMap_twoOpenIntersectionSwapMap

```lean
theorem AlgebraicTopology.integralSingularHomologyMap_twoOpenIntersectionSwapMap {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (n : ℕ) : HomologicalComplex.homologyMap (integralSingularChainMap (twoOpenIntersectionSwapMap U V)) n = HomologicalComplex.homologyMap (twoOpenIntersectionSwapChainIso U V).hom n
```

On homology, the map induced by the sign-free literal-intersection swap is
the accepted swap map.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1538) (retained native site: line 1535).

### AlgebraicTopology.twoOpenIntersectionHomologyIso_swap

```lean
theorem AlgebraicTopology.twoOpenIntersectionHomologyIso_swap {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (n : ℕ) : CategoryTheory.CategoryStruct.comp (twoOpenIntersectionHomologyIso U V n).hom (HomologicalComplex.homologyMap (twoOpenIntersectionSwapChainIso U V).hom n) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (integralSingularChainMap (twoOpenIntersectionSwapMap U V)) n) (twoOpenIntersectionHomologyIso V U n).hom
```

The literal-intersection identification intertwines the actual sign-free
swap map with the accepted swap map.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1549) (retained native site: line 1546).

### AlgebraicTopology.twoOpenIntersectionHomologyIso_swap_assoc

```lean
theorem AlgebraicTopology.twoOpenIntersectionHomologyIso_swap_assoc {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (n : ℕ) {Z : ModuleCat ℤ} (h : HomologicalComplex.homology (twoOpenSmallShortComplex V U).X₁ n ⟶ Z) : CategoryTheory.CategoryStruct.comp (twoOpenIntersectionHomologyIso U V n).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (twoOpenIntersectionSwapChainIso U V).hom n) h) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (integralSingularChainMap (twoOpenIntersectionSwapMap U V)) n) (CategoryTheory.CategoryStruct.comp (twoOpenIntersectionHomologyIso V U n).hom h)
```

The literal-intersection identification intertwines the actual sign-free
swap map with the accepted swap map.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenIntersectionHomologyIso_swap`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1551) (retained native site: line 1548).

### AlgebraicTopology.twoOpenIntersectionSwapMap_comp

```lean
theorem AlgebraicTopology.twoOpenIntersectionSwapMap_comp {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : CategoryTheory.CategoryStruct.comp (twoOpenIntersectionSwapMap U V) (twoOpenIntersectionSwapMap V U) = CategoryTheory.CategoryStruct.id ((TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V))
```

Swapping the literal intersection twice is the identity.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1564) (retained native site: line 1561).

### AlgebraicTopology.integralSingularHomologyMap_eq_neg_id_of_twoOpen_swap

```lean
theorem AlgebraicTopology.integralSingularHomologyMap_eq_neg_id_of_twoOpen_swap {X : TopCat} (f : X ⟶ X) (U V : TopologicalSpace.Opens ↑X) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑V) (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑U) (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) (n : ℕ) (hIntersection : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (integralSingularChainMap (twoOpenIntersectionMap f V U U V hV hU)) n) (HomologicalComplex.homologyMap (integralSingularChainMap (twoOpenIntersectionSwapMap U V)) n) = CategoryTheory.CategoryStruct.id (HomologicalComplex.homology (integralSingularChains ((TopologicalSpace.Opens.toTopCat X).obj (V ⊓ U))) n)) [CategoryTheory.Mono (twoOpenMayerVietorisδ U V hUV n)] : HomologicalComplex.homologyMap (integralSingularChainMap f) (n + 1) = -CategoryTheory.CategoryStruct.id (HomologicalComplex.homology (integralSingularChains X) (n + 1))
```

A self-map which exchanges an ordered two-open cover and whose literal
intersection map agrees on homology with the sign-free swap acts by `-1` on
the next ordinary integral homology group, provided the displayed connecting
morphism is monic.  The minus sign comes from the ordered Mayer--Vietoris
convention; it is not part of the intersection transport hypothesis.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1572) (retained native site: line 1569).

### AlgebraicTopology.twoOpenMayerVietorisδ_isIso_of_isZero_outer

```lean
theorem AlgebraicTopology.twoOpenMayerVietorisδ_isIso_of_isZero_outer {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (n : ℕ) (hPrev : CategoryTheory.Limits.IsZero (integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj U) (n + 1) ⊞ integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj V) (n + 1))) (hNext : CategoryTheory.Limits.IsZero (integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj U) n ⊞ integralSingularHomology ((TopologicalSpace.Opens.toTopCat X).obj V) n)) : CategoryTheory.IsIso (twoOpenMayerVietorisδ U V hUV n)
```

If the two outer biproduct terms vanish, the ordinary two-open
Mayer--Vietoris connecting morphism is an isomorphism.

[Source](../SphereTopology/Homology/Singular/MayerVietoris.lean#L1628) (retained native site: line 1625).

## SphereTopology.Homology.Singular.Reduced

Scope: mathematical library leaf.

### AlgebraicTopology.integralSingularHomologyFunctor

```lean
noncomputable abbrev AlgebraicTopology.integralSingularHomologyFunctor (n : ℕ) : CategoryTheory.Functor TopCat (ModuleCat ℤ)
```

Integral singular homology, functorially in the topological space. Its
objects are the accepted `integralSingularHomology` groups.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L46) (retained native site: line 45).

### AlgebraicTopology.integralSingularHomologyFunctor_map

```lean
theorem AlgebraicTopology.integralSingularHomologyFunctor_map {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) : (integralSingularHomologyFunctor n).map f = HomologicalComplex.homologyMap (integralSingularChainMap f) n
```

**API note (not a source docstring):** The map part of the degree-n integral singular homology functor is the homology map induced by the integer singular chain map. This identifies the functor presentation with the chain-complex presentation for any continuous map and any nonnegative degree.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L51) (retained native site: line 50).

### TopCat.singularHomologyIntegerCoefficients

```lean
abbrev TopCat.singularHomologyIntegerCoefficients : ModuleCat ℤ
```

The integer coefficient object, lifted to the universe of the spaces under
consideration. This is the accepted coefficient bridge used by the ordinary
integral singular-chain and Mayer--Vietoris APIs.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L65) (retained native site: line 64).

### TopCat.integerSingularHomologyFunctor

```lean
noncomputable abbrev TopCat.integerSingularHomologyFunctor (n : ℕ) : CategoryTheory.Functor TopCat (ModuleCat ℤ)
```

Compatibility name for the accepted integral singular homology functor.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L71) (retained native site: line 70).

### SSet.homologyZeroPoint

```lean
noncomputable def SSet.homologyZeroPoint {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] [CategoryTheory.CategoryWithHomology C] (X : SSet) (R : C) (x : X.obj (Opposite.op { len := 0 })) : R ⟶ X.homology R 0
```

The degree-zero homology class represented by a vertex of a simplicial set.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L85) (retained native site: line 84).

### SSet.homologyZeroPoint_homology₀Iso

```lean
theorem SSet.homologyZeroPoint_homology₀Iso {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] [CategoryTheory.CategoryWithHomology C] (X : SSet) (R : C) (x : X.obj (Opposite.op { len := 0 })) : CategoryTheory.CategoryStruct.comp (X.homologyZeroPoint R x) (X.homology₀Iso R).hom = CategoryTheory.Limits.Sigma.ι (fun (x : X.π₀) => R) (π₀.mk x)
```

**API note (not a source docstring):** Under the coproduct description of zeroth simplicial homology, the class map of a zero-simplex is the coproduct inclusion of its connected component. The coefficient object is arbitrary in the category with coproducts, preadditive structure and homology appearing in the signature; this statement is not restricted to integer coefficients.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L91) (retained native site: line 90).

### SSet.homologyZeroPoint_homology₀Iso_assoc

```lean
theorem SSet.homologyZeroPoint_homology₀Iso_assoc {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] [CategoryTheory.CategoryWithHomology C] (X : SSet) (R : C) (x : X.obj (Opposite.op { len := 0 })) {Z : C} (h : (∐ fun (x : X.π₀) => R) ⟶ Z) : CategoryTheory.CategoryStruct.comp (X.homologyZeroPoint R x) (CategoryTheory.CategoryStruct.comp (X.homology₀Iso R).hom h) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.ι (fun (x : X.π₀) => R) (π₀.mk x)) h
```

**API note (not a source docstring):** Generated by the reassoc attribute on homologyZeroPoint_homology₀Iso: the same component-inclusion formula after an arbitrary morphism from the component coproduct to Z. Both the arbitrary coefficient category and the added postcomposition are part of this statement.

Generated `reassoc` declaration from `SSet.homologyZeroPoint_homology₀Iso`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L91) (retained native site: line 90).

### SSet.homologyZeroPoint_augmentation

```lean
theorem SSet.homologyZeroPoint_augmentation {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] [CategoryTheory.CategoryWithHomology C] (X : SSet) (R : C) (x : X.obj (Opposite.op { len := 0 })) : CategoryTheory.CategoryStruct.comp (X.homologyZeroPoint R x) (X.homology₀ε R) = CategoryTheory.CategoryStruct.id R
```

**API note (not a source docstring):** The class map of a zero-simplex followed by the total augmentation is the identity of the coefficient object R. The supplied zero-simplex, rather than a global nonemptiness instance, supplies the point; the ambient category is as general as the displayed assumptions.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L99) (retained native site: line 98).

### SSet.homologyZeroPoint_augmentation_assoc

```lean
theorem SSet.homologyZeroPoint_augmentation_assoc {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] [CategoryTheory.CategoryWithHomology C] (X : SSet) (R : C) (x : X.obj (Opposite.op { len := 0 })) {Z : C} (h : R ⟶ Z) : CategoryTheory.CategoryStruct.comp (X.homologyZeroPoint R x) (CategoryTheory.CategoryStruct.comp (X.homology₀ε R) h) = h
```

**API note (not a source docstring):** Generated reassociated augmentation identity: composing the point class, augmentation and any morphism h from R to Z returns h. This is the postcomposition form of homologyZeroPoint_augmentation, with the same categorical hypotheses.

Generated `reassoc` declaration from `SSet.homologyZeroPoint_augmentation`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L99) (retained native site: line 98).

### SSet.homologyZeroPoint_naturality

```lean
theorem SSet.homologyZeroPoint_naturality {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] [CategoryTheory.CategoryWithHomology C] {X Y : SSet} (f : X ⟶ Y) (R : C) (x : X.obj (Opposite.op { len := 0 })) : CategoryTheory.CategoryStruct.comp (X.homologyZeroPoint R x) (SSet.homologyMap f R 0) = Y.homologyZeroPoint R ((CategoryTheory.ConcreteCategory.hom (f.app (Opposite.op { len := 0 }))) x)
```

**API note (not a source docstring):** A simplicial map sends the zeroth-homology class map of x to the class map of its image zero-simplex. This naturality statement uses the arbitrary coefficient object R and the displayed categorical homology assumptions.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L106) (retained native site: line 105).

### SSet.homologyZeroPoint_naturality_assoc

```lean
theorem SSet.homologyZeroPoint_naturality_assoc {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] [CategoryTheory.CategoryWithHomology C] {X Y : SSet} (f : X ⟶ Y) (R : C) (x : X.obj (Opposite.op { len := 0 })) {Z : C} (h : Y.homology R 0 ⟶ Z) : CategoryTheory.CategoryStruct.comp (X.homologyZeroPoint R x) (CategoryTheory.CategoryStruct.comp (SSet.homologyMap f R 0) h) = CategoryTheory.CategoryStruct.comp (Y.homologyZeroPoint R ((CategoryTheory.ConcreteCategory.hom (f.app (Opposite.op { len := 0 }))) x)) h
```

**API note (not a source docstring):** Generated reassoc form of homologyZeroPoint_naturality: the point-class naturality square still agrees after any morphism from the target zeroth homology to Z. The extra codomain and postcomposition are explicit in the generated signature.

Generated `reassoc` declaration from `SSet.homologyZeroPoint_naturality`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L106) (retained native site: line 105).

### TopCat.singularHomologyZeroPoint

```lean
noncomputable def TopCat.singularHomologyZeroPoint (X : TopCat) (x : ↑X) : singularHomologyIntegerCoefficients ⟶ (AlgebraicTopology.integralSingularHomologyFunctor 0).obj X
```

The degree-zero homology class represented by a point.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L124) (retained native site: line 123).

### TopCat.singularHomologyZeroPoint_homology₀Iso

```lean
theorem TopCat.singularHomologyZeroPoint_homology₀Iso (X : TopCat) (x : ↑X) : CategoryTheory.CategoryStruct.comp (X.singularHomologyZeroPoint x) (X.singularHomology₀Iso singularHomologyIntegerCoefficients).hom = CategoryTheory.Limits.Sigma.ι (fun (x : ZerothHomotopy ↑X) => singularHomologyIntegerCoefficients) (ZerothHomotopy.mk x)
```

**API note (not a source docstring):** The integral H0 class map of a point becomes the inclusion of that point's path component in the coproduct description of singular H0. Coefficients are the universe-lifted integer module used by this file.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L132) (retained native site: line 131).

### TopCat.singularHomologyZeroPoint_homology₀Iso_assoc

```lean
theorem TopCat.singularHomologyZeroPoint_homology₀Iso_assoc (X : TopCat) (x : ↑X) {Z : ModuleCat ℤ} (h : (∐ fun (x : ZerothHomotopy ↑X) => singularHomologyIntegerCoefficients) ⟶ Z) : CategoryTheory.CategoryStruct.comp (X.singularHomologyZeroPoint x) (CategoryTheory.CategoryStruct.comp (X.singularHomology₀Iso singularHomologyIntegerCoefficients).hom h) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.ι (fun (x : ZerothHomotopy ↑X) => singularHomologyIntegerCoefficients) (ZerothHomotopy.mk x)) h
```

**API note (not a source docstring):** Generated reassociated point-component formula: after the H0 coproduct isomorphism and an arbitrary outgoing morphism, the point class equals the corresponding component inclusion followed by that morphism.

Generated `reassoc` declaration from `TopCat.singularHomologyZeroPoint_homology₀Iso`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L132) (retained native site: line 131).

### TopCat.singularHomologyZeroPoint_augmentation

```lean
theorem TopCat.singularHomologyZeroPoint_augmentation (X : TopCat) (x : ↑X) : CategoryTheory.CategoryStruct.comp (X.singularHomologyZeroPoint x) (X.singularHomology₀ε singularHomologyIntegerCoefficients) = CategoryTheory.CategoryStruct.id singularHomologyIntegerCoefficients
```

**API note (not a source docstring):** A point class followed by the integral H0 augmentation is the identity on the lifted integer coefficient module. The theorem takes an actual point x and makes no separate path-connectedness assumption.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L147) (retained native site: line 146).

### TopCat.singularHomologyZeroPoint_augmentation_assoc

```lean
theorem TopCat.singularHomologyZeroPoint_augmentation_assoc (X : TopCat) (x : ↑X) {Z : ModuleCat ℤ} (h : singularHomologyIntegerCoefficients ⟶ Z) : CategoryTheory.CategoryStruct.comp (X.singularHomologyZeroPoint x) (CategoryTheory.CategoryStruct.comp (X.singularHomology₀ε singularHomologyIntegerCoefficients) h) = h
```

**API note (not a source docstring):** Generated reassoc form of the point-augmentation identity: following the point class and augmentation by any coefficient-module morphism h returns h.

Generated `reassoc` declaration from `TopCat.singularHomologyZeroPoint_augmentation`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L147) (retained native site: line 146).

### TopCat.singularHomologyZeroPoint_naturality

```lean
theorem TopCat.singularHomologyZeroPoint_naturality {X Y : TopCat} (f : X ⟶ Y) (x : ↑X) : CategoryTheory.CategoryStruct.comp (X.singularHomologyZeroPoint x) ((AlgebraicTopology.integralSingularHomologyFunctor 0).map f) = Y.singularHomologyZeroPoint ((CategoryTheory.ConcreteCategory.hom f) x)
```

**API note (not a source docstring):** The ordinary integral H0 map of a continuous map sends the class map of x to the class map of f(x). No connectedness or nonemptiness beyond the supplied point is assumed.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L158) (retained native site: line 157).

### TopCat.singularHomologyZeroPoint_naturality_assoc

```lean
theorem TopCat.singularHomologyZeroPoint_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) (x : ↑X) {Z : ModuleCat ℤ} (h : (AlgebraicTopology.integralSingularHomologyFunctor 0).obj Y ⟶ Z) : CategoryTheory.CategoryStruct.comp (X.singularHomologyZeroPoint x) (CategoryTheory.CategoryStruct.comp ((AlgebraicTopology.integralSingularHomologyFunctor 0).map f) h) = CategoryTheory.CategoryStruct.comp (Y.singularHomologyZeroPoint ((CategoryTheory.ConcreteCategory.hom f) x)) h
```

**API note (not a source docstring):** Generated postcomposition form of singularHomologyZeroPoint_naturality, with an arbitrary morphism from the target space's ordinary integral H0 to Z.

Generated `reassoc` declaration from `TopCat.singularHomologyZeroPoint_naturality`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L158) (retained native site: line 157).

### TopCat.singularHomologyZeroAugmentation_naturality

```lean
theorem TopCat.singularHomologyZeroAugmentation_naturality {X Y : TopCat} (f : X ⟶ Y) : CategoryTheory.CategoryStruct.comp ((AlgebraicTopology.integralSingularHomologyFunctor 0).map f) (Y.singularHomology₀ε singularHomologyIntegerCoefficients) = X.singularHomology₀ε singularHomologyIntegerCoefficients
```

The total degree-zero augmentation commutes with every continuous map.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L169) (retained native site: line 168).

### TopCat.singularHomologyZeroAugmentation_naturality_assoc

```lean
theorem TopCat.singularHomologyZeroAugmentation_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) {Z : ModuleCat ℤ} (h : singularHomologyIntegerCoefficients ⟶ Z) : CategoryTheory.CategoryStruct.comp ((AlgebraicTopology.integralSingularHomologyFunctor 0).map f) (CategoryTheory.CategoryStruct.comp (Y.singularHomology₀ε singularHomologyIntegerCoefficients) h) = CategoryTheory.CategoryStruct.comp (X.singularHomology₀ε singularHomologyIntegerCoefficients) h
```

The total degree-zero augmentation commutes with every continuous map.

Generated `reassoc` declaration from `TopCat.singularHomologyZeroAugmentation_naturality`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L170) (retained native site: line 169).

### TopCat.reducedSingularHomologyZero

```lean
noncomputable abbrev TopCat.reducedSingularHomologyZero (X : TopCat) : ModuleCat ℤ
```

Reduced integer singular homology in degree zero.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L187) (retained native site: line 186).

### TopCat.reducedSingularHomologyZeroι

```lean
noncomputable abbrev TopCat.reducedSingularHomologyZeroι (X : TopCat) : X.reducedSingularHomologyZero ⟶ (AlgebraicTopology.integralSingularHomologyFunctor 0).obj X
```

The canonical inclusion of reduced degree-zero homology into ordinary
degree-zero homology.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L191) (retained native site: line 190).

### TopCat.reducedSingularHomologyZeroMap

```lean
noncomputable def TopCat.reducedSingularHomologyZeroMap {X Y : TopCat} (f : X ⟶ Y) : X.reducedSingularHomologyZero ⟶ Y.reducedSingularHomologyZero
```

The map on reduced degree-zero homology induced by a continuous map.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L197) (retained native site: line 196).

### TopCat.reducedSingularHomologyZeroMap_ι

```lean
theorem TopCat.reducedSingularHomologyZeroMap_ι {X Y : TopCat} (f : X ⟶ Y) : CategoryTheory.CategoryStruct.comp (reducedSingularHomologyZeroMap f) Y.reducedSingularHomologyZeroι = CategoryTheory.CategoryStruct.comp X.reducedSingularHomologyZeroι ((AlgebraicTopology.integralSingularHomologyFunctor 0).map f)
```

**API note (not a source docstring):** The reduced H0 map, defined on the total-augmentation kernel, commutes with its kernel inclusion into ordinary integral H0. This holds for every continuous map, without a nonempty-space hypothesis.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L209) (retained native site: line 208).

### TopCat.reducedSingularHomologyZeroMap_ι_assoc

```lean
theorem TopCat.reducedSingularHomologyZeroMap_ι_assoc {X Y : TopCat} (f : X ⟶ Y) {Z : ModuleCat ℤ} (h : (AlgebraicTopology.integralSingularHomologyFunctor 0).obj Y ⟶ Z) : CategoryTheory.CategoryStruct.comp (reducedSingularHomologyZeroMap f) (CategoryTheory.CategoryStruct.comp Y.reducedSingularHomologyZeroι h) = CategoryTheory.CategoryStruct.comp X.reducedSingularHomologyZeroι (CategoryTheory.CategoryStruct.comp ((AlgebraicTopology.integralSingularHomologyFunctor 0).map f) h)
```

**API note (not a source docstring):** Generated reassoc form of the reduced-H0 kernel-inclusion naturality equation, after any morphism from the target's ordinary H0 to Z. This adds postcomposition rather than an extra topological assumption.

Generated `reassoc` declaration from `TopCat.reducedSingularHomologyZeroMap_ι`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L209) (retained native site: line 208).

### TopCat.reducedSingularHomologyZeroMap_id

```lean
theorem TopCat.reducedSingularHomologyZeroMap_id (X : TopCat) : reducedSingularHomologyZeroMap (CategoryTheory.CategoryStruct.id X) = CategoryTheory.CategoryStruct.id X.reducedSingularHomologyZero
```

**API note (not a source docstring):** The map induced on the augmentation kernel by the identity continuous map is the identity on reduced H0, for an arbitrary space.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L215) (retained native site: line 214).

### TopCat.reducedSingularHomologyZeroMap_comp

```lean
theorem TopCat.reducedSingularHomologyZeroMap_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) : reducedSingularHomologyZeroMap (CategoryTheory.CategoryStruct.comp f g) = CategoryTheory.CategoryStruct.comp (reducedSingularHomologyZeroMap f) (reducedSingularHomologyZeroMap g)
```

**API note (not a source docstring):** The reduced H0 map of a composite continuous map is the composite of the reduced H0 maps, in categorical composition order. No connectedness hypothesis is needed.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L221) (retained native site: line 220).

### TopCat.reducedSingularHomologyZeroMap_comp_assoc

```lean
theorem TopCat.reducedSingularHomologyZeroMap_comp_assoc {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) {Z✝ : ModuleCat ℤ} (h : Z.reducedSingularHomologyZero ⟶ Z✝) : CategoryTheory.CategoryStruct.comp (reducedSingularHomologyZeroMap (CategoryTheory.CategoryStruct.comp f g)) h = CategoryTheory.CategoryStruct.comp (reducedSingularHomologyZeroMap f) (CategoryTheory.CategoryStruct.comp (reducedSingularHomologyZeroMap g) h)
```

**API note (not a source docstring):** Generated reassociated composition law: the reduced H0 map of f followed by g, then any outgoing morphism h, equals the successive reduced maps followed by h.

Generated `reassoc` declaration from `TopCat.reducedSingularHomologyZeroMap_comp`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L221) (retained native site: line 220).

### TopCat.reducedSingularHomologyZeroFunctor

```lean
noncomputable def TopCat.reducedSingularHomologyZeroFunctor : CategoryTheory.Functor TopCat (ModuleCat ℤ)
```

Reduced degree-zero singular homology is a functor.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L229) (retained native site: line 228).

### TopCat.reducedSingularHomologyZeroFunctor_map

```lean
theorem TopCat.reducedSingularHomologyZeroFunctor_map {X✝ Y✝ : TopCat} (f : X✝ ⟶ Y✝) : reducedSingularHomologyZeroFunctor.map f = reducedSingularHomologyZeroMap f
```

**API note (not a source docstring):** Generated by the simps attribute on reducedSingularHomologyZeroFunctor. It identifies the functor's map on a continuous map with the explicitly constructed augmentation-kernel map reducedSingularHomologyZeroMap.

Generated `simps` declaration from `TopCat.reducedSingularHomologyZeroFunctor`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L230) (retained native site: line 229).

### TopCat.reducedSingularHomologyZeroFunctor_obj

```lean
theorem TopCat.reducedSingularHomologyZeroFunctor_obj (X : TopCat) : reducedSingularHomologyZeroFunctor.obj X = X.reducedSingularHomologyZero
```

**API note (not a source docstring):** Generated by the simps attribute on reducedSingularHomologyZeroFunctor. Its object at X is precisely the total-augmentation kernel reducedSingularHomologyZero X, including for the empty space.

Generated `simps` declaration from `TopCat.reducedSingularHomologyZeroFunctor`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L230) (retained native site: line 229).

### TopCat.reducedSingularHomologyFunctor

```lean
noncomputable def TopCat.reducedSingularHomologyFunctor (n : ℕ) : CategoryTheory.Functor TopCat (ModuleCat ℤ)
```

Nonnegative reduced singular homology.  Degree zero is the augmentation
kernel, and positive degrees are ordinary integer singular homology.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L238) (retained native site: line 237).

### TopCat.reducedSingularHomology

```lean
noncomputable abbrev TopCat.reducedSingularHomology (X : TopCat) (n : ℕ) : ModuleCat ℤ
```

The object-level nonnegative reduced singular homology group.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L246) (retained native site: line 245).

### TopCat.reducedSingularHomologyMap

```lean
noncomputable abbrev TopCat.reducedSingularHomologyMap {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) : X.reducedSingularHomology n ⟶ Y.reducedSingularHomology n
```

The induced map on nonnegative reduced singular homology.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L251) (retained native site: line 250).

### TopCat.reducedSingularHomologyZeroIso

```lean
noncomputable def TopCat.reducedSingularHomologyZeroIso (X : TopCat) : X.reducedSingularHomology 0 ≅ X.reducedSingularHomologyZero
```

In degree zero, the nonnegative interface is the augmentation kernel.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L257) (retained native site: line 256).

### TopCat.reducedSingularHomologyZeroInclusion

```lean
noncomputable def TopCat.reducedSingularHomologyZeroInclusion (X : TopCat) : X.reducedSingularHomology 0 ⟶ (AlgebraicTopology.integralSingularHomologyFunctor 0).obj X
```

The canonical inclusion from the degree-zero nonnegative reduced-homology
interface into ordinary degree-zero integral singular homology.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L262) (retained native site: line 261).

### TopCat.reducedSingularHomologyZeroInclusion_mono

```lean
instance TopCat.reducedSingularHomologyZeroInclusion_mono (X : TopCat) : CategoryTheory.Mono X.reducedSingularHomologyZeroInclusion
```

**API note (not a source docstring):** The degree-zero inclusion from the file's reduced-homology convention to the ordinary integral H0 functor is a categorical monomorphism. This instance is inherited from the augmentation-kernel inclusion and needs no nonemptiness hypothesis.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L270) (retained native site: line 269).

### TopCat.reducedSingularHomologyZeroInclusion_naturality

```lean
theorem TopCat.reducedSingularHomologyZeroInclusion_naturality {X Y : TopCat} (f : X ⟶ Y) : CategoryTheory.CategoryStruct.comp (reducedSingularHomologyMap f 0) Y.reducedSingularHomologyZeroInclusion = CategoryTheory.CategoryStruct.comp X.reducedSingularHomologyZeroInclusion ((AlgebraicTopology.integralSingularHomologyFunctor 0).map f)
```

The degree-zero reduced inclusion is natural for continuous maps.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L275) (retained native site: line 274).

### TopCat.reducedSingularHomologyZeroInclusion_naturality_assoc

```lean
theorem TopCat.reducedSingularHomologyZeroInclusion_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) {Z : ModuleCat ℤ} (h : (AlgebraicTopology.integralSingularHomologyFunctor 0).obj Y ⟶ Z) : CategoryTheory.CategoryStruct.comp (reducedSingularHomologyMap f 0) (CategoryTheory.CategoryStruct.comp Y.reducedSingularHomologyZeroInclusion h) = CategoryTheory.CategoryStruct.comp X.reducedSingularHomologyZeroInclusion (CategoryTheory.CategoryStruct.comp ((AlgebraicTopology.integralSingularHomologyFunctor 0).map f) h)
```

The degree-zero reduced inclusion is natural for continuous maps.

Generated `reassoc` declaration from `TopCat.reducedSingularHomologyZeroInclusion_naturality`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L276) (retained native site: line 275).

### TopCat.reducedSingularHomologyZeroToOrdinary

```lean
noncomputable def TopCat.reducedSingularHomologyZeroToOrdinary (X : TopCat) : X.reducedSingularHomology 0 ⟶ AlgebraicTopology.integralSingularHomology X 0
```

The degree-zero reduced inclusion with its codomain displayed using the
ordinary integral singular-homology abbreviation.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L289) (retained native site: line 288).

### TopCat.reducedSingularHomologyZeroToOrdinary_mono

```lean
instance TopCat.reducedSingularHomologyZeroToOrdinary_mono (X : TopCat) : CategoryTheory.Mono X.reducedSingularHomologyZeroToOrdinary
```

**API note (not a source docstring):** The degree-zero reduced inclusion is a categorical monomorphism when its codomain is displayed using integralSingularHomology X 0. This is the same inclusion as reducedSingularHomologyZeroInclusion, with a definitionally equal presentation of ordinary homology.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L295) (retained native site: line 294).

### TopCat.reducedSingularHomologyZeroToOrdinary_naturality

```lean
theorem TopCat.reducedSingularHomologyZeroToOrdinary_naturality {X Y : TopCat} (f : X ⟶ Y) : CategoryTheory.CategoryStruct.comp (reducedSingularHomologyMap f 0) Y.reducedSingularHomologyZeroToOrdinary = CategoryTheory.CategoryStruct.comp X.reducedSingularHomologyZeroToOrdinary (HomologicalComplex.homologyMap (AlgebraicTopology.integralSingularChainMap f) 0)
```

Naturality of the degree-zero reduced inclusion, with ordinary homology
displayed explicitly.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L300) (retained native site: line 299).

### TopCat.reducedSingularHomologyZeroToOrdinary_naturality_assoc

```lean
theorem TopCat.reducedSingularHomologyZeroToOrdinary_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) {Z : ModuleCat ℤ} (h : AlgebraicTopology.integralSingularHomology Y 0 ⟶ Z) : CategoryTheory.CategoryStruct.comp (reducedSingularHomologyMap f 0) (CategoryTheory.CategoryStruct.comp Y.reducedSingularHomologyZeroToOrdinary h) = CategoryTheory.CategoryStruct.comp X.reducedSingularHomologyZeroToOrdinary (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (AlgebraicTopology.integralSingularChainMap f) 0) h)
```

Naturality of the degree-zero reduced inclusion, with ordinary homology
displayed explicitly.

Generated `reassoc` declaration from `TopCat.reducedSingularHomologyZeroToOrdinary_naturality`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L302) (retained native site: line 301).

### TopCat.reducedSingularHomologyIsoOfNeZero

```lean
noncomputable def TopCat.reducedSingularHomologyIsoOfNeZero (X : TopCat) (n : ℕ) (hn : n ≠ 0) : X.reducedSingularHomology n ≅ AlgebraicTopology.integralSingularHomology X n
```

In every positive degree, reduced and ordinary integer singular homology
are canonically identical.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L311) (retained native site: line 310).

### TopCat.reducedSingularHomologyMap_isoOfNeZero

```lean
theorem TopCat.reducedSingularHomologyMap_isoOfNeZero {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) (hn : n ≠ 0) : CategoryTheory.CategoryStruct.comp (reducedSingularHomologyMap f n) (Y.reducedSingularHomologyIsoOfNeZero n hn).hom = CategoryTheory.CategoryStruct.comp (X.reducedSingularHomologyIsoOfNeZero n hn).hom (HomologicalComplex.homologyMap (AlgebraicTopology.integralSingularChainMap f) n)
```

**API note (not a source docstring):** In a specified nonzero natural-number degree, the reduced map agrees with the ordinary integral homology map under the canonical reduced-to-ordinary isomorphisms. The hypothesis n ≠ 0 is essential to this presentation.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L320) (retained native site: line 319).

### TopCat.reducedSingularHomologyMap_isoOfNeZero_assoc

```lean
theorem TopCat.reducedSingularHomologyMap_isoOfNeZero_assoc {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) (hn : n ≠ 0) {Z : ModuleCat ℤ} (h : AlgebraicTopology.integralSingularHomology Y n ⟶ Z) : CategoryTheory.CategoryStruct.comp (reducedSingularHomologyMap f n) (CategoryTheory.CategoryStruct.comp (Y.reducedSingularHomologyIsoOfNeZero n hn).hom h) = CategoryTheory.CategoryStruct.comp (X.reducedSingularHomologyIsoOfNeZero n hn).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (AlgebraicTopology.integralSingularChainMap f) n) h)
```

**API note (not a source docstring):** Generated reassoc form of the nonzero-degree reduced-to-ordinary naturality equation. It retains n ≠ 0 and allows any subsequent morphism from the target's ordinary integral homology to Z.

Generated `reassoc` declaration from `TopCat.reducedSingularHomologyMap_isoOfNeZero`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L320) (retained native site: line 319).

### TopCat.reducedSingularHomologyZeroMap_eq_of_homotopy

```lean
theorem TopCat.reducedSingularHomologyZeroMap_eq_of_homotopy {X Y : TopCat} {f g : X ⟶ Y} (H : Homotopy f g) : reducedSingularHomologyZeroMap f = reducedSingularHomologyZeroMap g
```

Homotopic maps induce the same map on reduced degree-zero homology.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L331) (retained native site: line 330).

### TopCat.reducedSingularHomologyMap_eq_of_homotopy

```lean
theorem TopCat.reducedSingularHomologyMap_eq_of_homotopy {X Y : TopCat} {f g : X ⟶ Y} (H : Homotopy f g) (n : ℕ) : reducedSingularHomologyMap f n = reducedSingularHomologyMap g n
```

Homotopic maps induce the same map on reduced integer singular homology in
every nonnegative degree.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L349) (retained native site: line 348).

### TopCat.reducedSingularHomologyIsoOfHomotopyEquiv

```lean
noncomputable def TopCat.reducedSingularHomologyIsoOfHomotopyEquiv {X Y : TopCat} (e : ContinuousMap.HomotopyEquiv ↑X ↑Y) (n : ℕ) : X.reducedSingularHomology n ≅ Y.reducedSingularHomology n
```

A homotopy equivalence induces an isomorphism on reduced integer singular
homology in every nonnegative degree.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L360) (retained native site: line 359).

### TopCat.isZero_reducedSingularHomologyZero_of_pathConnected

```lean
theorem TopCat.isZero_reducedSingularHomologyZero_of_pathConnected (X : TopCat) [PathConnectedSpace ↑X] : CategoryTheory.Limits.IsZero X.reducedSingularHomologyZero
```

A path-connected space has zero reduced degree-zero integer homology.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L386) (retained native site: line 385).

### TopCat.isZero_reducedSingularHomologyZero_of_contractible

```lean
theorem TopCat.isZero_reducedSingularHomologyZero_of_contractible (X : TopCat) [ContractibleSpace ↑X] : CategoryTheory.Limits.IsZero X.reducedSingularHomologyZero
```

In particular, a contractible space has zero reduced degree-zero integer
homology.  A `ContractibleSpace` instance includes nonemptiness.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L393) (retained native site: line 392).

### TopCat.onePointSpace

```lean
abbrev TopCat.onePointSpace : TopCat
```

The canonical one-point space, lifted into an arbitrary universe.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L400) (retained native site: line 399).

### TopCat.isZero_reducedSingularHomology_onePoint

```lean
theorem TopCat.isZero_reducedSingularHomology_onePoint (n : ℕ) : CategoryTheory.Limits.IsZero (onePointSpace.reducedSingularHomology n)
```

Reduced integer singular homology of a point vanishes in every
nonnegative degree.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L403) (retained native site: line 402).

### TopCat.isZero_reducedSingularHomology_of_contractible

```lean
theorem TopCat.isZero_reducedSingularHomology_of_contractible (X : TopCat) [ContractibleSpace ↑X] (n : ℕ) : CategoryTheory.Limits.IsZero (X.reducedSingularHomology n)
```

Every contractible space has zero reduced integer singular homology in
every nonnegative degree. This statement preserves the universe of the
ambient space.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L418) (retained native site: line 417).

### TopCat.emptySpace

```lean
abbrev TopCat.emptySpace : TopCat
```

The canonical empty space, lifted into an arbitrary universe.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L429) (retained native site: line 428).

### TopCat.isZero_reducedSingularHomologyZero_empty

```lean
theorem TopCat.isZero_reducedSingularHomologyZero_empty : CategoryTheory.Limits.IsZero emptySpace.reducedSingularHomologyZero
```

Under the nonnegative convention of this file, reduced degree-zero
homology of the empty space is zero: its ordinary `H₀` is already zero.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L432) (retained native site: line 431).

### TopCat.twoPointSpace

```lean
abbrev TopCat.twoPointSpace : TopCat
```

The canonical discrete two-point space used below.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L454) (retained native site: line 453).

### TopCat.twoPointSwap

```lean
def TopCat.twoPointSwap : twoPointSpace ⟶ twoPointSpace
```

Transposition of the canonical discrete two-point space.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L457) (retained native site: line 456).

### TopCat.twoPointSwap_apply

```lean
theorem TopCat.twoPointSwap_apply (b : Bool) : (CategoryTheory.ConcreteCategory.hom twoPointSwap) b = !b
```

**API note (not a source docstring):** The transposition of the canonical discrete two-point space Bool evaluates to Boolean negation. It swaps false and true in the fixed coordinate order.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L461) (retained native site: line 460).

### TopCat.path_endpoints_eq_of_totallyDisconnected

```lean
theorem TopCat.path_endpoints_eq_of_totallyDisconnected {X : Type u_1} [TopologicalSpace X] [TotallyDisconnectedSpace X] {x y : X} (p : Path x y) : x = y
```

On a totally disconnected space every path has equal endpoints.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L464) (retained native site: line 463).

### TopCat.twoPointZerothHomotopyEquiv

```lean
noncomputable def TopCat.twoPointZerothHomotopyEquiv : ZerothHomotopy ↑twoPointSpace ≃ Bool
```

Path components of the discrete two-point space, with no choice of
representatives: the component of `b` is sent to `b`.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L471) (retained native site: line 470).

### TopCat.twoPointZerothHomotopyEquiv_mk

```lean
theorem TopCat.twoPointZerothHomotopyEquiv_mk (b : Bool) : twoPointZerothHomotopyEquiv (ZerothHomotopy.mk b) = b
```

**API note (not a source docstring):** The component of b in the discrete Bool space is sent back to b by the chosen path-component equivalence. This fixes the labels used by the two-point H0 coordinates.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L481) (retained native site: line 480).

### TopCat.twoPointSingularHomologyZeroIso

```lean
noncomputable def TopCat.twoPointSingularHomologyZeroIso : (AlgebraicTopology.integralSingularHomologyFunctor 0).obj twoPointSpace ≅ ∐ fun (x : Bool) => singularHomologyIntegerCoefficients
```

The canonical presentation of `H₀` of the two-point space by the two
point classes, ordered as `false`, `true`.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L485) (retained native site: line 484).

### TopCat.singularHomologyZeroPoint_twoPoint_iso

```lean
theorem TopCat.singularHomologyZeroPoint_twoPoint_iso (b : Bool) : CategoryTheory.CategoryStruct.comp (twoPointSpace.singularHomologyZeroPoint b) twoPointSingularHomologyZeroIso.hom = CategoryTheory.Limits.Sigma.ι (fun (x : Bool) => singularHomologyIntegerCoefficients) b
```

**API note (not a source docstring):** Under the ordered two-point ordinary H0 isomorphism, the class map of b becomes the coproduct inclusion indexed by b. The order is false, true; it is not chosen up to permutation.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L494) (retained native site: line 493).

### TopCat.singularHomologyZeroPoint_twoPoint_iso_assoc

```lean
theorem TopCat.singularHomologyZeroPoint_twoPoint_iso_assoc (b : Bool) {Z : ModuleCat ℤ} (h : (∐ fun (x : Bool) => singularHomologyIntegerCoefficients) ⟶ Z) : CategoryTheory.CategoryStruct.comp (twoPointSpace.singularHomologyZeroPoint b) (CategoryTheory.CategoryStruct.comp twoPointSingularHomologyZeroIso.hom h) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.ι (fun (x : Bool) => singularHomologyIntegerCoefficients) b) h
```

**API note (not a source docstring):** Generated reassoc form of the ordered two-point class-coordinate identity, followed by any morphism from the two-component coproduct to Z.

Generated `reassoc` declaration from `TopCat.singularHomologyZeroPoint_twoPoint_iso`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L494) (retained native site: line 493).

### TopCat.twoPoint_sigmaι_iso_inv

```lean
theorem TopCat.twoPoint_sigmaι_iso_inv (b : Bool) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.ι (fun (x : Bool) => singularHomologyIntegerCoefficients) b) twoPointSingularHomologyZeroIso.inv = twoPointSpace.singularHomologyZeroPoint b
```

**API note (not a source docstring):** The inverse two-point H0 isomorphism sends the coproduct inclusion at b to the singular point-class map of b. This is the inverse-coordinate form of the fixed false/true presentation.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L509) (retained native site: line 503).

### TopCat.twoPoint_sigmaι_iso_inv_assoc

```lean
theorem TopCat.twoPoint_sigmaι_iso_inv_assoc (b : Bool) {Z : ModuleCat ℤ} (h : (AlgebraicTopology.integralSingularHomologyFunctor 0).obj twoPointSpace ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.ι (fun (x : Bool) => singularHomologyIntegerCoefficients) b) (CategoryTheory.CategoryStruct.comp twoPointSingularHomologyZeroIso.inv h) = CategoryTheory.CategoryStruct.comp (twoPointSpace.singularHomologyZeroPoint b) h
```

**API note (not a source docstring):** Generated reassociated inverse-coordinate identity: the inclusion at b followed by the inverse H0 isomorphism and any outgoing morphism equals the class map of b followed by that morphism.

Generated `reassoc` declaration from `TopCat.twoPoint_sigmaι_iso_inv`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L509) (retained native site: line 503).

### TopCat.twoPointSingularHomologyZeroIso_hom_desc

```lean
theorem TopCat.twoPointSingularHomologyZeroIso_hom_desc : CategoryTheory.CategoryStruct.comp twoPointSingularHomologyZeroIso.hom (CategoryTheory.Limits.Sigma.desc fun (x : Bool) => CategoryTheory.CategoryStruct.id singularHomologyIntegerCoefficients) = twoPointSpace.singularHomology₀ε singularHomologyIntegerCoefficients
```

**API note (not a source docstring):** In the ordered two-point coproduct coordinates, summing the two coefficient components is exactly the ordinary H0 augmentation. Both coproduct summands are mapped by the identity coefficient morphism.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L517) (retained native site: line 511).

### TopCat.twoPointSingularHomologyZeroIso_hom_desc_assoc

```lean
theorem TopCat.twoPointSingularHomologyZeroIso_hom_desc_assoc {Z : ModuleCat ℤ} (h : singularHomologyIntegerCoefficients ⟶ Z) : CategoryTheory.CategoryStruct.comp twoPointSingularHomologyZeroIso.hom (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.desc fun (x : Bool) => CategoryTheory.CategoryStruct.id singularHomologyIntegerCoefficients) h) = CategoryTheory.CategoryStruct.comp (twoPointSpace.singularHomology₀ε singularHomologyIntegerCoefficients) h
```

**API note (not a source docstring):** Generated postcomposition form of the two-point total-augmentation formula. The coordinate sum and the ordinary H0 augmentation agree before any subsequent coefficient-module morphism.

Generated `reassoc` declaration from `TopCat.twoPointSingularHomologyZeroIso_hom_desc`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L517) (retained native site: line 511).

### TopCat.twoPointReducedBasisClass

```lean
noncomputable def TopCat.twoPointReducedBasisClass : singularHomologyIntegerCoefficients ⟶ (AlgebraicTopology.integralSingularHomologyFunctor 0).obj twoPointSpace
```

The chosen reduced `H₀` basis class is `[false] - [true]`.  This fixes the
sign used by the two-point computation and all naturality statements below.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L529) (retained native site: line 523).

### TopCat.twoPointReducedBasisClass_augmentation

```lean
theorem TopCat.twoPointReducedBasisClass_augmentation : CategoryTheory.CategoryStruct.comp twoPointReducedBasisClass (twoPointSpace.singularHomology₀ε singularHomologyIntegerCoefficients) = 0
```

**API note (not a source docstring):** The ordinary H0 class [false] − [true] has zero total augmentation. This is the kernel condition used to lift the chosen signed basis class to reduced H0.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L537) (retained native site: line 531).

### TopCat.twoPointReducedBasisClass_augmentation_assoc

```lean
theorem TopCat.twoPointReducedBasisClass_augmentation_assoc {Z : ModuleCat ℤ} (h : singularHomologyIntegerCoefficients ⟶ Z) : CategoryTheory.CategoryStruct.comp twoPointReducedBasisClass (CategoryTheory.CategoryStruct.comp (twoPointSpace.singularHomology₀ε singularHomologyIntegerCoefficients) h) = CategoryTheory.CategoryStruct.comp 0 h
```

**API note (not a source docstring):** Generated reassoc form of the signed basis class's zero-augmentation equation. The displayed right side is the zero morphism followed by the arbitrary outgoing morphism; no basis sign is changed.

Generated `reassoc` declaration from `TopCat.twoPointReducedBasisClass_augmentation`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L537) (retained native site: line 531).

### TopCat.twoPointReducedBasis

```lean
noncomputable def TopCat.twoPointReducedBasis : singularHomologyIntegerCoefficients ⟶ twoPointSpace.reducedSingularHomologyZero
```

The basis vector `1 ↦ [false] - [true]` in reduced `H₀`.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L543) (retained native site: line 537).

### TopCat.twoPointReducedBasis_ι

```lean
theorem TopCat.twoPointReducedBasis_ι : CategoryTheory.CategoryStruct.comp twoPointReducedBasis twoPointSpace.reducedSingularHomologyZeroι = twoPointReducedBasisClass
```

**API note (not a source docstring):** Including the chosen reduced basis into ordinary H0 gives the explicitly ordered difference [false] − [true]. This characterizes its lift through the augmentation kernel.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L550) (retained native site: line 544).

### TopCat.twoPointReducedBasis_ι_assoc

```lean
theorem TopCat.twoPointReducedBasis_ι_assoc {Z : ModuleCat ℤ} (h : (AlgebraicTopology.integralSingularHomologyFunctor 0).obj twoPointSpace ⟶ Z) : CategoryTheory.CategoryStruct.comp twoPointReducedBasis (CategoryTheory.CategoryStruct.comp twoPointSpace.reducedSingularHomologyZeroι h) = CategoryTheory.CategoryStruct.comp twoPointReducedBasisClass h
```

**API note (not a source docstring):** Generated reassociated kernel-lift identity for the chosen two-point reduced basis, followed by any morphism from ordinary H0 to Z.

Generated `reassoc` declaration from `TopCat.twoPointReducedBasis_ι`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L550) (retained native site: line 544).

### TopCat.twoPointReducedCoordinate

```lean
noncomputable def TopCat.twoPointReducedCoordinate : twoPointSpace.reducedSingularHomologyZero ⟶ singularHomologyIntegerCoefficients
```

The `false` coordinate on reduced `H₀`, after the ordered two-point
presentation and its canonical finite biproduct structure.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L556) (retained native site: line 550).

### TopCat.twoPointReducedBasis_coordinate

```lean
theorem TopCat.twoPointReducedBasis_coordinate : CategoryTheory.CategoryStruct.comp twoPointReducedBasis twoPointReducedCoordinate = CategoryTheory.CategoryStruct.id singularHomologyIntegerCoefficients
```

**API note (not a source docstring):** Applying the false coordinate to the reduced basis [false] − [true] gives the identity coefficient morphism. This is one of the two inverse identities for the explicit reduced-H0 coordinate isomorphism.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L566) (retained native site: line 560).

### TopCat.twoPointReducedBasis_coordinate_assoc

```lean
theorem TopCat.twoPointReducedBasis_coordinate_assoc {Z : ModuleCat ℤ} (h : singularHomologyIntegerCoefficients ⟶ Z) : CategoryTheory.CategoryStruct.comp twoPointReducedBasis (CategoryTheory.CategoryStruct.comp twoPointReducedCoordinate h) = h
```

**API note (not a source docstring):** Generated reassoc form of the basis-then-coordinate identity: following these two maps by any coefficient-module morphism h returns h.

Generated `reassoc` declaration from `TopCat.twoPointReducedBasis_coordinate`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L566) (retained native site: line 560).

### TopCat.twoPointReducedCoordinate_basis

```lean
theorem TopCat.twoPointReducedCoordinate_basis : CategoryTheory.CategoryStruct.comp twoPointReducedCoordinate twoPointReducedBasis = CategoryTheory.CategoryStruct.id twoPointSpace.reducedSingularHomologyZero
```

**API note (not a source docstring):** Taking the false coordinate of a reduced H0 class and then multiplying the chosen basis [false] − [true] reconstructs that class. The augmentation-kernel condition supplies the relation between its two coordinates.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L576) (retained native site: line 570).

### TopCat.reducedSingularHomologyZeroTwoPointIso

```lean
noncomputable def TopCat.reducedSingularHomologyZeroTwoPointIso : twoPointSpace.reducedSingularHomologyZero ≅ singularHomologyIntegerCoefficients
```

The explicit two-point computation with basis `[false] - [true]`.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L651) (retained native site: line 645).

### TopCat.singularHomologyIntegerCoefficientsIso

```lean
def TopCat.singularHomologyIntegerCoefficientsIso : singularHomologyIntegerCoefficients ≅ ↧ℤ
```

The universe-zero coefficient object is canonically the ordinary integer
module.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L660) (retained native site: line 654).

### TopCat.reducedSingularHomologyZeroTwoPointIntegerIso

```lean
noncomputable def TopCat.reducedSingularHomologyZeroTwoPointIntegerIso : twoPointSpace.reducedSingularHomologyZero ≅ ↧ℤ
```

The two-point computation stated with the literal integer module as its
target.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L666) (retained native site: line 660).

### TopCat.twoPointReducedBasis_swap

```lean
theorem TopCat.twoPointReducedBasis_swap : CategoryTheory.CategoryStruct.comp twoPointReducedBasis (reducedSingularHomologyZeroMap twoPointSwap) = -twoPointReducedBasis
```

Transposition sends the chosen basis `[false] - [true]` to its negative.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L673) (retained native site: line 667).

### TopCat.twoPointReducedBasis_swap_assoc

```lean
theorem TopCat.twoPointReducedBasis_swap_assoc {Z : ModuleCat ℤ} (h : twoPointSpace.reducedSingularHomologyZero ⟶ Z) : CategoryTheory.CategoryStruct.comp twoPointReducedBasis (CategoryTheory.CategoryStruct.comp (reducedSingularHomologyZeroMap twoPointSwap) h) = CategoryTheory.CategoryStruct.comp (-twoPointReducedBasis) h
```

Transposition sends the chosen basis `[false] - [true]` to its negative.

Generated `reassoc` declaration from `TopCat.twoPointReducedBasis_swap`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L674) (retained native site: line 668).

### TopCat.reducedSingularHomologyZeroTwoPointIso_swap

```lean
theorem TopCat.reducedSingularHomologyZeroTwoPointIso_swap : CategoryTheory.CategoryStruct.comp reducedSingularHomologyZeroTwoPointIso.inv (CategoryTheory.CategoryStruct.comp (reducedSingularHomologyZeroMap twoPointSwap) reducedSingularHomologyZeroTwoPointIso.hom) = -CategoryTheory.CategoryStruct.id singularHomologyIntegerCoefficients
```

In the basis `[false] - [true]`, transposition acts on reduced `H₀` by
multiplication by `-1`.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L687) (retained native site: line 681).

### TopCat.reducedSingularHomologyZeroTwoPointIntegerIso_swap

```lean
theorem TopCat.reducedSingularHomologyZeroTwoPointIntegerIso_swap : CategoryTheory.CategoryStruct.comp reducedSingularHomologyZeroTwoPointIntegerIso.inv (CategoryTheory.CategoryStruct.comp (reducedSingularHomologyZeroMap twoPointSwap) reducedSingularHomologyZeroTwoPointIntegerIso.hom) = -CategoryTheory.CategoryStruct.id ↧ℤ
```

The literal-integer form of the transposition computation: conjugating by
`reducedSingularHomologyZeroTwoPointIntegerIso` gives `-𝟙` on `ℤ`.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L700) (retained native site: line 694).

### TopCat.reducedSingularHomologyZeroTwoPointIso_id

```lean
theorem TopCat.reducedSingularHomologyZeroTwoPointIso_id : CategoryTheory.CategoryStruct.comp reducedSingularHomologyZeroTwoPointIso.inv (CategoryTheory.CategoryStruct.comp (reducedSingularHomologyZeroMap (CategoryTheory.CategoryStruct.id twoPointSpace)) reducedSingularHomologyZeroTwoPointIso.hom) = CategoryTheory.CategoryStruct.id singularHomologyIntegerCoefficients
```

The identity map acts as the identity in the same ordered basis.

[Source](../SphereTopology/Homology/Singular/Reduced.lean#L715) (retained native site: line 709).

## SphereTopology.Homology.Singular.ReducedMayerVietoris

Scope: mathematical library leaf.

### AlgebraicTopology.twoOpenReducedMayerVietorisδZero

```lean
noncomputable def AlgebraicTopology.twoOpenReducedMayerVietorisδZero {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) : X.reducedSingularHomology 1 ⟶ ((TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V)).reducedSingularHomology 0
```

The reduced degree-zero connecting morphism for the ordered cover `(U,V)`.
It is the unique factorization of the accepted ordinary connecting morphism
through the degree-zero augmentation kernel.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L105) (retained native site: line 105).

### AlgebraicTopology.twoOpenReducedMayerVietorisδZero_ordinary

```lean
theorem AlgebraicTopology.twoOpenReducedMayerVietorisδZero_ordinary {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) : CategoryTheory.CategoryStruct.comp (twoOpenReducedMayerVietorisδZero U V hUV) (CategoryTheory.CategoryStruct.comp ((TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V)).reducedSingularHomologyZeroToOrdinary (twoOpenIntersectionHomologyIso U V 0).hom) = CategoryTheory.CategoryStruct.comp (X.reducedSingularHomologyIsoOfNeZero 1 twoOpenReducedMayerVietorisδZero_ordinary._proof_1).hom (twoOpenMayerVietorisδ U V hUV 0)
```

Composing the reduced connecting morphism with the augmentation-kernel
inclusion and literal-intersection identification recovers the accepted
ordinary connecting morphism with its owned sign.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L159) (retained native site: line 159).

### AlgebraicTopology.twoOpenReducedMayerVietorisδZero_ordinary_assoc

```lean
theorem AlgebraicTopology.twoOpenReducedMayerVietorisδZero_ordinary_assoc {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) {Z : ModuleCat ℤ} (h : HomologicalComplex.homology (twoOpenSmallShortComplex U V).X₁ 0 ⟶ Z) : CategoryTheory.CategoryStruct.comp (twoOpenReducedMayerVietorisδZero U V hUV) (CategoryTheory.CategoryStruct.comp ((TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V)).reducedSingularHomologyZeroToOrdinary (CategoryTheory.CategoryStruct.comp (twoOpenIntersectionHomologyIso U V 0).hom h)) = CategoryTheory.CategoryStruct.comp (X.reducedSingularHomologyIsoOfNeZero 1 twoOpenReducedMayerVietorisδZero_ordinary._proof_1).hom (CategoryTheory.CategoryStruct.comp (twoOpenMayerVietorisδ U V hUV 0) h)
```

Composing the reduced connecting morphism with the augmentation-kernel
inclusion and literal-intersection identification recovers the accepted
ordinary connecting morphism with its owned sign.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenReducedMayerVietorisδZero_ordinary`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L162) (retained native site: line 162).

### AlgebraicTopology.twoOpenReducedMayerVietorisFromIntersectionZero

```lean
noncomputable def AlgebraicTopology.twoOpenReducedMayerVietorisFromIntersectionZero {X : TopCat} (U V : TopologicalSpace.Opens ↑X) : ((TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V)).reducedSingularHomology 0 ⟶ ((TopologicalSpace.Opens.toTopCat X).obj U).reducedSingularHomology 0 ⊞ ((TopologicalSpace.Opens.toTopCat X).obj V).reducedSingularHomology 0
```

The ordered reduced degree-zero difference map
`H̃₀(U∩V) → H̃₀(U) ⊕ H̃₀(V)`, with convention `(c,-c)`.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L173) (retained native site: line 173).

### AlgebraicTopology.twoOpenReducedMayerVietorisδZero_comp_fromIntersection

```lean
theorem AlgebraicTopology.twoOpenReducedMayerVietorisδZero_comp_fromIntersection {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) : CategoryTheory.CategoryStruct.comp (twoOpenReducedMayerVietorisδZero U V hUV) (twoOpenReducedMayerVietorisFromIntersectionZero U V) = 0
```

The reduced connecting morphism is followed by zero in the reduced
degree-zero Mayer--Vietoris sequence.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L216) (retained native site: line 216).

### AlgebraicTopology.twoOpenReducedMayerVietorisδZero_comp_fromIntersection_assoc

```lean
theorem AlgebraicTopology.twoOpenReducedMayerVietorisδZero_comp_fromIntersection_assoc {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) {Z : ModuleCat ℤ} (h : ((TopologicalSpace.Opens.toTopCat X).obj U).reducedSingularHomology 0 ⊞ ((TopologicalSpace.Opens.toTopCat X).obj V).reducedSingularHomology 0 ⟶ Z) : CategoryTheory.CategoryStruct.comp (twoOpenReducedMayerVietorisδZero U V hUV) (CategoryTheory.CategoryStruct.comp (twoOpenReducedMayerVietorisFromIntersectionZero U V) h) = CategoryTheory.CategoryStruct.comp 0 h
```

The reduced connecting morphism is followed by zero in the reduced
degree-zero Mayer--Vietoris sequence.

Generated `reassoc` declaration from `AlgebraicTopology.twoOpenReducedMayerVietorisδZero_comp_fromIntersection`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L218) (retained native site: line 218).

### AlgebraicTopology.twoOpenReducedMayerVietoris_exact_intersectionZero

```lean
theorem AlgebraicTopology.twoOpenReducedMayerVietoris_exact_intersectionZero {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) : { X₁ := X.reducedSingularHomology 1, X₂ := ((TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V)).reducedSingularHomology 0, X₃ := ((TopologicalSpace.Opens.toTopCat X).obj U).reducedSingularHomology 0 ⊞ ((TopologicalSpace.Opens.toTopCat X).obj V).reducedSingularHomology 0, f := twoOpenReducedMayerVietorisδZero U V hUV, g := twoOpenReducedMayerVietorisFromIntersectionZero U V, zero := ⋯ }.Exact
```

Exactness at the reduced degree-zero homology of the literal
intersection.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L237) (retained native site: line 237).

### AlgebraicTopology.twoOpenReducedMayerVietorisδZero_naturality

```lean
theorem AlgebraicTopology.twoOpenReducedMayerVietorisδZero_naturality {X Y : TopCat} (f : X ⟶ Y) (U V : TopologicalSpace.Opens ↑X) (U' V' : TopologicalSpace.Opens ↑Y) (hU : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑U ↑U') (hV : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑V ↑V') (hUV : U ⊔ V = ⊤) (hU'V' : U' ⊔ V' = ⊤) : CategoryTheory.CategoryStruct.comp (twoOpenReducedMayerVietorisδZero U V hUV) (TopCat.reducedSingularHomologyMap (twoOpenIntersectionMap f U V U' V' hU hV) 0) = CategoryTheory.CategoryStruct.comp (TopCat.reducedSingularHomologyMap f 1) (twoOpenReducedMayerVietorisδZero U' V' hU'V')
```

Naturality of the reduced connecting morphism for a continuous map
respecting both ordered opens, stated using the actual literal-intersection
map.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L296) (retained native site: line 296).

### AlgebraicTopology.twoOpenReducedMayerVietorisδZero_swap_eq_neg

```lean
theorem AlgebraicTopology.twoOpenReducedMayerVietorisδZero_swap_eq_neg {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (hVU : V ⊔ U = ⊤) : CategoryTheory.CategoryStruct.comp (twoOpenReducedMayerVietorisδZero U V hUV) (TopCat.reducedSingularHomologyMap (twoOpenIntersectionSwapMap U V) 0) = -twoOpenReducedMayerVietorisδZero V U hVU
```

Swapping the ordered cover and transporting by the actual sign-free
literal-intersection swap negates the reduced connecting morphism.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L320) (retained native site: line 320).

### AlgebraicTopology.twoOpenReducedMayerVietorisδZero_isIso_of_acyclic_opens

```lean
theorem AlgebraicTopology.twoOpenReducedMayerVietorisδZero_isIso_of_acyclic_opens {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (hU₀ : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat X).obj U).reducedSingularHomology 0)) (hV₀ : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat X).obj V).reducedSingularHomology 0)) (hU₁ : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat X).obj U).reducedSingularHomology 1)) (hV₁ : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat X).obj V).reducedSingularHomology 1)) : CategoryTheory.IsIso (twoOpenReducedMayerVietorisδZero U V hUV)
```

If both opens have zero reduced homology in degrees zero and one, the
reduced connecting morphism is an isomorphism.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L341) (retained native site: line 341).

### AlgebraicTopology.twoOpenReducedMayerVietorisIsoOfAcyclicOpens

```lean
noncomputable def AlgebraicTopology.twoOpenReducedMayerVietorisIsoOfAcyclicOpens {X : TopCat} (U V : TopologicalSpace.Opens ↑X) (hUV : U ⊔ V = ⊤) (hU₀ : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat X).obj U).reducedSingularHomology 0)) (hV₀ : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat X).obj V).reducedSingularHomology 0)) (hU₁ : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat X).obj U).reducedSingularHomology 1)) (hV₁ : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat X).obj V).reducedSingularHomology 1)) : X.reducedSingularHomology 1 ≅ ((TopologicalSpace.Opens.toTopCat X).obj (U ⊓ V)).reducedSingularHomology 0
```

The reduced Mayer--Vietoris isomorphism furnished by an acyclic ordered
two-open cover in the adjacent degrees.

[Source](../SphereTopology/Homology/Singular/ReducedMayerVietoris.lean#L390) (retained native site: line 390).

## SphereTopology.Homology.Singular.SmallChains

Scope: mathematical library leaf.

### TopCat.smallSingularSet

```lean
def TopCat.smallSingularSet {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) : (toSSet.obj X).Subcomplex
```

Singular simplices whose range is contained in one member of `U`.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L44) (retained native site: line 43).

### TopCat.mem_smallSingularSet_iff

```lean
theorem TopCat.mem_smallSingularSet_iff {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) {n : SimplexCategoryᵒᵖ} (x : (toSSet.obj X).obj n) : x ∈ (smallSingularSet U).obj n ↔ ∃ (i : ι), Set.range ⇑((X.toSSetObjEquiv n) x) ⊆ ↑(U i)
```

**API note (not a source docstring):** A singular simplex belongs to the small singular subcomplex exactly when its continuous representative has range contained in one member of the family U. U may be any family of opens; this characterization does not require it to cover the space.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L54) (retained native site: line 53).

### TopCat.smallSingularSet_mono

```lean
theorem TopCat.smallSingularSet_mono {X : TopCat} {ι : Type u_1} {κ : Type u_2} {U : ι → TopologicalSpace.Opens ↑X} {V : κ → TopologicalSpace.Opens ↑X} (h : ∀ (i : ι), ∃ (j : κ), U i ≤ V j) : smallSingularSet U ≤ smallSingularSet V
```

Refining every member of `U` into a member of `V` gives an inclusion of
the corresponding small-singular subcomplexes.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L60) (retained native site: line 59).

### TopCat.smallSingularSetHomOfRefinement

```lean
noncomputable def TopCat.smallSingularSetHomOfRefinement {X : TopCat} {ι : Type u_1} {κ : Type u_2} {U : ι → TopologicalSpace.Opens ↑X} {V : κ → TopologicalSpace.Opens ↑X} (h : ∀ (i : ι), ∃ (j : κ), U i ≤ V j) : (smallSingularSet U).toSSet ⟶ (smallSingularSet V).toSSet
```

The simplicial map on small singular sets induced by a cover refinement.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L70) (retained native site: line 69).

### TopCat.smallSingularSetMap

```lean
noncomputable def TopCat.smallSingularSetMap {X Y : TopCat} {ι : Type u_1} {κ : Type u_2} (f : X ⟶ Y) (U : ι → TopologicalSpace.Opens ↑X) (V : κ → TopologicalSpace.Opens ↑Y) (h : ∀ (i : ι), ∃ (j : κ), Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑(U i) ↑(V j)) : (smallSingularSet U).toSSet ⟶ (smallSingularSet V).toSSet
```

A continuous map induces a map of small-singular simplicial sets whenever
it sends each member of the source cover into a member of the target cover.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L77) (retained native site: line 76).

### TopCat.smallSingularSetMap_comp_inclusion

```lean
theorem TopCat.smallSingularSetMap_comp_inclusion {X Y : TopCat} {ι : Type u_1} {κ : Type u_2} (f : X ⟶ Y) (U : ι → TopologicalSpace.Opens ↑X) (V : κ → TopologicalSpace.Opens ↑Y) (h : ∀ (i : ι), ∃ (j : κ), Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑(U i) ↑(V j)) : CategoryTheory.CategoryStruct.comp (smallSingularSetMap f U V h) (smallSingularSet V).ι = CategoryTheory.CategoryStruct.comp (smallSingularSet U).ι (toSSet.map f)
```

**API note (not a source docstring):** The small-singular simplicial map induced by a continuous map respecting the two families of opens commutes with inclusion into all singular simplices. The hypothesis sends each source member into some target member; no covering hypothesis is used.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L93) (retained native site: line 92).

### TopCat.smallSingularSetMap_comp_inclusion_assoc

```lean
theorem TopCat.smallSingularSetMap_comp_inclusion_assoc {X Y : TopCat} {ι : Type u_1} {κ : Type u_2} (f : X ⟶ Y) (U : ι → TopologicalSpace.Opens ↑X) (V : κ → TopologicalSpace.Opens ↑Y) (h : ∀ (i : ι), ∃ (j : κ), Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑(U i) ↑(V j)) {Z : SSet} (h✝ : toSSet.obj Y ⟶ Z) : CategoryTheory.CategoryStruct.comp (smallSingularSetMap f U V h) (CategoryTheory.CategoryStruct.comp (smallSingularSet V).ι h✝) = CategoryTheory.CategoryStruct.comp (smallSingularSet U).ι (CategoryTheory.CategoryStruct.comp (toSSet.map f) h✝)
```

**API note (not a source docstring):** Generated reassoc form of small-singular simplicial-map compatibility with inclusion, followed by an arbitrary simplicial map from the target singular set. The family-respecting condition remains unchanged.

Generated `reassoc` declaration from `TopCat.smallSingularSetMap_comp_inclusion`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L93) (retained native site: line 92).

### AlgebraicTopology.integerCoefficients

```lean
abbrev AlgebraicTopology.integerCoefficients : ModuleCat ℤ
```

Integer coefficients lifted into the universe of the singular simplices.
The underlying module is canonically linearly equivalent to `ℤ`.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L105) (retained native site: line 104).

### AlgebraicTopology.isCoverSmall_zero

```lean
theorem AlgebraicTopology.isCoverSmall_zero {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) (hU : TopologicalSpace.IsOpenCover U) (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := 0 })) : IsCoverSmall U x
```

Every singular zero-simplex is small relative to an open cover.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L110) (retained native site: line 109).

### AlgebraicTopology.smallSingularChainComplex

```lean
noncomputable def AlgebraicTopology.smallSingularChainComplex {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) : ChainComplex (ModuleCat ℤ) ℕ
```

The integer chain complex generated by singular simplices small in `U`.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L120) (retained native site: line 119).

### AlgebraicTopology.smallSingularChainInclusion

```lean
noncomputable def AlgebraicTopology.smallSingularChainInclusion {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) : smallSingularChainComplex U ⟶ ((singularChainComplexFunctor (ModuleCat ℤ)).obj integerCoefficients).obj X
```

Inclusion of the `U`-small integer singular chain complex into all chains.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L125) (retained native site: line 124).

### AlgebraicTopology.smallSingularChainMapOfRefinement

```lean
noncomputable def AlgebraicTopology.smallSingularChainMapOfRefinement {X : TopCat} {ι : Type u_1} {κ : Type u_2} {U : ι → TopologicalSpace.Opens ↑X} {V : κ → TopologicalSpace.Opens ↑X} (h : ∀ (i : ι), ∃ (j : κ), U i ≤ V j) : smallSingularChainComplex U ⟶ smallSingularChainComplex V
```

The integer-chain map induced by a refinement of open covers.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L131) (retained native site: line 130).

### AlgebraicTopology.smallSingularChainMapOfRefinement_comp_inclusion

```lean
theorem AlgebraicTopology.smallSingularChainMapOfRefinement_comp_inclusion {X : TopCat} {ι : Type u_1} {κ : Type u_2} {U : ι → TopologicalSpace.Opens ↑X} {V : κ → TopologicalSpace.Opens ↑X} (h : ∀ (i : ι), ∃ (j : κ), U i ≤ V j) : CategoryTheory.CategoryStruct.comp (smallSingularChainMapOfRefinement h) (smallSingularChainInclusion V) = smallSingularChainInclusion U
```

**API note (not a source docstring):** A refinement from U to V induces a map of small integer chain complexes whose composite with the V-inclusion is the U-inclusion. Each U member need only lie in some V member; the families need not cover.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L138) (retained native site: line 137).

### AlgebraicTopology.smallSingularChainMapOfRefinement_comp_inclusion_assoc

```lean
theorem AlgebraicTopology.smallSingularChainMapOfRefinement_comp_inclusion_assoc {X : TopCat} {ι : Type u_1} {κ : Type u_2} {U : ι → TopologicalSpace.Opens ↑X} {V : κ → TopologicalSpace.Opens ↑X} (h : ∀ (i : ι), ∃ (j : κ), U i ≤ V j) {Z : ChainComplex (ModuleCat ℤ) ℕ} (h✝ : ((singularChainComplexFunctor (ModuleCat ℤ)).obj integerCoefficients).obj X ⟶ Z) : CategoryTheory.CategoryStruct.comp (smallSingularChainMapOfRefinement h) (CategoryTheory.CategoryStruct.comp (smallSingularChainInclusion V) h✝) = CategoryTheory.CategoryStruct.comp (smallSingularChainInclusion U) h✝
```

**API note (not a source docstring):** Generated reassoc form of refinement compatibility with inclusion, after any chain map from the full singular chain complex. The additional target complex and postcomposition are explicit in the signature.

Generated `reassoc` declaration from `AlgebraicTopology.smallSingularChainMapOfRefinement_comp_inclusion`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L138) (retained native site: line 137).

### AlgebraicTopology.smallSingularChainMap

```lean
noncomputable def AlgebraicTopology.smallSingularChainMap {X Y : TopCat} {ι : Type u_1} {κ : Type u_2} (f : X ⟶ Y) (U : ι → TopologicalSpace.Opens ↑X) (V : κ → TopologicalSpace.Opens ↑Y) (h : ∀ (i : ι), ∃ (j : κ), Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑(U i) ↑(V j)) : smallSingularChainComplex U ⟶ smallSingularChainComplex V
```

The chain map on cover-small chains induced by a cover-respecting
continuous map.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L155) (retained native site: line 154).

### AlgebraicTopology.smallSingularChainMap_comp_inclusion

```lean
theorem AlgebraicTopology.smallSingularChainMap_comp_inclusion {X Y : TopCat} {ι : Type u_1} {κ : Type u_2} (f : X ⟶ Y) (U : ι → TopologicalSpace.Opens ↑X) (V : κ → TopologicalSpace.Opens ↑Y) (h : ∀ (i : ι), ∃ (j : κ), Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑(U i) ↑(V j)) : CategoryTheory.CategoryStruct.comp (smallSingularChainMap f U V h) (smallSingularChainInclusion V) = CategoryTheory.CategoryStruct.comp (smallSingularChainInclusion U) (SSet.chainComplexMap (TopCat.toSSet.map f) integerCoefficients)
```

**API note (not a source docstring):** For a continuous map taking each U member into some V member, the induced map of small integer chains commutes with inclusion and the full singular chain map. Neither family is assumed to cover here.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L163) (retained native site: line 162).

### AlgebraicTopology.smallSingularChainMap_comp_inclusion_assoc

```lean
theorem AlgebraicTopology.smallSingularChainMap_comp_inclusion_assoc {X Y : TopCat} {ι : Type u_1} {κ : Type u_2} (f : X ⟶ Y) (U : ι → TopologicalSpace.Opens ↑X) (V : κ → TopologicalSpace.Opens ↑Y) (h : ∀ (i : ι), ∃ (j : κ), Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom f) ↑(U i) ↑(V j)) {Z : ChainComplex (ModuleCat ℤ) ℕ} (h✝ : ((singularChainComplexFunctor (ModuleCat ℤ)).obj integerCoefficients).obj Y ⟶ Z) : CategoryTheory.CategoryStruct.comp (smallSingularChainMap f U V h) (CategoryTheory.CategoryStruct.comp (smallSingularChainInclusion V) h✝) = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (smallSingularChainInclusion U) (SSet.chainComplexMap (TopCat.toSSet.map f) integerCoefficients)) h✝
```

**API note (not a source docstring):** Generated reassociated compatibility of the small-chain map with inclusion and the full singular chain map, followed by any chain map into Z. It retains the same family-respecting condition.

Generated `reassoc` declaration from `AlgebraicTopology.smallSingularChainMap_comp_inclusion`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L163) (retained native site: line 162).

### AlgebraicTopology.chainGroupIsoFinsupp

```lean
noncomputable def AlgebraicTopology.chainGroupIsoFinsupp (X : SSet) (n : ℕ) : (X.chainComplex integerCoefficients).X n ≅ ↧(X.obj (Opposite.op { len := n }) →₀ ℤ)
```

Identify the degree-`n` integer-coefficient simplicial chain group with
finitely supported integer functions on the `n`-simplices. The construction
also removes the coefficient `ULift` used to accommodate the universe of `X`.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L182) (retained native site: line 181).

### AlgebraicTopology.ι_chainGroupIsoFinsupp_hom

```lean
theorem AlgebraicTopology.ι_chainGroupIsoFinsupp_hom (X : SSet) {n : ℕ} (x : X.obj (Opposite.op { len := n })) : CategoryTheory.CategoryStruct.comp (X.ιChainComplex x) (chainGroupIsoFinsupp X n).hom = ModuleCat.ofHom (Finsupp.lsingle x ∘ₗ ↑ULift.moduleEquiv)
```

**API note (not a source docstring):** The coefficient inclusion of a simplex followed by the chain-to-finsupp isomorphism is the linear singleton map at that simplex, composed with removal of the coefficient ULift. This is a morphism-level identity for any simplicial set and degree.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L196) (retained native site: line 195).

### AlgebraicTopology.chainGroupIsoFinsupp_hom_ι

```lean
theorem AlgebraicTopology.chainGroupIsoFinsupp_hom_ι (X : SSet) {n : ℕ} (x : X.obj (Opposite.op { len := n })) : (ModuleCat.Hom.hom (chainGroupIsoFinsupp X n).hom) ((ModuleCat.Hom.hom (X.ιChainComplex x)) { down := 1 }) = Finsupp.single x 1
```

**API note (not a source docstring):** Under the chain-to-finsupp isomorphism, the coefficient-one generator at a simplex is its finitely supported singleton with integer coefficient one. The lifted coefficient on the chain side is made explicit.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L216) (retained native site: line 215).

### AlgebraicTopology.moduleCat_quasiIso_of_representatives

```lean
theorem AlgebraicTopology.moduleCat_quasiIso_of_representatives {S₁ S₂ : CategoryTheory.ShortComplex (ModuleCat ℤ)} (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] (hsurj : ∀ (y : ↑S₂.X₂), (CategoryTheory.ConcreteCategory.hom S₂.g) y = 0 → ∃ (x : ↑S₁.X₂), (CategoryTheory.ConcreteCategory.hom S₁.g) x = 0 ∧ ∃ (b : ↑S₂.X₁), (CategoryTheory.ConcreteCategory.hom φ.τ₂) x - y = (CategoryTheory.ConcreteCategory.hom S₂.f) b) (hinj : ∀ (x : ↑S₁.X₂), (CategoryTheory.ConcreteCategory.hom S₁.g) x = 0 → ∀ (b : ↑S₂.X₁), (CategoryTheory.ConcreteCategory.hom φ.τ₂) x = (CategoryTheory.ConcreteCategory.hom S₂.f) b → ∃ (a : ↑S₁.X₁), x = (CategoryTheory.ConcreteCategory.hom S₁.f) a) : CategoryTheory.ShortComplex.QuasiIso φ
```

**API note (not a source docstring):** A morphism of integer-module short complexes is a quasi-isomorphism if every target cycle is represented by an image cycle modulo a boundary and every source cycle whose image is a boundary is itself a boundary. The two displayed elementwise hypotheses are the surjectivity and injectivity criteria on homology; both complexes have the displayed homology instances.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L236) (retained native site: line 235).

### AlgebraicTopology.sSetFinsuppBoundary

```lean
noncomputable def AlgebraicTopology.sSetFinsuppBoundary (Z : SSet) (n : ℕ) : (Z.obj (Opposite.op { len := n + 1 }) →₀ ℤ) →ₗ[ℤ] Z.obj (Opposite.op { len := n }) →₀ ℤ
```

The integer-linear boundary from degree `n + 1` to degree `n`, sending a
simplex to the alternating face sum with coefficient `(-1)^i` on its `i`th face.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L307) (retained native site: line 306).

### AlgebraicTopology.sSetFinsuppBoundary_single

```lean
theorem AlgebraicTopology.sSetFinsuppBoundary_single (Z : SSet) (n : ℕ) (x : Z.obj (Opposite.op { len := n + 1 })) : (sSetFinsuppBoundary Z n) (Finsupp.single x 1) = ∑ i : Fin (n + 2), (-1) ^ ↑i • Finsupp.single ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.SimplicialObject.δ Z i)) x) 1
```

**API note (not a source docstring):** The boundary of a coefficient-one simplex is the sum of its faces, with integer sign (−1)^i on face i. The input degree is n+1, the output degree is n, and there are n+2 faces.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L314) (retained native site: line 313).

### AlgebraicTopology.chainGroupIsoFinsupp_sSet_d

```lean
theorem AlgebraicTopology.chainGroupIsoFinsupp_sSet_d (Z : SSet) (n : ℕ) : CategoryTheory.CategoryStruct.comp (chainGroupIsoFinsupp Z (n + 1)).inv (CategoryTheory.CategoryStruct.comp ((Z.chainComplex integerCoefficients).d (n + 1) n) (chainGroupIsoFinsupp Z n).hom) = ModuleCat.ofHom (sSetFinsuppBoundary Z n)
```

**API note (not a source docstring):** Conjugating the simplicial integer-chain differential from degree n+1 to n by the two chain-to-finsupp isomorphisms yields the alternating-face linear boundary map. This is an equality of module morphisms for any simplicial set.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L320) (retained native site: line 319).

### AlgebraicTopology.chainGroupIsoFinsupp_sSet_d_apply

```lean
theorem AlgebraicTopology.chainGroupIsoFinsupp_sSet_d_apply (Z : SSet) (n : ℕ) (c : Z.obj (Opposite.op { len := n + 1 }) →₀ ℤ) : (CategoryTheory.ConcreteCategory.hom (chainGroupIsoFinsupp Z n).hom) ((CategoryTheory.ConcreteCategory.hom ((Z.chainComplex integerCoefficients).d (n + 1) n)) ((CategoryTheory.ConcreteCategory.hom (chainGroupIsoFinsupp Z (n + 1)).inv) c)) = (sSetFinsuppBoundary Z n) c
```

**API note (not a source docstring):** Elementwise form of chainGroupIsoFinsupp_sSet_d: transporting a finitely supported chain into the simplicial chain group, differentiating and transporting back is the alternating-face boundary.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L347) (retained native site: line 346).

### AlgebraicTopology.mapDomain_smallFinsuppBoundary

```lean
theorem AlgebraicTopology.mapDomain_smallFinsuppBoundary {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) (n : ℕ) (c : (TopCat.smallSingularSet U).toSSet.obj (Opposite.op { len := n + 1 }) →₀ ℤ) : Finsupp.mapDomain Subtype.val ((sSetFinsuppBoundary (TopCat.smallSingularSet U).toSSet n) c) = (singularFinsuppBoundary X n) (Finsupp.mapDomain Subtype.val c)
```

**API note (not a source docstring):** Forgetting the smallness subtype commutes with the finitely supported alternating-face boundary. This holds for an arbitrary family U of opens, since the faces of a simplex small in U remain small in U.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L358) (retained native site: line 357).

### AlgebraicTopology.chainGroupIsoFinsupp_d

```lean
theorem AlgebraicTopology.chainGroupIsoFinsupp_d (X : TopCat) (n : ℕ) : CategoryTheory.CategoryStruct.comp (chainGroupIsoFinsupp (TopCat.toSSet.obj X) (n + 1)).inv (CategoryTheory.CategoryStruct.comp (((TopCat.toSSet.obj X).chainComplex integerCoefficients).d (n + 1) n) (chainGroupIsoFinsupp (TopCat.toSSet.obj X) n).hom) = ModuleCat.ofHom (singularFinsuppBoundary X n)
```

**API note (not a source docstring):** For a topological space's singular simplicial set, the transported integer-chain differential is singularFinsuppBoundary. This specializes the general simplicial chain-to-finsupp differential identity to singular chains.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L380) (retained native site: line 379).

### AlgebraicTopology.chainGroupIsoFinsupp_smallInclusion

```lean
theorem AlgebraicTopology.chainGroupIsoFinsupp_smallInclusion {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) (n : ℕ) : CategoryTheory.CategoryStruct.comp (chainGroupIsoFinsupp (TopCat.smallSingularSet U).toSSet n).inv (CategoryTheory.CategoryStruct.comp ((smallSingularChainInclusion U).f n) (chainGroupIsoFinsupp (TopCat.toSSet.obj X) n).hom) = ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ Subtype.val)
```

**API note (not a source docstring):** In finitely supported coordinates, inclusion of U-small singular chains is the integer-linear mapDomain along the small-simplex subtype inclusion. No open-cover hypothesis is needed for this morphism-level equality.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L408) (retained native site: line 407).

### AlgebraicTopology.chainGroupIsoFinsupp_d_apply

```lean
theorem AlgebraicTopology.chainGroupIsoFinsupp_d_apply (X : TopCat) (n : ℕ) (c : SingularChainFinsupp X (n + 1)) : (CategoryTheory.ConcreteCategory.hom (chainGroupIsoFinsupp (TopCat.toSSet.obj X) n).hom) ((CategoryTheory.ConcreteCategory.hom (((TopCat.toSSet.obj X).chainComplex integerCoefficients).d (n + 1) n)) ((CategoryTheory.ConcreteCategory.hom (chainGroupIsoFinsupp (TopCat.toSSet.obj X) (n + 1)).inv) c)) = (singularFinsuppBoundary X n) c
```

**API note (not a source docstring):** Elementwise singular-chain specialization: transport a degree-(n+1) finitely supported chain to singular chains, take the differential and transport back to obtain its singularFinsuppBoundary.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L430) (retained native site: line 429).

### AlgebraicTopology.chainGroupIsoFinsupp_smallInclusion_apply

```lean
theorem AlgebraicTopology.chainGroupIsoFinsupp_smallInclusion_apply {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) (n : ℕ) (c : (TopCat.smallSingularSet U).toSSet.obj (Opposite.op { len := n }) →₀ ℤ) : (CategoryTheory.ConcreteCategory.hom (chainGroupIsoFinsupp (TopCat.toSSet.obj X) n).hom) ((CategoryTheory.ConcreteCategory.hom ((smallSingularChainInclusion U).f n)) ((CategoryTheory.ConcreteCategory.hom (chainGroupIsoFinsupp (TopCat.smallSingularSet U).toSSet n).inv) c)) = Finsupp.mapDomain Subtype.val c
```

**API note (not a source docstring):** Elementwise form of the small-chain inclusion coordinate identity: transport a finitely supported chain on small simplices into small chains and then all chains to obtain mapDomain along Subtype.val.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L441) (retained native site: line 440).

### AlgebraicTopology.smallSingularChainInclusion_f_injective

```lean
theorem AlgebraicTopology.smallSingularChainInclusion_f_injective {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) (n : ℕ) : Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom ((smallSingularChainInclusion U).f n))
```

**API note (not a source docstring):** In every nonnegative degree, the map including U-small integer singular chains into all singular chains is injective as a function. U may be any family of opens; surjectivity or an open-cover condition is not asserted.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L456) (retained native site: line 455).

### AlgebraicTopology.smallChainOfSupport

```lean
noncomputable def AlgebraicTopology.smallChainOfSupport {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) {n : ℕ} (c : SingularChainFinsupp X n) : (TopCat.smallSingularSet U).toSSet.obj (Opposite.op { len := n }) →₀ ℤ
```

Restrict a finitely supported singular chain to the subtype of simplices
small in one member of `U`, discarding any other terms. No support or cover
hypothesis is required here; `mapDomain_smallChainOfSupport` recovers the original
chain when every simplex in its support is small.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L483) (retained native site: line 482).

### AlgebraicTopology.mapDomain_smallChainOfSupport

```lean
theorem AlgebraicTopology.mapDomain_smallChainOfSupport {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) {n : ℕ} (c : SingularChainFinsupp X n) (hc : ∀ x ∈ c.support, IsCoverSmall U x) : Finsupp.mapDomain Subtype.val (smallChainOfSupport U c) = c
```

**API note (not a source docstring):** If every simplex in the support of c is small in U, then forgetting the subtype after restricting c with smallChainOfSupport recovers c. The support hypothesis is essential: without it the restriction discards non-small terms.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L492) (retained native site: line 491).

### AlgebraicTopology.isCoverSmall_of_mem_mapDomain_small

```lean
theorem AlgebraicTopology.isCoverSmall_of_mem_mapDomain_small {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) {n : ℕ} (c : (TopCat.smallSingularSet U).toSSet.obj (Opposite.op { len := n }) →₀ ℤ) {x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })} (hx : x ∈ (Finsupp.mapDomain Subtype.val c).support) : IsCoverSmall U x
```

**API note (not a source docstring):** Every simplex in the support of a finitely supported chain obtained by forgetting the small-simplex subtype is small in U. This needs no assertion that U covers the entire space.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L504) (retained native site: line 503).

### AlgebraicTopology.quasiIso_smallSingularChainInclusion

```lean
theorem AlgebraicTopology.quasiIso_smallSingularChainInclusion {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) (hU : TopologicalSpace.IsOpenCover U) : QuasiIso (smallSingularChainInclusion U)
```

The inclusion of cover-small integer singular chains is a quasi-isomorphism.

[Source](../SphereTopology/Homology/Singular/SmallChains.lean#L523) (retained native site: line 522).

## SphereTopology.Homology.Singular.Sphere

Scope: mathematical library leaf.

### SphereTopology.E3

```lean
abbrev SphereTopology.E3 : Type
```

Real Euclidean three-space, with coordinate order `(x, y, z)`.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L37) (retained native site: line 37).

### SphereTopology.sphere2NorthVector

```lean
def SphereTopology.sphere2NorthVector : E3
```

The vector `(0, 0, 1)` in `E3`, with the third coordinate indexed by `2`.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L40) (retained native site: line 40).

### SphereTopology.sphere2NorthVector_norm

```lean
theorem SphereTopology.sphere2NorthVector_norm : ‖sphere2NorthVector‖ = 1
```

**API note (not a source docstring):** The vector (0,0,1) has norm one in real Euclidean three-space. It therefore supplies the north pole of the literal unit two-sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L43) (retained native site: line 43).

### SphereTopology.sphere2NorthPoint

```lean
def SphereTopology.sphere2NorthPoint : ↑(Metric.sphere 0 1)
```

The north pole `(0, 0, 1)` bundled as a point of the metric unit two-sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L46) (retained native site: line 46).

### SphereTopology.sphere2SouthPoint

```lean
noncomputable def SphereTopology.sphere2SouthPoint : ↑(Metric.sphere 0 1)
```

The south pole `(0, 0, -1)`, defined as the antipode of the north pole.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L51) (retained native site: line 51).

### SphereTopology.sphere2NorthPoint_first

```lean
theorem SphereTopology.sphere2NorthPoint_first : (↑sphere2NorthPoint).ofLp 0 = 0
```

**API note (not a source docstring):** The north pole has coordinate zero equal to zero; the coordinate order is (x,y,z).

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L54) (retained native site: line 54).

### SphereTopology.sphere2NorthPoint_second

```lean
theorem SphereTopology.sphere2NorthPoint_second : (↑sphere2NorthPoint).ofLp 1 = 0
```

**API note (not a source docstring):** The north pole has coordinate one equal to zero.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L57) (retained native site: line 57).

### SphereTopology.sphere2NorthPoint_third

```lean
theorem SphereTopology.sphere2NorthPoint_third : (↑sphere2NorthPoint).ofLp 2 = 1
```

**API note (not a source docstring):** The north pole has coordinate two equal to one. Fin 3 coordinates are numbered from zero.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L60) (retained native site: line 60).

### SphereTopology.sphere2SouthPoint_first

```lean
theorem SphereTopology.sphere2SouthPoint_first : (↑sphere2SouthPoint).ofLp 0 = 0
```

**API note (not a source docstring):** The south pole has coordinate zero equal to zero, as the antipode of the north pole.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L63) (retained native site: line 63).

### SphereTopology.sphere2SouthPoint_second

```lean
theorem SphereTopology.sphere2SouthPoint_second : (↑sphere2SouthPoint).ofLp 1 = 0
```

**API note (not a source docstring):** The south pole has coordinate one equal to zero.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L66) (retained native site: line 66).

### SphereTopology.sphere2SouthPoint_third

```lean
theorem SphereTopology.sphere2SouthPoint_third : (↑sphere2SouthPoint).ofLp 2 = -1
```

**API note (not a source docstring):** The south pole has coordinate two equal to minus one.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L69) (retained native site: line 69).

### SphereTopology.sphere2NorthPoint_ne_southPoint

```lean
theorem SphereTopology.sphere2NorthPoint_ne_southPoint : sphere2NorthPoint ≠ sphere2SouthPoint
```

**API note (not a source docstring):** The two poles are distinct, as witnessed by their third coordinates. Their complements consequently form an open cover.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L72) (retained native site: line 72).

### SphereTopology.sphere2

```lean
abbrev SphereTopology.sphere2 : TopCat
```

The literal standard metric two-sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L77) (retained native site: line 77).

### SphereTopology.sphere2NorthPunctured

```lean
def SphereTopology.sphere2NorthPunctured : TopologicalSpace.Opens ↑sphere2
```

The first open in the ordered cover: the complement of the north pole.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L81) (retained native site: line 81).

### SphereTopology.sphere2SouthPunctured

```lean
def SphereTopology.sphere2SouthPunctured : TopologicalSpace.Opens ↑sphere2
```

The second open in the ordered cover: the complement of the south pole.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L85) (retained native site: line 85).

### SphereTopology.sphere2Punctured_join

```lean
theorem SphereTopology.sphere2Punctured_join : sphere2NorthPunctured ⊔ sphere2SouthPunctured = ⊤
```

**API note (not a source docstring):** The north-pole complement followed by the south-pole complement covers the literal two-sphere. This fixes the cover order used for the chosen homology coordinate.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L89) (retained native site: line 89).

### SphereTopology.sphere2Punctured_join_reversed

```lean
theorem SphereTopology.sphere2Punctured_join_reversed : sphere2SouthPunctured ⊔ sphere2NorthPunctured = ⊤
```

**API note (not a source docstring):** The south/north order of those same two punctured opens also covers the sphere. Ordered connecting-map formulas distinguish this order from north/south.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L99) (retained native site: line 99).

### SphereTopology.sphere2NorthPuncturedHomeomorph

```lean
noncomputable def SphereTopology.sphere2NorthPuncturedHomeomorph : ↑((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured) ≃ₜ EuclideanSpace ℝ (Fin 2)
```

Stereographic coordinates on the north-punctured sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L104) (retained native site: line 104).

### SphereTopology.sphere2SouthPuncturedHomeomorph

```lean
noncomputable def SphereTopology.sphere2SouthPuncturedHomeomorph : ↑((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured) ≃ₜ EuclideanSpace ℝ (Fin 2)
```

Stereographic coordinates on the south-punctured sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L114) (retained native site: line 114).

### SphereTopology.sphere2PunctureIntersection

```lean
abbrev SphereTopology.sphere2PunctureIntersection : Type
```

The literal intersection of the ordered north/south puncture cover.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L124) (retained native site: line 124).

### SphereTopology.sphere2Equator

```lean
abbrev SphereTopology.sphere2Equator : Type
```

The literal equator, as a subtype of the literal standard two-sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L129) (retained native site: line 129).

### SphereTopology.sphere2_eq_north_or_south_of_first_second_eq_zero

```lean
theorem SphereTopology.sphere2_eq_north_or_south_of_first_second_eq_zero (p : ↑(Metric.sphere 0 1)) (hx : (↑p).ofLp 0 = 0) (hy : (↑p).ofLp 1 = 0) : p = sphere2NorthPoint ∨ p = sphere2SouthPoint
```

**API note (not a source docstring):** A unit-sphere point with both first coordinates zero is a north or south pole. Its unit norm, encoded by the sphere subtype, forces the third coordinate to be plus or minus one.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L133) (retained native site: line 133).

### SphereTopology.sphere2PunctureIntersection_first_second_not_both_zero

```lean
theorem SphereTopology.sphere2PunctureIntersection_first_second_not_both_zero (p : sphere2PunctureIntersection) : ¬((↑↑p).ofLp 0 = 0 ∧ (↑↑p).ofLp 1 = 0)
```

**API note (not a source docstring):** In the sphere with both poles removed, the first two coordinates cannot both vanish. This makes the projection toward the equator safe to normalize.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L154) (retained native site: line 154).

### SphereTopology.sphere2PunctureIntersectionLinearVector

```lean
def SphereTopology.sphere2PunctureIntersectionLinearVector (t : ↑unitInterval) (p : sphere2PunctureIntersection) : E3
```

Before normalization, scale only the third coordinate by the homotopy
parameter.  The first two coordinates remain unchanged.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L162) (retained native site: line 162).

### SphereTopology.sphere2PunctureIntersectionLinearVector_first

```lean
theorem SphereTopology.sphere2PunctureIntersectionLinearVector_first (t : ↑unitInterval) (p : sphere2PunctureIntersection) : (sphere2PunctureIntersectionLinearVector t p).ofLp 0 = (↑↑p).ofLp 0
```

**API note (not a source docstring):** The unnormalized equatorial deformation keeps coordinate zero unchanged at every time.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L169) (retained native site: line 169).

### SphereTopology.sphere2PunctureIntersectionLinearVector_second

```lean
theorem SphereTopology.sphere2PunctureIntersectionLinearVector_second (t : ↑unitInterval) (p : sphere2PunctureIntersection) : (sphere2PunctureIntersectionLinearVector t p).ofLp 1 = (↑↑p).ofLp 1
```

**API note (not a source docstring):** The unnormalized equatorial deformation keeps coordinate one unchanged at every time.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L174) (retained native site: line 174).

### SphereTopology.sphere2PunctureIntersectionLinearVector_third

```lean
theorem SphereTopology.sphere2PunctureIntersectionLinearVector_third (t : ↑unitInterval) (p : sphere2PunctureIntersection) : (sphere2PunctureIntersectionLinearVector t p).ofLp 2 = ↑t * (↑↑p).ofLp 2
```

**API note (not a source docstring):** Only coordinate two changes before normalization: it is multiplied by the unit-interval parameter t. Thus t=0 removes the vertical coordinate and t=1 restores it.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L179) (retained native site: line 179).

### SphereTopology.sphere2PunctureIntersectionLinearVector_ne_zero

```lean
theorem SphereTopology.sphere2PunctureIntersectionLinearVector_ne_zero (t : ↑unitInterval) (p : sphere2PunctureIntersection) : sphere2PunctureIntersectionLinearVector t p ≠ 0
```

**API note (not a source docstring):** The vector (x,y,t*z) never vanishes on the twice-punctured sphere, because x and y are not both zero. This licenses radial normalization for every allowed t.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L185) (retained native site: line 185).

### SphereTopology.sphere2PunctureIntersectionRadialVector

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionRadialVector (t : ↑unitInterval) (p : sphere2PunctureIntersection) : E3
```

The normalized equatorial-deformation vector.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L196) (retained native site: line 196).

### SphereTopology.sphere2PunctureIntersectionRadialVector_norm

```lean
theorem SphereTopology.sphere2PunctureIntersectionRadialVector_norm (t : ↑unitInterval) (p : sphere2PunctureIntersection) : ‖sphere2PunctureIntersectionRadialVector t p‖ = 1
```

**API note (not a source docstring):** Normalizing the equatorial-deformation vector gives norm one, so it stays on the unit sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L202) (retained native site: line 202).

### SphereTopology.sphere2PunctureIntersectionRadialVector_first_second_not_both_zero

```lean
theorem SphereTopology.sphere2PunctureIntersectionRadialVector_first_second_not_both_zero (t : ↑unitInterval) (p : sphere2PunctureIntersection) : ¬((sphere2PunctureIntersectionRadialVector t p).ofLp 0 = 0 ∧ (sphere2PunctureIntersectionRadialVector t p).ofLp 1 = 0)
```

**API note (not a source docstring):** Normalization does not make both first coordinates zero. The normalized homotopy therefore avoids both removed poles.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L210) (retained native site: line 210).

### SphereTopology.sphere2PunctureIntersectionRadialPoint

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionRadialPoint (t : ↑unitInterval) (p : sphere2PunctureIntersection) : sphere2PunctureIntersection
```

The normalized homotopy stays on the literal twice-punctured sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L227) (retained native site: line 227).

### SphereTopology.continuous_sphere2PunctureIntersectionLinearVector

```lean
theorem SphereTopology.continuous_sphere2PunctureIntersectionLinearVector : Continuous fun (q : ↑unitInterval × sphere2PunctureIntersection) => sphere2PunctureIntersectionLinearVector q.1 q.2
```

**API note (not a source docstring):** The map (t,p) to the unnormalized vector (x,y,t*z) is jointly continuous on the unit interval times the twice-punctured sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L248) (retained native site: line 248).

### SphereTopology.continuous_sphere2PunctureIntersectionRadialPoint

```lean
theorem SphereTopology.continuous_sphere2PunctureIntersectionRadialPoint : Continuous fun (q : ↑unitInterval × sphere2PunctureIntersection) => sphere2PunctureIntersectionRadialPoint q.1 q.2
```

**API note (not a source docstring):** The normalized deformation is jointly continuous into the twice-punctured sphere; the vector nonvanishing result supplies continuity of the inverse norm.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L255) (retained native site: line 255).

### SphereTopology.sphere2PunctureIntersectionRadialHomotopyMap

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionRadialHomotopyMap : C(↑unitInterval × sphere2PunctureIntersection, sphere2PunctureIntersection)
```

The jointly continuous map obtained by normalizing `(x, y, t * z)` on the
twice-punctured sphere. At time zero it projects to the equator; at time one it
is the identity, and equatorial points remain fixed throughout.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L265) (retained native site: line 265).

### SphereTopology.sphere2PunctureIntersectionRadialVector_zero_third

```lean
theorem SphereTopology.sphere2PunctureIntersectionRadialVector_zero_third (p : sphere2PunctureIntersection) : (sphere2PunctureIntersectionRadialVector 0 p).ofLp 2 = 0
```

**API note (not a source docstring):** At time zero the normalized vector has third coordinate zero. Its value lies on the literal equator.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L273) (retained native site: line 273).

### SphereTopology.sphere2PunctureIntersectionRadialAtZero

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionRadialAtZero : C(sphere2PunctureIntersection, sphere2PunctureIntersection)
```

Evaluation of the radial homotopy at its equatorial endpoint.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L279) (retained native site: line 279).

### SphereTopology.sphere2PunctureIntersectionToEquatorPoint

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionToEquatorPoint (p : sphere2PunctureIntersection) : sphere2Equator
```

The point-valued equatorial projection underlying the continuous map.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L285) (retained native site: line 285).

### SphereTopology.continuous_sphere2PunctureIntersectionToEquatorPoint

```lean
theorem SphereTopology.continuous_sphere2PunctureIntersectionToEquatorPoint : Continuous sphere2PunctureIntersectionToEquatorPoint
```

**API note (not a source docstring):** The equatorial projection is continuous as a map into the equator subtype, not only after forgetting to ambient three-space.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L291) (retained native site: line 291).

### SphereTopology.sphere2PunctureIntersectionToEquator

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionToEquator : C(sphere2PunctureIntersection, sphere2Equator)
```

Projection of the twice-punctured sphere onto the literal equator.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L296) (retained native site: line 296).

### SphereTopology.sphere2EquatorToPunctureIntersectionPoint

```lean
def SphereTopology.sphere2EquatorToPunctureIntersectionPoint (p : sphere2Equator) : sphere2PunctureIntersection
```

The point-valued inclusion underlying the equator continuous map.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L302) (retained native site: line 302).

### SphereTopology.continuous_sphere2EquatorToPunctureIntersectionPoint

```lean
theorem SphereTopology.continuous_sphere2EquatorToPunctureIntersectionPoint : Continuous sphere2EquatorToPunctureIntersectionPoint
```

**API note (not a source docstring):** The literal equator includes continuously into the twice-punctured sphere; its zero third coordinate excludes both poles.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L320) (retained native site: line 320).

### SphereTopology.sphere2EquatorToPunctureIntersection

```lean
def SphereTopology.sphere2EquatorToPunctureIntersection : C(sphere2Equator, sphere2PunctureIntersection)
```

Inclusion of the literal equator into the twice-punctured sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L324) (retained native site: line 324).

### SphereTopology.sphere2PunctureIntersectionRadialPoint_zero

```lean
theorem SphereTopology.sphere2PunctureIntersectionRadialPoint_zero (p : sphere2PunctureIntersection) : sphere2PunctureIntersectionRadialPoint 0 p = sphere2EquatorToPunctureIntersection (sphere2PunctureIntersectionToEquator p)
```

**API note (not a source docstring):** At time zero the homotopy is equatorial projection followed by inclusion back into the puncture intersection.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L330) (retained native site: line 330).

### SphereTopology.sphere2PunctureIntersectionRadialPoint_one

```lean
theorem SphereTopology.sphere2PunctureIntersectionRadialPoint_one (p : sphere2PunctureIntersection) : sphere2PunctureIntersectionRadialPoint 1 p = p
```

**API note (not a source docstring):** At time one the normalized homotopy is the identity on the puncture intersection.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L341) (retained native site: line 341).

### SphereTopology.sphere2PunctureIntersectionRadialPoint_fixed

```lean
theorem SphereTopology.sphere2PunctureIntersectionRadialPoint_fixed (t : ↑unitInterval) (p : sphere2Equator) : sphere2PunctureIntersectionRadialPoint t (sphere2EquatorToPunctureIntersection p) = sphere2EquatorToPunctureIntersection p
```

The normalized deformation fixes every equator point at every time.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L355) (retained native site: line 355).

### SphereTopology.sphere2PunctureIntersectionToEquator_inclusion

```lean
theorem SphereTopology.sphere2PunctureIntersectionToEquator_inclusion (p : sphere2Equator) : sphere2PunctureIntersectionToEquator (sphere2EquatorToPunctureIntersection p) = p
```

**API note (not a source docstring):** Projection after equator inclusion is exactly the identity on the equator. Along with the pointwise-fixed homotopy, this gives the stated equatorial homotopy equivalence.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L379) (retained native site: line 379).

### SphereTopology.sphere2PunctureIntersectionRadialHomotopy

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionRadialHomotopy : (sphere2EquatorToPunctureIntersection.comp sphere2PunctureIntersectionToEquator).Homotopy (ContinuousMap.id sphere2PunctureIntersection)
```

The explicit normalized deformation homotopy, from equatorial projection
followed by inclusion to the identity.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L395) (retained native site: line 395).

### SphereTopology.sphere2PunctureIntersectionEquatorHomotopyEquiv

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionEquatorHomotopyEquiv : ContinuousMap.HomotopyEquiv sphere2PunctureIntersection sphere2Equator
```

The literal twice-punctured sphere is homotopy equivalent to its literal
equator through the displayed projection, inclusion, and deformation.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L405) (retained native site: line 405).

### SphereTopology.sphere2PunctureIntersectionEquatorHomotopyEquivULift

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionEquatorHomotopyEquivULift : ContinuousMap.HomotopyEquiv (ULift.{u_1, 0} sphere2PunctureIntersection) (ULift.{u_2, 0} sphere2Equator)
```

A genuine universe-lifted client of the intersection/equator geometry.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L421) (retained native site: line 421).

### SphereTopology.sphere2EquatorToCircleVector

```lean
def SphereTopology.sphere2EquatorToCircleVector (p : sphere2Equator) : E2
```

Keep coordinates zero and one of an equator point, in that order.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L428) (retained native site: line 428).

### SphereTopology.sphere1ToSphere2EquatorVector

```lean
def SphereTopology.sphere1ToSphere2EquatorVector (p : ↑(Metric.sphere 0 1)) : E3
```

Insert a circle point into the first two coordinates of `E3`; the third
coordinate is zero.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L432) (retained native site: line 432).

### SphereTopology.sphere2EquatorToCircleVector_first

```lean
theorem SphereTopology.sphere2EquatorToCircleVector_first (p : sphere2Equator) : (sphere2EquatorToCircleVector p).ofLp 0 = (↑↑p).ofLp 0
```

**API note (not a source docstring):** The equator-to-circle coordinate map retains coordinate zero. It does not exchange the x and y axes.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L437) (retained native site: line 437).

### SphereTopology.sphere2EquatorToCircleVector_second

```lean
theorem SphereTopology.sphere2EquatorToCircleVector_second (p : sphere2Equator) : (sphere2EquatorToCircleVector p).ofLp 1 = (↑↑p).ofLp 1
```

**API note (not a source docstring):** The equator-to-circle coordinate map retains coordinate one, completing the prescribed (x,y) order.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L441) (retained native site: line 441).

### SphereTopology.sphere1ToSphere2EquatorVector_first

```lean
theorem SphereTopology.sphere1ToSphere2EquatorVector_first (p : ↑(Metric.sphere 0 1)) : (sphere1ToSphere2EquatorVector p).ofLp 0 = (↑p).ofLp 0
```

**API note (not a source docstring):** The inverse coordinate construction inserts a circle point's coordinate zero as coordinate zero in three-space.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L445) (retained native site: line 445).

### SphereTopology.sphere1ToSphere2EquatorVector_second

```lean
theorem SphereTopology.sphere1ToSphere2EquatorVector_second (p : ↑(Metric.sphere 0 1)) : (sphere1ToSphere2EquatorVector p).ofLp 1 = (↑p).ofLp 1
```

**API note (not a source docstring):** The inverse coordinate construction inserts a circle point's coordinate one as coordinate one in three-space.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L450) (retained native site: line 450).

### SphereTopology.sphere1ToSphere2EquatorVector_third

```lean
theorem SphereTopology.sphere1ToSphere2EquatorVector_third (p : ↑(Metric.sphere 0 1)) : (sphere1ToSphere2EquatorVector p).ofLp 2 = 0
```

**API note (not a source docstring):** The inverse coordinate construction inserts zero as coordinate two, placing its image on the equator.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L455) (retained native site: line 455).

### SphereTopology.sphere2EquatorToCircleVector_norm

```lean
theorem SphereTopology.sphere2EquatorToCircleVector_norm (p : sphere2Equator) : ‖sphere2EquatorToCircleVector p‖ = 1
```

**API note (not a source docstring):** Discarding the zero third coordinate of an equator point preserves unit norm. The two-coordinate vector is therefore a point of the standard circle.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L460) (retained native site: line 460).

### SphereTopology.sphere1ToSphere2EquatorVector_norm

```lean
theorem SphereTopology.sphere1ToSphere2EquatorVector_norm (p : ↑(Metric.sphere 0 1)) : ‖sphere1ToSphere2EquatorVector p‖ = 1
```

**API note (not a source docstring):** Appending a zero third coordinate to a unit-circle point preserves norm one. This supplies the sphere membership proof for the inverse equator coordinate map.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L471) (retained native site: line 471).

### SphereTopology.sphere2EquatorHomeomorphSphere1

```lean
noncomputable def SphereTopology.sphere2EquatorHomeomorphSphere1 : sphere2Equator ≃ₜ ↑sphere1
```

The orientation-fixed coordinate homeomorphism from the equator to the
accepted standard circle: `(x,y,0)` is sent to `(x,y)`.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L487) (retained native site: line 487).

### SphereTopology.sphere2PunctureIntersectionSphere1HomotopyEquiv

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionSphere1HomotopyEquiv : ContinuousMap.HomotopyEquiv sphere2PunctureIntersection ↑sphere1
```

The full geometric transport from the literal twice-punctured sphere to
the accepted standard circle, with the equatorial coordinate order `(x,y)`.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L521) (retained native site: line 521).

### SphereTopology.sphere2NorthPunctured_contractibleSpace

```lean
theorem SphereTopology.sphere2NorthPunctured_contractibleSpace : ContractibleSpace ↑((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured)
```

**API note (not a source docstring):** The sphere with its north pole removed is contractible through its stereographic homeomorphism with the Euclidean plane. This theorem returns the contractibility class witness.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L528) (retained native site: line 528).

### SphereTopology.sphere2SouthPunctured_contractibleSpace

```lean
theorem SphereTopology.sphere2SouthPunctured_contractibleSpace : ContractibleSpace ↑((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured)
```

**API note (not a source docstring):** The sphere with its south pole removed is contractible through its stereographic homeomorphism with the Euclidean plane.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L534) (retained native site: line 534).

### SphereTopology.isZero_reducedSingularHomology_sphere2NorthPunctured

```lean
theorem SphereTopology.isZero_reducedSingularHomology_sphere2NorthPunctured (n : ℕ) : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2NorthPunctured).reducedSingularHomology n)
```

**API note (not a source docstring):** All nonnegative reduced integral homology objects of the north-punctured sphere are zero, using the contractibility witness.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L540) (retained native site: line 540).

### SphereTopology.isZero_reducedSingularHomology_sphere2SouthPunctured

```lean
theorem SphereTopology.isZero_reducedSingularHomology_sphere2SouthPunctured (n : ℕ) : CategoryTheory.Limits.IsZero (((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured).reducedSingularHomology n)
```

**API note (not a source docstring):** All nonnegative reduced integral homology objects of the south-punctured sphere are zero. This is vanishing for the open, not for the full sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L547) (retained native site: line 547).

### SphereTopology.sphere2MayerVietorisδOne_isIso

```lean
theorem SphereTopology.sphere2MayerVietorisδOne_isIso : CategoryTheory.IsIso (AlgebraicTopology.twoOpenMayerVietorisδ sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1)
```

The accepted positive-degree connecting morphism for the ordered
north/south cover is an isomorphism in degree two.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L555) (retained native site: line 555).

### SphereTopology.sphere2ReducedMayerVietorisIso

```lean
noncomputable def SphereTopology.sphere2ReducedMayerVietorisIso : sphere2.reducedSingularHomology 2 ≅ ((TopologicalSpace.Opens.toTopCat sphere2).obj (sphere2NorthPunctured ⊓ sphere2SouthPunctured)).reducedSingularHomology 1
```

Positive-degree reduced Mayer--Vietoris for the ordered north/south cover,
with its target identified with the literal puncture intersection.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L589) (retained native site: line 589).

### SphereTopology.sphere2ReducedMayerVietorisIso_hom

```lean
theorem SphereTopology.sphere2ReducedMayerVietorisIso_hom : sphere2ReducedMayerVietorisIso.hom = CategoryTheory.CategoryStruct.comp (sphere2.reducedSingularHomologyIsoOfNeZero 2 sphere2ReducedMayerVietorisIso._proof_1).hom (CategoryTheory.CategoryStruct.comp (AlgebraicTopology.twoOpenMayerVietorisδ sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1) (CategoryTheory.CategoryStruct.comp (AlgebraicTopology.twoOpenIntersectionHomologyIso sphere2NorthPunctured sphere2SouthPunctured 1).inv (((TopologicalSpace.Opens.toTopCat sphere2).obj (sphere2NorthPunctured ⊓ sphere2SouthPunctured)).reducedSingularHomologyIsoOfNeZero 1 sphere2ReducedMayerVietorisIso._proof_2).inv))
```

**API note (not a source docstring):** The chosen reduced H2-to-H1 isomorphism is reduced-to-ordinary conversion, the north/south ordinary connecting morphism, the inverse intersection homology identification, and conversion back to reduced H1. Native _proof_1/_proof_2 tokens express the required positive-degree witnesses; they are not extra mathematical hypotheses.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L606) (retained native site: line 606).

### SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso

```lean
noncomputable def SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso : sphere2.reducedSingularHomology 2 ≅ ↧ℤ
```

The fixed-coordinate reduced integral homology computation
`H̃₂(S²; ℤ) ≅ ℤ` for the literal standard two-sphere.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L619) (retained native site: line 619).

### SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso_hom

```lean
theorem SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso_hom : reducedSingularHomologyTwoSphereTwoIntegerIso.hom = CategoryTheory.CategoryStruct.comp sphere2ReducedMayerVietorisIso.hom (CategoryTheory.CategoryStruct.comp (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv sphere2PunctureIntersectionSphere1HomotopyEquiv 1).hom reducedSingularHomologyOneSphereOneIntegerIso.hom)
```

The computation uses the accepted ordered connecting morphism, then the
literal intersection/equator transport, the coordinate-ordered equator/circle
transport, and finally the accepted fixed circle integer coordinate.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L628) (retained native site: line 628).

### SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso_hom_explicit

```lean
theorem SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso_hom_explicit : reducedSingularHomologyTwoSphereTwoIntegerIso.hom = CategoryTheory.CategoryStruct.comp (sphere2.reducedSingularHomologyIsoOfNeZero 2 sphere2ReducedMayerVietorisIso._proof_1).hom (CategoryTheory.CategoryStruct.comp (AlgebraicTopology.twoOpenMayerVietorisδ sphere2NorthPunctured sphere2SouthPunctured sphere2Punctured_join 1) (CategoryTheory.CategoryStruct.comp (AlgebraicTopology.twoOpenIntersectionHomologyIso sphere2NorthPunctured sphere2SouthPunctured 1).inv (CategoryTheory.CategoryStruct.comp (((TopologicalSpace.Opens.toTopCat sphere2).obj (sphere2NorthPunctured ⊓ sphere2SouthPunctured)).reducedSingularHomologyIsoOfNeZero 1 sphere2ReducedMayerVietorisIso._proof_2).inv (CategoryTheory.CategoryStruct.comp (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv sphere2PunctureIntersectionSphere1HomotopyEquiv 1).hom reducedSingularHomologyOneSphereOneIntegerIso.hom))))
```

Fully expanded comparison with the accepted positive-degree connecting
morphism and the fixed circle coordinate.

[Source](../SphereTopology/Homology/Singular/Sphere.lean#L639) (retained native site: line 639).

## SphereTopology.Homology.Singular.SphereAntipodal

Scope: mathematical library leaf.

### SphereTopology.sphere2Antipodal

```lean
noncomputable def SphereTopology.sphere2Antipodal : sphere2 ⟶ sphere2
```

The bundled antipodal self-map of the literal standard two-sphere.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L31) (retained native site: line 31).

### SphereTopology.sphere2Antipodal_apply

```lean
theorem SphereTopology.sphere2Antipodal_apply (p : ↑sphere2) : (CategoryTheory.ConcreteCategory.hom sphere2Antipodal) p = -p
```

**API note (not a source docstring):** The bundled antipodal self-map of the literal two-sphere evaluates by pointwise negation.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L35) (retained native site: line 35).

### SphereTopology.sphere2Antipodal_north

```lean
theorem SphereTopology.sphere2Antipodal_north : (CategoryTheory.ConcreteCategory.hom sphere2Antipodal) sphere2NorthPoint = sphere2SouthPoint
```

**API note (not a source docstring):** The antipodal map sends the north pole to the south pole.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L39) (retained native site: line 39).

### SphereTopology.sphere2Antipodal_south

```lean
theorem SphereTopology.sphere2Antipodal_south : (CategoryTheory.ConcreteCategory.hom sphere2Antipodal) sphere2SouthPoint = sphere2NorthPoint
```

**API note (not a source docstring):** The antipodal map sends the south pole back to the north pole. Thus it exchanges the ordered puncture cover.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L43) (retained native site: line 43).

### SphereTopology.sphere2Antipodal_mapsTo_north_south

```lean
theorem SphereTopology.sphere2Antipodal_mapsTo_north_south : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom sphere2Antipodal) ↑sphere2NorthPunctured ↑sphere2SouthPunctured
```

Antipodal negation sends the north-punctured open into the
south-punctured open.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L49) (retained native site: line 49).

### SphereTopology.sphere2Antipodal_mapsTo_south_north

```lean
theorem SphereTopology.sphere2Antipodal_mapsTo_south_north : Set.MapsTo ⇑(CategoryTheory.ConcreteCategory.hom sphere2Antipodal) ↑sphere2SouthPunctured ↑sphere2NorthPunctured
```

Antipodal negation sends the south-punctured open into the
north-punctured open.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L59) (retained native site: line 59).

### SphereTopology.sphere2PunctureIntersectionAntipodalPoint

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionAntipodalPoint (p : sphere2PunctureIntersection) : sphere2PunctureIntersection
```

Antipodal negation as a point of the literal puncture intersection.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L72) (retained native site: line 72).

### SphereTopology.sphere2PunctureIntersectionAntipodal

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionAntipodal : C(sphere2PunctureIntersection, sphere2PunctureIntersection)
```

The antipodal endomorphism of the literal puncture intersection.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L89) (retained native site: line 89).

### SphereTopology.sphere2PunctureIntersectionAntipodalInduced

```lean
noncomputable def SphereTopology.sphere2PunctureIntersectionAntipodalInduced : ↧sphere2PunctureIntersection ⟶ ↧sphere2PunctureIntersection
```

The sign-free endomorphism induced from the swapped two-open cover: first
restrict antipodal negation to the south/north intersection, then forget the
order by the accepted swap map.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L95) (retained native site: line 95).

### SphereTopology.sphere2PunctureIntersectionAntipodalInduced_eq

```lean
theorem SphereTopology.sphere2PunctureIntersectionAntipodalInduced_eq : sphere2PunctureIntersectionAntipodalInduced = TopCat.ofHom sphere2PunctureIntersectionAntipodal
```

The induced sign-free endomorphism is literally antipodal negation.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L109) (retained native site: line 109).

### SphereTopology.sphere2PunctureIntersectionAntipodal_coe

```lean
theorem SphereTopology.sphere2PunctureIntersectionAntipodal_coe (p : sphere2PunctureIntersection) : ↑↑(sphere2PunctureIntersectionAntipodal p) = -↑↑p
```

**API note (not a source docstring):** After forgetting the puncture and sphere subtype proofs, the antipodal map on the intersection is ordinary vector negation in E3.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L116) (retained native site: line 116).

### SphereTopology.sphere2PunctureIntersectionAntipodal_comp

```lean
theorem SphereTopology.sphere2PunctureIntersectionAntipodal_comp : sphere2PunctureIntersectionAntipodal.comp sphere2PunctureIntersectionAntipodal = ContinuousMap.id sphere2PunctureIntersection
```

Antipodal negation is involutive on the literal puncture intersection.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L123) (retained native site: line 123).

### SphereTopology.sphere2EquatorAntipodalPoint

```lean
noncomputable def SphereTopology.sphere2EquatorAntipodalPoint (p : sphere2Equator) : sphere2Equator
```

Antipodal negation on the literal equator.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L133) (retained native site: line 133).

### SphereTopology.sphere2EquatorAntipodal

```lean
noncomputable def SphereTopology.sphere2EquatorAntipodal : C(sphere2Equator, sphere2Equator)
```

Continuous antipodal negation on the literal equator, preserving its zero
third coordinate.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L137) (retained native site: line 137).

### SphereTopology.sphere2EquatorAntipodal_coe

```lean
theorem SphereTopology.sphere2EquatorAntipodal_coe (p : sphere2Equator) : ↑↑(sphere2EquatorAntipodal p) = -↑↑p
```

**API note (not a source docstring):** After forgetting the equator and sphere subtype proofs, equatorial antipodal negation is ordinary vector negation in E3.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L144) (retained native site: line 144).

### SphereTopology.sphere2EquatorHalfTurnVector

```lean
noncomputable def SphereTopology.sphere2EquatorHalfTurnVector (t : ↑unitInterval) (p : sphere2Equator) : E3
```

Rotate an equator point through angle `π t` in its first two
coordinates, keeping the third coordinate fixed at zero.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L149) (retained native site: line 149).

### SphereTopology.sphere2EquatorHalfTurnVector_first

```lean
theorem SphereTopology.sphere2EquatorHalfTurnVector_first (t : ↑unitInterval) (p : sphere2Equator) : (sphere2EquatorHalfTurnVector t p).ofLp 0 = Real.cos (Real.pi * ↑t) * (↑↑p).ofLp 0 - Real.sin (Real.pi * ↑t) * (↑↑p).ofLp 1
```

**API note (not a source docstring):** The first coordinate of the equatorial half-turn is cos(pi*t)*x - sin(pi*t)*y. Together with the next coordinate law this specifies the rotation's orientation.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L160) (retained native site: line 160).

### SphereTopology.sphere2EquatorHalfTurnVector_second

```lean
theorem SphereTopology.sphere2EquatorHalfTurnVector_second (t : ↑unitInterval) (p : sphere2Equator) : (sphere2EquatorHalfTurnVector t p).ofLp 1 = Real.sin (Real.pi * ↑t) * (↑↑p).ofLp 0 + Real.cos (Real.pi * ↑t) * (↑↑p).ofLp 1
```

**API note (not a source docstring):** The second coordinate of the equatorial half-turn is sin(pi*t)*x + cos(pi*t)*y, with the same unit-interval time parameter.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L168) (retained native site: line 168).

### SphereTopology.sphere2EquatorHalfTurnVector_third

```lean
theorem SphereTopology.sphere2EquatorHalfTurnVector_third (t : ↑unitInterval) (p : sphere2Equator) : (sphere2EquatorHalfTurnVector t p).ofLp 2 = 0
```

**API note (not a source docstring):** The equatorial half-turn has third coordinate zero at every time, so it remains in the equatorial plane.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L176) (retained native site: line 176).

### SphereTopology.sphere2EquatorHalfTurnVector_norm

```lean
theorem SphereTopology.sphere2EquatorHalfTurnVector_norm (t : ↑unitInterval) (p : sphere2Equator) : ‖sphere2EquatorHalfTurnVector t p‖ = 1
```

**API note (not a source docstring):** The half-turn preserves unit norm for an equator input. The trigonometric identity cos squared plus sin squared equals one supplies sphere membership.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L182) (retained native site: line 182).

### SphereTopology.sphere2EquatorHalfTurnPoint

```lean
noncomputable def SphereTopology.sphere2EquatorHalfTurnPoint (t : ↑unitInterval) (p : sphere2Equator) : sphere2Equator
```

The equatorial half-turn as a point of the literal equator.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L196) (retained native site: line 196).

### SphereTopology.continuous_sphere2EquatorHalfTurnPoint

```lean
theorem SphereTopology.continuous_sphere2EquatorHalfTurnPoint : Continuous fun (q : ↑unitInterval × sphere2Equator) => sphere2EquatorHalfTurnPoint q.1 q.2
```

**API note (not a source docstring):** The equatorial half-turn is jointly continuous in its time parameter and equator point, as a map into the equator subtype.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L203) (retained native site: line 203).

### SphereTopology.sphere2EquatorHalfTurnMap

```lean
noncomputable def SphereTopology.sphere2EquatorHalfTurnMap : C(↑unitInterval × sphere2Equator, sphere2Equator)
```

The jointly continuous equatorial rotation by angle `π * t`, from the
identity at time zero to antipodal negation at time one. The rotation uses the
ordered first two coordinates and leaves the third coordinate zero.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L212) (retained native site: line 212).

### SphereTopology.sphere2EquatorHalfTurnPoint_zero

```lean
theorem SphereTopology.sphere2EquatorHalfTurnPoint_zero (p : sphere2Equator) : sphere2EquatorHalfTurnPoint 0 p = p
```

**API note (not a source docstring):** At time zero the equatorial rotation is the identity.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L220) (retained native site: line 220).

### SphereTopology.sphere2EquatorHalfTurnPoint_one

```lean
theorem SphereTopology.sphere2EquatorHalfTurnPoint_one (p : sphere2Equator) : sphere2EquatorHalfTurnPoint 1 p = sphere2EquatorAntipodal p
```

**API note (not a source docstring):** At time one the equatorial rotation reaches equatorial antipodal negation. This is a homotopy on the equator, not a homotopy from identity to antipodal on the full two-sphere.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L229) (retained native site: line 229).

### SphereTopology.sphere2EquatorHalfTurnHomotopy

```lean
noncomputable def SphereTopology.sphere2EquatorHalfTurnHomotopy : (ContinuousMap.id sphere2Equator).Homotopy sphere2EquatorAntipodal
```

The explicit equatorial half-turn from the identity to antipodal
negation.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L240) (retained native site: line 240).

### SphereTopology.sphere2PunctureIntersectionLinearVector_antipodal

```lean
theorem SphereTopology.sphere2PunctureIntersectionLinearVector_antipodal (t : ↑unitInterval) (p : sphere2PunctureIntersection) : sphere2PunctureIntersectionLinearVector t (sphere2PunctureIntersectionAntipodal p) = -sphere2PunctureIntersectionLinearVector t p
```

The accepted radial deformation is equivariant for antipodal negation at
the unnormalized-vector level.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L248) (retained native site: line 248).

### SphereTopology.sphere2PunctureIntersectionRadialPoint_antipodal

```lean
theorem SphereTopology.sphere2PunctureIntersectionRadialPoint_antipodal (t : ↑unitInterval) (p : sphere2PunctureIntersection) : sphere2PunctureIntersectionRadialPoint t (sphere2PunctureIntersectionAntipodal p) = sphere2PunctureIntersectionAntipodal (sphere2PunctureIntersectionRadialPoint t p)
```

The accepted normalized radial deformation commutes with antipodal
negation.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L262) (retained native site: line 262).

### SphereTopology.sphere2PunctureIntersectionToEquator_antipodal

```lean
theorem SphereTopology.sphere2PunctureIntersectionToEquator_antipodal (p : sphere2PunctureIntersection) : sphere2PunctureIntersectionToEquator (sphere2PunctureIntersectionAntipodal p) = sphere2EquatorAntipodal (sphere2PunctureIntersectionToEquator p)
```

Equatorial projection commutes with antipodal negation.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L280) (retained native site: line 280).

### SphereTopology.sphere2EquatorToPunctureIntersection_antipodal

```lean
theorem SphereTopology.sphere2EquatorToPunctureIntersection_antipodal (p : sphere2Equator) : sphere2EquatorToPunctureIntersection (sphere2EquatorAntipodal p) = sphere2PunctureIntersectionAntipodal (sphere2EquatorToPunctureIntersection p)
```

Equator inclusion commutes with antipodal negation.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L298) (retained native site: line 298).

### SphereTopology.sphere2PunctureIntersectionAntipodal_projection_eq

```lean
theorem SphereTopology.sphere2PunctureIntersectionAntipodal_projection_eq : sphere2PunctureIntersectionAntipodal.comp (sphere2EquatorToPunctureIntersection.comp sphere2PunctureIntersectionToEquator) = sphere2EquatorToPunctureIntersection.comp (sphere2EquatorAntipodal.comp sphere2PunctureIntersectionToEquator)
```

**API note (not a source docstring):** Applying antipodal negation after equatorial projection and re-inclusion agrees with projection, equatorial antipodal negation and re-inclusion. This identity is used to splice the equatorial half-turn with the radial deformation on the puncture intersection.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L309) (retained native site: line 309).

### SphereTopology.sphere2PunctureIntersectionAntipodal_homotopic_id

```lean
theorem SphereTopology.sphere2PunctureIntersectionAntipodal_homotopic_id : sphere2PunctureIntersectionAntipodal.Homotopic (ContinuousMap.id sphere2PunctureIntersection)
```

The sign-free antipodal endomorphism of the literal puncture intersection
is homotopic to the identity.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L320) (retained native site: line 320).

### SphereTopology.sphere2PunctureIntersectionAntipodal_homology_eq_id

```lean
theorem SphereTopology.sphere2PunctureIntersectionAntipodal_homology_eq_id (n : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (AlgebraicTopology.integralSingularChainMap (AlgebraicTopology.twoOpenIntersectionMap sphere2Antipodal sphere2NorthPunctured sphere2SouthPunctured sphere2SouthPunctured sphere2NorthPunctured sphere2Antipodal_mapsTo_north_south sphere2Antipodal_mapsTo_south_north)) n) (HomologicalComplex.homologyMap (AlgebraicTopology.integralSingularChainMap (AlgebraicTopology.twoOpenIntersectionSwapMap sphere2SouthPunctured sphere2NorthPunctured)) n) = CategoryTheory.CategoryStruct.id (HomologicalComplex.homology (AlgebraicTopology.integralSingularChains ((TopologicalSpace.Opens.toTopCat sphere2).obj (sphere2NorthPunctured ⊓ sphere2SouthPunctured))) n)
```

On ordinary integral homology, the antipodal restriction followed by the
sign-free intersection swap acts as the identity.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L350) (retained native site: line 350).

### SphereTopology.sphere2MayerVietorisδOne_reversed_isIso

```lean
theorem SphereTopology.sphere2MayerVietorisδOne_reversed_isIso : CategoryTheory.IsIso (AlgebraicTopology.twoOpenMayerVietorisδ sphere2SouthPunctured sphere2NorthPunctured sphere2Punctured_join_reversed 1)
```

The connecting morphism for the reversed south/north cover is an
isomorphism.  This is derived from the accepted north/south isomorphism and
the ordered-cover swap theorem.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L379) (retained native site: line 379).

### SphereTopology.integralSingularHomologyMap_sphere2Antipodal_two

```lean
theorem SphereTopology.integralSingularHomologyMap_sphere2Antipodal_two : HomologicalComplex.homologyMap (AlgebraicTopology.integralSingularChainMap sphere2Antipodal) 2 = -CategoryTheory.CategoryStruct.id (HomologicalComplex.homology (AlgebraicTopology.integralSingularChains sphere2) 2)
```

The literal antipodal map acts by `-1` on ordinary integral second
homology of the literal standard two-sphere.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L414) (retained native site: line 414).

### SphereTopology.reducedSingularHomologyMap_sphere2Antipodal_two

```lean
theorem SphereTopology.reducedSingularHomologyMap_sphere2Antipodal_two : TopCat.reducedSingularHomologyMap sphere2Antipodal 2 = -CategoryTheory.CategoryStruct.id (sphere2.reducedSingularHomology 2)
```

The matching positive-degree reduced integral homology action is `-1`.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L429) (retained native site: line 429).

### SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso_antipodal

```lean
theorem SphereTopology.reducedSingularHomologyTwoSphereTwoIntegerIso_antipodal : CategoryTheory.CategoryStruct.comp reducedSingularHomologyTwoSphereTwoIntegerIso.inv (CategoryTheory.CategoryStruct.comp (TopCat.reducedSingularHomologyMap sphere2Antipodal 2) reducedSingularHomologyTwoSphereTwoIntegerIso.hom) = -CategoryTheory.CategoryStruct.id ↧ℤ
```

In the accepted fixed integer coordinate on reduced `H₂`, the literal
antipodal map is multiplication by `-1`.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L434) (retained native site: line 434).

### SphereTopology.sphere2_id_not_homotopic_antipodal

```lean
theorem SphereTopology.sphere2_id_not_homotopic_antipodal : ¬(ContinuousMap.id ↑sphere2).Homotopic (TopCat.Hom.hom sphere2Antipodal)
```

The identity and literal antipodal self-maps of the standard two-sphere
are not homotopic.

[Source](../SphereTopology/Homology/Singular/SphereAntipodal.lean#L444) (retained native site: line 444).

## SphereTopology.Homology.Singular.Subdivision

Scope: mathematical library leaf.

### Convexity.StdSimplex.affineContinuousMap

```lean
noncomputable def Convexity.StdSimplex.affineContinuousMap {m n : ℕ} (v : Fin (n + 1) → StdSimplex ℝ (Fin (m + 1))) : C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (m + 1)))
```

The continuous affine map specified by the images of the vertices.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L45) (retained native site: line 44).

### Convexity.StdSimplex.affineContinuousMap_single

```lean
theorem Convexity.StdSimplex.affineContinuousMap_single {m n : ℕ} (v : Fin (n + 1) → StdSimplex ℝ (Fin (m + 1))) (i : Fin (n + 1)) : (affineContinuousMap v) (single i) = v i
```

**API note (not a source docstring):** The continuous affine map with prescribed vertices v takes the i-th standard vertex to v(i). Both source and target are real standard simplices, with their dimensions given by n and m.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L76) (retained native site: line 75).

### Convexity.StdSimplex.AffineSimplex

```lean
abbrev Convexity.StdSimplex.AffineSimplex (m n : ℕ) : Type
```

An affine `n`-simplex in the real standard `m`-simplex, specified by its
ordered `n + 1` vertices. The associated affine map is `affineMapMk`.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L84) (retained native site: line 83).

### Convexity.StdSimplex.AffineChain

```lean
abbrev Convexity.StdSimplex.AffineChain (m n : ℕ) : Type
```

Finite integer linear combinations of affine `n`-simplices in the standard
`m`-simplex, represented by finitely supported coefficient functions.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L89) (retained native site: line 88).

### Convexity.StdSimplex.affineSSet

```lean
def Convexity.StdSimplex.affineSSet (m : ℕ) : SSet
```

The simplicial set of ordered tuples of points of the standard `m`-simplex.
Its simplicial operators select or repeat vertices by the given order map.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L93) (retained native site: line 92).

### Convexity.StdSimplex.affineIntegerCoefficients

```lean
abbrev Convexity.StdSimplex.affineIntegerCoefficients : ModuleCat ℤ
```

The integers as a module over themselves, used as coefficients for affine
simplicial chains.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L101) (retained native site: line 100).

### Convexity.StdSimplex.affineChainIso

```lean
noncomputable def Convexity.StdSimplex.affineChainIso (m n : ℕ) : ((affineSSet m).chainComplex affineIntegerCoefficients).X n ≅ ↧(AffineChain m n)
```

Identify the degree-`n` simplicial chain object of `affineSSet m` with
finitely supported integer coefficients on affine `n`-simplices.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L105) (retained native site: line 104).

### Convexity.StdSimplex.affineChainIso_ι

```lean
theorem Convexity.StdSimplex.affineChainIso_ι (m n : ℕ) (a : AffineSimplex m n) : CategoryTheory.CategoryStruct.comp ((affineSSet m).ιChainComplex a) (affineChainIso m n).hom = ModuleCat.ofHom (Finsupp.lsingle a)
```

**API note (not a source docstring):** The simplicial-chain inclusion of an ordered affine simplex, followed by the chain-to-finsupp isomorphism, is the integer-linear singleton map at that simplex. This identifies the coefficient-module inclusion, not only its value at coefficient one.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L113) (retained native site: line 112).

### Convexity.StdSimplex.affineChainIso_ι_assoc

```lean
theorem Convexity.StdSimplex.affineChainIso_ι_assoc (m n : ℕ) (a : AffineSimplex m n) {Z : ModuleCat ℤ} (h : ↧(AffineChain m n) ⟶ Z) : CategoryTheory.CategoryStruct.comp ((affineSSet m).ιChainComplex a) (CategoryTheory.CategoryStruct.comp (affineChainIso m n).hom h) = CategoryTheory.CategoryStruct.comp (ModuleCat.ofHom (Finsupp.lsingle a)) h
```

**API note (not a source docstring):** Generated reassoc form of affineChainIso_ι: the coefficient inclusion and singleton map still agree after any integer-module morphism from the affine-chain coordinate module to Z.

Generated `reassoc` declaration from `Convexity.StdSimplex.affineChainIso_ι`; the source link locates its owner.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L113) (retained native site: line 112).

### Convexity.StdSimplex.affineBoundaryHom

```lean
noncomputable def Convexity.StdSimplex.affineBoundaryHom (m n : ℕ) : ↧(AffineChain m (n + 1)) ⟶ ↧(AffineChain m n)
```

The categorical simplicial differential from degree `n + 1` to degree `n`,
transported through `affineChainIso` to finitely supported affine chains.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L124) (retained native site: line 123).

### Convexity.StdSimplex.AffineSimplex.face

```lean
def Convexity.StdSimplex.AffineSimplex.face {m n : ℕ} (a : AffineSimplex m (n + 1)) (i : Fin (n + 2)) : AffineSimplex m n
```

The `i`th face of an affine simplex, obtained by deleting vertex `i`
and retaining the order of the remaining vertices.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L132) (retained native site: line 131).

### Convexity.StdSimplex.lsingle_comp_affineBoundaryHom

```lean
theorem Convexity.StdSimplex.lsingle_comp_affineBoundaryHom {m n : ℕ} (a : AffineSimplex m (n + 1)) : CategoryTheory.CategoryStruct.comp (ModuleCat.ofHom (Finsupp.lsingle a)) (affineBoundaryHom m n) = ∑ i : Fin (n + 2), (-1) ^ ↑i • ModuleCat.ofHom (Finsupp.lsingle (a.face i))
```

**API note (not a source docstring):** The transported categorical boundary after the singleton inclusion of an affine (n+1)-simplex is the sum of the singleton inclusions of its n-faces, with integer coefficient (-1)^i on the i-th deleted vertex. This is a morphism-level generator formula.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L139) (retained native site: line 138).

### Convexity.StdSimplex.affineBoundaryHom_squared

```lean
theorem Convexity.StdSimplex.affineBoundaryHom_squared (m n : ℕ) : CategoryTheory.CategoryStruct.comp (affineBoundaryHom m (n + 1)) (affineBoundaryHom m n) = 0
```

**API note (not a source docstring):** Two consecutive transported categorical affine-chain differentials compose to zero, from degree n+2 through n+1 to n. This is the chain-complex identity in module-morphism form.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L154) (retained native site: line 153).

### Convexity.StdSimplex.AffineSimplex.cone

```lean
def Convexity.StdSimplex.AffineSimplex.cone {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m n) : AffineSimplex m (n + 1)
```

Cone an affine simplex to the apex `b`, inserting `b` as its first vertex.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L160) (retained native site: line 159).

### Convexity.StdSimplex.AffineSimplex.point

```lean
def Convexity.StdSimplex.AffineSimplex.point {m : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) : AffineSimplex m 0
```

The affine zero-simplex whose unique vertex is `b`.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L165) (retained native site: line 164).

### Convexity.StdSimplex.affineBoundaryGenerator

```lean
noncomputable def Convexity.StdSimplex.affineBoundaryGenerator {m n : ℕ} (a : AffineSimplex m (n + 1)) : AffineChain m n
```

The oriented boundary of one affine simplex: the finite sum of its faces
with coefficient `(-1)^i` on the face obtained by deleting vertex `i`.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L169) (retained native site: line 168).

### Convexity.StdSimplex.affineBoundary

```lean
noncomputable def Convexity.StdSimplex.affineBoundary (m n : ℕ) : AffineChain m (n + 1) →ₗ[ℤ] AffineChain m n
```

Extend the alternating face boundary integer-linearly to affine chains.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L175) (retained native site: line 174).

### Convexity.StdSimplex.affineCone

```lean
noncomputable def Convexity.StdSimplex.affineCone (m n : ℕ) (b : StdSimplex ℝ (Fin (m + 1))) : AffineChain m n →ₗ[ℤ] AffineChain m (n + 1)
```

The integer-linear cone operator on affine chains, prepending the common
apex `b` to each simplex and raising degree by one.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L180) (retained native site: line 179).

### Convexity.StdSimplex.affineAugmentation

```lean
noncomputable def Convexity.StdSimplex.affineAugmentation (m : ℕ) : AffineChain m 0 →ₗ[ℤ] ℤ
```

The augmentation of affine zero-chains, summing their integer coefficients.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L187) (retained native site: line 186).

### Convexity.StdSimplex.affineBoundary_single

```lean
theorem Convexity.StdSimplex.affineBoundary_single {m n : ℕ} (a : AffineSimplex m (n + 1)) : (affineBoundary m n) (Finsupp.single a 1) = affineBoundaryGenerator a
```

**API note (not a source docstring):** The integer-linear affine boundary of a coefficient-one (n+1)-simplex is its explicitly signed alternating face chain affineBoundaryGenerator.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L191) (retained native site: line 190).

### Convexity.StdSimplex.lsingle_comp_affineBoundary

```lean
theorem Convexity.StdSimplex.lsingle_comp_affineBoundary {m n : ℕ} (a : AffineSimplex m (n + 1)) : CategoryTheory.CategoryStruct.comp (ModuleCat.ofHom (Finsupp.lsingle a)) (ModuleCat.ofHom (affineBoundary m n)) = ∑ i : Fin (n + 2), (-1) ^ ↑i • ModuleCat.ofHom (Finsupp.lsingle (a.face i))
```

**API note (not a source docstring):** Composing a simplex's integer-linear singleton inclusion with the explicit affine boundary gives the alternating sum of the singleton inclusions of its faces. The equality covers arbitrary input coefficients through linearity.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L196) (retained native site: line 195).

### Convexity.StdSimplex.affineBoundaryHom_eq

```lean
theorem Convexity.StdSimplex.affineBoundaryHom_eq (m n : ℕ) : affineBoundaryHom m n = ModuleCat.ofHom (affineBoundary m n)
```

**API note (not a source docstring):** The categorical simplicial differential transported by affineChainIso is exactly the module morphism of the explicit finitely supported alternating-face boundary. It reconciles the two boundary presentations in every degree.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L205) (retained native site: line 204).

### Convexity.StdSimplex.affineBoundary_squared

```lean
theorem Convexity.StdSimplex.affineBoundary_squared {m n : ℕ} (c : AffineChain m (n + 2)) : (affineBoundary m n) ((affineBoundary m (n + 1)) c) = 0
```

**API note (not a source docstring):** For every affine integer chain in degree n+2, taking the explicit alternating-face boundary twice gives zero. No cycle hypothesis on the input is needed.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L215) (retained native site: line 214).

### Convexity.StdSimplex.affineCone_single

```lean
theorem Convexity.StdSimplex.affineCone_single {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m n) : (affineCone m n b) (Finsupp.single a 1) = Finsupp.single (AffineSimplex.cone b a) 1
```

**API note (not a source docstring):** The integer-linear cone operator sends a coefficient-one affine simplex to the coefficient-one simplex obtained by prepending the apex b. The degree increases by one.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L221) (retained native site: line 220).

### Convexity.StdSimplex.affineAugmentation_single

```lean
theorem Convexity.StdSimplex.affineAugmentation_single {m : ℕ} (a : AffineSimplex m 0) (z : ℤ) : (affineAugmentation m) (Finsupp.single a z) = z
```

**API note (not a source docstring):** The augmentation of a single affine zero-simplex with integer coefficient z is z. The vertex location does not affect augmentation.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L227) (retained native site: line 226).

### Convexity.StdSimplex.AffineSimplex.face_cone_zero

```lean
theorem Convexity.StdSimplex.AffineSimplex.face_cone_zero {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m n) : (cone b a).face 0 = a
```

**API note (not a source docstring):** Deleting vertex zero from the cone, whose apex is prepended, recovers the original ordered affine simplex. This fixes the positive first-face term in the cone boundary formula.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L232) (retained native site: line 231).

### Convexity.StdSimplex.AffineSimplex.face_cone_one

```lean
theorem Convexity.StdSimplex.AffineSimplex.face_cone_one {m : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m 0) : (cone b a).face 1 = point b
```

**API note (not a source docstring):** For a zero-simplex a, deleting vertex one from its cone to b leaves the zero-simplex at the apex b. This is the other endpoint in the degree-zero cone boundary formula.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L238) (retained native site: line 237).

### Convexity.StdSimplex.AffineSimplex.face_cone_succ

```lean
theorem Convexity.StdSimplex.AffineSimplex.face_cone_succ {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m (n + 1)) (i : Fin (n + 2)) : (cone b a).face i.succ = cone b (a.face i)
```

**API note (not a source docstring):** Deleting vertex i+1 from the cone on a positive-dimensional affine simplex is the cone on the i-th face of the original simplex, with the same prepended apex.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L245) (retained native site: line 244).

### Convexity.StdSimplex.AffineSimplex.comp

```lean
noncomputable def Convexity.StdSimplex.AffineSimplex.comp {m n k : ℕ} (a : AffineSimplex m n) (b : AffineSimplex n k) : AffineSimplex m k
```

Compose affine simplices by applying the affine map determined by `a`
to every vertex of `b`. Thus `b` parametrizes a simplex in the domain of `a`.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L254) (retained native site: line 253).

### Convexity.StdSimplex.AffineSimplex.comp_face

```lean
theorem Convexity.StdSimplex.AffineSimplex.comp_face {m n k : ℕ} (a : AffineSimplex m n) (b : AffineSimplex n (k + 1)) (i : Fin (k + 2)) : (a.comp b).face i = a.comp (b.face i)
```

**API note (not a source docstring):** Affine composition commutes with taking a face in the parameter simplex: deleting a vertex before composition gives the same ordered simplex as deleting it afterward.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L260) (retained native site: line 259).

### Convexity.StdSimplex.AffineSimplex.comp_cone

```lean
theorem Convexity.StdSimplex.AffineSimplex.comp_cone {m n k : ℕ} (a : AffineSimplex m n) (b : AffineSimplex n k) (x : StdSimplex ℝ (Fin (n + 1))) : a.comp (cone x b) = cone ((affineMapMk a) x) (a.comp b)
```

**API note (not a source docstring):** Pushing an affine cone through the affine map of a carries its apex x to affineMapMk a x and its base b to a.comp b. The apex remains the first vertex.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L264) (retained native site: line 263).

### Convexity.StdSimplex.affineBoundary_cone_single

```lean
theorem Convexity.StdSimplex.affineBoundary_cone_single {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m (n + 1)) : (affineBoundary m (n + 1)) ((affineCone m (n + 1) b) (Finsupp.single a 1)) = Finsupp.single a 1 - (affineCone m n b) ((affineBoundary m n) (Finsupp.single a 1))
```

**API note (not a source docstring):** For a coefficient-one affine simplex of positive degree, the boundary of its cone is the original chain minus the cone on its boundary. The degree-zero augmentation correction is handled by separate lemmas.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L270) (retained native site: line 269).

### Convexity.StdSimplex.affineBoundary_cone_degree_zero_single

```lean
theorem Convexity.StdSimplex.affineBoundary_cone_degree_zero_single {m : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m 0) : (affineBoundary m 0) ((affineCone m 0 b) (Finsupp.single a 1)) = Finsupp.single a 1 - Finsupp.single (AffineSimplex.point b) 1
```

**API note (not a source docstring):** The boundary of the cone on a coefficient-one zero-simplex is that point chain minus the coefficient-one point chain at the apex. This records the endpoint sign explicitly.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L285) (retained native site: line 284).

### Convexity.StdSimplex.affineBoundary_cone_degree_zero

```lean
theorem Convexity.StdSimplex.affineBoundary_cone_degree_zero {m : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (c : AffineChain m 0) : (affineBoundary m 0) ((affineCone m 0 b) c) = c - (affineAugmentation m) c • Finsupp.single (AffineSimplex.point b) 1
```

**API note (not a source docstring):** For an arbitrary affine zero-chain c, the boundary of its cone equals c minus its total augmentation times the point chain at the apex. The augmentation term is essential in degree zero.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L295) (retained native site: line 293).

### Convexity.StdSimplex.affineBoundary_cone

```lean
theorem Convexity.StdSimplex.affineBoundary_cone {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (c : AffineChain m (n + 1)) : (affineBoundary m (n + 1)) ((affineCone m (n + 1) b) c) = c - (affineCone m n b) ((affineBoundary m n) c)
```

**API note (not a source docstring):** On affine chains of positive degree, the cone satisfies boundary(cone(c)) = c - cone(boundary(c)). The same fixed apex is used on both cone operators.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L316) (retained native site: line 314).

### Convexity.StdSimplex.AffineSimplex.center

```lean
noncomputable def Convexity.StdSimplex.AffineSimplex.center {m n : ℕ} (a : AffineSimplex m n) : StdSimplex ℝ (Fin (m + 1))
```

The center of an affine simplex, obtained by mapping the domain barycenter
through its affine map; equivalently, the equally weighted average of its vertices.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L330) (retained native site: line 328).

### Convexity.StdSimplex.AffineSimplex.comp_center

```lean
theorem Convexity.StdSimplex.AffineSimplex.comp_center {m n k : ℕ} (a : AffineSimplex m n) (b : AffineSimplex n k) : (a.comp b).center = (affineMapMk a) b.center
```

**API note (not a source docstring):** The center of the affine composite a.comp b is the image under a's affine map of the center of b. Centers are equally weighted affine barycenters, so this is compatibility with affine composition.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L336) (retained native site: line 334).

### Convexity.StdSimplex.mapAffineChain

```lean
noncomputable def Convexity.StdSimplex.mapAffineChain {m n : ℕ} (a : AffineSimplex m n) (k : ℕ) : AffineChain n k →ₗ[ℤ] AffineChain m k
```

Push affine chains forward along the affine map determined by `a`, adding
coefficients when distinct simplices have the same image.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L344) (retained native site: line 342).

### Convexity.StdSimplex.mapAffineChain_single

```lean
theorem Convexity.StdSimplex.mapAffineChain_single {m n k : ℕ} (a : AffineSimplex m n) (b : AffineSimplex n k) : (mapAffineChain a k) (Finsupp.single b 1) = Finsupp.single (a.comp b) 1
```

**API note (not a source docstring):** Pushforward of a coefficient-one affine simplex b along a is the coefficient-one simplex a.comp b. The linear pushforward may add coefficients for coincident images on general chains.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L350) (retained native site: line 348).

### Convexity.StdSimplex.mapAffineChain_cone

```lean
theorem Convexity.StdSimplex.mapAffineChain_cone {m n k : ℕ} (a : AffineSimplex m n) (b : StdSimplex ℝ (Fin (n + 1))) (c : AffineChain n k) : (mapAffineChain a (k + 1)) ((affineCone n k b) c) = (affineCone m k ((affineMapMk a) b)) ((mapAffineChain a k) c)
```

**API note (not a source docstring):** Affine-chain pushforward commutes with coning when the apex is also mapped through the same affine map. The input chain can have arbitrary integer coefficients.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L356) (retained native site: line 354).

### Convexity.StdSimplex.subdivideSimplex

```lean
noncomputable def Convexity.StdSimplex.subdivideSimplex {m : ℕ} (n : ℕ) : AffineSimplex m n → AffineChain m n
```

**Source-inspected correction:** Explicitly noncomputable in the current source; not fresh native output.

Signed barycentric subdivision of an affine simplex. A zero-simplex is
unchanged; in positive degree, cone the subdivided oriented boundary to its center.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L369) (retained native site: line 367).

### Convexity.StdSimplex.affineSubdivision

```lean
noncomputable def Convexity.StdSimplex.affineSubdivision (m n : ℕ) : AffineChain m n →ₗ[ℤ] AffineChain m n
```

Extend signed barycentric subdivision integer-linearly to affine chains.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L378) (retained native site: line 376).

### Convexity.StdSimplex.affineSubdivision_single

```lean
theorem Convexity.StdSimplex.affineSubdivision_single {m n : ℕ} (a : AffineSimplex m n) : (affineSubdivision m n) (Finsupp.single a 1) = subdivideSimplex n a
```

**API note (not a source docstring):** The linear affine subdivision operator on a coefficient-one simplex agrees with the recursively defined signed subdivision subdivideSimplex of that simplex.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L382) (retained native site: line 380).

### Convexity.StdSimplex.subdivideSimplex_zero

```lean
theorem Convexity.StdSimplex.subdivideSimplex_zero {m : ℕ} (a : AffineSimplex m 0) : subdivideSimplex 0 a = Finsupp.single a 1
```

**API note (not a source docstring):** Signed barycentric subdivision leaves an affine zero-simplex unchanged as a coefficient-one chain. This is the base case of the recursive subdivision definition.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L387) (retained native site: line 385).

### Convexity.StdSimplex.subdivideSimplex_succ

```lean
theorem Convexity.StdSimplex.subdivideSimplex_succ {m n : ℕ} (a : AffineSimplex m (n + 1)) : subdivideSimplex (n + 1) a = (affineCone m n a.center) ((affineSubdivision m n) (affineBoundaryGenerator a))
```

**API note (not a source docstring):** Subdivision of a positive-dimensional affine simplex is the cone, with apex its center, on the linear subdivision of its oriented boundary. The integer alternating-face signs are retained.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L391) (retained native site: line 389).

### Convexity.StdSimplex.mapAffineChain_subdivideSimplex

```lean
theorem Convexity.StdSimplex.mapAffineChain_subdivideSimplex {m n k : ℕ} (a : AffineSimplex m n) (b : AffineSimplex n k) : (mapAffineChain a k) (subdivideSimplex k b) = subdivideSimplex k (a.comp b)
```

**API note (not a source docstring):** Signed subdivision of one affine simplex is natural under affine-chain pushforward: subdividing b and then mapping along a equals subdividing a.comp b.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L401) (retained native site: line 399).

### Convexity.StdSimplex.affineAugmentation_subdivide_zero

```lean
theorem Convexity.StdSimplex.affineAugmentation_subdivide_zero {m : ℕ} (a : AffineSimplex m 0) : (affineAugmentation m) (subdivideSimplex 0 a) = 1
```

**API note (not a source docstring):** The augmentation of the subdivision of an affine zero-simplex is one. This declaration retains its pre-simplification registration (simp↓), which is distinct from changing the mathematical statement or deleting the simp rule.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L416) (retained native site: line 414).

### Convexity.StdSimplex.affineAugmentation_affineSubdivision_zero

```lean
theorem Convexity.StdSimplex.affineAugmentation_affineSubdivision_zero {m : ℕ} (c : AffineChain m 0) : (affineAugmentation m) ((affineSubdivision m 0) c) = (affineAugmentation m) c
```

**API note (not a source docstring):** Linear affine subdivision preserves the total augmentation of every zero-chain. Coefficients may be arbitrary integers, not just one.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L421) (retained native site: line 419).

### Convexity.StdSimplex.affineAugmentation_boundaryGenerator_degree_one

```lean
theorem Convexity.StdSimplex.affineAugmentation_boundaryGenerator_degree_one {m : ℕ} (a : AffineSimplex m 1) : (affineAugmentation m) (affineBoundaryGenerator a) = 0
```

**API note (not a source docstring):** The signed boundary of an affine one-simplex has total augmentation zero: its two endpoint coefficients cancel.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L432) (retained native site: line 430).

### Convexity.StdSimplex.affineSubdivision_boundary

```lean
theorem Convexity.StdSimplex.affineSubdivision_boundary (m n : ℕ) (c : AffineChain m (n + 1)) : (affineBoundary m n) ((affineSubdivision m (n + 1)) c) = (affineSubdivision m n) ((affineBoundary m n) c)
```

**API note (not a source docstring):** Affine subdivision commutes with the alternating-face boundary on every positive-degree affine integer chain. This is the chain-map identity, including the case of boundary into degree zero.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L437) (retained native site: line 435).

### Convexity.StdSimplex.homotopySimplex

```lean
noncomputable def Convexity.StdSimplex.homotopySimplex {m : ℕ} (n : ℕ) : AffineSimplex m n → AffineChain m (n + 1)
```

**Source-inspected correction:** Explicitly noncomputable in the current source; not fresh native output.

The degree-raising subdivision homotopy on one affine simplex. It is zero
in degree zero and otherwise cones `a - Sd(a) - H(∂a)` to the center of `a`.
This convention gives `∂H + H∂ = id - Sd`.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L475) (retained native site: line 473).

### Convexity.StdSimplex.affineHomotopy

```lean
noncomputable def Convexity.StdSimplex.affineHomotopy (m n : ℕ) : AffineChain m n →ₗ[ℤ] AffineChain m (n + 1)
```

Extend `homotopySimplex` integer-linearly, giving the degree-raising affine
chain homotopy with boundary identity `∂H + H∂ = id - Sd`.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L486) (retained native site: line 484).

### Convexity.StdSimplex.affineHomotopy_single

```lean
theorem Convexity.StdSimplex.affineHomotopy_single {m n : ℕ} (a : AffineSimplex m n) : (affineHomotopy m n) (Finsupp.single a 1) = homotopySimplex n a
```

**API note (not a source docstring):** The integer-linear affine homotopy sends a coefficient-one simplex to its recursively constructed homotopySimplex chain in the next degree.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L491) (retained native site: line 489).

### Convexity.StdSimplex.homotopySimplex_zero

```lean
theorem Convexity.StdSimplex.homotopySimplex_zero {m : ℕ} (a : AffineSimplex m 0) : homotopySimplex 0 a = 0
```

**API note (not a source docstring):** The affine subdivision homotopy on a zero-simplex is the zero one-chain. Subdivision itself is already the identity in degree zero.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L496) (retained native site: line 494).

### Convexity.StdSimplex.homotopySimplex_succ

```lean
theorem Convexity.StdSimplex.homotopySimplex_succ {m n : ℕ} (a : AffineSimplex m (n + 1)) : homotopySimplex (n + 1) a = (affineCone m (n + 1) a.center) (Finsupp.single a 1 - subdivideSimplex (n + 1) a - (affineHomotopy m n) (affineBoundaryGenerator a))
```

**API note (not a source docstring):** In positive degree the affine homotopy is the cone to the simplex's center on the original simplex minus its subdivision minus the lower-degree homotopy of its boundary. This uses the id - Sd sign convention.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L500) (retained native site: line 498).

### Convexity.StdSimplex.mapAffineChain_homotopySimplex

```lean
theorem Convexity.StdSimplex.mapAffineChain_homotopySimplex {m n k : ℕ} (a : AffineSimplex m n) (b : AffineSimplex n k) : (mapAffineChain a (k + 1)) (homotopySimplex k b) = homotopySimplex k (a.comp b)
```

**API note (not a source docstring):** The affine homotopy of a simplex commutes with affine-chain pushforward, in degree one higher than the input simplex. Its recursive centers and cones are mapped by the same affine map.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L509) (retained native site: line 507).

### Convexity.StdSimplex.affineHomotopy_degree_zero

```lean
theorem Convexity.StdSimplex.affineHomotopy_degree_zero (m : ℕ) (c : AffineChain m 0) : (affineBoundary m 0) ((affineHomotopy m 0) c) = c - (affineSubdivision m 0) c
```

**API note (not a source docstring):** In degree zero, the boundary of the affine homotopy is c minus the subdivision of c. No negative-degree boundary/homotopy term is introduced.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L527) (retained native site: line 525).

### Convexity.StdSimplex.affineHomotopy_boundary

```lean
theorem Convexity.StdSimplex.affineHomotopy_boundary (m n : ℕ) (c : AffineChain m (n + 1)) : (affineBoundary m (n + 1)) ((affineHomotopy m (n + 1)) c) + (affineHomotopy m n) ((affineBoundary m n) c) = c - (affineSubdivision m (n + 1)) c
```

**API note (not a source docstring):** For every positive-degree affine integer chain, boundary(H(c)) + H(boundary(c)) = c - Sd(c). This gives the homotopy between the identity and signed affine subdivision, in that order.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L539) (retained native site: line 537).

### Convexity.StdSimplex.stdSimplexMetricSpace

```lean
noncomputable def Convexity.StdSimplex.stdSimplexMetricSpace (M : Type u_1) [Fintype M] : MetricSpace (StdSimplex ℝ M)
```

The metric pulled back from the finite real weight-function space along the
standard simplex's weight embedding, with its existing topology.

Source registration: **local instance**, not a globally registered instance.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L600) (retained native site: line 599).

### Convexity.StdSimplex.stdSimplex_dist_eq_weights

```lean
theorem Convexity.StdSimplex.stdSimplex_dist_eq_weights {M : Type u_1} [Fintype M] (x y : StdSimplex ℝ M) : dist x y = dist ⇑x.weights ⇑y.weights
```

**API note (not a source docstring):** For the file's locally installed metric on the real standard simplex of a finite type, distance is exactly distance between the real weight functions. This fixes the metric used in all subsequent diameter estimates.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L607) (retained native site: line 606).

### Convexity.StdSimplex.stdSimplexIsConvexDist

```lean
theorem Convexity.StdSimplex.stdSimplexIsConvexDist (M : Type u_1) [Fintype M] : IsConvexDist (StdSimplex ℝ M)
```

**API note (not a source docstring):** The weight-induced metric on the real standard simplex of a finite type has convex distance. The source registers this named instance locally; the native theorem display does not mean the instance is globally registered for downstream typeclass search.

Source registration: **local instance**, not a globally registered instance.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L610) (retained native site: line 609).

### Convexity.StdSimplex.AffineSimplex.vertexDiameter

```lean
noncomputable def Convexity.StdSimplex.AffineSimplex.vertexDiameter {m n : ℕ} (a : AffineSimplex m n) : ℝ
```

The diameter of the finite set of vertices, using the metric pulled back
from the standard simplex's real weight functions.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L623) (retained native site: line 622).

### Convexity.StdSimplex.AffineSimplex.vertexDiameter_nonneg

```lean
theorem Convexity.StdSimplex.AffineSimplex.vertexDiameter_nonneg {m n : ℕ} (a : AffineSimplex m n) : 0 ≤ a.vertexDiameter
```

**API note (not a source docstring):** The diameter of the finite vertex set of any affine simplex is nonnegative, using the file's metric induced by real weight functions.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L628) (retained native site: line 627).

### Convexity.StdSimplex.AffineSimplex.dist_le_vertexDiameter

```lean
theorem Convexity.StdSimplex.AffineSimplex.dist_le_vertexDiameter {m n : ℕ} (a : AffineSimplex m n) (i j : Fin (n + 1)) : dist (a i) (a j) ≤ a.vertexDiameter
```

**API note (not a source docstring):** The distance between any two specified vertices is at most the diameter of the simplex's finite vertex set. Repeated vertices and degenerate simplices are permitted.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L631) (retained native site: line 630).

### Convexity.StdSimplex.AffineSimplex.dist_center_vertex

```lean
theorem Convexity.StdSimplex.AffineSimplex.dist_center_vertex {m n : ℕ} (a : AffineSimplex m n) (i : Fin (n + 1)) : dist a.center (a i) ≤ ↑n / (↑n + 1) * a.vertexDiameter
```

**API note (not a source docstring):** For an affine n-simplex, the distance from its equally weighted center to any vertex is at most n/(n+1) times its vertex diameter. This also covers n = 0, where both sides vanish.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L635) (retained native site: line 634).

### Convexity.StdSimplex.AffineSimplex.dist_center_affineMapMk

```lean
theorem Convexity.StdSimplex.AffineSimplex.dist_center_affineMapMk {m n k : ℕ} (a : AffineSimplex m n) (x : StdSimplex ℝ (Fin (k + 1))) (v : Fin (k + 1) → Fin (n + 1)) : dist a.center ((affineMapMk (a ∘ v)) x) ≤ ↑n / (↑n + 1) * a.vertexDiameter
```

**API note (not a source docstring):** The center-to-point bound n/(n+1) times the vertex diameter holds for any affine combination of vertices chosen by v. The index map v need not be injective or preserve order.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L661) (retained native site: line 660).

### Convexity.StdSimplex.exists_mem_support_of_mem_support_sum

```lean
theorem Convexity.StdSimplex.exists_mem_support_of_mem_support_sum {α : Type u_1} {β : Type u_2} [Fintype β] (c : β → α →₀ ℤ) {a : α} (ha : a ∈ (∑ i : β, c i).support) : ∃ (i : β), a ∈ (c i).support
```

**Source-inspected correction:** The unused DecidableEq binder was removed; explicit positional or named-class clients may need adjustment. This is not fresh native output.

**API note (not a source docstring):** A nonzero coefficient in a finite sum of integer-valued finitely supported functions must occur in the support of at least one summand. The converse need not hold because coefficients can cancel.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L680) (retained native site: line 679).

### Convexity.StdSimplex.affineCone_eq_mapDomain

```lean
theorem Convexity.StdSimplex.affineCone_eq_mapDomain {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (c : AffineChain m n) : (affineCone m n b) c = Finsupp.mapDomain (AffineSimplex.cone b) c
```

**API note (not a source docstring):** Coning an affine chain is the finitely supported mapDomain along the function that prepends the fixed apex. This identifies the linear cone with coefficient-collecting pushforward.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L688) (retained native site: line 686).

### Convexity.StdSimplex.mem_support_affineCone

```lean
theorem Convexity.StdSimplex.mem_support_affineCone {m n : ℕ} (b : StdSimplex ℝ (Fin (m + 1))) (c : AffineChain m n) {a : AffineSimplex m (n + 1)} (ha : a ∈ ((affineCone m n b) c).support) : ∃ a' ∈ c.support, a = AffineSimplex.cone b a'
```

**API note (not a source docstring):** Every simplex with nonzero coefficient in a coned affine chain is the cone on some simplex in the original support, with the same apex. This is an existence implication, not an asserted equality of support sets.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L700) (retained native site: line 698).

### Convexity.StdSimplex.AffineSimplex.VerticesIn

```lean
def Convexity.StdSimplex.AffineSimplex.VerticesIn {m n k : ℕ} (a : AffineSimplex m n) (b : AffineSimplex m k) : Prop
```

Every vertex of `b` lies in the affine image of `a`. Such a vertex may be
an interior point of that image; it need not equal one of the vertices of `a`.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L710) (retained native site: line 708).

### Convexity.StdSimplex.AffineSimplex.verticesIn_self

```lean
theorem Convexity.StdSimplex.AffineSimplex.verticesIn_self {m n : ℕ} (a : AffineSimplex m n) : a.VerticesIn a
```

**API note (not a source docstring):** Every vertex of an affine simplex lies in its own affine image, witnessed by the corresponding standard vertex. This uses the VerticesIn predicate's affine-image meaning.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L716) (retained native site: line 714).

### Convexity.StdSimplex.AffineSimplex.VerticesIn.trans_face

```lean
theorem Convexity.StdSimplex.AffineSimplex.VerticesIn.trans_face {m n k : ℕ} (a : AffineSimplex m (n + 1)) (i : Fin (n + 2)) {b : AffineSimplex m k} (h : (a.face i).VerticesIn b) : a.VerticesIn b
```

**API note (not a source docstring):** If all vertices of b lie in the affine image of a face of a, then they also lie in the affine image of a. The face inclusion supplies the domain reparametrization.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L721) (retained native site: line 719).

### Convexity.StdSimplex.AffineSimplex.VerticesIn.cone

```lean
theorem Convexity.StdSimplex.AffineSimplex.VerticesIn.cone {m n k : ℕ} (a : AffineSimplex m n) {b : AffineSimplex m k} (h : a.VerticesIn b) : a.VerticesIn (AffineSimplex.cone a.center b)
```

**API note (not a source docstring):** If b has all vertices in the affine image of a, coning b to the center of a preserves that property. The new apex is itself an affine combination of a's vertices.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L730) (retained native site: line 728).

### Convexity.StdSimplex.subdivideSimplex_support_verticesIn

```lean
theorem Convexity.StdSimplex.subdivideSimplex_support_verticesIn {m n : ℕ} (a : AffineSimplex m n) {b : AffineSimplex m n} (hb : b ∈ (subdivideSimplex n a).support) : a.VerticesIn b
```

**API note (not a source docstring):** Every simplex in the support of the signed subdivision of a has all its vertices in the affine image of a. The vertices need not be original vertices of a.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L738) (retained native site: line 736).

### Convexity.StdSimplex.homotopySimplex_support_verticesIn

```lean
theorem Convexity.StdSimplex.homotopySimplex_support_verticesIn {m n : ℕ} (a : AffineSimplex m n) {b : AffineSimplex m (n + 1)} (hb : b ∈ (homotopySimplex n a).support) : a.VerticesIn b
```

**API note (not a source docstring):** Every next-degree simplex in the support of the affine homotopy of a has all its vertices in the affine image of a. The statement is vacuous in degree zero, where the homotopy is zero.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L755) (retained native site: line 753).

### Convexity.StdSimplex.AffineSimplex.reparametrization

```lean
noncomputable def Convexity.StdSimplex.AffineSimplex.reparametrization {m n k : ℕ} (a : AffineSimplex m n) {b : AffineSimplex m k} (h : a.VerticesIn b) : AffineSimplex n k
```

Choose preimages of the vertices of `b` in the domain of `a`, using
`a.VerticesIn b`. Composing this simplex with `a` recovers `b`; no uniqueness
or invertibility of the chosen parametrization is asserted.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L775) (retained native site: line 773).

### Convexity.StdSimplex.AffineSimplex.comp_reparametrization

```lean
theorem Convexity.StdSimplex.AffineSimplex.comp_reparametrization {m n k : ℕ} (a : AffineSimplex m n) {b : AffineSimplex m k} (h : a.VerticesIn b) : a.comp (a.reparametrization h) = b
```

**API note (not a source docstring):** Under a.VerticesIn b, composing a with the classically chosen vertex-preimage simplex reconstructs b exactly. No uniqueness or injectivity of the chosen reparametrization is asserted.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L783) (retained native site: line 781).

### Convexity.StdSimplex.AffineSimplex.range_affineContinuousMap_subset

```lean
theorem Convexity.StdSimplex.AffineSimplex.range_affineContinuousMap_subset {m n k : ℕ} (a : AffineSimplex m n) {b : AffineSimplex m k} (h : a.VerticesIn b) : Set.range ⇑(affineContinuousMap b) ⊆ Set.range ⇑(affineContinuousMap a)
```

**API note (not a source docstring):** If every vertex of b lies in the affine image of a, the entire continuous affine image of b lies in that of a. The conclusion concerns all points, not only vertices.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L789) (retained native site: line 787).

### Convexity.StdSimplex.AffineSimplex.vertexDiameter_face_le

```lean
theorem Convexity.StdSimplex.AffineSimplex.vertexDiameter_face_le {m n : ℕ} (a : AffineSimplex m (n + 1)) (i : Fin (n + 2)) : (a.face i).vertexDiameter ≤ a.vertexDiameter
```

**API note (not a source docstring):** Deleting a vertex cannot increase the vertex diameter of an affine simplex. This uses inclusion of the finite vertex sets and does not require a nondegenerate simplex.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L800) (retained native site: line 798).

### Convexity.StdSimplex.AffineSimplex.vertexDiameter_cone_le

```lean
theorem Convexity.StdSimplex.AffineSimplex.vertexDiameter_cone_le {m n : ℕ} (a : AffineSimplex m (n + 1)) (i : Fin (n + 2)) (b : AffineSimplex m n) (hvertices : (a.face i).VerticesIn b) (hdiam : b.vertexDiameter ≤ ↑(n + 1) / (↑n + 2) * a.vertexDiameter) : (cone a.center b).vertexDiameter ≤ ↑(n + 1) / (↑n + 2) * a.vertexDiameter
```

**API note (not a source docstring):** Coning b to the center of an affine (n+1)-simplex a preserves the bound (n+1)/(n+2) times a's vertex diameter when b lies in the affine image of a specified face and already satisfies that bound. Both hypotheses are required.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L807) (retained native site: line 805).

### Convexity.StdSimplex.subdivideSimplex_support_vertexDiameter_le

```lean
theorem Convexity.StdSimplex.subdivideSimplex_support_vertexDiameter_le {m n : ℕ} (a : AffineSimplex m n) {b : AffineSimplex m n} (hb : b ∈ (subdivideSimplex n a).support) : b.vertexDiameter ≤ ↑n / (↑n + 1) * a.vertexDiameter
```

**API note (not a source docstring):** Each simplex surviving in the signed subdivision of an affine n-simplex has vertex diameter at most n/(n+1) times the original vertex diameter. The bound includes degenerate and zero-dimensional cases.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L842) (retained native site: line 840).

### Convexity.StdSimplex.mem_support_affineSubdivision

```lean
theorem Convexity.StdSimplex.mem_support_affineSubdivision {m n : ℕ} (c : AffineChain m n) {b : AffineSimplex m n} (hb : b ∈ ((affineSubdivision m n) c).support) : ∃ a ∈ c.support, b ∈ (subdivideSimplex n a).support
```

**API note (not a source docstring):** A simplex in the support of the subdivision of a finite affine chain occurs in the subdivision support of some simplex in the original support. The result does not preclude cancellation between different input contributions.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L882) (retained native site: line 880).

### Convexity.StdSimplex.affineSubdivision_iterate_support_vertexDiameter_le

```lean
theorem Convexity.StdSimplex.affineSubdivision_iterate_support_vertexDiameter_le {m n N : ℕ} (c : AffineChain m n) (D : ℝ) (hc : ∀ a ∈ c.support, a.vertexDiameter ≤ D) {b : AffineSimplex m n} (hb : b ∈ ((⇑(affineSubdivision m n))^[N] c).support) : b.vertexDiameter ≤ (↑n / (↑n + 1)) ^ N * D
```

**API note (not a source docstring):** If every simplex in the initial affine-chain support has vertex diameter at most D, each support simplex after N subdivisions has diameter at most (n/(n+1))^N times D. N may be zero; the hypothesis on the original support is explicit.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L896) (retained native site: line 894).

### Convexity.StdSimplex.AffineSimplex.dist_center_affineMapMk_self

```lean
theorem Convexity.StdSimplex.AffineSimplex.dist_center_affineMapMk_self {m n : ℕ} (a : AffineSimplex m n) (x : StdSimplex ℝ (Fin (n + 1))) : dist a.center ((affineMapMk a) x) ≤ ↑n / (↑n + 1) * a.vertexDiameter
```

**API note (not a source docstring):** The distance from the center of an affine n-simplex to any point of its affine image is at most n/(n+1) times the vertex diameter. This is the unreindexed version of the affine-combination estimate.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L915) (retained native site: line 913).

### Convexity.StdSimplex.AffineSimplex.diam_range_affineContinuousMap_le

```lean
theorem Convexity.StdSimplex.AffineSimplex.diam_range_affineContinuousMap_le {m n : ℕ} (a : AffineSimplex m n) : Metric.diam (Set.range ⇑(affineContinuousMap a)) ≤ 2 * a.vertexDiameter
```

**API note (not a source docstring):** The metric diameter of the full affine image is at most twice the vertex diameter. This is the bound actually proved; it does not assert equality or the sharper vertex-diameter bound.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L921) (retained native site: line 919).

### Convexity.StdSimplex.AffineSimplex.standard

```lean
noncomputable def Convexity.StdSimplex.AffineSimplex.standard (n : ℕ) : AffineSimplex n n
```

The standard affine simplex, with its `i`th vertex the `i`th unit weight vector.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L944) (retained native site: line 942).

### Convexity.StdSimplex.exists_affineSubdivision_iterate_diam_lt

```lean
theorem Convexity.StdSimplex.exists_affineSubdivision_iterate_diam_lt {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) : ∃ (N : ℕ), ∀ {b : AffineSimplex n n}, b ∈ ((⇑(affineSubdivision n n))^[N] (Finsupp.single (AffineSimplex.standard n) 1)).support → Metric.diam (Set.range ⇑(affineContinuousMap b)) < ε
```

**API note (not a source docstring):** For positive dimension n and epsilon > 0, some number N of subdivisions makes every support simplex of the standard coefficient-one n-simplex have affine-image diameter less than epsilon. The theorem is existential, not a chosen numerical algorithm for N.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L948) (retained native site: line 946).

### Convexity.StdSimplex.exists_affineSubdivision_iterate_cover_small

```lean
theorem Convexity.StdSimplex.exists_affineSubdivision_iterate_cover_small {X : Type u_1} [TopologicalSpace X] {ι : Type u_2} (U : ι → TopologicalSpace.Opens X) (hU : TopologicalSpace.IsOpenCover U) {n : ℕ} (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) : ∃ (N : ℕ), ∀ {b : AffineSimplex n n}, b ∈ ((⇑(affineSubdivision n n))^[N] (Finsupp.single (AffineSimplex.standard n) 1)).support → ∃ (i : ι), Set.range ⇑(σ.comp (affineContinuousMap b)) ⊆ ↑(U i)
```

**API note (not a source docstring):** Given an open cover of any topological space and one continuous singular simplex, some subdivision of its standard domain has every surviving affine piece mapped into a cover member. The member may depend on the piece; no metric on the target space is assumed.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L982) (retained native site: line 980).

### AlgebraicTopology.SingularChainFinsupp

```lean
abbrev AlgebraicTopology.SingularChainFinsupp (X : TopCat) (n : ℕ) : Type u
```

Finite integer linear combinations of singular `n`-simplices in `X`,
represented as finitely supported functions on its native singular simplicial set.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1022) (retained native site: line 1020).

### AlgebraicTopology.singularFinsuppMap

```lean
noncomputable def AlgebraicTopology.singularFinsuppMap {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) : SingularChainFinsupp X n →ₗ[ℤ] SingularChainFinsupp Y n
```

Postcomposition of finitely supported singular chains by a continuous map.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1027) (retained native site: line 1025).

### AlgebraicTopology.singularFinsuppMap_single

```lean
theorem AlgebraicTopology.singularFinsuppMap_single {X Y : TopCat} (f : X ⟶ Y) {n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) : (singularFinsuppMap f n) (Finsupp.single x 1) = Finsupp.single ((CategoryTheory.ConcreteCategory.hom ((TopCat.toSSet.map f).app (Opposite.op { len := n }))) x) 1
```

**API note (not a source docstring):** Postcomposition of a coefficient-one singular simplex by a continuous map is the coefficient-one image simplex in the target singular set. This is the generator formula for integer-linear singular-chain pushforward.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1032) (retained native site: line 1030).

### AlgebraicTopology.affinePostcompose

```lean
noncomputable def AlgebraicTopology.affinePostcompose {X : TopCat} {n k : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) (a : Convexity.StdSimplex.AffineSimplex n k) : (TopCat.toSSet.obj X).obj (Opposite.op { len := k })
```

Turn an affine `k`-simplex in the standard `n`-simplex into a singular
`k`-simplex in `X`. Despite the name, this precomposes the singular simplex `x`
with the continuous affine map determined by `a`.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1039) (retained native site: line 1037).

### AlgebraicTopology.realizeAffineChain

```lean
noncomputable def AlgebraicTopology.realizeAffineChain {X : TopCat} {n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) (k : ℕ) : Convexity.StdSimplex.AffineChain n k →ₗ[ℤ] SingularChainFinsupp X k
```

Map an affine chain in the domain of a singular simplex `x` to a singular
chain in `X`, adding coefficients whenever the resulting singular simplices coincide.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1048) (retained native site: line 1046).

### AlgebraicTopology.mem_support_realizeAffineChain

```lean
theorem AlgebraicTopology.mem_support_realizeAffineChain {X : TopCat} {n k : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) (c : Convexity.StdSimplex.AffineChain n k) {y : (TopCat.toSSet.obj X).obj (Opposite.op { len := k })} (hy : y ∈ ((realizeAffineChain x k) c).support) : ∃ a ∈ c.support, y = affinePostcompose x a
```

**API note (not a source docstring):** Every singular simplex with nonzero coefficient after realizing an affine chain through x comes from some affine simplex in the original support. Distinct affine pieces may realize to the same singular simplex, so this is only the stated support implication.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1055) (retained native site: line 1053).

### AlgebraicTopology.affinePostcompose_range_subset

```lean
theorem AlgebraicTopology.affinePostcompose_range_subset {X : TopCat} {n k : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) (a : Convexity.StdSimplex.AffineSimplex n k) : Set.range ⇑((X.toSSetObjEquiv (Opposite.op { len := k })) (affinePostcompose x a)) ⊆ Set.range ⇑((X.toSSetObjEquiv (Opposite.op { len := n })) x)
```

**API note (not a source docstring):** Precomposing a singular simplex x with an affine parameter map produces a singular simplex whose range is contained in the range of x. Despite its name, affinePostcompose performs this domain precomposition.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1066) (retained native site: line 1064).

### AlgebraicTopology.realizeAffineChain_single

```lean
theorem AlgebraicTopology.realizeAffineChain_single {X : TopCat} {n k : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) (a : Convexity.StdSimplex.AffineSimplex n k) : (realizeAffineChain x k) (Finsupp.single a 1) = Finsupp.single (affinePostcompose x a) 1
```

**API note (not a source docstring):** Realizing the coefficient-one affine simplex a through a singular simplex x gives the coefficient-one singular simplex affinePostcompose x a. The resulting degree is the dimension of a.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1075) (retained native site: line 1073).

### AlgebraicTopology.affinePostcompose_naturality

```lean
theorem AlgebraicTopology.affinePostcompose_naturality {X Y : TopCat} (f : X ⟶ Y) {n k : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) (a : Convexity.StdSimplex.AffineSimplex n k) : (CategoryTheory.ConcreteCategory.hom ((TopCat.toSSet.map f).app (Opposite.op { len := k }))) (affinePostcompose x a) = affinePostcompose ((CategoryTheory.ConcreteCategory.hom ((TopCat.toSSet.map f).app (Opposite.op { len := n }))) x) a
```

**API note (not a source docstring):** Continuous postcomposition on the target space commutes with the affine domain precomposition used to form affinePostcompose. Both operations give the same resulting singular simplex.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1082) (retained native site: line 1080).

### AlgebraicTopology.singularFinsuppMap_realizeAffineChain

```lean
theorem AlgebraicTopology.singularFinsuppMap_realizeAffineChain {X Y : TopCat} (f : X ⟶ Y) {n k : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) (c : Convexity.StdSimplex.AffineChain n k) : (singularFinsuppMap f k) ((realizeAffineChain x k) c) = (realizeAffineChain ((CategoryTheory.ConcreteCategory.hom ((TopCat.toSSet.map f).app (Opposite.op { len := n }))) x) k) c
```

**API note (not a source docstring):** Realization of an affine chain is natural under continuous maps of target spaces: postcompose the realized chain, or postcompose the outer singular simplex before realization. The equality holds for arbitrary integer coefficients.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1088) (retained native site: line 1086).

### AlgebraicTopology.affinePostcompose_standard

```lean
theorem AlgebraicTopology.affinePostcompose_standard {X : TopCat} {n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) : affinePostcompose x (Convexity.StdSimplex.AffineSimplex.standard n) = x
```

**API note (not a source docstring):** Precomposing a singular simplex with the standard affine simplex leaves it unchanged. The standard affine map is the identity on the domain simplex.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1101) (retained native site: line 1099).

### AlgebraicTopology.affinePostcompose_face

```lean
theorem AlgebraicTopology.affinePostcompose_face {X : TopCat} {n k : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) (a : Convexity.StdSimplex.AffineSimplex n (k + 1)) (i : Fin (k + 2)) : affinePostcompose x (a.face i) = (CategoryTheory.ConcreteCategory.hom (CategoryTheory.SimplicialObject.δ (TopCat.toSSet.obj X) i)) (affinePostcompose x a)
```

**API note (not a source docstring):** Realizing a face of the affine parameter simplex gives the corresponding singular face of the realized simplex. The same deleted-vertex index is used on both sides.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1112) (retained native site: line 1110).

### AlgebraicTopology.affinePostcompose_comp

```lean
theorem AlgebraicTopology.affinePostcompose_comp {X : TopCat} {m n k : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := m })) (a : Convexity.StdSimplex.AffineSimplex m n) (b : Convexity.StdSimplex.AffineSimplex n k) : affinePostcompose x (a.comp b) = affinePostcompose (affinePostcompose x a) b
```

**API note (not a source docstring):** Realization of an affine composite agrees with successive affine precompositions of the singular simplex. The dimension indices record the two domain changes.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1127) (retained native site: line 1125).

### AlgebraicTopology.realizeAffineChain_mapAffineChain

```lean
theorem AlgebraicTopology.realizeAffineChain_mapAffineChain {X : TopCat} {m n k : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := m })) (a : Convexity.StdSimplex.AffineSimplex m n) (c : Convexity.StdSimplex.AffineChain n k) : (realizeAffineChain x k) ((Convexity.StdSimplex.mapAffineChain a k) c) = (realizeAffineChain (affinePostcompose x a) k) c
```

**API note (not a source docstring):** Realizing a chain after affine-chain pushforward along a equals realizing it directly through the singular simplex affinePostcompose x a. This is the linear-chain form of compatibility with affine composition.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1140) (retained native site: line 1138).

### AlgebraicTopology.singularFinsuppBoundary

```lean
noncomputable def AlgebraicTopology.singularFinsuppBoundary (X : TopCat) (n : ℕ) : SingularChainFinsupp X (n + 1) →ₗ[ℤ] SingularChainFinsupp X n
```

The integer-linear singular boundary in finitely supported coordinates,
with coefficient `(-1)^i` on the `i`th face of each simplex.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1154) (retained native site: line 1152).

### AlgebraicTopology.singularFinsuppBoundary_single

```lean
theorem AlgebraicTopology.singularFinsuppBoundary_single {X : TopCat} {n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n + 1 })) : (singularFinsuppBoundary X n) (Finsupp.single x 1) = ∑ i : Fin (n + 2), (-1) ^ ↑i • Finsupp.single ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.SimplicialObject.δ (TopCat.toSSet.obj X) i)) x) 1
```

**API note (not a source docstring):** The boundary of a coefficient-one singular (n+1)-simplex is the sum of its n-faces with integer coefficient (-1)^i at face i. This fixes the orientation convention for the finitely supported singular chains.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1162) (retained native site: line 1160).

### AlgebraicTopology.singularFinsuppBoundary_realizeAffineChain

```lean
theorem AlgebraicTopology.singularFinsuppBoundary_realizeAffineChain {X : TopCat} {n k : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) (c : Convexity.StdSimplex.AffineChain n (k + 1)) : (singularFinsuppBoundary X k) ((realizeAffineChain x (k + 1)) c) = (realizeAffineChain x k) ((Convexity.StdSimplex.affineBoundary n k) c)
```

**API note (not a source docstring):** Realization commutes with boundary: the singular boundary of a realized affine chain is the realization of its affine boundary. Both differentials lower degree by one with the same alternating signs.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1170) (retained native site: line 1168).

### AlgebraicTopology.AffineSimplex.comp_standard

```lean
theorem AlgebraicTopology.AffineSimplex.comp_standard {m n : ℕ} (a : Convexity.StdSimplex.AffineSimplex m n) : a.comp (Convexity.StdSimplex.AffineSimplex.standard n) = a
```

**API note (not a source docstring):** Composing an affine simplex with the standard affine simplex of its domain gives the original affine simplex. The actual declaration is in AlgebraicTopology.AffineSimplex; this note does not rename it into Convexity.StdSimplex.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1187) (retained native site: line 1185).

### AlgebraicTopology.realize_subdivide_face_standard

```lean
theorem AlgebraicTopology.realize_subdivide_face_standard {X : TopCat} {n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n + 1 })) (i : Fin (n + 2)) : (realizeAffineChain x n) (Convexity.StdSimplex.subdivideSimplex n ((Convexity.StdSimplex.AffineSimplex.standard (n + 1)).face i)) = (realizeAffineChain ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.SimplicialObject.δ (TopCat.toSSet.obj X) i)) x) n) (Convexity.StdSimplex.subdivideSimplex n (Convexity.StdSimplex.AffineSimplex.standard n))
```

**API note (not a source docstring):** Subdividing a face of the standard domain simplex and realizing through x agrees with realizing the subdivision of the lower-dimensional standard simplex through the corresponding singular face of x. The result has degree n.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1192) (retained native site: line 1190).

### AlgebraicTopology.realize_homotopy_face_standard

```lean
theorem AlgebraicTopology.realize_homotopy_face_standard {X : TopCat} {n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n + 1 })) (i : Fin (n + 2)) : (realizeAffineChain x (n + 1)) (Convexity.StdSimplex.homotopySimplex n ((Convexity.StdSimplex.AffineSimplex.standard (n + 1)).face i)) = (realizeAffineChain ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.SimplicialObject.δ (TopCat.toSSet.obj X) i)) x) (n + 1)) (Convexity.StdSimplex.homotopySimplex n (Convexity.StdSimplex.AffineSimplex.standard n))
```

**API note (not a source docstring):** Applying the affine homotopy to a standard face and realizing through x agrees with realization through the corresponding singular face of the standard lower-dimensional homotopy. The degree-raising homotopy produces chains of degree n+1.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1207) (retained native site: line 1205).

### AlgebraicTopology.singularSubdivision

```lean
noncomputable def AlgebraicTopology.singularSubdivision (X : TopCat) (n : ℕ) : SingularChainFinsupp X n →ₗ[ℤ] SingularChainFinsupp X n
```

Subdivide each singular simplex by realizing the signed barycentric
subdivision of its standard domain, then extend integer-linearly to chains.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1221) (retained native site: line 1219).

### AlgebraicTopology.singularSubdivisionIterate

```lean
noncomputable def AlgebraicTopology.singularSubdivisionIterate (X : TopCat) (n N : ℕ) : SingularChainFinsupp X n →ₗ[ℤ] SingularChainFinsupp X n
```

**Source-inspected correction:** Explicitly noncomputable in the current source; not fresh native output.

Apply singular subdivision `N` times. The zeroth iterate is the identity
linear map, and each successor composes the preceding iterate with subdivision.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1229) (retained native site: line 1227).

### AlgebraicTopology.singularSubdivisionIterate_zero

```lean
theorem AlgebraicTopology.singularSubdivisionIterate_zero (X : TopCat) (n : ℕ) : singularSubdivisionIterate X n 0 = LinearMap.id
```

**API note (not a source docstring):** Zero iterations of singular subdivision give the identity integer-linear map on chains of the chosen degree. This is distinct from the zero initial value of the iterated homotopy.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1237) (retained native site: line 1235).

### AlgebraicTopology.singularSubdivisionIterate_succ

```lean
theorem AlgebraicTopology.singularSubdivisionIterate_succ (X : TopCat) (n N : ℕ) : singularSubdivisionIterate X n (N + 1) = singularSubdivisionIterate X n N ∘ₗ singularSubdivision X n
```

**API note (not a source docstring):** The (N+1)-fold subdivision map first performs one subdivision and then the N-fold iterate, as expressed by linear-map composition. The chain degree stays fixed.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1241) (retained native site: line 1239).

### AlgebraicTopology.singularSubdivisionIterate_apply

```lean
theorem AlgebraicTopology.singularSubdivisionIterate_apply (X : TopCat) (n N : ℕ) (c : SingularChainFinsupp X n) : (singularSubdivisionIterate X n N) c = (⇑(singularSubdivision X n))^[N] c
```

**API note (not a source docstring):** Applying the recursively defined linear singularSubdivisionIterate equals N-fold function iteration of singularSubdivision on the input chain. This relates the linear-map and function-iterate presentations.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1245) (retained native site: line 1243).

### AlgebraicTopology.singularSubdivision_single

```lean
theorem AlgebraicTopology.singularSubdivision_single {X : TopCat} {n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) : (singularSubdivision X n) (Finsupp.single x 1) = (realizeAffineChain x n) (Convexity.StdSimplex.subdivideSimplex n (Convexity.StdSimplex.AffineSimplex.standard n))
```

**API note (not a source docstring):** Subdivision of a coefficient-one singular simplex is obtained by realizing the signed subdivision of its standard affine domain through that simplex. General chains are treated by integer linearity.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1257) (retained native site: line 1255).

### AlgebraicTopology.singularSubdivision_degree_zero

```lean
theorem AlgebraicTopology.singularSubdivision_degree_zero (X : TopCat) (c : SingularChainFinsupp X 0) : (singularSubdivision X 0) c = c
```

In degree zero barycentric subdivision is the identity.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1265) (retained native site: line 1263).

### AlgebraicTopology.singularSubdivision_naturality

```lean
theorem AlgebraicTopology.singularSubdivision_naturality {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) (c : SingularChainFinsupp X n) : (singularFinsuppMap f n) ((singularSubdivision X n) c) = (singularSubdivision Y n) ((singularFinsuppMap f n) c)
```

Barycentric subdivision commutes with postcomposition of singular chains.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1279) (retained native site: line 1277).

### AlgebraicTopology.mem_support_singularSubdivision

```lean
theorem AlgebraicTopology.mem_support_singularSubdivision {X : TopCat} {n : ℕ} (c : SingularChainFinsupp X n) {y : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })} (hy : y ∈ ((singularSubdivision X n) c).support) : ∃ x ∈ c.support, Set.range ⇑((X.toSSetObjEquiv (Opposite.op { len := n })) y) ⊆ Set.range ⇑((X.toSSetObjEquiv (Opposite.op { len := n })) x)
```

**API note (not a source docstring):** Every simplex in a subdivided chain's support has range contained in the range of some simplex in the original support. This is a local range-control statement and assumes no open cover.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1293) (retained native site: line 1291).

### AlgebraicTopology.singularSubdivision_realizeAffineChain

```lean
theorem AlgebraicTopology.singularSubdivision_realizeAffineChain {X : TopCat} {m n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := m })) (c : Convexity.StdSimplex.AffineChain m n) : (singularSubdivision X n) ((realizeAffineChain x n) c) = (realizeAffineChain x n) ((Convexity.StdSimplex.affineSubdivision m n) c)
```

**API note (not a source docstring):** Singular subdivision of a realized affine chain equals realization of the affine subdivision of that chain. The outer singular simplex is unchanged.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1324) (retained native site: line 1322).

### AlgebraicTopology.singularSubdivision_iterate_single

```lean
theorem AlgebraicTopology.singularSubdivision_iterate_single {X : TopCat} {n N : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) : (⇑(singularSubdivision X n))^[N] (Finsupp.single x 1) = (realizeAffineChain x n) ((⇑(Convexity.StdSimplex.affineSubdivision n n))^[N] (Finsupp.single (Convexity.StdSimplex.AffineSimplex.standard n) 1))
```

**API note (not a source docstring):** N-fold singular subdivision of a coefficient-one singular simplex is realization of N-fold affine subdivision of the coefficient-one standard domain simplex. The equality includes N = 0.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1341) (retained native site: line 1339).

### AlgebraicTopology.exists_singularSubdivision_iterate_cover_small

```lean
theorem AlgebraicTopology.exists_singularSubdivision_iterate_cover_small {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) (hU : TopologicalSpace.IsOpenCover U) {n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) : ∃ (N : ℕ), ∀ {y : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })}, y ∈ ((⇑(singularSubdivision X n))^[N] (Finsupp.single x 1)).support → ∃ (i : ι), Set.range ⇑((X.toSSetObjEquiv (Opposite.op { len := n })) y) ⊆ ↑(U i)
```

**API note (not a source docstring):** For a given singular simplex and an open cover, some subdivision iterate has every support simplex contained in a cover member. The exponent is allowed to depend on the original simplex and the cover.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1354) (retained native site: line 1352).

### AlgebraicTopology.IsCoverSmall

```lean
def AlgebraicTopology.IsCoverSmall {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) {n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) : Prop
```

The range of a singular simplex lies in one member of the family `U`.
This predicate itself does not assume that `U` covers the whole space.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1370) (retained native site: line 1368).

### AlgebraicTopology.isCoverSmall_of_mem_singularSubdivision

```lean
theorem AlgebraicTopology.isCoverSmall_of_mem_singularSubdivision {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) {n : ℕ} {c : SingularChainFinsupp X n} (hc : ∀ x ∈ c.support, IsCoverSmall U x) {y : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })} (hy : y ∈ ((singularSubdivision X n) c).support) : IsCoverSmall U y
```

**API note (not a source docstring):** If every simplex in a chain's support is small in the family U, then every simplex after one subdivision is also small in U. The family need not cover the whole space; range containment suffices.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1377) (retained native site: line 1375).

### AlgebraicTopology.isCoverSmall_of_mem_singularSubdivisionIterate

```lean
theorem AlgebraicTopology.isCoverSmall_of_mem_singularSubdivisionIterate {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) {n N : ℕ} {c : SingularChainFinsupp X n} (hc : ∀ x ∈ c.support, IsCoverSmall U x) {y : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })} (hy : y ∈ ((singularSubdivisionIterate X n N) c).support) : IsCoverSmall U y
```

**API note (not a source docstring):** Smallness of a finite chain in an arbitrary family of opens is preserved by every subdivision iterate. No open-cover hypothesis is required for this preservation result.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1388) (retained native site: line 1386).

### AlgebraicTopology.isCoverSmall_of_mem_singularSubdivisionIterate_of_le

```lean
theorem AlgebraicTopology.isCoverSmall_of_mem_singularSubdivisionIterate_of_le {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) {n N M : ℕ} (hNM : N ≤ M) {c : SingularChainFinsupp X n} (hN : ∀ x ∈ ((singularSubdivisionIterate X n N) c).support, IsCoverSmall U x) {y : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })} (hy : y ∈ ((singularSubdivisionIterate X n M) c).support) : IsCoverSmall U y
```

**API note (not a source docstring):** If all support simplices are small after N subdivisions, they remain small after any M subdivisions with N <= M. U may be any family of opens; this is persistence of an already established smallness condition.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1401) (retained native site: line 1399).

### AlgebraicTopology.exists_singularSubdivisionIterate_chain_cover_small

```lean
theorem AlgebraicTopology.exists_singularSubdivisionIterate_chain_cover_small {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) (hU : TopologicalSpace.IsOpenCover U) {n : ℕ} (c : SingularChainFinsupp X n) : ∃ (N : ℕ), ∀ {y : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })}, y ∈ ((singularSubdivisionIterate X n N) c).support → IsCoverSmall U y
```

**API note (not a source docstring):** For any finitely supported singular integer chain and an actual open cover, there is one exponent N making every simplex in the subdivided chain's support small. N depends on that finite chain and cover, not uniformly on all chains.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1414) (retained native site: line 1412).

### AlgebraicTopology.singularHomotopy

```lean
noncomputable def AlgebraicTopology.singularHomotopy (X : TopCat) (n : ℕ) : SingularChainFinsupp X n →ₗ[ℤ] SingularChainFinsupp X (n + 1)
```

Realize the affine subdivision homotopy on each singular simplex and extend
integer-linearly. It raises degree by one and has sign `∂H + H∂ = id - Sd`.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1480) (retained native site: line 1478).

### AlgebraicTopology.singularHomotopy_single

```lean
theorem AlgebraicTopology.singularHomotopy_single {X : TopCat} {n : ℕ} (x : (TopCat.toSSet.obj X).obj (Opposite.op { len := n })) : (singularHomotopy X n) (Finsupp.single x 1) = (realizeAffineChain x (n + 1)) (Convexity.StdSimplex.homotopySimplex n (Convexity.StdSimplex.AffineSimplex.standard n))
```

**API note (not a source docstring):** The singular subdivision homotopy on a coefficient-one simplex is realization of the affine homotopy of its standard domain. It raises degree by one.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1489) (retained native site: line 1487).

### AlgebraicTopology.singularHomotopy_naturality

```lean
theorem AlgebraicTopology.singularHomotopy_naturality {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) (c : SingularChainFinsupp X n) : (singularFinsuppMap f (n + 1)) ((singularHomotopy X n) c) = (singularHomotopy Y n) ((singularFinsuppMap f n) c)
```

The subdivision prism homotopy commutes with postcomposition.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1497) (retained native site: line 1495).

### AlgebraicTopology.mem_support_singularHomotopy

```lean
theorem AlgebraicTopology.mem_support_singularHomotopy {X : TopCat} {n : ℕ} (c : SingularChainFinsupp X n) {y : (TopCat.toSSet.obj X).obj (Opposite.op { len := n + 1 })} (hy : y ∈ ((singularHomotopy X n) c).support) : ∃ x ∈ c.support, Set.range ⇑((X.toSSetObjEquiv (Opposite.op { len := n + 1 })) y) ⊆ Set.range ⇑((X.toSSetObjEquiv (Opposite.op { len := n })) x)
```

**API note (not a source docstring):** Every next-degree simplex in a singular homotopy chain has range contained in that of some input support simplex. This support control is independent of a cover hypothesis.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1511) (retained native site: line 1509).

### AlgebraicTopology.singularSubdivision_boundary

```lean
theorem AlgebraicTopology.singularSubdivision_boundary (X : TopCat) (n : ℕ) (c : SingularChainFinsupp X (n + 1)) : (singularFinsuppBoundary X n) ((singularSubdivision X (n + 1)) c) = (singularSubdivision X n) ((singularFinsuppBoundary X n) c)
```

**API note (not a source docstring):** Singular subdivision commutes with the finitely supported singular boundary on all positive-degree chains. The subdivisions on the two sides operate in consecutive degrees.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1542) (retained native site: line 1540).

### AlgebraicTopology.singularSubdivisionIterate_boundary

```lean
theorem AlgebraicTopology.singularSubdivisionIterate_boundary (X : TopCat) (n N : ℕ) (c : SingularChainFinsupp X (n + 1)) : (singularFinsuppBoundary X n) ((singularSubdivisionIterate X (n + 1) N) c) = (singularSubdivisionIterate X n N) ((singularFinsuppBoundary X n) c)
```

**API note (not a source docstring):** Every N-fold singular subdivision commutes with boundary. The same number N of subdivisions is used before and after lowering the degree.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1568) (retained native site: line 1566).

### AlgebraicTopology.singularHomotopy_degree_zero

```lean
theorem AlgebraicTopology.singularHomotopy_degree_zero (X : TopCat) (c : SingularChainFinsupp X 0) : (singularFinsuppBoundary X 0) ((singularHomotopy X 0) c) = c - (singularSubdivision X 0) c
```

**API note (not a source docstring):** For a singular zero-chain, the boundary of its subdivision homotopy is c minus Sd(c). There is no additional negative-degree term; subdivision is the identity in this degree.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1583) (retained native site: line 1581).

### AlgebraicTopology.singularHomotopy_boundary

```lean
theorem AlgebraicTopology.singularHomotopy_boundary (X : TopCat) (n : ℕ) (c : SingularChainFinsupp X (n + 1)) : (singularFinsuppBoundary X (n + 1)) ((singularHomotopy X (n + 1)) c) + (singularHomotopy X n) ((singularFinsuppBoundary X n) c) = c - (singularSubdivision X (n + 1)) c
```

**API note (not a source docstring):** For a positive-degree singular chain, boundary(H(c)) + H(boundary(c)) = c - Sd(c). This realizes the affine homotopy identity with the identity-minus-subdivision sign.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1598) (retained native site: line 1596).

### AlgebraicTopology.singularHomotopyIterate

```lean
noncomputable def AlgebraicTopology.singularHomotopyIterate (X : TopCat) (n N : ℕ) : SingularChainFinsupp X n →ₗ[ℤ] SingularChainFinsupp X (n + 1)
```

**Source-inspected correction:** Explicitly noncomputable in the current source; not fresh native output.

The telescoping homotopy from `N` subdivisions to the identity: it is zero
for `N = 0` and satisfies `H_(N+1) = H + H_N ∘ Sd`. This is a sum of
degree-raising maps, not function iteration of `singularHomotopy`.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1636) (retained native site: line 1634).

### AlgebraicTopology.singularHomotopyIterate_zero

```lean
theorem AlgebraicTopology.singularHomotopyIterate_zero (X : TopCat) (n : ℕ) : singularHomotopyIterate X n 0 = 0
```

**API note (not a source docstring):** The telescoping homotopy associated to zero subdivisions is the zero degree-raising linear map. It is not the identity map or a zero-fold function iterate of singularHomotopy.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1646) (retained native site: line 1644).

### AlgebraicTopology.singularHomotopyIterate_succ

```lean
theorem AlgebraicTopology.singularHomotopyIterate_succ (X : TopCat) (n N : ℕ) : singularHomotopyIterate X n (N + 1) = singularHomotopy X n + singularHomotopyIterate X n N ∘ₗ singularSubdivision X n
```

**API note (not a source docstring):** The homotopy for N+1 subdivisions is H plus the homotopy for N subdivisions applied after one subdivision. This is a sum of degree-raising linear maps, not self-composition of H.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1650) (retained native site: line 1648).

### AlgebraicTopology.singularHomotopyIterate_degree_zero

```lean
theorem AlgebraicTopology.singularHomotopyIterate_degree_zero (X : TopCat) (N : ℕ) (c : SingularChainFinsupp X 0) : (singularFinsuppBoundary X 0) ((singularHomotopyIterate X 0 N) c) = c - (singularSubdivisionIterate X 0 N) c
```

**API note (not a source docstring):** In degree zero, the boundary of the telescoping homotopy for N subdivisions equals c minus Sd^N(c). The equality includes N = 0.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1654) (retained native site: line 1652).

### AlgebraicTopology.singularHomotopyIterate_boundary

```lean
theorem AlgebraicTopology.singularHomotopyIterate_boundary (X : TopCat) (n N : ℕ) (c : SingularChainFinsupp X (n + 1)) : (singularFinsuppBoundary X (n + 1)) ((singularHomotopyIterate X (n + 1) N) c) + (singularHomotopyIterate X n N) ((singularFinsuppBoundary X n) c) = c - (singularSubdivisionIterate X (n + 1) N) c
```

**API note (not a source docstring):** The telescoping singular homotopy satisfies boundary(H_N(c)) + H_N(boundary(c)) = c - Sd^N(c) on every positive-degree chain. This supplies the homotopy identity for the subdivision iterate, with the same N in both degrees.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1666) (retained native site: line 1664).

### AlgebraicTopology.mem_support_singularHomotopyIterate

```lean
theorem AlgebraicTopology.mem_support_singularHomotopyIterate {X : TopCat} {n N : ℕ} (c : SingularChainFinsupp X n) {y : (TopCat.toSSet.obj X).obj (Opposite.op { len := n + 1 })} (hy : y ∈ ((singularHomotopyIterate X n N) c).support) : ∃ x ∈ c.support, Set.range ⇑((X.toSSetObjEquiv (Opposite.op { len := n + 1 })) y) ⊆ Set.range ⇑((X.toSSetObjEquiv (Opposite.op { len := n })) x)
```

**API note (not a source docstring):** Every simplex surviving in the telescoping homotopy for N subdivisions has range contained in an original input support simplex's range. The statement covers every N and does not require an open cover.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1703) (retained native site: line 1701).

### AlgebraicTopology.isCoverSmall_of_mem_singularHomotopyIterate

```lean
theorem AlgebraicTopology.isCoverSmall_of_mem_singularHomotopyIterate {X : TopCat} {ι : Type u_1} (U : ι → TopologicalSpace.Opens ↑X) {n N : ℕ} {c : SingularChainFinsupp X n} (hc : ∀ x ∈ c.support, IsCoverSmall U x) {y : (TopCat.toSSet.obj X).obj (Opposite.op { len := n + 1 })} (hy : y ∈ ((singularHomotopyIterate X n N) c).support) : IsCoverSmall U y
```

**API note (not a source docstring):** If an input chain is small in a family U, every simplex in the iterated homotopy chain remains small in U. This is a preservation statement for arbitrary families, not the separate existence theorem requiring an open cover.

[Source](../SphereTopology/Homology/Singular/Subdivision.lean#L1719) (retained native site: line 1717).

## SphereTopology.Homotopy.HairyBallSphere2

Scope: mathematical library leaf.

### SphereTopology.sphere2_exists_zero_of_orthogonal_field

```lean
theorem SphereTopology.sphere2_exists_zero_of_orthogonal_field (V : C(↑sphere2, E3)) (hV_orth : ∀ (p : ↑sphere2), inner ℝ (↑p) (V p) = 0) : ∃ (p : ↑sphere2), V p = 0
```

Every continuous field orthogonal to the radius on the standard two-sphere
vanishes somewhere.

[Source](../SphereTopology/Homotopy/HairyBallSphere2.lean#L24) (retained native site: line 24).

## SphereTopology.Homotopy.TangentField

Scope: mathematical library leaf.

### ContinuousMap.normalizeOfNoZero

```lean
noncomputable def ContinuousMap.normalizeOfNoZero {X : Type u_1} {E : Type u_2} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] (V : C(X, E)) (hV : ∀ (x : X), V x ≠ 0) : C(X, E)
```

Pointwise normalization of a nowhere-zero continuous vector-valued map.

[Source](../SphereTopology/Homotopy/TangentField.lean#L33) (retained native site: line 33).

### ContinuousMap.norm_normalizeOfNoZero

```lean
theorem ContinuousMap.norm_normalizeOfNoZero {X : Type u_1} {E : Type u_2} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] (V : C(X, E)) (hV : ∀ (x : X), V x ≠ 0) (x : X) : ‖(V.normalizeOfNoZero hV) x‖ = 1
```

**API note (not a source docstring):** Normalizing a bundled continuous map that is nonzero at every point produces a vector of norm one at every point. This uses a real normed vector space; no inner product, finite-dimensionality or nonempty-domain assumption is needed for this statement.

[Source](../SphereTopology/Homotopy/TangentField.lean#L43) (retained native site: line 43).

### Metric.Sphere.antipodal

```lean
def Metric.Sphere.antipodal {E : Type u_1} [NormedAddCommGroup E] : C(↑(sphere 0 1), ↑(sphere 0 1))
```

The antipodal continuous self-map of a unit sphere.

[Source](../SphereTopology/Homotopy/TangentField.lean#L54) (retained native site: line 54).

### Metric.Sphere.homotopyAntipodalOfUnitOrthogonal

```lean
noncomputable def Metric.Sphere.homotopyAntipodalOfUnitOrthogonal {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (W : C(↑(sphere 0 1), E)) (hW_norm : ∀ (p : ↑(sphere 0 1)), ‖W p‖ = 1) (hW_orth : ∀ (p : ↑(sphere 0 1)), inner ℝ (↑p) (W p) = 0) : (ContinuousMap.id ↑(sphere 0 1)).Homotopy antipodal
```

An orthogonal unit field rotates the identity map of a unit sphere to the
antipodal map.

[Source](../SphereTopology/Homotopy/TangentField.lean#L61) (retained native site: line 61).

### Metric.Sphere.homotopyAntipodalOfNowhereZeroOrthogonal

```lean
noncomputable def Metric.Sphere.homotopyAntipodalOfNowhereZeroOrthogonal {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V : C(↑(sphere 0 1), E)) (hV_ne : ∀ (p : ↑(sphere 0 1)), V p ≠ 0) (hV_orth : ∀ (p : ↑(sphere 0 1)), inner ℝ (↑p) (V p) = 0) : (ContinuousMap.id ↑(sphere 0 1)).Homotopy antipodal
```

A nowhere-zero orthogonal field can first be normalized and then used to
rotate the identity map to the antipodal map.

[Source](../SphereTopology/Homotopy/TangentField.lean#L92) (retained native site: line 92).
