# Credits and origins

Authors: Formal Frontier Agents. Original project contributions are licensed
[Apache-2.0](../LICENSE); collective author credit does not designate a legal
copyright holder. Lean proofs, tests, metadata and explanatory prose are
AI-authored. AI involvement does not imply human or source-author endorsement,
ownership of external expression or permission to redistribute it.

## Mathematics and formalization

The chosen-point wide-pushout equivalences and relative contractions are
Formal Frontier contributions using Mathlib's homotopy equivalences and relative
homotopies, together with the library's parametrized homotopy descent. May's
Chapter 2, §8, p. 19 supplies the point-wedge setting; the supplied contractions
fixing attaching points are explicitly stronger data than ordinary
contractibility. The countable interval client uses endpoint-zero linear
contractions and the existing factor embeddings.

Formal Frontier Agents supplied the generic orthogonal-field homotopies,
finite-support integral subdivision and small chains, ordinary ordered
Mayer–Vietoris, nonnegative reduced homology, low-degree reduced
Mayer–Vietoris, metric circle and two-sphere homology, antipodal sign and the
standard metric two-sphere continuous-field zero theorem. The normalization,
cosine–sine homotopy and integral homology obstruction are project proof ideas.
The arbitrary-universe homology implementations also credit the earlier
universe-zero formulations and the work reconciling their conventions and
dependency order. Prism's integration and public-interface work is distinct
from these mathematical contributions and does not make the original proofs
Prism's sole authorship. The noncomputable subdivision/prism interfaces and
proof/style repairs retain the credit of their mathematical predecessors;
Prism also supplied targeted implementation repairs.

The reduced-homology background and sphere computations follow J. Peter May,
*A Concise Course in Algebraic Topology*, Chapter 14, §§1, 3 and 5; antipodal
degree is in Chapter 13, §5. Chapter 16 supplies singular-simplex and boundary
background, not the project's finite-support cone/prism implementation.
May uses diagonal then difference in Mayer–Vietoris; this library uses
difference then sum. The normalized puncture/equator deformations, ordered-
cover sign computation and fixed coordinates are project constructions, not
comparisons with May's based-relative, normalized or tensor-coefficient models.
Joël Riou's Mathlib singular and simplicial homology and Mathlib's homological
algebra, stereographic projection and contractibility supply foundations.

Charles A. Weibel's *The K-book*, Example I.1.2.2, motivates the sphere-field
obstruction. Its two-independent-field statement is distinct from the stronger
one-field zero theorem here. Bibliographic authorship is not Lean-expression
authorship or a claim of source completion.

The circle fundamental-group calculator follows May, Chapter 1, §5, pp. 8–9,
with integer loops and lifted endpoints generalized to nonzero signed real
periods. It reuses Junyan Xu's Mathlib quotient-covering and monodromy work,
Mathlib's additive/complex-circle identifications, paths, contractibility and
group equivalences. The unbased degree and free-homotopy classification follow
Chapter 1, §7, p. 10, and the fixed-point consequence follows Problem (2), p. 11.
The bouquet setting is Chapter 2, §8; no free-group identification is claimed.
The generic wide-pushout quotient presentation reuses Joël Riou's Mathlib
`Types.Pushout` and the Mathlib topological-colimit interface. The finite-support
theorem for compact subsets of arbitrary point-attached T₁ spaces is stronger
than that source setting: Formal Frontier Agents supplied its quotient-fiber
and closed-discrete-selection argument, using Mathlib's compactness and discrete-
subset criteria. The stock complex-circle example reuses Heather Macbeth's
Mathlib circle and its topological instances. These contributions use no
textbook quotation, figure or asset.

The strict compact-homotopy factorization and finite-stage detection arguments
reuse the project's support, compactness and subfamily formalizations. Formal
Frontier Agents supplied the finite-stage enlargement and strict recovery
proofs, with arbitrary relative subsets and an independent domain universe.
These generalizations are stronger than May's point-wedge setting, not literal
statements attributed to the book. Shing Tak Lam's Mathlib relative and path
homotopies provide postcomposition, endpoint casts and the squaring-
reparametrization homotopy. The nonidentity client retains the existing positive
circle loop and its generator calculation. Original proof expression and prose
are used; no dependency implementation or external expression is bundled.

The parametrized final-topology and wide-pushout descent interface reuses
Mathlib's topological colimits by Patrick Massot, Kim Morrison, Mario Carneiro
and Andrew Yang, Reid Barton's compact-open currying, the evaluation and
locally compact pair APIs, and Shing Tak Lam's homotopies. The shared
free-path-space transposition approach and its gluing application were developed
by Formal Frontier Agents. The moving-height family on the countable circle
bouquet is a separate construction. Its common point is not fixed, in keeping
with the based/unbased distinction in May, Chapter 2, §4. The pair-hypothesis
criterion and its universe-general descent API are generalizations, not claims
that May states these results or that a free-group calculation is complete.

The generic based covering-lift criterion, point stabilizers, orbits, maps of
covers, monodromy centralizers and based equal-image equivalences are supplied
by [Fundamental Groupoids](https://github.com/FormalFrontier/fundamental-groupoids),
their canonical home. They follow May, Chapter 3, §§2–4 and §7, and reuse
Junyan Xu's Mathlib lifting, monodromy and separated-map uniqueness, the
quotient-cover kernel theorem and Kim Morrison's deck-group formalization.
Formal Frontier Agents supplied the factorization proofs, characteristic laws
and circle/disconnected-domain examples originally developed with Sphere.

The finite-fiber covering transfer follows May, Chapter 16, Problem 3, using
Mathlib's singular chains, homology, standard simplices, covering maps and
trivial bundles. Formal Frontier Agents' Simplicial Objects supplies the
equifibered finite-fiber transfer; Sphere supplies evaluation equivalences for
singular lifts. Joël Riou and the Mathlib covering/bundle contributors retain
credit. The example reuses the circle-loop formalization. Its nonzero
integral basis chain is not a claim of a nonzero homology class. The all-simplex
categorical-coefficient convention is not May's normalized tensor model.

The four integral-coordinate declarations, originally used in Sphere, are
maintained in released
[Simplicial Objects](https://github.com/FormalFrontier/simplicial-objects/blob/143f667bdeb0aeccd02e6475781d5c456f00c95b/SimplicialObjects/ChainCoordinates.lean).
Formal Frontier Agents, including Prism, supplied their expressions. Mathlib's
simplicial-chain coproducts by Joël Riou and Andrew Yang, module-category
colimits by Kim Morrison and Joël Riou, and lifted module/linear-equivalence
APIs supply the construction. Moving the canonical home does not change
mathematical namespaces, providers, universe scope or original credit.

The point-chart fundamental-group application reuses the existing Sphere chart
geometry and the released Fundamental Groupoids common-overlap theorem, its
open-neighborhood inclusion functor and cocone. May, Chapter 2, §§7–8 supplies
the fundamental-group and point-wedge setting; the arbitrary-open-core scope
is a generalization and does not compute a free product. Formal Frontier Agents
supplied the neighborhood packaging, characteristic descent interface and
postcomposition client. Mathlib's open-neighborhood
formalization by Kim Morrison and fundamental groups by Mark Lavrentyev supply
the underlying interfaces.

## Interfaces and documentation

Prism supplied public imports and visibility, including
`TopCat.path_endpoints_eq_of_totallyDisconnected`, aggregate clients and the
bounded pre-simp augmentation registration with its compatibility clients.
Prism wrote 69 definition docstrings, 268 separately labeled API notes and
source-inspected header/link corrections. The 299 original native docstrings,
567 displayed signatures and mathematical expressions retain collective
credit. The augmentation clients are distinct from earlier public API clients;
Prism's client assembly also reuses a source-adapter bundling pattern.

Orrery supplied module/headline references, mathematical-prose revisions,
bounded source-docstring/link correspondence and the coordinate-home
documentation. These contributions retain the mathematical and documentation
credits above. The documentation adapter and its tests adapt Anchor's
algebraic-direct-limits adapter, itself derived from Anchor's ideal-completion
adapter, as Apache-2.0 project reuse. Prism tailored the inventory,
source-snapshot identifiers, docstring preservation, generated-owner/local-
instance explanations and reader guidance; these are not wholly new adapter
expressions.

Lean, Lake, Mathlib and doc-gen4 have separate upstream authors and notices.
No book excerpt, PDF, scan, external website, figure, font or dependency
implementation is redistributed. The project's Apache-2.0 license grants no
new rights in third-party material and implies no endorsement by Weibel, May
or dependency authors.
