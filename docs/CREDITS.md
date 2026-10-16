# Credits and origins

Authors: Formal Frontier Agents. Verified original project contributions are
licensed [Apache-2.0](../LICENSE); collective author credit does not designate a
legal copyright holder. Lean proofs, tests, metadata and explanatory prose were
created by AI agents. AI involvement and project-agent review are not human or
source-author endorsement, and do not by themselves establish copyright
ownership or rights in external material.

## Mathematics and research predecessors

Distinct Formal Frontier agent executions authored the mathematical Lean leaves:
generic orthogonal-field homotopies, finite-support integral subdivision and
small chains, ordinary ordered Mayer–Vietoris, nonnegative reduced homology,
low-degree reduced Mayer–Vietoris, metric circle and two-sphere homology,
antipodal sign and the standard metric two-sphere continuous-field zero theorem. The
original service accounts denoted pooled executions, not individual humans.
Prism integrated the mathematical work and supplied public
interface/assembly work; collective credits must not turn the original proofs
into Prism's sole authorship.

An earlier project proof exposition supplied the normalization and cosine–sine
homotopy and integral homology-obstruction route. Separate topology/API planning
supplied interface ideas. Earlier universe-zero Mayer–Vietoris and reduced-
homology research supplied mathematical expression later reused and reconciled
for arbitrary universes and the production dependency order. The research
originals were not themselves the production library. Their original and reconciliation contributions are both credited;
original scratch not preserved in published inputs cannot be reconstructed or
assigned a new author from chronology. The original internal exposition and
research records are *not* public book sources or declared dependencies. The
citation to Weibel in [formalization.yaml](../formalization.yaml) gives
mathematical motivation, not formalization authorship or source completion.

Later distinct agent executions separately made four subdivision/prism definitions
explicitly noncomputable and supplied proof/style repairs including the removed
unused `DecidableEq` binder. Prism authored the subsequent targeted
build-diagnostic repair. These repairs are neither wholly new mathematical
bodies nor substitutes for the earlier reviewed theorem statements.

The reduced-homology background and sphere computations are described in
J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 14, §§1, 3 and 5;
the antipodal-degree result is in Chapter 13, §5. Singular-simplex and boundary
background is in Chapter 16, not a source for the project's finite-support
cone/prism implementation. May's Mayer–Vietoris convention is diagonal then
difference; this library uses difference then sum. The normalized puncture
and equator deformations, ordered-cover sign computation and fixed coordinates
are project constructions, not claims of a formal comparison with May's
based-relative, normalized or tensor-coefficient models. Joël Riou's Mathlib
singular and simplicial homology, together with Mathlib's homological algebra,
stereographic projection and contractibility formalizations, supply foundations.

The circle fundamental-group calculator follows the integer-loop and
lifted-endpoint idea in J. Peter May, *A Concise Course in Algebraic Topology*,
Chapter 1, §5, pp. 8–9, generalized to nonzero signed real periods. It reuses
Mathlib's quotient-covering and monodromy formalization by Junyan Xu, its
additive-circle and complex-circle identifications, and its path,
contractibility and group-equivalence APIs. These are mathematical and
formalization credits, separate from rights in this library's original
expression; no expression from May's book is redistributed.

The based covering-lift criterion follows J. P. May, *A Concise Course in
Algebraic Topology*, Chapter 3 §7. Its sufficient direction and uniqueness reuse
Mathlib's lifting formalization, especially Junyan Xu's approach. Formal Frontier
Agents formalized the fundamental-group factorization argument and the circle
and disconnected-domain examples.

The covering-space point-stabilizer, orbit and based equal-image equivalence
results follow J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3,
§§2–4 and §7, with the hypotheses and fixed-base interpretation described in the
modules. They reuse Junyan Xu's Mathlib monodromy, covering-space lifting and
uniqueness formalization, including the existing quotient-cover kernel result.
Formal Frontier Agents formalized the proofs, characteristic laws and
mathematical examples. The original Lean expressions and explanatory prose are
AI-authored; no book expression or assets are reproduced.

The finite-fiber covering transfer is motivated by May's revised edition,
Chapter 16, Problem 3. It uses Mathlib's singular chain and homology functors,
standard simplices, covering maps and trivial bundles, together with Formal
Frontier Agents' Simplicial Objects equifibered finite-fiber transfer and the
Sphere Topology singular-lift evaluation equivalences. Joël Riou's singular
homology formalization and the Mathlib covering and bundle contributors retain
credit for those foundations. The example uses the circle loop formalization
above. The all-simplex categorical coefficient convention does not assert a
comparison with May's normalized tensor-coefficient construction. No expression
from May's book is redistributed.

## Interfaces and documentation

Prism added public imports and visibility decisions, including public
`TopCat.path_endpoints_eq_of_totallyDisconnected`, aggregate clients, the
bounded pre-simp augmentation registration and its compatibility tests. Prism
wrote 69 definition docstrings from the Lean definitions, 268 separately
labeled authored API notes and the earlier source-inspected API header/link
corrections. The 299 historical native docstrings, 567 displayed signatures and
other mathematical expressions retain their original collective credit. Prism's
`SphereTopologyTest/AugmentationSimp.lean` clients are distinct from the earlier
client expressions underlying `SphereTopologyTest/PublicAPIClient.lean`; its
aggregate/client assembly reuses a source-adapter bundling pattern. Neither the
older clients nor the mathematical proof bodies become newly authored by Prism.

Orrery added the module and headline mathematical references, mathematical-prose
revisions and bounded current-source docstring/link inspection mode. These edits
retain the original mathematical and documentation-adapter contributions above.

The generator and tests adapt Anchor's algebraic-direct-limits documentation
adapter at `bbdcf43d28dd92312484adba53fe20b5b35a2f75`, which itself derives
from Anchor's ideal-completion adapter at
`22c8ea8b5a559df6e5f6257472378a19388f448d`. These expressions are
project-internal Apache-2.0 reuse, not wholly new Prism code. Prism tailored
the inventory, source-snapshot contract, native-doc preservation, local-instance
and generated-owner explanations, controls and reader guidance to this library.
The original source/research/production/repair contributor identities and
credit inverses remain in the separately preserved original project record;
this published library does not require those private records to understand its
mathematical API.

Lean, Lake, mathlib and doc-gen4 have separate upstream authors and notices and
are not vendored here. No book excerpt, PDF, scan, external website, figure,
font, script or dependency implementation is redistributed. Project Apache-2.0
authorization for verified original expression is not a new license for
third-party material or evidence of Weibel's endorsement.
