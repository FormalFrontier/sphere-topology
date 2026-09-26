# sphere-topology

Reusable Lean topology and singular-homology infrastructure. The library
constructs an identity-to-antipodal homotopy from a nowhere-zero continuous
orthogonal field, and proves that integer singular chains small relative to an
open cover include by a quasi-isomorphism. The latter package provides signed
barycentric subdivision, its support-preserving prism homotopy, and natural maps
for continuous maps and cover refinements. It also constructs the ordinary
integer two-open singular Mayer--Vietoris sequence in arbitrary universes,
including its connecting map, exactness, naturality and ordered-cover swap sign.
It also defines nonnegative reduced integral singular homology, with degree zero
given by the augmentation kernel, and computes the signed transposition action
on the canonical two-point basis.  The standard unit circle now has an explicit
ordered east/west puncture cover, stereographic puncture charts, an upper/lower
two-point deformation, and the resulting reduced integral homology isomorphism
`H̃₁(S¹; ℤ) ≅ ℤ`.  The literal unit two-sphere likewise has an ordered
north/south puncture cover, stereographic puncture charts, a normalized
equator deformation fixed pointwise on the equator, an orientation-explicit
equator-to-circle coordinate homeomorphism, and the resulting isomorphism
`H̃₂(S²; ℤ) ≅ ℤ`.  The literal antipodal self-map exchanges the
north/south cover, its sign-free action on the twice-punctured sphere is
homotopic to the identity through the equator, and ordered Mayer--Vietoris
naturality computes its ordinary and positive-degree reduced `H₂` action as
`-id`.  In the fixed `ℤ` coordinate this is multiplication by `-1`, which
directly proves that identity and antipodal are not homotopic on the literal
standard two-sphere.  Consequently, every bundled continuous field
`V : C(sphere2, E3)` that is pointwise orthogonal to its base point has a zero;
this is the library's literal-standard-`S²` hairy-ball theorem.


Authors: Formal Frontier Agents. Original project contributions are licensed
under Apache-2.0; see [LICENSE](LICENSE).
The status descriptions here and in `formalization.yaml` record the authoring
checkpoint **2026-09-26 19:10 UTC**, before final independent acceptance.
Subsequent review, protected-branch and publication records determine release
status; these historical descriptions do not deny a later accepted release.
At that checkpoint, source repair
`f66621f5ff0d90bad849d4f7fcef3c7b96720d55` follows proof/style successor
`0878090c2903928822d263dce8fa360bed3e5ce7`, which added focused repairs to
`47c239ba164c05e63e9d4955887b4ef252fd1a79`, which made four subdivision
definitions explicitly noncomputable. These descend from the ordinary-interface,
augmentation-simplifier, definition-documentation and metadata assembly on
accepted development mathematics `850c2a1712660fe9d725dcd49b31a2e077eda517`.
The first fresh build of `0878090` failed on three unused simp arguments and
a nonprogressing all-goals simplification with unresolved metavariables in the
reduced swap proof. The `f66621f5` repair removes those three arguments and
supplies the existing cover proofs explicitly to the swap rewrite before focused
sign simplification. The repaired source passed the pinned ordinary build
`lake --no-cache --wfail -v build` on 2026-09-26 at 18:48:26 UTC (3,029 jobs,
exit zero and no error or warning lines). The complete transitive-axiom audit
also passed for all 32 modules and 1,083 logical declarations, including private
and test declarations: only `propext`, `Classical.choice` and `Quot.sound` occur.
Consolidated independent release review was pending at that checkpoint. Documentation
inspection reuses the existing native reference with explicitly labeled source
corrections; no fresh doc-generation or separate stored-proof replay is required.
This checkpoint is not an accepted release record.

## Interfaces and conventions

Import `SphereTopology` for the public aggregate, or a focused leaf:

| Module beneath `SphereTopology` | Interface |
| --- | --- |
| `Homotopy.TangentField` | Generic normalization and explicit orthogonal-field homotopies on real metric unit spheres. |
| `Homology.Singular.Subdivision`, `SmallChains` | Integral subdivision, support-preserving prism homotopy, arbitrary-universe cover-small quasi-isomorphism, maps and refinements. |
| `Homology.Singular.MayerVietoris` | Ordinary two-open integral sequence, exactness, naturality and ordered-cover swap. |
| `Homology.Singular.Reduced`, `ReducedMayerVietoris` | Nonnegative reduced homology, augmentation-kernel degree zero, two-point sign and reduced connecting map. |
| `Homology.Singular.Circle`, `Sphere`, `SphereAntipodal` | Literal Euclidean circle/two-sphere geometry, integral homology and antipodal nonhomotopy. |
| `Homotopy.HairyBallSphere2` | Zero theorem for bundled continuous orthogonal fields on the literal two-sphere. |

The singular boundary is the alternating face sum; the subdivision homotopy
satisfies `∂H + H∂ = id - Sd`. For the ordered cover `(U,V)`, the first
Mayer–Vietoris map is `c ↦ (c,-c)`, followed by addition. Reversing the cover
changes the connecting-map sign. Empty spaces/covers and independent cover-index
universes are included where stated; nonemptiness is not implicit. Reduced homology
is indexed by natural numbers: reduced H0(empty)=0, with no degree −1 assertion.
The two-point basis is `[false]-[true]`; false is the circle's upper component.
The sphere uses north/south cover order and equator coordinate order `(x,y)`.

The [API reference](docs/API.md) reuses 567 native displayed
signatures, 299 native docstrings and 268 separately labeled authored API notes.
Its [manifest](docs/api-manifest.json) preserves the older native-generation
provenance separately from lightweight source inspection of this revision.
Four `noncomputable` modifiers, one removed class binder and shifted source links
are corrected from the actual source, not described as new native output. Display
counts are not a raw/private/generated declaration census or an axiom verdict.

Four definitions are explicitly noncomputable:
`Convexity.StdSimplex.subdivideSimplex`, `Convexity.StdSimplex.homotopySimplex`,
`AlgebraicTopology.singularSubdivisionIterate` and
`AlgebraicTopology.singularHomotopyIterate`. Their intended interface is
mathematical definitions and equation lemmas, not executable extraction. Runtime
callers relying on these functions are not supported by this interface. The
modifier change suppresses four compiler-generated partial companions; it is a
real narrowing of the executable interface, not executable equivalence. Bounded
compatibility checks of the earlier modifier-only source do not certify every
external consumer or the later proof/style edits.

`Convexity.StdSimplex.exists_mem_support_of_mem_support_sum` no longer requires
`[DecidableEq α]`; its proof uses local classical reasoning. Its name, conclusion,
other hypotheses and ordinary explicit arguments are preserved. External clients
using explicit `@` positional applications or a named class argument may need
adjustment. The five in-tree uses are included in the repaired source's successful build.

The native public values `TopCat.openSingularSetIso` and
`AlgebraicTopology.twoOpenReducedMayerVietorisδZero` retain private helpers.
Their bodies are not exposed through ordinary imports; their public types and
characteristic theorem interfaces remain available. A client unfolding these
legacy implementation bodies may need to use the public lemmas. This visibility
decision requires independent compatibility review. Diagnostic `import all`
is not the advertised client interface.

The previously private, documented theorem
`TopCat.path_endpoints_eq_of_totallyDisconnected` is now public with its existing
statement and proof. This retains the transparent two-point equivalence and its
existing definitional computation law. It also supplies a direct generic path
client; no new mathematical hypothesis or result was introduced.

`Convexity.StdSimplex.affineAugmentation_subdivide_zero` is registered with
`@[simp↓]`: it runs before simplification of its subdivision argument. Its name,
statement and proof are unchanged. This proposal preserves the tested restricted
`simp` uses that disable `subdivideSimplex_zero` and `affineAugmentation_single`,
as well as ordinary `simp`, explicit `simp only` and `rw`. Ten persistent clients
record these boundaries. Removing the registration broke four of those clients;
raising post-simp priority did not clear the native `simpNF` diagnostic. Changing
simp phase still requires independent API review and is not a guarantee for every
downstream custom simp set. Internal provenance locator: sphere-topology issue14,
comment40858 (the retained investigation, not a library dependency).

## Pinned build and use

Prerequisites are Git, elan and dependency-network access. Lean is
`leanprover/lean4:v4.34.0-rc2`; mathlib is
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. The manifest fixes all eight
transitive packages. There are no other Formal Frontier dependencies.
Use the committed manifest; routine reproduction does not require `lake update`.

From a checkout of the selected exact revision:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake -Kjobs=2 --wfail build
lake env lean -DwarningAsError=true SphereTopologyTest/PublicAPIClient.lean
```

The matching cache fetch must succeed before building. Fetch again after changing
pins or removing/replacing `.lake`. Cached dependencies do not substitute for
compiling this repository's changed sources. The 32 Lean modules include the
production root, ten mathematical leaves and twenty-one test/audit files. All
test/audit files are explicit default targets; the production root imports no tests.
Focused builds use the module names in the table.

For another Lake project, add a Git dependency pinned to a reviewed exact commit
and retain the same Lean/mathlib pins. The designated distribution URL is
`https://github.com/FormalFrontier/sphere-topology.git`, requiring private-project
access until public visibility is separately authorized. No accepted release
snapshot is claimed here. This ordinary-import
client needs no source-repository notes or private implementation imports:

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

The default aggregate client also checks normalization, subdivision, empty covers,
arbitrary-universe connecting-map types, empty reduced homology, literal model
equalities, antipodal coordinates and unbundled continuous fields. Focused clients
retain the older sign and boundary checks.

### Verification and resources

The computational release checks are an ordinary successful pinned build and a
complete transitive-axiom audit of repository declarations, including private
declarations and dependencies reached from them. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted; `sorryAx` or any additional
axiom fails. Selected `#print axioms` examples alone do not establish complete
coverage. The repaired build and complete axiom audit passed: 27 exact completed
module outputs account for 1,041 declarations; ordinary `Lean.collectAxioms`
checked the remaining five modules and 42 declarations in 22.610 seconds,
with private imports and no additional kernel constants omitted. The retained
verification record is sphere-topology commit
`f413ddc3451439d9fc089f85a2537c2082d77230`,
`release-checks/f666-build-axioms/REPORT.md` (private evidence, not a library dependency).
Ordinary compilation checks proof terms: separate exhaustive stored-proof
rechecking is not an additional release prerequisite.

Earlier experimental audits remain historical evidence. The modifier-only source
`47c239ba164c05e63e9d4955887b4ef252fd1a79` completed a 32-module/1,083-body
audit with seven controls; the older 673-prefix run with zero controls remains
incomplete. Neither is silently promoted to a result for changed proof inputs.
Lightweight inspection covers documentation, API claims, module organization,
source correspondence, notices, exact dependency pins and the release tree/history.
Independent final review and redistribution clearance were pending at the
authoring checkpoint above; subsequent decisions belong to the release records.
The root `formalization.yaml` records bounded mathematical scope, expression
origins and actual AI/Task credit; its presence and schema validity do not establish
proof checking, rights clearance or release acceptance.

Release tags and tag-specific work are currently deferred. A later accepted
snapshot still needs a durable record of its full commit and tree, full independent
acceptance, verified protected promotion and an exact mirrored commit/ref/private
destination. Documentation-only updates do not require another build, and repeating
the same compilation as internal and GitHub consumers is not a release gate.
A development branch, successful compilation or this README is not acceptance.

On 2026-09-25, after a successful matching-cache fetch and scoped
`lake clean sphere-topology`, the command above compiled all 32 project modules
(3,029 Lake jobs including cached dependencies) in 56.61 seconds. The run used
two Lean threads/two Lake jobs in a 23 GiB Linux x86-64 runtime. The recorder's
largest-child RSS was 1,694,824 KiB; this is not aggregate peak memory, a measured
minimum, or a portability guarantee. Detailed ordinary replay and selected-name
axiom results are retained in the readiness record. That historical run does not
replace the current complete axiom audit. The repaired source's incremental build
reused the matching cache and completed in a separate 8 GiB service; its reported
1.4 GiB peak is an observation, not a minimum-memory or portability guarantee.

Lint is not globally clean. After 69 definition docstrings were added, explicit
full imports with 15 pinned native declaration linters report zero findings in
654 library declarations (plus 246 generated) and 174 test declarations (plus 12
generated). This also checks the inherited pre-simp proposal; no new suppression
is added. These imported views are not a full stored-declaration audit.
These are historical results, not successor lint passes. Independent bounded
review accepts the truthful collective/SPDX header convention in nine mathematical
leaves, thirteen deliberately private regression modules and eight command-only
audit roots; it does not turn their literal diagnostics into exit-zero results.
The source successor attempts the six focused tactic repairs, two goal-focus
repairs, unused class removal, blank-line removal and six contributor wraps.
The first build failed as recorded above; the minimal three-path correction
passed the ordinary warning-fatal build. This is not a claim that every optional
linter has no findings. No checker filter,
proof admission or new suppression was added. Complete earlier commands,
diagnostics and failed attempts remain in the readiness record.

## Limits

The final zero theorem concerns continuous E3-valued fields on the literal metric
unit two-sphere, extrinsically orthogonal to the radius. No all-sphere, arbitrary
coefficient, characteristic-two, smooth tangent-bundle or general degree theorem
is claimed. The reduced Mayer–Vietoris isomorphism retains its adjacent-degree
vanishing hypotheses. No complete formal coverage of a source is asserted.

## References, contributors and provenance

The cosine–sine homotopy and singular-homology route implement standard
mathematical arguments. The motivating reference is Charles A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*, complete-book build dated
August 29, 2013, Example I.1.2.2. Citation is not permission to copy book expression;
no PDF, figure or book excerpt is shipped. Pinned mathlib APIs are imported, not
vendored; preserve dependency notices when redistributing those dependencies.

AI agents produced the project Lean proofs, tests and documentation, and project
agents reviewed the historical mathematical units. Contributors include
Formalization Worker A, Formalization Worker B and Prism (source maintainer).
Service identities denote distinct executions, not one human author. Exact Task/
UID and file origins are in the root metadata and Git. Internal provenance
locator: sphere-topology issue14 (the readiness record, not a use-time dependency).
These credits do not establish a legal copyright holder.

The tangent-field design used earlier project source exposition/API planning at
source-weibel commit `21da829968a3fa4055df276db98f7611a4af36a6`.
Mayer–Vietoris adapts internal research
`def7d11e8e1fc55fece64b1f24fb120ec54cf46d`; reduced homology adapts
`83f7535abc578a76a0dbfb3905d67c681a9588ae`, with later universe/accepted-main
reconciliation. These earlier contributions are not newly authored by the
readiness maintainer. The aggregate client's short applications reuse existing
repository tests and the bundling pattern of the source adapter at
`4cd8df74596bae9a81bb4515cde0165f3b02eb46`; the library has no source dependency.
Native layout, named regressions, test configuration, standalone guidance and
licensing assembly are Prism's readiness work. The 69 added definition docstrings
were written by Prism from the actual native definitions and their surrounding
lemmas: 25 in Circle, three in SmallChains, five in Sphere, two in SphereAntipodal
and 34 in Subdivision. They are newly authored descriptions, not copied book
exposition. The augmentation regression client uses the existing repository's
statement fragments and API conventions; its simp-phase proposal and negative
comparisons are separately preserved in the investigation record.

Later worker-a executions supplied the four explicit noncomputable modifiers
and the eight-path proof/style successor; these are separate from the original
production proofs. The exact commits and Task identities are recorded in
`formalization.yaml`. Prism authored the five-line build-diagnostic repair
`f66621f5ff0d90bad849d4f7fcef3c7b96720d55` and this documentation update.
These credits do not claim authorship of the earlier mathematical bodies or
independent acceptance of the repair. Its successful build is recorded separately.

Standing project authorization applies Apache-2.0 to verified original project
contributions, including internal reuse; it does not establish ownership or clear
third-party rights. Complete-artifact/public-history clearance remains an
independent review condition. Development discussion lives in repository issues
and the internal sphere-topology channel; no raw agent transcript is needed to
use this library.
