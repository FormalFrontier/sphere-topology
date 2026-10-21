# API reference and historical native provenance

[API.md](API.md) displays 567 named sites from ten mathematical leaves:
299 source-docstring displays (including the recorded generated-owner
inheritances) and 268 separately labeled, AI-authored API notes. The current
selection has 563 local sites and four released dependency declarations,
not 567 Sphere-owned declarations. Current prose and source links follow
bounded source-text correspondence; the
original native docstrings remain in the historical inventory, not as
unchanged current-page prose. In the historical 32-module record, the production
root and 21 test/audit modules have no public display sites. This is a bounded
selection, not the current module inventory. Import `SphereTopology` for the
aggregate library; it imports no tests. The [overview](../README.md) explains
the mathematics, client imports, limitations and pinned build.

For point-fiber deck actions and evaluation embeddings, see the focused
[`SphereTopology.Topology.DeckGroup`](../SphereTopology/Topology/DeckGroup.lean)
module and its sharp interfaces in the overview. This
module is outside the bounded display inventory below. The integer degree and
free-homotopy classification of unbased complex-circle self-maps are in
[`SphereTopology.Homotopy.CircleDegree`](../SphereTopology/Homotopy/CircleDegree.lean),
with [characteristic examples](../SphereTopology/Homotopy/CircleDegree.lean#L512)
in the same module. This module and its examples are outside the historical
32-module record and 567-site display selection; their inclusion in the library
does not extend that native inventory.

An API display is not a complete generated, public/exported, private or kernel
declaration census, a typeclass-registration promise, or an axiom audit.
Documentation formatting is separate from Lean builds and transitive axiom
checking, whose scope includes private declarations.

## Display and source contract

The historical native inventory retains original visible header tokens, kind,
module, signature hash, native source line, exact native docstring bytes and
source identifier. Of the 567 displays, **five** headers were subsequently
corrected by source inspection: four definitions gained explicit
`noncomputable`, and
`Convexity.StdSimplex.exists_mem_support_of_mem_support_sum` lost the unused
`[DecidableEq α]` binder. The remaining header tokens and all 299 original
native docstrings remain unchanged in `scripts/api_inventory.json`.
The current page instead uses attached source docstrings, including local
mathematical references, and the current authored notes. Current source links
point at each declaration's docstring or declaration; generated displays
locate the explicit recorded owner. The four coordinate APIs link to
`SimplicialObjects.ChainCoordinates` at the exact released GitHub revision in
the inventory's `current_source_origin` records. These records supplement,
not replace, historical native module ownership. Their complete source types,
coefficient RHS and universe context are retained; see [coordinates](coordinates.md).
Retained native-site annotations identify older lines. Source-text correspondence
is not a new native generation, elaborated-type comparison or a claim that
historical raw records match the later source verbatim.

Display authorship is preserved separately from current source documentation.
Under the recorded generated-owner inheritance policy, 301 sites have usable
source docstrings: 299 are displayed, while the two released coordinate laws
retain their explicitly labeled authored notes. The two generated functor
map/object displays also retain notes rather than inheriting their owner's
docstring, just as in the historical inventory. The 301 count uses this explicit
display policy; it is not a count of every raw source-or-owner attachment or a
new API census.

Pretty-printing depends on source namespaces, notation and type inference;
displayed fragments need not elaborate alone in a new namespace. Linked source
is authoritative for omitted inferred types. The 268 notes reside in
`scripts/api_notes.json` and are visibly labeled **API note (not a source
docstring)**, never silently substituted for missing native documentation.
Their authorship and the native mathematical expressions are distinct; see
[CREDITS.md](CREDITS.md).

The adapter explicitly records **43** generated-owner relationships (41
`reassoc`, two `simps`), not all generated declarations. Two named
standard-simplex metric/convex-distance instances are **locally** registered;
the native `def`/`theorem` displays do not imply global instance status.
The `isOpenCover_twoOpenCover` API explains its displayed formal implication
boundary; its docstring does not prove a separate converse. This reference changes
no theorem, proof, local option or simplifier registration.

## Historical reproduction and limits

The original native generation used source
`19926ec8e295231297edb086107c7b444fcabf80` and a separate doc-gen4
checkout `97d4ecdfc8e09e7f511724c25e303d448de6a3db`, under Lean
`v4.34.0-rc2`. `docs/api-manifest.json` retains **35** source/pin input hashes
(32 Lean files and three pinned configuration files), **three** adapter,
inventory and note input hashes, all **32** native-record hashes and the
original native Markdown hash. Its distinct historical `source_inspection`
binds the later `f66621f5ff0d90bad849d4f7fcef3c7b96720d55` source, five
amended headers, 328 shifted links and that inspection's API SHA-256
`fc758327c811e4c2b5c2e36f0115fdc5d089652037a0a52dfa510ffb84f62be0`.
Neither layer is rebound to current documentation. The separate
`current_source_inspection` is a schema-version-2 relative pointer to
[source-inspection.json](source-inspection.json), the sole current binding.
Its `binding` records the current bounded 35 local source/pin inputs, three
formatter/inventory/note inputs, explicitly supplied released module bytes and
current page by SHA-256. It records the four released declaration origins,
local/dependency display counts and source-docstring display policy. Its method,
`bounded-source-text-correspondence`, describes source syntax, prose and locations,
not compiled types or proof coverage. The sidecar does not hash itself or the
manifest containing its pointer; no canonical JSON serialization or self-referential
inventory digest is required. Neither historical layer is a current binding.
This is not a native export, build or proof certificate.

The historical generator's strict `--check` validates its matching *original*
source/native inputs. It is **not** a current-page validator: the corrected
current API is intentionally different. Reproducing that historical check
requires the original source, corresponding native records and matching original
formatter, inventory and note inputs;
merely possessing official published history does not supply those inputs.
Never overwrite source-inspected corrections with the older native output.

To format or check current source docstrings, authored notes and local/released
source links without Lean or doc-gen4, first supply the public released
`SimplicialObjects/ChainCoordinates.lean` file from revision
`143f667bdeb0aeccd02e6475781d5c456f00c95b` of
[FormalFrontier/simplicial-objects](https://github.com/FormalFrontier/simplicial-objects).
For example, with `COORDINATE_SOURCE` set to that file's explicit path:

```sh
python scripts/generate_api.py --inspect-current \
  --dependency-source "SimplicialObjects/ChainCoordinates.lean=$COORDINATE_SOURCE"
python scripts/generate_api.py --inspect-current --check \
  --dependency-source "SimplicialObjects/ChainCoordinates.lean=$COORDINATE_SOURCE"
PYTHONDONTWRITEBYTECODE=1 python scripts/test_generate_api.py \
  --dependency-source "SimplicialObjects/ChainCoordinates.lean=$COORDINATE_SOURCE"
```

The caller prepares that exact public file; the adapter does not fetch it,
search workspaces/caches or prepare dependencies. The argument's module path
must be inventory-allowlisted. Both the released module digest and the local
manifest's repository/full revision must match. Missing input, a changed module
or a conflicting pin is refused, not replaced with a local declaration or a
skipped current check. A prepared build environment may supply that same explicit
file, but these commands do not prepare or certify a build environment.

This fixed-library mode reads uniquely matched declaration-line names,
immediately attached docstrings and the inventory's explicit generated owners.
It preserves the shipped display headers and the five labeled corrections,
interfaces outside the bounded display inventory, all historical inventory
fields and both historical manifest layers. Only the four explicit origin
records supplement that historical inventory. The Python API is
`inspect_current(page_bytes, local_sources, dependency_sources=None)`, with local
inputs keyed by the exact 35 paths and released bytes keyed by the allowlisted
module path. The older two-argument call remains usable when the selected names
are still present in the supplied local source; it cannot resolve a moved
name without its explicit dependency input. The current page requires that input.
The adapter refuses missing or ambiguous source sites or a changed display
selection. It is not a general Lean parser
and does not check elaboration or infer public API completeness. The source
links and content hashes, not a fabricated native source revision, identify
the current inputs.

For an intentional future native refresh, use a separate pinned doc-gen4,
built repository modules in pinned `lake env` and the generator's documented
`single`, `bibPrepass`, `fromDb` workflow; read
`scripts/generate_api.py --help` for the adapter interface. Fetch the matching
precompiled mathlib cache successfully before **any** mathlib-dependent build.
Do not change mathematical pins simply to install doc-gen4. A refresh needs
new input/record provenance rather than replacing original hashes in place.

Native source identifiers have the exact form
`source-snapshot:<40-character-commit>/<module-specific-path>` with no line
range. They are identifiers, not resolvable public URLs. The adapter checks
exact equality, source line bounds and inventory, and refuses invented paths,
URLs, revisions or ranges. When the analyzed Git commit exists, source/pin
payloads must equal its bytes. A source-only tree or Git's explicit `missing`
result permits fallback to the shipped exact source/pin hashes and complete
module/path/tool selection; damaged Git, a non-commit object or a conflicting
source does **not** permit fallback. Current local Markdown links are relative
to this checkout; the four dependency links use their immutable public release,
without requiring older development commits on a public host.

`scripts/test_generate_api.py` reconstructs synthetic headers from the shipped
API, verifying the exact five source amendments before restoring matching
historical fixture headers. Native docstring bytes still come from the fixed
inventory for historical reproduction. The same existing controls also check
current source-inspection idempotence, sidecar binding, required explicit
released input and missing/changed-source/conflicting-pin refusals. There is no
optional-success path when the full current consumer lacks the released source.
These controls test bounded parser/inventory/refusal behavior;
they are not native record authentication, native regeneration, Lean proof
checking, independent review, copyright clearance or release acceptance.
No third-party documentation site, book excerpt, asset, font, script or
implementation is bundled in the reference.
