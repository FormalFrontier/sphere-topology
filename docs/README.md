# API reference and historical native provenance

[API.md](API.md) displays 567 named sites from ten mathematical leaves:
299 source-docstring displays (including the recorded generated-owner
inheritances) and 268 separately labeled, AI-authored API notes. Current
prose and source links are formatted by bounded source inspection; the
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
with examples in
[`SphereTopologyTest.CircleDegree`](../SphereTopologyTest/CircleDegree.lean).
Neither module is part of the historical 32-module record or 567-site display
selection; their inclusion in the library does not extend that native inventory.

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
The current page instead reads attached source docstrings, including local
mathematical references, and the current authored notes. Current source links
point at each declaration's docstring or declaration; generated displays
locate the explicit recorded owner. Retained native-site annotations identify
older lines. This is inspection, not a new native generation or a claim that
historical raw records match the later source verbatim.

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
`current_source_inspection` binds the current bounded 35 source/pin inputs,
three formatter/inventory/note inputs and current page by SHA-256, recording
the number of source docstrings differing from the historical native prose.
It is not a native export, build or proof certificate.

The historical generator's strict `--check` validates its matching *original*
source/native inputs. It is **not** a current-page validator: the corrected
current API is intentionally different. Reproducing that historical check
requires the original source, corresponding native records and matching original
formatter, inventory and note inputs;
merely possessing official published history does not supply those inputs.
Never overwrite source-inspected corrections with the older native output.

To format or check current source docstrings, authored notes and relative links
without Lean or doc-gen4:

```sh
python scripts/generate_api.py --inspect-current
python scripts/generate_api.py --inspect-current --check
PYTHONDONTWRITEBYTECODE=1 python scripts/test_generate_api.py
```

This fixed-library mode reads uniquely matched declaration-line names,
immediately attached docstrings and the inventory's explicit generated owners.
It preserves the shipped display headers and the five labeled corrections,
interfaces outside the bounded display inventory, all historical inventory
bytes and both historical manifest layers. It refuses missing or ambiguous
source sites or a changed display selection. It is not a general Lean parser
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
source does **not** permit fallback. Current Markdown links are relative to
this checkout, without requiring the older internal commit on a public host.

`scripts/test_generate_api.py` reconstructs synthetic headers from the shipped
API, verifying the exact five source amendments before restoring matching
historical fixture headers. Native docstring bytes still come from the fixed
inventory for historical reproduction. The same existing controls also check
current source-inspection idempotence, content binding and missing/ambiguous-site
refusals. These controls test bounded parser/inventory/refusal behavior;
they are not native record authentication, native regeneration, Lean proof
checking, independent review, copyright clearance or release acceptance.
No third-party documentation site, book excerpt, asset, font, script or
implementation is bundled in the reference.
