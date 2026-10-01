# API reference and historical native provenance

[API.md](API.md) displays 567 named sites from ten mathematical leaves:
299 retained native docstrings and 268 separately labeled, AI-authored API
notes. The production root and 21 test/audit modules have no public display
sites but occur in the historical 32-module record. Import `SphereTopology`
for the aggregate library; it imports no tests. The [overview](../README.md)
explains the mathematics, client imports, limitations and pinned build.

An API display is not a complete generated, public/exported, private or kernel
declaration census, a typeclass-registration promise, or an axiom audit. The
previous accepted mathematical release had a successful build and complete
transitive standard-axiom audit including private declarations. Separate
stored-proof replay is not a release requirement.

## Display and source contract

The historical native inventory retains original visible header tokens, kind,
module, signature hash, native source line, exact native docstring bytes and
source identifier. Of the 567 displays, **five** headers were subsequently
corrected by source inspection: four definitions gained explicit
`noncomputable`, and
`Convexity.StdSimplex.exists_mem_support_of_mem_support_sum` lost the unused
`[DecidableEq α]` binder. The remaining header tokens and all 299 original
native docstrings are unchanged. Current source links point at the amended
source; retained native-site annotations identify older lines. This is
inspection, not a new native generation or a claim that historical raw records
match the later source verbatim.

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
The `isOpenCover_twoOpenCover` prose is historically retained while the API
explains its displayed formal implication boundary. This reference changes
no theorem, proof, local option or simplifier registration.

## Historical reproduction and limits

The original native generation used source
`19926ec8e295231297edb086107c7b444fcabf80` and a separate doc-gen4
checkout `97d4ecdfc8e09e7f511724c25e303d448de6a3db`, under Lean
`v4.34.0-rc2`. `docs/api-manifest.json` retains **35** source/pin input hashes
(32 Lean files and three pinned configuration files), **three** adapter,
inventory and note input hashes, all **32** native-record hashes and the
original native Markdown hash. Its distinct `source_inspection` binds the
later `f66621f5ff0d90bad849d4f7fcef3c7b96720d55` source, five amended
headers, 328 shifted links and current API SHA-256
`fc758327c811e4c2b5c2e36f0115fdc5d089652037a0a52dfa510ffb84f62be0`.
Neither manifest layer is silently rebound to this reader update.

The historical generator's strict `--check` validates its matching *original*
source/native inputs. It is **not** a current-page validator: the corrected
current API is intentionally different. Reproducing that historical check
requires access to the original source and corresponding native records;
merely possessing official published history does not supply those inputs.
Never overwrite source-inspected corrections with the older native output.

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
inventory. These controls test bounded parser/inventory/refusal behavior;
they are not native record authentication, native regeneration, Lean proof
checking, independent review, copyright clearance or release acceptance.
No third-party documentation site, book excerpt, asset, font, script or
implementation is bundled in the reference.
