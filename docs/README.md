# API reference and retained native provenance

[API.md](API.md) contains all 567 retained native display sites from this
library's ten mathematical leaves. The root and 21 private test/audit modules
have no public display sites but remain in the retained 32-module generation
record. Five headers and shifted source links have been corrected by lightweight
inspection of `f66621f5ff0d90bad849d4f7fcef3c7b96720d55`; this is not a new
native generation. Import `SphereTopology` for the library; its root imports no tests.
Read the [library overview](../README.md) for mathematics, conventions, clients,
pins, resource expectations and the dated pre-acceptance authoring checkpoint.

This is not a full raw/kernel declaration census. A complete actual transitive-
axiom audit must include private declarations and reached dependencies. The
ordinary successful build checks proofs; separate stored-proof replay is not a
release prerequisite. An API display is neither an axiom audit nor a guarantee
of global typeclass registration.

## What is preserved

The historical adapter retained all native visible header tokens, including implicit
arguments and literal `noncomputable`/`abbrev` modifiers, normalizing whitespace
only. Its exact module/name/kind, displayed-signature hash, native source line,
native docstring bytes and source identifier remain in the original inventory.
Current source inspection adds four `noncomputable` modifiers and removes the
obsolete `[DecidableEq α]` binder from
`Convexity.StdSimplex.exists_mem_support_of_mem_support_sum`. Those five headers
are explicitly labeled. Source links target the current declaration lines;
the separately labeled retained native line is historical. All other header
tokens and all 299 native docstrings remain unchanged. Pretty-printing uses each source namespace, notation and type
inference; displayed fragments are not promised to elaborate alone in a fresh
namespace. Linked source is authoritative for suppressed inferred types.

There are 299 nonempty native docstrings. The other 268 entries have separate
AI-assisted prose in `scripts/api_notes.json`, explicitly labeled **API note
(not a source docstring)**. Missing native docs are not fabricated or filtered
out. The inventory preserves native docs separately from the notes. Both
source documentation and authored API prose require semantic review.

The reference identifies 43 explicitly reconciled generated-owner relationships
(41 `reassoc`, two `simps`). These are not a census of all generated declarations.
The two named standard-simplex metric/convex-distance instances are locally
registered in their source: their native `def`/`theorem` displays do not assert
global instance registration. The `isOpenCover_twoOpenCover` native prose is
retained while the API calls out the displayed implication's formal boundary.
No theorem, proof, import, visibility, local option or simplifier attribute is
changed by this documentation adapter.

Only this project's own signatures, docstrings and new API notes are shipped.
No third-party documentation website, assets, styles, fonts, JavaScript or
interactive search are bundled. See [CREDITS.md](CREDITS.md).

## Optional historical native reproduction

Use an unchanged, separate doc-gen4 checkout at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, its committed manifest and Lean
`v4.34.0-rc2`. No fresh docgen build or generation is required for release.
The existing generator and fixed inventory are retained as historical tooling,
bound to analyzed source `19926ec8e295231297edb086107c7b444fcabf80` and the
original documentation inputs in the manifest. They are not a current-source
validator: running their strict `--check` on this manually corrected reference
is not expected to reproduce it. Do not replace the source-inspected corrections
with the older generated text.

For a deliberate future native refresh, use a separately built pinned doc-gen4,
the library's actual pinned `lake env`, and its built modules. The native workflow
is `single` per selected module, then `bibPrepass` and `fromDb`; the existing
`scripts/generate_api.py --help` documents the adapter inputs. Such maintenance
must distinguish newly generated records from retained records and renew any
stale fixed inventory. Do not change mathematical pins to install docgen.
Any mathlib-dependent build still requires successful matching-cache acquisition.

The actual native source identifiers are
`source-snapshot:<full-40-character-commit>/<module-specific-path>`, without a
line-range suffix. They are identifiers, not resolvable web URLs. The adapter
requires exact equality, validates the separate native line against source
bounds and inventory, and refuses invented GitHub ranges, paths or revisions.
Shipped Markdown uses relative links into this checkout; it does not require
an unpublished internal development object to exist on a public host.

## Provenance without development history

`api-manifest.json` records the analyzed full source commit, exact 32-module/path
selection, doc-gen revision, all 35 Lean/source-and-pin hashes, three adapter/
inventory/note hashes, canonical hashes of all 32 native records and the Markdown
hash for the historical native baseline. `source_inspection` separately records
the actual source revision, five source-inspected header corrections, current
relative links and the current Markdown hash. The original native hashes are
not rewritten as though this inspection had generated new native records.
Later documentation-only commits reuse an applicable build and axiom audit.

When the source Git object exists, every source/pin payload must equal that
commit's bytes. Independent public ancestry may omit this development object:
only Git's explicit `missing` response or a source-only tree without `.git`
permits fallback to the shipped manifest's exact source/pin hashes and full
source/module/path/tool tuple. Broken Git, a damaged repository or a non-commit
object refuses fallback. These historical generator checks do not certify the
later source-inspected amendment.

The data tests use synthetic header markup reconstructed from the shipped API
and retained doc text. They test the adapter, not native record authenticity.
Neither the manifest nor the adapter certifies axioms, copyright clearance,
independent review or release acceptance. The present documentation update uses
source inspection, not synthetic data as native evidence, and claims no new
native run or proof audit.
