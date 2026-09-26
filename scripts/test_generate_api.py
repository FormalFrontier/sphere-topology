# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only adapter controls, not native doc-gen, Lean or proof verification.

Synthetic markup is reconstructed from the shipped display signatures. This
tests the bounded parser/inventory/refusal contract, not whether native records
are genuine; actual native generation and source binding are separate evidence.
"""
import copy
from html import escape
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

import generate_api as api

ROOT = Path(__file__).resolve().parent.parent
REV = "a" * 40
FIRST = "SphereTopology.Homology.Singular.Circle"
SECOND = "SphereTopology.Homology.Singular.MayerVietoris"


def fixture():
    pairs = re.findall(r"^### ([^\n]+)\n\n```lean\n([^\n]+)\n```",
                       (ROOT / "docs/API.md").read_text(), re.M)
    api.require(len(pairs) == 567 and len(dict(pairs)) == 567, "fixture headers differ")
    headers = dict(pairs)
    api.require(set(headers) == set(api.EXPECTED), "fixture names differ")
    records = {m: dict(name=m, declarations=[]) for m in api.MODULES}
    sources = {p: (ROOT / p).read_bytes() for p in api.INPUTS}
    for name, meta in api.EXPECTED.items():
        prefix = meta["display_kind"] + " " + name
        api.require(headers[name].startswith(prefix), "fixture identity")
        tail = headers[name][len(prefix):]
        header = ('<div class="decl_header"><span class="decl_kind">'
                  + escape(meta["display_kind"]) + '</span> '
                  + '<span class="decl_name">' + escape(name) + '</span>'
                  + '<span>' + escape(tail) + '</span></div>')
        module = meta["module"]
        path = api.MODULE_PATHS[module]
        records[module]["declarations"].append(dict(header=header, info=dict(
            name=name, kind=meta["kind"], line=meta["line"],
            sourceLink=api.SOURCE_PREFIX + REV + "/" + path,
            docLink="./" + module.replace(".", "/") + ".html#" + name,
            doc=meta["native_doc"])))
    return records, sources


def first(records):
    return records[FIRST]["declarations"][0]


class Controls(unittest.TestCase):
    def test_complete_display_inventory(self):
        records, sources = fixture()
        raw, manifest = api.render(records, REV, sources)
        facts = json.loads(manifest)
        self.assertEqual(raw.count(b"\n### "), 567)
        self.assertEqual(raw.count(b"**API note (not a source docstring):**"), 268)
        self.assertEqual(facts["library_display_sites"], 567)
        self.assertEqual(facts["boundary_client_display_sites"], 0)
        self.assertEqual(facts["modules"], list(api.MODULES))
        self.assertEqual(facts["module_paths"], api.MODULE_PATHS)
        self.assertEqual(set(facts["inputs"]), set(api.INPUTS))
        self.assertEqual(len(facts["inputs"]), 35)
        self.assertEqual(len(facts["documentation_inputs"]), 3)
        self.assertEqual(facts["api_sha256"], api.digest(raw))
        self.assertFalse(facts["proof_certification"])
        self.assertIn(b"not a complete kernel-declaration census", raw)
        self.assertIn(b"../SphereTopology/Homology/Singular/Circle.lean#L", raw)
        self.assertEqual(facts["explicitly_bound_generated_sites"], 43)
        self.assertEqual(facts["named_local_instances"], 2)
        self.assertEqual(raw.count(b"Source registration: **local instance**"), 2)
        self.assertEqual(raw.count(b"Generated `reassoc`"), 41)
        self.assertEqual(raw.count(b"Generated `simps`"), 2)
        empty = ("SphereTopology",) + tuple(m for m in api.MODULES if m.startswith("SphereTopologyTest."))
        self.assertEqual(len(empty), 22)
        for module in empty:
            self.assertEqual(records[module]["declarations"], [])
            self.assertIn(module, facts["native_record_sha256"])

    def test_all_literal_kinds_and_signature_tokens(self):
        records, sources = fixture()
        raw, _ = api.render(records, REV, sources)
        self.assertEqual(sum(m["kind"] != m["display_kind"] for m in api.EXPECTED.values()), 162)
        for module in api.MODULES:
            for row in records[module]["declarations"]:
                text = api.Header(row["header"]).rendered()
                self.assertIn(text.encode(), raw)
                self.assertEqual(api.digest(text.encode()),
                                 api.EXPECTED[row["info"]["name"]]["header_sha256"])
        self.assertIn(b"[TopologicalSpace X]", raw)
        self.assertIn(b"noncomputable def", raw)
        self.assertIn(b"abbrev", raw)

    def test_parser_entities_and_nested_names(self):
        self.assertEqual(api.Header('<div><span>{A : Type u} [Module R A]</span> :'
                                    '<div class="decl_type">x &lt; y ∧ x ≤ y</div></div>').rendered(),
                         '{A : Type u} [Module R A] : x < y ∧ x ≤ y')
        self.assertEqual(api.Header('<span><span>DirectLimit</span>.<span>VaryingScalar</span></span>').rendered(),
                         'DirectLimit.VaryingScalar')

    def test_parser_rejects_invalid_markup(self):
        for text in ('<script>x</script>', '<div><span></div>', '<div>unclosed',
                     '<span onclick="x">x</span>', '<div><!--comment--></div>',
                     '<!DOCTYPE html>', 'outside', '<div/>tail'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                api.Header(text)

    def test_module_name_kind_and_completeness_refusals(self):
        mutations = [
            lambda r: r.pop(api.MODULES[-1]),
            lambda r: r.update(Extra=dict(name="Extra", declarations=[])),
            lambda r: r[FIRST]["declarations"].pop(),
            lambda r: r[FIRST]["declarations"].append(copy.deepcopy(first(r))),
            lambda r: r[SECOND]["declarations"].append(copy.deepcopy(first(r))),
            lambda r: r[FIRST].update(name="Wrong"),
            lambda r: r["SphereTopologyTest.PublicAPIClient"]["declarations"].append(copy.deepcopy(first(r))),
        ]
        for key, value in (("name", "Wrong"), ("kind", "axiom"), ("line", 0),
                           ("line", 999999), ("line", True), ("docLink", "wrong"),
                           ("doc", "```inject")):
            mutations.append(lambda r, k=key, v=value: first(r)["info"].update({k: v}))
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                records, sources = fixture()
                mutate(records)
                with self.assertRaises(ValueError):
                    api.render(records, REV, sources)

    def test_signatures_refuse_implicit_and_modifier_loss(self):
        for needle in ("[TopologicalSpace X]", "noncomputable ", "abbrev"):
            records, sources = fixture()
            row = next(row for r in records.values() for row in r["declarations"]
                       if needle in row["header"])
            replacement = "def" if needle == "abbrev" else ""
            row["header"] = row["header"].replace(needle, replacement)
            with self.subTest(needle=needle), self.assertRaises(ValueError):
                api.render(records, REV, sources)
        records, sources = fixture()
        first(records)["header"] += '<span>invented implicit premise</span>'
        with self.assertRaises(ValueError):
            api.render(records, REV, sources)

    def test_docstring_absence_is_not_silently_fabricated(self):
        for absent in (False, True):
            records, sources = fixture()
            row = next(row for r in records.values() for row in r["declarations"]
                       if (row["info"]["name"] in api.NOTES) == absent)
            row["info"]["doc"] = "fabricated" if absent else ""
            with self.subTest(absent=absent), self.assertRaises(ValueError):
                api.render(records, REV, sources)

    def test_existing_native_doc_content_is_exact(self):
        records, sources = fixture()
        row = next(row for r in records.values() for row in r["declarations"]
                   if row["info"]["doc"].strip())
        row["info"]["doc"] += "Invented extra claim."
        with self.assertRaisesRegex(ValueError, "content differs"):
            api.render(records, REV, sources)

    def test_source_snapshot_identifier_and_exact_path(self):
        records, sources = fixture()
        valid = first(records)["info"]["sourceLink"]
        changes = [valid.replace("source-snapshot:", "https://example.invalid/"),
                   valid.replace("source-snapshot:", "SOURCE-SNAPSHOT:"),
                   valid.replace("/SphereTopology/", "/Other/"),
                   valid.replace(REV, "b" * 40),
                   valid.replace("Circle.lean", "Other.lean"),
                   valid + "#L1-L2", valid + "?query=1", valid + "\n",
                   valid.replace("/Homology/", "/Homology/../Homology/"),
                   valid.replace(REV, "main")]
        for value in changes:
            with self.subTest(value=value):
                altered = copy.deepcopy(records)
                first(altered)["info"]["sourceLink"] = value
                with self.assertRaises(ValueError): api.render(altered, REV, sources)
        first(records)["info"]["line"] += 1
        with self.assertRaises(ValueError): api.render(records, REV, sources)

    def test_source_inventory_and_full_revision(self):
        records, sources = fixture()
        for revision in ("main", "a" * 39, "A" * 40, "-" * 40):
            with self.subTest(revision=revision), self.assertRaises(ValueError):
                api.render(records, revision, sources)
        for path in sources:
            altered = dict(sources)
            altered.pop(path)
            with self.subTest(path=path), self.assertRaises(ValueError):
                api.render(records, REV, altered)

    def test_manifest_binding_all_thirty_five_inputs(self):
        records, sources = fixture()
        _, raw = api.render(records, REV, sources)
        manifest = json.loads(raw)
        api.manifest_source_binding(manifest, REV, sources)
        for key, value in (("format", 2), ("format", True), ("docgen_revision", "b" * 40),
                           ("analyzed_source_revision", "b" * 40),
                           ("modules", list(api.MODULES[:-1])), ("module_paths", {}),
                           ("native_source_prefix", "other:"), ("inputs", {})):
            with self.subTest(key=key), self.assertRaises(ValueError):
                api.manifest_source_binding(dict(manifest, **{key: value}), REV, sources)
        for path in api.INPUTS:
            with self.subTest(path=path), self.assertRaises(ValueError):
                api.manifest_source_binding(manifest, REV, dict(sources, **{path: b"changed"}))

    def test_git_source_absence_presence_and_failure(self):
        with tempfile.TemporaryDirectory(prefix="sphere-api-git-") as temp:
            root = Path(temp)
            self.assertFalse(api.git_source_available(root, REV))
            (root / ".git").write_text("invalid worktree marker\n")
            with self.assertRaisesRegex(ValueError, "refusing fallback"):
                api.git_source_available(root, REV)
            (root / ".git").unlink()
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            self.assertFalse(api.git_source_available(root, REV))
            def git(*args, data=None):
                return subprocess.check_output(["git", "-C", str(root), *args], input=data).decode().strip()
            tree = git("mktree", data=b"")
            commit = git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                         "commit-tree", tree, data=b"Synthetic fixture only\n")
            self.assertTrue(api.git_source_available(root, commit))
            with self.assertRaisesRegex(ValueError, "not a commit"):
                api.git_source_available(root, tree)


if __name__ == "__main__":
    unittest.main()
