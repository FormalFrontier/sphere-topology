#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Format this library's API from historical records or current source inspection.

Adapted by Prism from Anchor's algebraic-direct-limits adapter at
bbdcf43d28dd92312484adba53fe20b5b35a2f75. See docs/CREDITS.md.
This is a deliberately fixed-library adapter, not a general documentation
certifier, a Lean parser, or a proof check. Native generation receipts remain
separate review evidence. See docs/README.md for the reproduction contract.
"""
import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess

TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
MODULE_PATHS = {
    "SphereTopology": "SphereTopology.lean",
    **{"SphereTopology.Homology.Singular." + name:
       "SphereTopology/Homology/Singular/" + name + ".lean"
       for name in ("Circle", "MayerVietoris", "Reduced", "ReducedMayerVietoris",
                    "SmallChains", "Sphere", "SphereAntipodal", "Subdivision")},
    **{"SphereTopology.Homotopy." + name: "SphereTopology/Homotopy/" + name + ".lean"
       for name in ("HairyBallSphere2", "TangentField")},
    **{"SphereTopologyTest." + name: "SphereTopologyTest/" + name + ".lean"
       for name in ("AugmentationSimp", "Axioms", "Circle", "CircleModuleAxioms",
                    "Clients", "HairyBallSphere2", "HairyBallSphere2ModuleAxioms",
                    "HairyBallSphere2Root", "MayerVietoris", "PublicAPIClient", "Reduced",
                    "ReducedAxioms", "ReducedMayerVietoris", "ReducedMayerVietorisModuleAxioms",
                    "ReducedModuleAxioms", "SmallChains", "Sphere", "SphereAntipodal",
                    "SphereAntipodalModuleAxioms", "SphereAntipodalRoot", "SphereModuleAxioms")},
}
MODULES = tuple(MODULE_PATHS)
INPUTS = tuple(MODULE_PATHS.values()) + (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json")
HERE = Path(__file__).resolve().parent
EXPECTED = json.loads((HERE / "api_inventory.json").read_bytes())
NOTES = json.loads((HERE / "api_notes.json").read_bytes())
SOURCE_PREFIX = "source-snapshot:"
CURRENT_POINTER = {"schema_version": 2, "source_inspection": "source-inspection.json"}
DEPENDENCY_ORIGINS = {name: meta["current_source_origin"]
                      for name, meta in EXPECTED.items() if "current_source_origin" in meta}
DEPENDENCY_PATHS = {origin["path"] for origin in DEPENDENCY_ORIGINS.values()}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def source_site(info, revision, path, sources):
    """Validate the native source-snapshot identifier, not a remote URL."""
    line_count = len(sources[path].splitlines())
    require(type(info["line"]) is int and 0 < info["line"] <= line_count,
            "invalid native source line")
    expected = SOURCE_PREFIX + revision + "/" + path
    require(info["sourceLink"] == expected, "native source-snapshot identifier differs")
    require(info["line"] == EXPECTED[info["name"]]["line"], "native source line differs")


def manifest_source_binding(manifest, revision, sources):
    """Reproduction without development ancestry; metadata is not an attestation."""
    require(type(manifest.get("format")) is int and manifest["format"] == 1
            and manifest.get("docgen_revision") == TOOL,
            "unsupported provenance manifest")
    require(manifest.get("analyzed_source_revision") == revision and
            manifest.get("modules") == list(MODULES) and
            manifest.get("module_paths") == MODULE_PATHS and
            manifest.get("native_source_prefix") == SOURCE_PREFIX,
            "manifest source selection differs")
    require(manifest.get("inputs") == {p: digest(sources[p]) for p in sorted(INPUTS)},
            "source/pin drift from recorded manifest")


def git_source_available(root, revision):
    """Only a source-only tree or Git's explicit missing result permits fallback."""
    marker = root / ".git"
    if not marker.exists() and not marker.is_symlink():
        return False
    probe = subprocess.run(["git", "--no-replace-objects", "cat-file", "--batch-check"],
                           input=(revision + "\n").encode(), cwd=root,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(probe.returncode == 0, "cannot inspect selected Git object; refusing fallback")
    line = probe.stdout.decode().strip()
    if line == revision + " missing":
        return False
    require(re.fullmatch(re.escape(revision) + r" commit [0-9]+", line) is not None,
            "selected Git object is not a commit")
    return True


class Header(HTMLParser):
    """Keep all visible text, including every implicit argument; discard markup."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        attrs = dict(attrs)
        require(not any(k.startswith("on") for k in attrs), "active header attribute")
        if tag == "div" and "decl_type" in attrs.get("class", "").split():
            self.text.append(" ")
        self.stack.append((tag, set(attrs.get("class", "").split())))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected header declaration")

    def rendered(self):
        # Whitespace alone is normalized; all tokens and implicit binders remain.
        return " ".join("".join(self.text).split())


def render(records, revision, sources):
    require(re.fullmatch(r"[0-9a-f]{40}", revision) is not None, "full source revision required")
    require(set(records) == set(MODULES), "shipped module records differ")
    require(set(sources) == set(INPUTS), "source/pin inventory differs")
    require(len(EXPECTED) == 567 and len(NOTES) == 268 and set(NOTES) <= set(EXPECTED),
            "bounded documentation inventory differs")
    rows = []
    found = {}
    for module in MODULES:
        record = records[module]
        require(record["name"] == module, "native module name differs")
        for row in record["declarations"]:
            info = row["info"]
            name, kind = info["name"], info["kind"]
            require(name in EXPECTED and EXPECTED[name]["kind"] == kind
                    and EXPECTED[name]["module"] == module, "unexpected public name/kind/module")
            require(name not in found, "duplicate public declaration")
            path = MODULE_PATHS[module]
            source_site(info, revision, path, sources)
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs")
            header = Header(row["header"])
            require("".join(header.names) == name
                    and "".join(header.kinds) == EXPECTED[name]["display_kind"],
                    "native header identity differs")
            text = header.rendered()
            require(digest(text.encode()) == EXPECTED[name]["header_sha256"],
                    "native display signature differs, including implicit parameters")
            require("```" not in text and "```" not in info["doc"], "unsupported Markdown fence")
            require(bool(info["doc"].strip()) == (name not in NOTES),
                    "native docstring presence differs from source inventory")
            require(info["doc"] == EXPECTED[name]["native_doc"] and
                    digest(info["doc"].encode()) == EXPECTED[name]["native_doc_sha256"],
                    "native docstring content differs")
            found[name] = EXPECTED[name]
            rows.append(dict(name=name, kind=kind, header=text, module=module,
                             doc=info["doc"].strip(), path=path, line=info["line"]))
    require(found == EXPECTED, "missing public declaration")
    rows.sort(key=lambda row: (MODULES.index(row["module"]), row["line"], row["name"]))
    lines = ["# Generated API reference", "",
             "This reference contains 567 native display sites in ten mathematical library leaves.",
             "Import `SphereTopology` for the library; the 21 test/audit modules are separate.",
             "All 32 shipped module records are retained, including 22 empty display records.",
             "Private/generated proof declarations still require the separate complete audit.",
             "Native display-site counts are not a complete kernel-declaration census.", "",
             "Headers below are native doc-gen4 display signatures, not complete declarations",
             "with proof bodies. All native visible tokens, including implicit parameters and",
             "noncomputable/abbrev modifiers, are retained; whitespace alone is normalized.",
             "Native pretty-printing uses each source namespace, notation and type inference;",
             "consult the linked source for suppressed inferred types and universe conventions.",
             "These displayed fragments are not promised to elaborate alone in a fresh namespace.",
             "Source links are relative to this same checkout.", "",
             "The source/pin hashes and generation provenance are in [api-manifest.json](api-manifest.json).",
             "See [generation instructions](README.md) and the [library overview](../README.md).",
             "Where no source docstring exists, a separately authored **API note** is labeled explicitly.", ""]
    previous = None
    for row in rows:
        if row["module"] != previous:
            previous = row["module"]
            lines += ["## " + previous, "", "Scope: mathematical library leaf.", ""]
        lines += ["### " + row["name"], "", "```lean", row["header"], "```", ""]
        if row["doc"]:
            lines += [row["doc"], ""]
        else:
            note = NOTES[row["name"]]
            require(isinstance(note, str) and bool(note.strip()) and "```" not in note,
                    "invalid authored API note")
            lines += ["**API note (not a source docstring):** " + note, ""]
        meta = EXPECTED[row["name"]]
        if meta["generated_owner"]:
            lines += ["Generated `" + meta["generated_attribute"] + "` declaration from `"
                      + meta["generated_owner"] + "`; the source link locates its owner.", ""]
        if meta["local_instance"]:
            lines += ["Source registration: **local instance**, not a globally registered instance.", ""]
        if row["name"] == "TopCat.isOpenCover_twoOpenCover":
            lines += ["Formal boundary: the displayed theorem supplies the stated implication;"
                      " the retained native prose above is not evidence of a separate converse.", ""]
        lines += [f"[Source](../{row['path']}#L{row['line']}) (native source site: line {row['line']}).", ""]
    markdown = "\n".join(lines).encode()
    manifest = dict(format=1, generator="scripts/generate_api.py", docgen_revision=TOOL,
                    analyzed_source_revision=revision, modules=list(MODULES),
                    module_paths=MODULE_PATHS, native_source_prefix=SOURCE_PREFIX,
                    library_display_sites=567, boundary_client_display_sites=0,
                    existing_native_docs=299, authored_api_notes=268,
                    explicitly_bound_generated_sites=43, named_local_instances=2,
                    documentation_inputs={str(p.relative_to(HERE.parent)): digest(p.read_bytes())
                        for p in (HERE / "generate_api.py", HERE / "api_inventory.json", HERE / "api_notes.json")},
                    inputs={p: digest(sources[p]) for p in sorted(sources)},
                    public_declarations=[r["name"] for r in rows],
                    native_record_sha256={m: digest(json.dumps(records[m], sort_keys=True).encode())
                                          for m in MODULES},
                    api_sha256=digest(markdown), proof_certification=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()


def inspected_source_site(name, meta, source):
    """Locate a unique declaration/owner in this fixed library, not arbitrary Lean.

    Only declaration-line names and immediately attached doc comments are read.
    Generated declarations use the inventory's explicit owner, never guessed names.
    """
    target = meta["generated_owner"] or name
    candidates = [m for m in re.finditer(
        r"(?m)^(?:(?:noncomputable|private|public|protected|local)\s+|"
        r"@\[[^\]\n]*\]\s+)*(?:def|theorem|lemma|abbrev|instance)\s+([\w.₀-₉]+)", source)
        if target == m[1].rstrip(".") or target.endswith("." + m[1].rstrip("."))]
    require(bool(candidates), "source declaration absent: " + name)
    longest = max(len(m[1]) for m in candidates)
    candidates = [m for m in candidates if len(m[1]) == longest]
    require(len(candidates) == 1, "ambiguous source declaration: " + name)
    declaration = candidates[0]
    prefix = source[:declaration.start()].rstrip()
    doc = ""
    site = declaration.start()
    if prefix.endswith("-/"):
        start = prefix.rfind("/--")
        if start >= 0 and "-/" not in prefix[start:-2]:
            doc = prefix[start + 3:-2].strip()
            site = start
    # Generated displays inherit owner prose only where the historical record
    # already did so; other generated displays keep separately authored notes.
    if meta["generated_owner"] and not meta["native_doc"].strip():
        doc = ""
    return source.count("\n", 0, site) + 1, doc


def read_dependency_sources(arguments):
    """Read only explicitly supplied, inventory-allowlisted public module files.

    No workspace search, dependency preparation, Git checkout or network access.
    File provenance is checked against the released module digest during inspection.
    """
    result = {}
    for argument in arguments:
        path, separator, filename = argument.partition("=")
        require(separator and filename and path in DEPENDENCY_PATHS,
                "expected --dependency-source RELEASED_MODULE_PATH=FILE")
        require(path not in result, "duplicate dependency source: " + path)
        result[path] = Path(filename).read_bytes()
    return result


def released_source(name, sources, dependency_sources):
    """Resolve one explicit released origin, never a guessed local declaration."""
    origin = DEPENDENCY_ORIGINS[name]
    path = origin["path"]
    require(path in dependency_sources, "missing required released dependency source: " + path)
    raw = dependency_sources[path]
    require(isinstance(raw, bytes) and digest(raw) == origin["source_sha256"],
            "released dependency source digest differs: " + path)
    packages = json.loads(sources["lake-manifest.json"])["packages"]
    require(any(p.get("url") == origin["repository"] and p.get("type") == "git"
                and p.get("rev") == origin["revision"]
                and p.get("inputRev") == origin["revision"]
                and p.get("inherited") is False and p.get("subDir") is None
                for p in packages), "released dependency pin differs: " + path)
    source = raw.decode()
    # These four complete, release-bound line slices are explicit inventory
    # data. Do not split at ':=': named arguments such as '(R := ...)' occur
    # inside the theorem types themselves.
    declaration = "\n".join(source.splitlines()[
        origin["declaration_line"] - 1:origin["declaration_end_line"]])
    require(declaration.removesuffix(" := by") == origin["source_type"]
            and all(context in source for context in origin["universe_context"]),
            "released declaration type/context differs: " + name)
    meta = EXPECTED[name]
    line, doc = inspected_source_site(name, meta, source)
    url = (origin["repository"] + "/blob/" + origin["revision"] + "/" + path
           + "#L" + str(line))
    require(line == origin["line"] and url == origin["source_url"],
            "released source location differs: " + name)
    return line, doc, url


def inspect_current(markdown, sources, dependency_sources=None):
    """Refresh only current prose/links; keep historical headers and provenance.

    The input is the shipped, five-header-corrected page, not a new native record.
    Later interfaces outside the 567-site inventory remain untouched.
    """
    require(set(sources) == set(INPUTS), "source/pin inventory differs")
    dependency_sources = {} if dependency_sources is None else dependency_sources
    require(set(dependency_sources) <= DEPENDENCY_PATHS, "unexpected dependency source")
    sites = {}
    origins = {}
    pattern = (r"(?m)^### ([^\n]+)\n\n```lean\n([^\n]+)\n```\n\n"
               r"(.*?)\[Source\]\(([^)\n]+)\) "
               r"\(retained native site: line ([0-9]+)\)\.")
    def update(match):
        name, header, body, target, native_line = match.groups()
        require(name in EXPECTED and name not in sites, "current display differs")
        meta = EXPECTED[name]
        path = MODULE_PATHS[meta["module"]]
        local_target = re.fullmatch(re.escape("../" + path) + r"#L[0-9]+", target)
        origin = DEPENDENCY_ORIGINS.get(name)
        require((local_target is not None or origin and target == origin["source_url"])
                and int(native_line) == meta["line"], "historical display selection differs")
        if origin and origin["path"] in dependency_sources:
            line, doc, url = released_source(name, sources, dependency_sources)
            origins[name] = origin
        else:
            try:
                line, doc = inspected_source_site(name, meta, sources[path].decode())
            except ValueError as error:
                if not origin or str(error) != "source declaration absent: " + name:
                    raise
                line, doc, url = released_source(name, sources, dependency_sources)
                origins[name] = origin
            else:
                url = "../" + path + "#L" + str(line)
        require(name in NOTES or bool(doc), "current source docstring absent: " + name)
        require("```" not in doc, "unsupported source docstring fence")
        # Keep the five previously labeled source-inspected header corrections.
        correction = re.match(r"(\*\*Source-inspected correction:\*\*[^\n]+\n\n)", body)
        content = correction[1] if correction else ""
        # Display authorship is historical: newly attached dependency docs do not
        # silently relabel an authored note as source prose.
        content += ("**API note (not a source docstring):** " + NOTES[name]
                    if name in NOTES else doc)
        if meta["generated_owner"]:
            content += ("\n\nGenerated `" + meta["generated_attribute"] + "` declaration from `"
                        + meta["generated_owner"] + "`; the source link locates its owner.")
        if meta["local_instance"]:
            content += "\n\nSource registration: **local instance**, not a globally registered instance."
        if name == "TopCat.isOpenCover_twoOpenCover":
            content += ("\n\nFormal boundary: the displayed theorem supplies the stated implication;"
                        " its docstring does not establish a separate converse.")
        sites[name] = dict(line=line, has_source_docstring=bool(doc),
                           source_docstring_sha256=digest(doc.encode()))
        return ("### " + name + "\n\n```lean\n" + header + "\n```\n\n" + content
                + f"\n\n[Source]({url}) (retained native site: line {native_line}).")
    current = re.sub(pattern, update, markdown.decode(), flags=re.S).encode()
    require(set(sites) == set(EXPECTED), "incomplete current display inspection")
    details = dict(method="bounded-source-text-correspondence",
                   source_inputs={p: digest(sources[p]) for p in sorted(sources)},
                   documentation_inputs={str(p.relative_to(HERE.parent)): digest(p.read_bytes())
                       for p in (HERE / "generate_api.py", HERE / "api_inventory.json", HERE / "api_notes.json")},
                   dependency_source_inputs={p: digest(dependency_sources[p])
                                             for p in sorted({o["path"] for o in origins.values()})},
                   declaration_origins=origins,
                   local_display_sites=len(sites) - len(origins),
                   dependency_display_sites=len(origins),
                   api_sha256=digest(current), source_links_checked=len(sites),
                   source_docstrings_displayed=sum(n not in NOTES for n in sites),
                   authored_api_notes_displayed=sum(n in NOTES for n in sites),
                   source_docstrings_available_under_display_policy=sum(
                       s["has_source_docstring"] for s in sites.values()),
                   source_docstrings_not_displayed=sum(
                       s["has_source_docstring"] and n in NOTES for n, s in sites.items()),
                   source_docstrings_differing_from_native=sum(
                       sites[n]["source_docstring_sha256"] != digest(m["native_doc"].strip().encode())
                       for n, m in EXPECTED.items()),
                   scope="Historical 567-site display selection only; source-text correspondence, "
                         "not compiled types, a whole-library declaration census or proof assurance.",
                   proof_certification=False)
    return current, details


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--inspect-current", action="store_true",
                   help="format current source docstrings and links, without native records")
    p.add_argument("--native-data", type=Path,
                   help="native fromDb output doc-data directory")
    p.add_argument("--source-revision")
    p.add_argument("--dependency-source", action="append", default=[], metavar="MODULE_PATH=FILE",
                   help="explicit released public module file for current inspection; repeat per module")
    p.add_argument("--check", action="store_true", help="compare, never write")
    args = p.parse_args()
    root = Path(__file__).resolve().parent.parent
    sources = {path: (root / path).read_bytes() for path in INPUTS}
    if args.inspect_current:
        require(args.native_data is None and args.source_revision is None,
                "current inspection does not consume native records or a native revision")
        page = root / "docs/API.md"
        provenance = root / "docs/api-manifest.json"
        dependency_sources = read_dependency_sources(args.dependency_source)
        current, details = inspect_current(page.read_bytes(), sources, dependency_sources)
        manifest = json.loads(provenance.read_bytes())
        # Historical top-level fields and source_inspection are not rebound.
        # The sidecar hashes its inputs, not itself or the manifest pointer.
        manifest["current_source_inspection"] = CURRENT_POINTER
        sidecar = root / "docs/source-inspection.json"
        binding = dict(schema_version=2, binding=details)
        if args.check:
            require(page.read_bytes() == current, "current API differs")
            require(json.loads(provenance.read_bytes()) == manifest, "current inspection pointer differs")
            require(json.loads(sidecar.read_bytes()) == binding, "current inspection binding differs")
        else:
            page.write_bytes(current)
            sidecar.write_text(json.dumps(binding, indent=2, ensure_ascii=False) + "\n")
            provenance.write_text(json.dumps(manifest, indent=2) + "\n")
        print(json.dumps(dict(status="matched" if args.check else "source-inspected",
                              display_sites=len(EXPECTED), api_sha256=digest(current),
                              native_generation=False, proof_certification=False)))
        return
    require(not args.dependency_source, "dependency source inputs are only for current inspection")
    require(args.native_data is not None and args.source_revision is not None,
            "historical generation requires native data and its source revision")
    require(re.fullmatch(r"[0-9a-f]{40}", args.source_revision) is not None,
            "full source revision required")
    # A public release has independent ancestry: its analyzed development commit
    # need not be present. Prefer the exact Git object when available, otherwise
    # require the already committed complete source/pin manifest. Neither branch
    # attests that supplied JSON was genuinely produced by the native tool.
    if git_source_available(root, args.source_revision):
        for path, raw in sources.items():
            old = subprocess.check_output(["git", "--no-replace-objects", "show",
                                           args.source_revision + ":" + path], cwd=root)
            require(old == raw, "source/pin drift from analyzed revision: " + path)
        binding = "git-object"
    else:
        manifest = json.loads((root / "docs/api-manifest.json").read_bytes())
        manifest_source_binding(manifest, args.source_revision, sources)
        binding = "committed-source-hashes"
    records = {m: json.loads((args.native_data / ("declaration-data-" + m + ".bmp")).read_bytes())
               for m in MODULES}
    api, manifest = render(records, args.source_revision, sources)
    for name, raw in [("API.md", api), ("api-manifest.json", manifest)]:
        target = root / "docs" / name
        if args.check:
            require(target.read_bytes() == raw, "generated file differs: " + name)
        else:
            target.write_bytes(raw)
    print(json.dumps(dict(status="matched" if args.check else "generated",
                          declarations=len(EXPECTED), api_sha256=digest(api),
                          source_binding=binding, release_acceptance=False)))


if __name__ == "__main__":
    main()
