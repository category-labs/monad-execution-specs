#!/usr/bin/env python3
"""Census project theorem assumptions; optionally require a closed runtime bundle."""

from pathlib import Path
import re
import subprocess
import sys


THEOREM = re.compile(
    r"^\s*(?:Local |Global |Program )?"
    r"(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark)\s+"
    r"([A-Za-z_][A-Za-z_0-9]*)\b",
    re.MULTILINE,
)
MARKER = re.compile(r'^"CENSUS-BEGIN ([0-9]+)"$', re.MULTILINE)
AXIOM = "OCamlBigarray.Array1.get"
AXIOM_DECL = re.compile(
    r"^([A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)\s*:",
    re.MULTILINE,
)


def printed_axioms(section: str) -> set[str]:
    if "Axioms:" not in section:
        return set()
    axioms = set(AXIOM_DECL.findall(section.split("Axioms:", 1)[1]))
    if not axioms:
        raise SystemExit("An axiom section contained no parseable declarations")
    return axioms


def check_bundle(build: Path, translator: Path, switch: Path,
                 theorem_axioms: dict[tuple[str, str], set[str]]) -> None:
    query = build / "RuntimeAxiomBundleCensus.v"
    query.write_text(
        "From Stdlib Require Import String.\n"
        "Open Scope string_scope.\n"
        "Require Import RocqOfOCaml.RuntimeAxiomRealizability.\n"
        'Check "BUNDLE-BEGIN".\n'
        "Print Assumptions RocqOfOCaml.RuntimeAxiomRealizability.actual_bundle.\n"
        'Check "CLOSED-BEGIN".\n'
        "Print Assumptions RocqOfOCaml.RuntimeAxiomRealizability.closed_bundle.\n"
    )
    command = [
        "opam", "exec", f"--switch={switch}", "--", "rocq", "c",
        "-Q", str(translator), "RocqOfOCaml", query.name,
    ]
    result = subprocess.run(command, cwd=build, text=True, capture_output=True)
    log = build / "runtime-axiom-bundle-census.log"
    log.write_text(result.stdout + result.stderr)
    if result.returncode:
        raise SystemExit(f"Runtime bundle census failed; see {log}:\n"
                         f"{result.stderr[-2000:]}")
    bundle_marker = '"BUNDLE-BEGIN"'
    closed_marker = '"CLOSED-BEGIN"'
    if result.stdout.count(bundle_marker) != 1 or result.stdout.count(closed_marker) != 1:
        raise SystemExit(f"Incomplete runtime bundle census; see {log}")
    bundle_start = result.stdout.index(bundle_marker) + len(bundle_marker)
    closed_start = result.stdout.index(closed_marker)
    if closed_start <= bundle_start:
        raise SystemExit(f"Out-of-order runtime bundle census; see {log}")
    bundle_axioms = printed_axioms(result.stdout[bundle_start:closed_start])
    closed_section = result.stdout[closed_start + len(closed_marker):]
    if not bundle_axioms or printed_axioms(closed_section):
        raise SystemExit(f"Runtime bundle is empty or its witness is not closed; see {log}")
    if "Closed under the global context" not in closed_section:
        raise SystemExit(f"Runtime witness did not report closure; see {log}")

    missing = {
        theorem: sorted(axioms - bundle_axioms)
        for theorem, axioms in theorem_axioms.items()
        if axioms - bundle_axioms
    }
    if missing:
        details = "\n".join(f"{theorem}: {names}" for theorem, names in sorted(missing.items()))
        raise SystemExit(
            f"Theorem-used axioms absent from the closed runtime bundle:\n{details}\n"
            f"See {log}"
        )
    used = set().union(*theorem_axioms.values())
    print(
        f"Runtime axiom bundle covers {len(used)} theorem-used axioms "
        f"across {len(theorem_axioms)} theorems; "
        f"actual bundle has {len(bundle_axioms)} axioms and closed witness."
    )


def main() -> None:
    if len(sys.argv) not in (5, 6) or (len(sys.argv) == 6 and sys.argv[5] != "--bundle"):
        raise SystemExit("usage: check-bigarray-assumption-census.py "
                         "BUILD TRANSLATOR MANIFEST SWITCH [--bundle]")
    build, translator, manifest, switch = map(Path, sys.argv[1:5])
    require_bundle = len(sys.argv) == 6
    project = build / "project-proofs"
    declarations = []
    modules = []
    for source in sorted(project.rglob("*.v")):
        if source.name == "AssumptionCensus.v":
            continue
        relative = source.relative_to(project)
        module = "MonadExecutionSpecs." + ".".join(relative.with_suffix("").parts)
        modules.append(module)
        declarations.extend(
            (str(relative), name, module)
            for name in THEOREM.findall(source.read_text())
        )
    if not declarations:
        raise SystemExit("No project theorems found for assumption census")

    census = project / "AssumptionCensus.v"
    lines = ["From Stdlib Require Import String.", "Open Scope string_scope."]
    lines.extend(f"Require Import {module}." for module in modules)
    for index, (_, name, module) in enumerate(declarations):
        lines.append(f'Check "CENSUS-BEGIN {index}".')
        lines.append(f"Print Assumptions {module}.{name}.")
    census.write_text("\n".join(lines) + "\n")

    command = [
        "opam", "exec", f"--switch={switch}", "--", "rocq", "c",
        "-Q", "generated", "MonadVM",
        "-Q", "support", "MonadVM.Support",
        "-Q", "project-proofs", "MonadExecutionSpecs",
        "-Q", str(translator), "RocqOfOCaml",
        "project-proofs/AssumptionCensus.v",
    ]
    result = subprocess.run(command, cwd=build, text=True, capture_output=True)
    log = build / "bigarray-assumption-census.log"
    log.write_text(result.stdout + result.stderr)
    if result.returncode:
        raise SystemExit(f"Assumption census failed; see {log}:\n{result.stderr[-2000:]}")

    markers = list(MARKER.finditer(result.stdout))
    if len(markers) != len(declarations):
        raise SystemExit(
            f"Incomplete assumption census: {len(markers)} markers for "
            f"{len(declarations)} theorems; see {log}"
        )
    actual = set()
    dependencies = {}
    theorem_axioms = {}
    for index, marker in enumerate(markers):
        if int(marker.group(1)) != index:
            raise SystemExit(f"Out-of-order assumption census marker {marker.group(1)}")
        end = markers[index + 1].start() if index + 1 < len(markers) else len(result.stdout)
        relative, name, _ = declarations[index]
        section = result.stdout[marker.end():end]
        theorem_axioms[(relative, name)] = printed_axioms(section)
        if AXIOM in theorem_axioms[(relative, name)]:
            actual.add((relative, name))
            dependencies[(relative, name)] = section

    runtime = (translator / "OCamlBigarray.v").read_text()
    if str(manifest) == "-":
        if "Definition get `{Unreachable ascii}" in runtime:
            if actual:
                raise SystemExit(
                    f"Executable Bigarray read still occurs as a theorem axiom: {sorted(actual)}"
                )
            print(f"Executable Bigarray census: {len(declarations)} theorems, "
                  "zero Array1.get axiom dependents.")
        elif "Parameter get : Bigstring.t -> int -> ascii" in runtime:
            concrete = "OCamlBigarray.Array1.get : Bigstring.t -> Basics.int -> Ascii.ascii"
            for dependent, assumptions in dependencies.items():
                if concrete not in assumptions:
                    raise SystemExit(f"Unexpected Bigarray assumption type: {dependent}")
            print(f"Concrete Bigarray census: {len(declarations)} theorems, "
                  f"{len(actual)} byte-read dependents, all monomorphic.")
        else:
            raise SystemExit("Bigarray read has an unrecognised definition or axiom")
        if require_bundle:
            check_bundle(build, translator, switch, theorem_axioms)
        for relative, name in sorted(actual):
            print(f"{relative}\t{name}")
        return

    expected = set()
    for line in manifest.read_text().splitlines():
        if not line or line.startswith("#") or line.startswith("file\t"):
            continue
        fields = line.split("\t")
        if len(fields) != 2:
            raise SystemExit(f"Malformed manifest row: {line}")
        expected.add(tuple(fields))
    if expected and "Parameter get : forall" not in runtime:
        raise SystemExit("Bigarray axiom changed; reassess and retire the warning manifest")
    if actual != expected:
        extra = sorted(actual - expected)
        stale = sorted(expected - actual)
        raise SystemExit(
            f"Bigarray assumption census differs from manifest: "
            f"unlisted={extra}, stale={stale}; see {log}"
        )
    print(
        f"Bigarray assumption census matches: {len(declarations)} theorems, "
        f"{len(actual)} flagged dependents."
    )


if __name__ == "__main__":
    main()
