#!/usr/bin/env python3
"""Expand synthetic Dune namespace imports into concrete Rocq imports."""

from __future__ import annotations

import re
import sys
from pathlib import Path


def read_text(path: Path) -> str:
    # The translator can emit OCaml byte-string payloads that are not valid
    # UTF-8. Ruby's File.binread preserves them, and this rewrite only matches
    # ASCII syntax, so use a reversible one-byte mapping here as well.
    with path.open(encoding="latin-1", newline="") as source:
        return source.read()


def write_text(path: Path, contents: str) -> None:
    with path.open("w", encoding="latin-1", newline="") as target:
        target.write(contents)


def main() -> None:
    if len(sys.argv) != 5:
        raise SystemExit(
            f"usage: {sys.argv[0]} TARGET MANIFEST DEPENDENCIES CURRENT_LOGICAL_PATH"
        )

    target, manifest_path, dependency_path = map(Path, sys.argv[1:4])
    current_logical_path = sys.argv[4]

    logical_paths: dict[str, str] = {}
    for line in read_text(manifest_path).splitlines():
        fields = line.split("\t", 2)
        if len(fields) == 3:
            unit, _source, prefix = fields
            logical_paths[unit] = f"MonadVM.{prefix}"

    dependencies: list[str] = []
    if dependency_path.is_file():
        for unit in read_text(dependency_path).splitlines():
            logical_path = logical_paths.get(unit)
            if logical_path is not None:
                dependencies.append(logical_path)

    contents = read_text(target)
    requirement_pattern = re.compile(
        r"^Require (MonadVM(?:\.[A-Za-z0-9_']+)+)\.\n", re.MULTILINE
    )

    def replace_requirement(match: re.Match[str]) -> str:
        namespace = match.group(1)
        if namespace == current_logical_path:
            return ""
        if namespace in dependencies:
            return match.group(0)

        concrete = sorted(
            {path for path in dependencies if path.startswith(f"{namespace}.")}
        )
        if not concrete:
            if current_logical_path.startswith(f"{namespace}."):
                return ""
            return match.group(0)
        return "".join(f"Require {path}.\n" for path in concrete)

    contents = requirement_pattern.sub(replace_requirement, contents)

    existing_requirements = set(
        re.findall(
            r"^Require(?: Import| Export)? (MonadVM(?:\.[A-Za-z0-9_']+)+)\.",
            contents,
            re.MULTILINE,
        )
    )
    missing_requirements = [
        path
        for path in sorted(set(dependencies))
        if path not in existing_requirements
        and re.search(
            rf"(?<![A-Za-z0-9_']){re.escape(path)}(?![A-Za-z0-9_'])", contents
        )
    ]

    if missing_requirements:
        lines = contents.splitlines(keepends=True)
        insertion_index = -1
        for index, line in enumerate(lines):
            if re.match(r"^Require(?: Import| Export)? ", line):
                insertion_index = index
        lines[insertion_index + 1 : insertion_index + 1] = [
            f"Require {path}.\n" for path in missing_requirements
        ]
        contents = "".join(lines)

    write_text(target, contents)


if __name__ == "__main__":
    main()
