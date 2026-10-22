#!/usr/bin/env python3
"""Require the refinement assumption report to match the reviewed budget."""

import argparse
from pathlib import Path
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("report", type=Path)
parser.add_argument("--allow-subset", action="store_true",
                    help="accept fewer, but never new, compatibility parameters")
args = parser.parse_args()

expected_axioms = [
    "Axioms:",
    "Basics.Stdlib.polymorphic_compare : forall a : Set, a -> a -> Basics.int",
    "Basics.Stdlib.physical_equal : forall a : Set, a -> a -> bool",
    "OCamlZ.hash : BinNums.Z -> Basics.int",
    "OCamlZ.format : String.string -> BinNums.Z -> String.string",
]
expected = ["Closed under the global context"] * 19 + expected_axioms * 5
actual = args.report.read_text().splitlines()
if args.allow_subset:
    closed = actual[:19]
    remainder = actual[19:]
    allowed = set(expected_axioms[1:])
    if closed != ["Closed under the global context"] * 19 or not remainder:
        raise SystemExit("Refinement assumption budget changed")
    if len(remainder) % 5:
        raise SystemExit("Refinement assumption report is incomplete")
    block = remainder[:len(remainder) // 5]
    if block[0] != "Axioms:" or not set(block[1:]).issubset(allowed) or \
       len(block[1:]) != len(set(block[1:])) or remainder != block * 5:
        raise SystemExit("Pruned refinement assumptions exceed the recorded budget")
    print(f"Pruned refinement assumptions match: 19 closed, 5 with {len(block) - 1} recorded parameters.")
    sys.exit(0)
if actual != expected:
    raise SystemExit(
        "Refinement assumption budget changed: expected 19 closed laws "
        "and 5 laws using only the four recorded compatibility parameters"
    )

print("Refinement assumptions match: 19 closed, 5 with four recorded parameters.")
