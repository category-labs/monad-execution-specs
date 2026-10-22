#!/usr/bin/env python3
"""Check that hand-written block equality visits every generated record field."""

from collections import Counter
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
SUPPORT = (ROOT / "rocq/support/BlockEquality.v").read_text()
CHECKS = (
    ("access_equal", "Transaction.Access.t", "T.Access.t"),
    ("authorization_equal", "Transaction.Authorization.t", "T.Authorization.t"),
    ("legacy_equal", "Transaction.legacy_tx", "T.legacy_tx"),
    ("access_list_equal", "Transaction.access_list_tx", "T.access_list_tx"),
    ("fee_market_equal", "Transaction.fee_market_tx", "T.fee_market_tx"),
    ("set_code_equal", "Transaction.set_code_tx", "T.set_code_tx"),
    ("withdrawal_equal", "Withdrawal.t", "E.Withdrawal.t"),
    ("header_equal", "Block.Header.t", "E.Block.Header.t"),
    ("equal", "Block.t", "E.Block.t"),
)


def records(source: str) -> dict[str, list[str]]:
    stack: list[str] = []
    found: dict[str, list[str]] = {}
    current: tuple[str, list[str]] | None = None
    for line in source.splitlines():
        module = re.match(r"\s*Module\s+([A-Za-z_]\w*)\.", line)
        if module and ":=" not in line:
            stack.append(module.group(1))
        if re.match(r"\s*Record record\b.*:= Build \{", line):
            current = (".".join(stack), [])
        elif current is not None:
            field = re.match(r"\s*([A-Za-z_]\w*)\s*:", line)
            if field:
                current[1].append(field.group(1))
            if "}." in line:
                if current[0] in found:
                    raise ValueError(f"duplicate generated record: {current[0]}")
                found[current[0]] = current[1]
                current = None
        end = re.match(r"\s*End\s+([A-Za-z_]\w*)\.", line)
        if end:
            if not stack or stack.pop() != end.group(1):
                raise ValueError(f"unexpected module end: {line}")
    if stack or current is not None:
        raise ValueError("unclosed generated module or record")
    return found


def definitions(source: str) -> dict[str, str]:
    starts = list(re.finditer(r"^Definition\s+([a-z_]\w*)\b", source, re.MULTILINE))
    return {
        match.group(1): source[match.end() : starts[index + 1].start()]
        if index + 1 < len(starts)
        else source[match.end() :]
        for index, match in enumerate(starts)
    }


def check_tree(profile: str) -> int:
    path = ROOT / f"rocq/generated/{profile}/Chain/Ethereum.v"
    # The generated source may contain raw byte literals outside UTF-8.
    generated = path.read_bytes().decode("utf-8", "surrogateescape")
    record_fields = records(generated)
    functions = definitions(SUPPORT)
    checked = 0
    for function, record, prefix in CHECKS:
        expected = record_fields[record]
        body = functions[function]
        for side in ("x", "y"):
            selectors = re.findall(rf"\b{side}\.\(([^)]+)\)", body)
            selected = []
            for selector in selectors:
                marker = prefix + "."
                if not selector.startswith(marker):
                    raise ValueError(
                        f"{profile}: {function} has unrelated {side} selector {selector}"
                    )
                selected.append(selector[len(marker) :])
            if Counter(selected) != Counter(expected):
                raise ValueError(
                    f"{profile}: {function} {side} fields differ: "
                    f"expected={expected}, selected={selected}"
                )
        checked += len(expected)

    transaction_source = generated.split("Module Transaction.", 1)[1].split(
        "End Transaction.", 1
    )[0]
    constructor_declaration = re.search(
        r"^\s*Inductive t : Set :=\s*\n((?:\s*\|\s*\w+[^\n]*\n)+)",
        transaction_source,
        re.MULTILINE,
    )
    if constructor_declaration is None:
        raise ValueError(f"{profile}: transaction constructors not found")
    expected_branches = set(
        re.findall(r"^\s*\|\s*(\w+)\s*:",
                   constructor_declaration.group(1), re.MULTILINE)
    )
    transaction = functions["transaction_equal"]
    branches = re.findall(
        r"^\s*\|\s*T\.(\w+)\s+x,\s*T\.(\w+)\s+y\s*=>",
        transaction,
        re.MULTILINE,
    )
    if {left for left, right in branches if left == right} != expected_branches:
        raise ValueError(f"{profile}: transaction branches differ: {branches}")
    if len(branches) != len(expected_branches) or "| _, _ => false" not in transaction:
        raise ValueError(f"{profile}: transaction constructor coverage is incomplete")

    print(f"{profile}: {checked} fields across {len(CHECKS)} records; "
          "all transaction constructors covered")
    return checked


def main() -> None:
    check_tree("next")


if __name__ == "__main__":
    main()
