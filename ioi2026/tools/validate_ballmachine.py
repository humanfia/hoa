#!/usr/bin/env python3

"""Validate a Ball Machine grader output up to legal internal-node relabeling."""

from __future__ import annotations

import pathlib
import sys


def fail(message: str) -> "NoReturn":
    raise SystemExit(f"Ball Machine validation failed: {message}")


def read_integers(path: pathlib.Path) -> list[int]:
    try:
        return [int(token) for token in path.read_text().split()]
    except (OSError, ValueError) as error:
        fail(f"cannot parse {path}: {error}")


def tree_signature(parent: list[int], leaf_count: int) -> str:
    node_count = len(parent) + 1
    root = node_count - 1
    children: list[list[int]] = [[] for _ in range(node_count)]

    for node, ancestor in enumerate(parent):
        if not 0 <= ancestor < node_count:
            fail(f"parent of node {node} is out of range")
        if ancestor == node:
            fail(f"node {node} is its own parent")
        children[ancestor].append(node)

    for leaf in range(leaf_count):
        if children[leaf]:
            fail(f"fixed leaf {leaf} has children")

    state = [0] * node_count

    def visit(node: int) -> str:
        if state[node] == 1:
            fail("parent array contains a cycle")
        if state[node] == 2:
            fail("parent array reaches a node more than once")
        state[node] = 1
        if node < leaf_count:
            signature = f"L{node};"
        else:
            parts = sorted(visit(child) for child in children[node])
            signature = "I" + "".join(f"{len(part)}:{part}" for part in parts)
        state[node] = 2
        return signature

    signature = visit(root)
    if any(value != 2 for value in state):
        fail("parent array is not one tree rooted at N-1")
    return signature


def main() -> None:
    if len(sys.argv) != 3:
        fail("usage: validate_ballmachine.py INPUT OUTPUT")

    input_values = read_integers(pathlib.Path(sys.argv[1]))
    if len(input_values) < 2:
        fail("public input is incomplete")
    node_count, leaf_count = input_values[:2]
    expected_parent = input_values[2:]
    if len(expected_parent) != node_count - 1:
        fail("public input parent array has the wrong length")

    output_values = read_integers(pathlib.Path(sys.argv[2]))
    if len(output_values) < 4:
        fail("grader output is incomplete")
    collect_count, maximum_value, resource_cost, result_size = output_values[:4]
    actual_parent = output_values[4:]

    if min(collect_count, maximum_value, resource_cost) < 0:
        fail("resource counters must be nonnegative")
    if collect_count + maximum_value != resource_cost:
        fail("K + B does not equal C")
    if resource_cost > 44:
        fail("public run exceeds the full-score resource bound")
    if result_size != node_count - 1 or len(actual_parent) != result_size:
        fail("returned parent array has the wrong length")

    expected = tree_signature(expected_parent, leaf_count)
    actual = tree_signature(actual_parent, leaf_count)
    if actual != expected:
        fail("returned tree is not leaf- and root-preserving isomorphic")


if __name__ == "__main__":
    main()
