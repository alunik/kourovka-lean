#!/usr/bin/env python3
"""Reproduce and compare the inline rootWords certificate for Problem 21.44.

Uses only the Python standard library. The permutations and multiplication
convention are specified here independently of the Lean source. The emitted
fragment is data; Lean's rootWords_cover theorem checks its coverage.
"""

import argparse
from collections import deque
import hashlib
from itertools import permutations
from pathlib import Path
import sys


REPOSITORY = Path(__file__).resolve().parent.parent
DEFAULT_SOURCE = (
    REPOSITORY / "Kourovka/Problems/P21_44/Proof/WreathGeneration.lean"
)
HEADER = b"private def rootWords : List (List Bool) :=\n"
NEXT_DECLARATION = b"\n\nset_option maxRecDepth 100000 in\n"

# Zero-based images. These are (0 1 2)^-1 and (2 3 4)^-1, matching
# rootA = swap 1 2 * swap 0 1 and rootB = swap 3 4 * swap 2 3.
IDENTITY = (0, 1, 2, 3, 4)
ROOT_A = (2, 0, 1, 3, 4)
ROOT_B = (0, 1, 4, 2, 3)


def multiply(left, right):
    """Mathlib permutation multiplication: (left * right)(i) = left(right(i))."""
    return tuple(left[right[i]] for i in range(5))


def is_even(permutation):
    inversions = sum(
        permutation[i] > permutation[j] for i in range(5) for j in range(i + 1, 5)
    )
    return inversions % 2 == 0


def generate_words():
    """Breadth-first discovery, appending rootA before rootB at every vertex."""
    words = {IDENTITY: ()}
    pending = deque([IDENTITY])
    while pending:
        current = pending.popleft()
        for letter, generator in ((True, ROOT_A), (False, ROOT_B)):
            following = multiply(current, generator)
            if following not in words:
                words[following] = words[current] + (letter,)
                pending.append(following)

    alternating_group = {p for p in permutations(range(5)) if is_even(p)}
    if set(words) != alternating_group or len(words) != 60:
        raise RuntimeError("The generated permutations do not equal the 60 elements of A5")
    result = list(words.values())
    if max(map(len, result)) != 8:
        raise RuntimeError("The expected maximum word length is eight")
    return result


def render_fragment(words):
    rendered = [
        "[" + ", ".join("true" if letter else "false" for letter in word) + "]"
        for word in words
    ]
    return HEADER + ("  [" + ",\n   ".join(rendered) + "]\n").encode("ascii")


def source_fragment(source):
    """Extract the complete definition and its final LF, without the blank separator."""
    contents = source.read_bytes()
    if contents.count(HEADER) != 1:
        raise ValueError(f"Expected exactly one rootWords definition in {source}")
    start = contents.index(HEADER)
    try:
        end = contents.index(NEXT_DECLARATION, start)
    except ValueError as error:
        raise ValueError(f"Cannot find the end of rootWords in {source}") from error
    return contents[start:end] + b"\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--output", type=Path, metavar="FILE", help="write the Lean fragment to FILE")
    output.add_argument(
        "--output-dir", type=Path, metavar="DIR", help="write DIR/rootWords.lean.fragment"
    )
    parser.add_argument(
        "--check",
        nargs="?",
        type=Path,
        const=DEFAULT_SOURCE,
        metavar="SOURCE",
        help="byte-compare with SOURCE (default: the repository's WreathGeneration.lean)",
    )
    args = parser.parse_args()
    try:
        words = generate_words()
        generated = render_fragment(words)
        destination = args.output
        if args.output_dir is not None:
            destination = args.output_dir / "rootWords.lean.fragment"
        if destination is not None:
            protected_sources = {DEFAULT_SOURCE.resolve()}
            if args.check is not None:
                protected_sources.add(args.check.resolve())
            if destination.resolve() in protected_sources:
                raise ValueError("Choose a separate output file; this script never replaces the Lean module")
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(generated)
        elif args.check is None:
            sys.stdout.buffer.write(generated)

        if args.check is not None:
            existing = source_fragment(args.check)
            if generated != existing:
                print(f"MISMATCH: generated rootWords differs from {args.check}", file=sys.stderr)
                return 1
            print(f"PASS: rootWords matches {args.check} byte for byte")
        digest = hashlib.sha256(generated).hexdigest()
        print(f"60 words; maximum length 8; fragment SHA256 {digest}", file=sys.stderr)
        return 0
    except (OSError, ValueError, RuntimeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
