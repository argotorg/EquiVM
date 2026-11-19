#!/usr/bin/env python3
"""Reproduce the superseded capacity-cutoff calculation, not the current gas bound.

TakeCapacityWitness.lean invalidates the former minimal-cost claim. Conditions.lean
now uses the user-authorized g.toNat <= 2^24 bound. This script preserves the
historical arithmetic and measurements described in HANDOFF.md.
"""
from fractions import Fraction
import json
from pathlib import Path
import re

directory = Path(__file__).resolve().parent


def memory(words):
    return 3 * words + words * words // 512


def inverse_cap(gas):
    """Least x with x - floor(x/64) >= gas, for positive gas."""
    assert gas > 0
    result = gas + (gas - 1) // 63
    assert result - result // 64 >= gas
    assert result - 1 - (result - 1) // 64 < gas
    return result


total = 2**59 - 1
center = (64 * total - 47616) // 127


def cost(parent):
    reply = total - parent
    return memory(parent) + 3 * parent + 26767 + inverse_cap(memory(reply) + 15)


# Removing floors changes the cost by less than 4. The real quadratic has
# curvature 127/(63*512); distance 63 already increases it by more than 15.
# Therefore all integer minimizers occur in this interval.
assert Fraction(127 * 63**2, 63 * 512) > 4
candidates = [(cost(p), p) for p in range(center - 64, center + 65)]
bound = min(c for c, _ in candidates)
minimizers = [p for c, p in candidates if c == bound]
assert bound == 327073817860464196263953616796569
assert bound > 2**24
assert "g.toNat ≤ 2^24" in (directory / "Conditions.lean").read_text()

# Check the measured pre-CALL cost and capacities, including the copy slope.
log = (directory / "provenance/gas-trace.log").read_text()
parts = re.split(r"n=(\d+), buy=(true|false), assets=(true|false),", log)
measured = []
for i in range(1, len(parts), 4):
    size, buy, assets, body = parts[i:i + 4]
    calls = re.findall(r"pc=23522, spent=(\d+), words=(\d+), free=(\d+), returned=(\d+)", body)
    assert len(calls) == 2 and "succeeded" in body
    spent, words, free, _ = map(int, calls[1])
    assert free == 4064 + int(size) and words * 32 == free
    base = spent - memory(words) - 3 * words
    if buy == "true" and assets == "false":
        assert base == 26667
    else:
        assert base > 26667
    measured.append({"inputBytes": int(size), "buy": buy == "true",
                     "assetsCap": assets == "true", "baseGas": base})
assert len(measured) == 7

parent = minimizers[0]
reply = total - parent
record = {
    "strictUpperBound": str(bound),
    "formula": "min_p C(p)+3*p+26767+J(C(2^59-1-p)+15)",
    "C": "3*w+floor(w*w/512)",
    "J": "q+floor((q-1)/63)",
    "minimizingParentWords": list(map(str, minimizers)),
    "witness": {
        "parentWords": str(parent), "replyWords": str(reply),
        "replyBytes": str(32 * reply), "takerCallbackDataBytes": str(32 * (parent - 127)),
        "parentGasBeforeCall": str(memory(parent) + 3 * parent + 26667),
        "calleeGas": str(memory(reply) + 15),
        "parentGasAfterCall": str(inverse_cap(memory(reply) + 15) - memory(reply) - 15),
    },
    "ordinarySizeMeasurements": measured,
    "status": "historical cutoff superseded by 2^24; minimal-cost claim invalidated",
}
(directory / "provenance/gas-bound.json").write_text(json.dumps(record, indent=2) + "\n")
print(f"Historical cutoff: {bound}; seven recorded measurements match; current bound: 2^24")
