#!/usr/bin/env python3
"""Compile, translate and execute reference-passing regressions (SOLC selects the compiler).

Run after `lake build Solm.Interp Solm.Notation Solm.MetaSolidityLayout`:
  SOLC=/path/to/solc python3 -B -m unittest discover -s scripts -p test_sol2solm.py
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from sol2solm import Translator

ROOT = Path(__file__).resolve().parent.parent
SOLC = os.environ.get("SOLC") or shutil.which("solc")

SOURCE = """
pragma solidity ^0.8.23;
library Positions {
    struct State { uint128 value; }
    function set(State storage self, uint128 value) internal { self.value = value; }
}
library Pools {
    using Positions for Positions.State;
    struct State {
        uint128 value;
        mapping(int24 => Positions.State) positions;
        mapping(int24 => uint256) ticks;
    }
    function writeBoth(State storage a, State storage b) internal {
        a.value = 4;
        b.value += 3;
        a.positions[-2].set(9);
    }
}
contract References {
    mapping(uint256 => Pools.State) pools;
    function exercise() external returns (uint128, uint128, uint256, uint128) {
        Pools.State storage p = getPool(7);
        Pools.writeBoth(p, p);
        (Pools.State storage same, uint256 n) = pair(p);
        same.value += uint128(n);
        bump(same.ticks);
        Pools.State storage rebound = same;
        rebound = pools[8];
        rebound.value = 99;
        (rebound, n) = forward(p);
        rebound.value += 1;
        (rebound, p) = (pools[8], rebound);
        p.value += 1;
        rebound.value += 1;
        return (pools[7].value, pools[7].positions[-2].value, pools[7].ticks[-2], pools[8].value);
    }
    function getPool(uint256 id) internal view returns (Pools.State storage pool) {
        pool = pools[id];
    }
    function pair(Pools.State storage p) internal pure returns (Pools.State storage, uint256) {
        return (p, 5);
    }
    function forward(Pools.State storage p) internal pure returns (Pools.State storage, uint256) {
        return pair(p);
    }
    function bump(mapping(int24 => uint256) storage ticks) internal { ticks[-2] += 9; }
}
"""

CHECK = """
open Solm
private def cfg : Config :=
  { storageBackend := solidityStorage! [ReferenceDraft.Syntax.contractSyntax.structs]
      [ReferenceDraft.Syntax.contractSyntax.storage]
    externalABI := defaultExternalCallABI
    selfDeployment := fun code _ => some code }
private def evm : EVM.State :=
  { (default : EVM.State) with
    executionEnv := { (default : Ethereum.ExecutionEnv) with codeOwner := .ofNat 256, perm := true }
    accountMap := (∅ : Ethereum.AccountMap).insert (.ofNat 256) default }
private def result : Option (List Value) := do
  let c := ReferenceDraft.Syntax.contractSyntax
  let t ← c.transitions.find? (·.name == "exercise")
  let .result (.returned _ _ vs) :=
    (Interp.execTransitionBody 200 Interp.thetaOracle () cfg c evm ∅ t.body ∅).1 | none
  vs
#guard result = some [.int 14, .int 9, .int 9, .int 100]
"""

# Memory structs are passed by reference in Solidity: every modification below is visible to the
# caller, except through the argument copied from storage.
MEMORY_SOURCE = """
pragma solidity ^0.8.23;
library L {
    struct M { uint256 v; uint256 w; }
    function bump(M memory self, uint256 k) internal pure { self.v += k; }
}
contract References {
    using L for L.M;
    struct N { L.M a; L.M b; }
    mapping(uint256 => L.M) store;
    function set(L.M memory x) internal pure { x.v = 7; }
    function setRet(L.M memory x) internal pure returns (uint256) { x.w = 4; return x.v + 1; }
    function viaCallee(L.M memory x) internal pure returns (uint256 r) {
        set(x);
        x.bump(10);
        r = 3;
    }
    function early(L.M memory x) internal pure { if (x.v > 100) { return; } x.v = 1000; }
    function pub(L.M memory x) public pure returns (uint256) { x.v = 55; return 1; }
    function two(L.M memory x) internal view returns (L.M storage, uint256) { x.w += 1; return (store[1], 2); }
    function exercise() external returns (uint256, uint256, uint256, uint256) {
        L.M memory m = L.M(1, 0);
        set(m);
        uint256 r = setRet(m) + viaCallee(m);
        N memory n = N(L.M(0, 0), L.M(200, 0));
        early(n.a);
        early(n.b);
        uint256 p = pub(m);
        store[0].v = 9;
        set(store[0]);
        (L.M storage s, uint256 k) = two(m);
        s.v = k;
        return (m.v * 1000 + m.w, r + p, n.a.v + n.b.v, store[0].v + store[1].v);
    }
}
"""

MEMORY_CHECK = CHECK.replace("#guard result = some [.int 14, .int 9, .int 9, .int 100]",
                             "#guard result = some [.int 55005, .int 12, .int 1200, .int 11]")

# Patterns the write-back cannot model become holes.
MEMORY_HOLES_SOURCE = """
pragma solidity ^0.8.23;
contract References {
    struct M { uint256 v; }
    function aliased(M memory x) internal pure { M memory y = x; y.v = 3; }
    function rebound(M memory x) internal pure { x = M(0); x.v = 3; }
    function both(M memory a, M memory b) internal pure { a.v = 1; b.v = 2; }
    function exercise() external {
        M memory m = M(1);
        aliased(m);
        rebound(m);
        both(m, m);
    }
}
"""


def translate(test: unittest.TestCase, source: str) -> Translator:
    request = {"language": "Solidity", "sources": {"References.sol": {"content": source}},
               "settings": {"outputSelection": {"*": {"": ["ast"]}}}}
    result = subprocess.run([SOLC, "--standard-json"], input=json.dumps(request),
                            text=True, capture_output=True, check=True)
    output = json.loads(result.stdout)
    errors = [e for e in output.get("errors", []) if e["severity"] == "error"]
    test.assertEqual(errors, [], errors)
    return Translator({name: unit["ast"] for name, unit in output["sources"].items()},
                      "References", (0, 8, 23), via_ir=False, comment_holes=False,
                      extcodesize="auto", calldata_guard="auto")


def elaborate(test: unittest.TestCase, draft: str, check: str) -> None:
    with tempfile.TemporaryDirectory(prefix="solm-reference-test-") as directory:
        path = Path(directory) / "References.lean"
        path.write_text("import Solm.Interp\nimport Solm.MetaSolidityLayout\n" + draft + check)
        checked = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                 text=True, capture_output=True, timeout=120)
        test.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr + "\n" + draft)


@unittest.skipUnless(SOLC, "set SOLC to a Solidity 0.8.23+ compiler")
class StorageReferences(unittest.TestCase):
    def test_source_to_execution(self):
        translator = translate(self, SOURCE)
        self.assertEqual(translator.stype_of_string("struct Pools.State[] storage ref"), "Pools_State[]")
        draft = translator.render("ReferenceDraft", "source")
        self.assertEqual(translator.holes, [])
        self.assertIn("Pools_State storage", draft)
        self.assertIn("Positions_State storage", draft)
        self.assertIn("returns (Pools_State storage)", draft)
        elaborate(self, draft, CHECK)


@unittest.skipUnless(SOLC, "set SOLC to a Solidity 0.8.23+ compiler")
class MemoryReferences(unittest.TestCase):
    def test_writeback_to_execution(self):
        translator = translate(self, MEMORY_SOURCE)
        draft = translator.render("ReferenceDraft", "source")
        self.assertEqual(translator.holes, [])
        self.assertIn("function set(M memory x) internal returns (M)", draft)
        self.assertIn("returns (M storage, uint256, M)", draft)
        elaborate(self, draft, MEMORY_CHECK)

    def test_unsupported_patterns_are_holes(self):
        translator = translate(self, MEMORY_HOLES_SOURCE)
        translator.render("ReferenceDraft", "source")
        holes = " ".join(translator.holes)
        self.assertIn("modified through a local alias", holes)
        self.assertIn("x is reassigned and modified", holes)
        self.assertIn("overlapping memory arguments", holes)


if __name__ == "__main__":
    unittest.main()
