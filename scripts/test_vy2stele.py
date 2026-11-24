#!/usr/bin/env python3
"""Compile, translate and execute Vyper translation regressions (VYPER selects the compiler).

Run after `lake build Stele.Interp Stele.Notation Stele.MetaVyperLayout`:
  VYPER=/path/to/vyper-0.4.3 python3 -B -m unittest discover -s scripts -p test_vy2stele.py
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from vy2stele import Translator

ROOT = Path(__file__).resolve().parent.parent
VYPER = os.environ.get("VYPER") or shutil.which("vyper")

# Default arguments, tuple returns, loops over ranges and arrays, unsafe arithmetic, convert,
# abs/min/max, flags, struct literals, DynArray push/pop.  `exercise(2)` returns (10, 6, 3, 4).
SOURCE = """
# pragma version ^0.4.3

struct Pos:
    amount: uint256
    owner: address

flag Perm:
    READ
    WRITE

FEE: constant(uint256) = 3
balances: public(HashMap[address, uint256])
positions: HashMap[uint256, Pos]
items: DynArray[uint256, 8]
perms: HashMap[address, Perm]
count: uint256

@internal
def _bump(x: uint256, y: uint256 = 2) -> uint256:
    return x + y

@internal
def _pair(x: uint256) -> (uint256, uint256):
    return x + 1, x * 2

@external
def exercise(n: uint256, k: uint256 = 5) -> (uint256, uint256, uint256, uint256):
    self.count = self._bump(n)
    a: uint256 = 0
    b: uint256 = 0
    a, b = self._pair(self.count)
    total: uint256 = 0
    for i: uint256 in range(4):
        self.items.append(i)
    for v: uint256 in self.items:
        total += v
    for j: uint256 in range(n, bound=10):
        total = unsafe_sub(total, 1)
    s: int256 = convert(total, int256) - 10
    m: uint256 = convert(abs(s), uint256)
    self.perms[msg.sender] = Perm.READ | Perm.WRITE
    self.positions[n] = Pos(amount=m, owner=msg.sender)
    x: uint256 = max(a, FEE) + min(b, k)
    y: uint256 = self.positions[n].amount if Perm.WRITE in self.perms[msg.sender] else 0
    self.items.pop()
    return x, y, len(self.items), total
"""

CHECK = """
open Stele ABI
private abbrev u256 : StorageType := .elem (.int (.uint ⟨256, by decide⟩))
private def decls : List VyperStorageDecl :=
  [{ name := "balances", ty := .mapping .address (.elem (.int (.uint ⟨256, by decide⟩))) },
   { name := "positions", ty := .mapping (.int (.uint ⟨256, by decide⟩))
       (.struct "Pos" [("amount", .elem (.int (.uint ⟨256, by decide⟩))), ("owner", .elem .address)]) },
   { name := "items", ty := .dynamicArray (.elem (.int (.uint ⟨256, by decide⟩))) 8 },
   { name := "perms", ty := .mapping .address (.elem (.int (.uint ⟨256, by decide⟩))) },
   { name := "count", ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
private def cfg : Config :=
  { storageBackend := vyperBoundedStorage! [decls]
    externalABI := defaultExternalCallABI.withMode DecodeMode.vyper
    selfDeployment := fun code _ => some code }
private def evm : EVM.State :=
  { (default : EVM.State) with
    executionEnv := { (default : Ethereum.ExecutionEnv) with codeOwner := .ofNat 256, perm := true }
    accountMap := (∅ : Ethereum.AccountMap).insert (.ofNat 256) default }
private def result : Option (List Value) := do
  let c := VyperDraft.Syntax.contractSyntax
  let t ← c.transitions.find? (fun t => t.name == "exercise" && t.params.length == 1)
  let locals : Store := (∅ : Store).insert "n" (.int 2)
  let .result (.returned _ _ vs) :=
    (Interp.execTransitionBody .cancun 2000 (Interp.thetaOracle .cancun) () cfg c evm locals t.body ∅).1 | none
  vs
#guard result = some [.int 10, .int 6, .int 3, .int 4]
#guard VyperDraft.Syntax.contractSyntax.transitions.map (·.params.length) = [1, 2, 1]
"""

# Modules, exports, flags, raw_call, send, nonreentrancy, external calls and the holes the
# translator leaves (sha256, a bytes literal).
MODULE_SOURCES = {
    "lib/ownable.vy": """
# pragma version ^0.4.3
owner: public(address)
tally: HashMap[address, uint256]

@deploy
def __init__():
    self.owner = msg.sender

@internal
def _check_owner():
    assert msg.sender == self.owner, "not owner"

@external
def transfer_ownership(new_owner: address):
    self._check_owner()
    self.owner = new_owner
""",
    "Main.vy": """
# pragma version ^0.4.3
from lib import ownable

initializes: ownable
exports: ownable.transfer_ownership

interface IOracle:
    def price(token: address) -> uint256: view
    def poke(x: uint256): nonpayable

oracle: IOracle
scores: HashMap[address, uint256]

@deploy
def __init__(oracle: address):
    ownable.__init__()
    self.oracle = IOracle(oracle)

@external
@nonreentrant
def sweep(targets: DynArray[address, 3], data: Bytes[64]) -> uint256:
    ownable._check_owner()
    total: uint256 = 0
    for t: address in targets:
        total += self.scores[t]
    ok: bool = raw_call(msg.sender, data, max_outsize=0, value=0, revert_on_failure=False)
    send(msg.sender, total)
    p: uint256 = staticcall self.oracle.price(msg.sender)
    extcall self.oracle.poke(p)
    ownable.tally[msg.sender] = total
    h: bytes32 = sha256(data)
    c: Bytes[100] = concat(data, b"\\x01")
    return total
""",
}


def compile_vyper(test: unittest.TestCase, directory: Path, main: str) -> tuple[dict, dict, dict[str, str]]:
    outputs = []
    for fmt in ("annotated_ast", "layout", "method_identifiers"):
        result = subprocess.run([VYPER, "-f", fmt, "--evm-version", "cancun", "--path", str(directory),
                                 str(directory / main)], text=True, capture_output=True)
        test.assertEqual(result.returncode, 0, result.stderr)
        outputs.append(json.loads(result.stdout))
    return outputs[0], outputs[1], outputs[2]


def translate(test: unittest.TestCase, sources: dict[str, str], main: str) -> Translator:
    with tempfile.TemporaryDirectory(prefix="vy2stele-test-") as directory:
        root = Path(directory)
        for name, text in sources.items():
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            (root / name).write_text(text, encoding="utf-8")
        annotated, layout, method_ids = compile_vyper(test, root, main)
    return Translator(annotated, comment_holes=False, evm_version="cancun", layout=layout,
                      method_identifiers=method_ids)


def elaborate(test: unittest.TestCase, draft: str, check: str) -> None:
    with tempfile.TemporaryDirectory(prefix="stele-vyper-test-") as directory:
        path = Path(directory) / "Draft.lean"
        path.write_text("import Stele.Interp\nimport Stele.MetaVyperLayout\n" + draft + check)
        checked = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                 text=True, capture_output=True, timeout=300)
        test.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr + "\n" + draft)


@unittest.skipUnless(VYPER, "set VYPER to a Vyper 0.4.3 compiler")
class Execution(unittest.TestCase):
    def test_source_to_execution(self):
        translator = translate(self, {"Exercise.vy": SOURCE}, "Exercise.vy")
        draft = translator.render("VyperDraft", "selector")
        self.assertEqual(translator.holes, [])
        self.assertIn("function exercise(uint256 n) external", draft)
        self.assertIn("uint256 k = 5;", draft)
        self.assertIn("var __c1 = _pair(count);", draft)
        self.assertIn("total = uint256(total - 1);", draft)
        self.assertIn("require(n <= 10);", draft)
        self.assertIn("perms[msg.sender] = 1 |[uint256] 2;", draft)
        self.assertEqual([v["signature"] for v in translator.variants],
                         ["balances(address)", "exercise(uint256)", "exercise(uint256,uint256)"])
        elaborate(self, draft, CHECK)


@unittest.skipUnless(VYPER, "set VYPER to a Vyper 0.4.3 compiler")
class Modules(unittest.TestCase):
    def test_modules_calls_and_holes(self):
        translator = translate(self, MODULE_SOURCES, "Main.vy")
        draft = translator.render("VyperDraft", "selector")
        holes = " ".join(translator.holes)
        self.assertIn("sha256", holes)
        self.assertIn("bytes literal", holes)
        self.assertEqual(len(translator.holes), 2)
        self.assertIn("address ownable_owner;", draft)
        self.assertIn("uint256 transient nonreentrant_lock;", draft)
        self.assertIn("var __c0 = ownable___init__();", draft)
        self.assertIn("function transfer_ownership(address new_owner) external", draft)
        self.assertIn("function sweep_body(address[] memory targets, bytes memory data) internal", draft)
        self.assertIn("require(nonreentrant_lock != 1);", draft)
        self.assertIn("uint256 p = oracle.price{view}(msg.sender);", draft)
        self.assertIn("require(oracle.code.length > 0);", draft)
        self.assertIn("var __c", draft)
        self.assertIn(".call{value: total}(new bytes(0));", draft)
        self.assertIn("msg.sender.call{value: 0}(data);", draft)
        self.assertIn("oracle = oracle_;", draft)   # the constructor parameter shadows the state variable
        self.assertEqual(sorted(translator.external_calls), ["poke", "price"])
        self.assertTrue(translator.external_calls["price"]["view"])
        self.assertEqual([v["bounded"] for v in translator.variants if v["name"] == "sweep"], [["targets", "data"]])
        # with holes as comments the rest of the draft elaborates
        translator = translate(self, MODULE_SOURCES, "Main.vy")
        translator.comment_holes = True
        elaborate(self, translator.render("VyperDraft", "selector"), "")


if __name__ == "__main__":
    unittest.main()
