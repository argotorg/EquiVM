#!/usr/bin/env python3
"""Reproduce Morpho's deployment artifacts and adapt the generic skeleton generators.

No shared generator or generated Lean file is edited. The local rendering adapters select
the audited configuration in SpecSyntax and the existing bytes32 immutable round-trip lemma.
"""
from __future__ import annotations

import argparse
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import scaffold
import proof_skeleton
from evm_tools import keccak256

MODULE = "Benchmarks.Morpho.MorphoBlue"
ADDRESS = "bbbbbbbbbb9cc5e90e3b3af64bdaf62c37eeffcb"
COMMON = ["--dir", str(HERE), "--module", MODULE]


def immutable_header() -> None:
    render = scaffold.render_immutables_lean
    scaffold.render_immutables_lean = lambda *a: render(*a).replace(
        "`runtime.hex` is the runtime template with every\nimmutable site zeroed;",
        "`runtime.hex` is the exact mainnet runtime; `runtime.template.hex` has zeroed\nimmutable sites;")


def call_facts() -> None:
    """Derive callee types from the pinned solc ASTs, resolving struct ABI tuples."""
    build = json.loads((HERE / "Morpho.build.json").read_text())
    nodes = {n["id"]: n for ast in build["ast"].values()
             for n in scaffold.walk(ast) if "id" in n}

    def abi_type(node):
        ty = node["typeName"] if "typeName" in node else node
        if ty["nodeType"] == "ElementaryTypeName":
            return ty["name"]
        if ty["nodeType"] == "UserDefinedTypeName":
            decl = nodes[ty["referencedDeclaration"]]
            if decl["nodeType"] == "StructDefinition":
                return "(" + ",".join(abi_type(m) for m in decl["members"]) + ")"
            if decl["nodeType"] == "UserDefinedValueTypeDefinition":
                return abi_type(decl["underlyingType"])
            return "address"
        raise ValueError(ty)

    wanted = {"borrowRate", "price", "transfer", "transferFrom", "onMorphoSupply",
              "onMorphoRepay", "onMorphoSupplyCollateral", "onMorphoLiquidate", "onMorphoFlashLoan"}
    calls = {}
    for n in nodes.values():
        if n.get("nodeType") == "FunctionDefinition" and n.get("name") in wanted:
            calls[n["name"]] = {"name": n["name"],
                "params": [abi_type(p) for p in n["parameters"]["parameters"]],
                "returns": [abi_type(p) for p in n["returnParameters"]["parameters"]],
                "view": n["stateMutability"] in ["view", "pure"]}
    assert calls.keys() == wanted
    facts = {"contract": "Morpho", "externalCalls": list(calls.values()), "holes": [],
             "notes": ["Configuration lives in SpecSyntax.lean; raw calls also include precompile 1.",
                       "Selector 0x8069218f uses the raw fallback to delay signature.v decoding."]}
    (HERE / "Morpho.spec.json").write_text(json.dumps(facts, indent=2) + "\n")


def deployment_check() -> None:
    build = json.loads((HERE / "Morpho.build.json").read_text())
    template = bytes.fromhex((HERE / "runtime.template.hex").read_text())
    deployed = bytes.fromhex((HERE / "deployment.hex").read_text())
    domain_type = keccak256(b"EIP712Domain(uint256 chainId,address verifyingContract)")
    domain = keccak256(domain_type + (1).to_bytes(32, "big") + int(ADDRESS, 16).to_bytes(32, "big"))
    patched = bytearray(template)
    for imm in build["immutables"]:
        assert imm["name"] == "DOMAIN_SEPARATOR"
        for offset in imm["offsets"]:
            assert template[offset:offset + 32] == bytes(32)
            patched[offset:offset + 32] = domain
    assert bytes(patched) == deployed, "compiled runtime differs from deployment"
    assert bytes.fromhex((HERE / "runtime.hex").read_text()) == deployed
    evidence = json.loads((HERE / "deployment.json").read_text())
    assert hashlib.sha256(deployed).hexdigest() == evidence["runtime_sha256"]
    creation = bytes.fromhex((HERE / "creation.hex").read_text())
    assert hashlib.sha256(creation).hexdigest() == evidence["creation_sha256"]
    for name, digest in evidence["source_sha256"].items():
        assert hashlib.sha256((HERE.parent / "contracts" / name).read_bytes()).hexdigest() == digest
    print(f"ok   deployment: {len(deployed)} runtime bytes identical, including metadata")
    print(f"ok   constructor bytecode identical ({len(creation)} bytes, excluding argument)")
    print(f"ok   DOMAIN_SEPARATOR = 0x{domain.hex()}")
    print("ok   all 14 verified source files match the pinned upstream commit")


def artifacts(solc: str) -> None:
    args = ["compile", "--dir", str(HERE), "--solc", solc,
            "--sources-root", "../contracts", "--main", "src/Morpho.sol", "--contract", "Morpho",
            "--runs", "999999", "--via-ir", "--evm-version", "paris", "--metadata-hash", "",
            "--remapping", ":ds-test/=lib/forge-std/lib/ds-test/src/",
            "--remapping", ":forge-std/=lib/forge-std/src/"]
    assert scaffold.main(args) == 0
    template = (HERE / "runtime.hex").read_text()
    (HERE / "runtime.template.hex").write_text(template)
    build = json.loads((HERE / "Morpho.build.json").read_text())
    domain = keccak256(keccak256(b"EIP712Domain(uint256 chainId,address verifyingContract)")
                       + (1).to_bytes(32, "big") + int(ADDRESS, 16).to_bytes(32, "big"))
    patched = bytearray.fromhex(template)
    for imm in build["immutables"]:
        for offset in imm["offsets"]:
            patched[offset:offset + 32] = domain
    (HERE / "runtime.hex").write_text(patched.hex() + "\n")
    deployment_check()
    scaffold.write_hashes(HERE, "Morpho", HERE.parent / "contracts")
    immutable_header()
    assert scaffold.main(["lean", *COMMON, "--force"]) == 0
    assert scaffold.main(["blocks", *COMMON, "--force"]) == 0
    assert scaffold.main(["check", "--dir", str(HERE)]) == 0


def skeleton() -> None:
    immutable_header()
    call_facts()
    # Re-read the manually audited model instead of using incomplete draft call facts.
    original_spec = proof_skeleton.render_spec

    def render_spec(c):
        c.external_calls = []
        out = original_spec(c)
        raw_index = next(t.index for t in c.transitions if t.name == "setAuthorizationWithSig")
        for t in c.transitions:
            old = f"contract.transitions[{t.index}]!  -- {t.signature}"
            new = ("contract.fallback.getD default" if t.index == raw_index else
                   f"contract.transitions[{t.index if t.index < raw_index else t.index - 1}]!")
            out = out.replace(old, f"{new}  -- {t.signature}")
        out = out.replace("solidityStorage! [contract.structs] [contract.storage]",
                          "Syntax.modelStorageBackend")
        out = out.replace("/-! ## Config -/",
                          "def externalABI : ExternalCallABI := Syntax.modelExternalABI\n\n/-! ## Config -/")
        return out.replace("externalABI := defaultExternalCallABI", "externalABI := externalABI")

    proof_skeleton.render_spec = render_spec
    old_value = proof_skeleton.Immutable.value.fget
    old_word = proof_skeleton.Immutable.word.fget
    proof_skeleton.Immutable.value = property(lambda imm:
        f".fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE v.{imm.name})"
        if imm.solidity_type == "bytes32" else old_value(imm))
    proof_skeleton.Immutable.word = property(lambda imm:
        f"v.{imm.name}" if imm.solidity_type == "bytes32" else old_word(imm))
    old_plumbing = proof_skeleton.render_immutable_plumbing

    def plumbing(c):
        return [line.replace("(immStore_get_DOMAIN_SEPARATOR v) rfl",
                             "(immStore_get_DOMAIN_SEPARATOR v) (valueToWord_bytes32_word _)")
                for line in old_plumbing(c)]

    proof_skeleton.render_immutable_plumbing = plumbing
    raw_entry_skeleton()
    assert scaffold.main(["lean", *COMMON, "--force"]) == 0
    assert proof_skeleton.main([*COMMON, "--force"]) == 0


def raw_entry_skeleton() -> None:
    """Keep all 28 bytecode selector arms, with the signature arm served by a raw fallback.

    The generic renderer assumes one typed transition per selector. Preserve its EVM reach
    proofs and function obligations; omit the inapplicable typed selector bridge, and add a
    generated fallback obligation for short/unmatched calldata. No theorem assumes a typed
    signature for the raw entry, or that a contract with a fallback dispatches to `none`.
    """
    original_common = proof_skeleton.render_common

    def common(c):
        out = original_common(c)
        handles = ", ".join(t.handle for t in c.transitions)
        typed_handles = ", ".join(t.handle for t in c.transitions
                                  if t.name != "setAuthorizationWithSig")
        out = out.replace(f"contract.transitions = [{handles}]",
                          f"contract.transitions = [{typed_handles}]")
        out, count = re.subn(
            r"set_option maxHeartbeats 0 in\nset_option maxRecDepth 1000000 in\n"
            r"/-- `selectorOf setAuthorizationWithSigTransition.*?"
            r"  exact setAuthorizationWithSigSelectorFact\n\n", "", out, flags=re.S)
        assert count == 1
        return out

    proof_skeleton.render_common = common
    original_dispatch = proof_skeleton.render_dispatch

    def dispatch(*args):
        out, info = original_dispatch(*args)
        # The EVM has no fallback: only the Solm representation uses a raw entry. Render
        # actual short/no-match bytecode paths without the generic fallback-entry heuristic.
        evm_out, info = original_dispatch(replace(args[0], has_fallback=False), *args[1:])
        marker = "/-! ## Runtime dispatcher paths -/"
        out = out.split(marker)[0] + marker + evm_out.split(marker, 1)[1]
        out = out.replace("dispatchMsg contract cd = none", "selectorDispatchMsg contract cd = none")
        out = out.replace("dispatchMsg contract I.calldata = none",
                          "selectorDispatchMsg contract I.calldata = none")
        return out, info

    proof_skeleton.render_dispatch = dispatch
    original_correct = proof_skeleton.render_correct

    def correct(c, global_guard):
        assert not global_guard
        out = original_correct(c, global_guard)
        start = out.index("theorem morphoNoDispatch ")
        stop = out.index("theorem morphoNoSelectorMatches ", start)
        obligation = out[start:stop].split(" := by", 1)[0] + " := by\n  sorry\n\n"
        prelude = out[:start]
        prelude = re.sub(r"\A(?:import [^\n]+\n)+", f"import {c.module}.Dispatch\n", prelude)
        prelude = re.sub(r"/-!.*?-/", "/-!\n# Morpho fallback correctness\n\n"
            "Generated by `regenerate.py`: reject short calldata and unknown selectors.\n-/",
            prelude, count=1, flags=re.S)
        # Reuse the renderer's imports, namespace, binders, and exact refinement target.
        (HERE / "Fallback.lean").write_text(prelude +
            "-- Generated obligation: the raw fallback rejects short and unmatched calldata.\n" +
            obligation + f"end {c.namespace}\n")
        out = out[:start] + out[stop:]
        return f"import {c.module}.Fallback\n" + out

    proof_skeleton.render_correct = correct


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("step", choices=["artifacts", "skeleton", "check-deployment"])
    parser.add_argument("--solc", default="/tmp/morpho-solc-0.8.19")
    args = parser.parse_args()
    if args.step == "artifacts":
        artifacts(args.solc)
    elif args.step == "skeleton":
        skeleton()
    else:
        deployment_check()
