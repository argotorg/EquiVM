#!/usr/bin/env python3
"""Generate Midnight's scaffold assembly using the pinned compiler ABI.

The shared generator does not emit tuple-bearing call ABIs, custom transient
layouts, or raw-data creation configurations. This local adapter supplies those
three parts without modifying any shared generator or hand-editing its outputs.
SpecSyntax.lean and Model.lean are authored inputs and are never overwritten.
"""
from pathlib import Path
import argparse
import json
import subprocess
import sys

directory = Path(__file__).resolve().parent
repo = directory.parents[1]
sys.path.insert(0, str(repo / "scripts"))
import proof_skeleton as skeleton
import scaffold
from evm_tools import selector


def canonical(parameter):
    ty = parameter["type"]
    if ty.startswith("tuple"):
        return "(" + ",".join(map(canonical, parameter["components"])) + ")" + ty[5:]
    return ty


def type_term(parameter):
    ty = parameter["type"]
    if ty.endswith("[]"):
        return "(.dynamicArray " + type_term({**parameter, "type": ty[:-2]}) + ")"
    if ty == "tuple":
        return "(.tuple [" + ", ".join(map(type_term, parameter["components"])) + "])"
    term = skeleton.abi_type_term(ty)
    if term is None:
        raise ValueError(f"Unsupported ABI type: {ty}")
    return term


def interface_abis():
    build = json.loads((directory / "Midnight.build.json").read_text())
    request = {
        "language": "Solidity",
        "sources": {s["path"]: {"content": (directory / "contracts" / s["path"]).read_text()}
                    for s in build["sources"]},
        "settings": {**build["settings"], "outputSelection": {"*": {"*": ["abi"]}}},
    }
    process = subprocess.run([build["compiler"]["path"], "--standard-json"],
        input=json.dumps(request), text=True, capture_output=True, check=True)
    output = json.loads(process.stdout)
    errors = [e for e in output.get("errors", []) if e["severity"] == "error"]
    if errors:
        raise ValueError(errors)
    interfaces = {name: unit["abi"] for path, units in output["contracts"].items()
                  if path.startswith("src/interfaces/") for name, unit in units.items()}
    (directory / "provenance/interfaces.abi.json").write_text(
        json.dumps(interfaces, indent=2) + "\n")
    return interfaces


def render_abi(interfaces):
    facts = json.loads((directory / "Midnight.spec.json").read_text())["externalCalls"]
    wanted = {fact["name"] for fact in facts} | {"transfer", "transferFrom"}
    functions = {}
    for abi in interfaces.values():
        for function in abi:
            if function.get("type") == "function" and function["name"] in wanted:
                if function["name"] in functions:
                    assert functions[function["name"]] == function
                functions[function["name"]] = function
    assert set(functions) == wanted
    out = ["/-! ## ABI table, generated from the pinned interfaces -/", "",
        "def externalABI : ExternalCallABI where",
        "  encode? := fun name args ↦", "    let args := Model.abiValues args",
        '    if name = "encodeMarket" then ABI.encodeReturnValues? [Model.marketABI] args',
        '    else if name = "encodeOffer" then ABI.encodeReturnValues? [Model.offerABI] args']
    for name, f in sorted(functions.items()):
        signature = name + "(" + ",".join(map(canonical, f["inputs"])) + ")"
        sel = ", ".join(f"0x{x:02x}" for x in selector(signature))
        types = ", ".join(map(type_term, f["inputs"]))
        out += [f'    else if name = "{name}" then  -- {signature}',
                f"      ABI.encodeCallWithSelector? ⟨#[{sel}]⟩ [{types}] args"]
    out += ["    else none", "  decode? := fun name bytes ↦"]
    for i, (name, f) in enumerate(sorted(functions.items())):
        types = ", ".join(map(type_term, f["outputs"]))
        assert len(f["outputs"]) == 1 and f["outputs"][0]["type"] in {
            "bool", "uint256", "bytes32"}
        out += [f'    {"if" if i == 0 else "else if"} name = "{name}" then',
                f"      ABI.decodeReturnValues? [{types}] (bytes.extract 0 32)"]
    out += ["    else none", "  decodeCalldata? := Model.decodeCalldata",
            "  decodeValue? := ABI.decodeReturnValueWithMode? .modern", ""]
    return "\n".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true", help="regenerate the shared skeleton first")
    args = parser.parse_args()
    original_signature = skeleton.body_signature
    def signature(c, t, global_guard):
        return original_signature(c, t, global_guard).replace(
            "    (hsel :", "    (hfork : fork ≥ .osaka)\n"
            "    (hgas : midnightGasBound g)\n    (hsel :")
    skeleton.body_signature = signature
    original_correct = skeleton.render_correct
    def correct(c, global_guard):
        result = original_correct(c, global_guard)
        result = result.replace("runtimeRefinement config",
            "runtimeRefinementWithWFOn midnightForks trivialStorageWF midnightGasBound config")
        result = result.replace("contractRefinement config",
            "contractRefinementWFOn midnightForks trivialStorageWF midnightGasBound config")
        result = result.replace(f"contractRefinement.of_constant {c.prefix}ConstructorCorrect",
            "contractRefinementWF.of_constant\n"
            f"    ({c.prefix}ConstructorCorrect.mono fun fork _ => supportedForks_mem fork)")
        result = result.replace("fun fork _hfork σ σ₀ g A I hcode hsize ↦",
            "fun fork hfork σ σ₀ g A I hcode hsize _ hgas ↦")
        for t in c.transitions:
            before = f"{c.prefix}{t.cap}Body hcode hsize"
            result = result.replace(before, before + " hfork hgas")
        return result
    skeleton.render_correct = correct
    if args.all:
        skeleton.main(["--dir", str(directory), "--module", "Benchmarks.Midnight", "--force"])
    c = skeleton.load_contract(directory, "Benchmarks.Midnight", None, None, "Midnight")
    generated = skeleton.render_spec(c)
    prelude = generated.split("/-! ## External-call ABI")[0]
    prelude = ("import Benchmarks.Midnight.Model\n"
               "import Benchmarks.Midnight.Conditions\n" + prelude)
    prelude = prelude.replace("generated by `scripts/proof_skeleton.py`",
                              "generated by `Benchmarks/Midnight/generate.py`")
    config = """
/-! ## Config: SSTORE2 and the source's transient slot derivation -/

def config : Config :=
  { storageBackend := storageBackend
    transientBackend := Model.transientBackend
    externalABI := externalABI
    creationCode := Model.creationCode
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Midnight
"""
    (directory / "Spec.lean").write_text(prelude + render_abi(interface_abis()) + config)
    target = scaffold.render_difftarget_lean("Benchmarks.Midnight", "Benchmarks.Midnight",
                                           "midnight", "Midnight", True, False)
    target = "import Benchmarks.Midnight.Fixtures\n" + target
    target = target.replace(
        "Registered in `Tests/DiffTest/Generated.lean`; run with `lake exe stele-difftest --only Midnight`.",
        "Registered locally by `Benchmarks/Midnight/run_difftest.py`.")
    target = target.replace("callees := standardCallees, words := [10 ^ 18]",
        "callees := midnightCallees, words := [1, 4, 3372, 10 ^ 18, 10 ^ 36]")
    (directory / "DiffTarget.lean").write_text(target)
    print("Generated Midnight Spec.lean with pinned interface ABI, transient layout, and SSTORE2.")


if __name__ == "__main__":
    main()
