#!/usr/bin/env python3
"""Generate the proof skeleton of a contract directory.

Inputs (all produced by the other scripts): ``SpecSyntax.lean`` (the specification; its external
functions fix the transition order), ``Selectors.lean``, ``Bytecode.lean`` and
``CreationBytecode.lean`` (the listings of ``scaffold.py lean``), ``runtime.hex``,
``<Name>.build.json`` (compiler version, immutables), optionally ``<Name>.spec.json`` (the
translator's external-call facts) and the generated ``RuntimeBlocks_NNN.lean`` summaries.
An optional ``def abiDecodeMode : ABI.DecodeMode`` in the specification's ``Syntax`` namespace
selects a decoder profile explicitly; otherwise compiler-version defaults are preserved.

Outputs (existing files are kept unless ``--force``):

  Spec.lean         derived assembly: the contract, transition handles, storage backend from the
                    layout elaborator, the external-call ABI table, the Config.
  Common.lean       selector bridges (`selectorOf t = table entry`), selector-word facts, the
                    immutables valuation plumbing, bytecode size facts, and `<prefix>Jumpdest`:
                    jump validity from the listing (`Listing.jumpdest_code`).
  Dispatch.lean     Stele dispatch facts (which transition a selector reaches) and the runtime
                    dispatcher reach lemmas composed from the block summaries: one per arm, the
                    short-calldata path, the no-match path, the non-payable path.  Proofs are
                    generated; `--sorry-dispatch` leaves them as `sorry`.
  <Fn>.lean         one stub per transition: the `…Body` theorem Correct.lean consumes, `sorry`.
  Constructor.lean  the constructor theorem, `sorry`.
  Correct.lean      the capstone: revert paths, the selector case split, the contract theorem.

Example:
  scripts/proof_skeleton.py --dir Benchmarks/Scaffolds/Foo --module Benchmarks.Scaffolds.Foo

Vyper artifacts get the same files: ``SpecSyntax.lean`` comes from ``vy2stele.py`` (holes closed
by hand), the Config uses Vyper storage/ABI defaults that must be reviewed for bounded types, and
``Dispatch.lean`` proves the jump-table dispatcher (``Reasoning/VyperDispatch.lean``): the lookup
of every bucket, the selector-compare chain to each function's guard block, and the revert paths.
With immutables the prelude's ``deployed_of_fit`` is the stub that bridges the store to the code
suffix.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, field
from pathlib import Path

import generate_rd_blocks as rd
from bytecode_io import read_bytecode
from evm_tools import jump_dests, overload_names, selector
from scaffold import (contract_name, default_module, find_build, lean_selector_table, load_json,
                      lower_camel, rel_to_root, spec_syntax_order, write_file)

ROOT = Path(__file__).resolve().parent.parent


# --------------------------------------------------------------------------------------------
# Contract description

@dataclass
class Transition:
    index: int
    signature: str
    name: str          # Lean-safe lowerCamel name (overloads suffixed)
    selector: bytes
    payable: bool

    @property
    def cap(self) -> str:
        return self.name[0].upper() + self.name[1:]

    @property
    def handle(self) -> str:
        return f"{self.name}Transition"


@dataclass
class Immutable:
    name: str
    solidity_type: str

    @property
    def lean_type(self) -> str:
        return "EVM.Address" if self.solidity_type.startswith(("address", "contract")) else "EVM.Word"

    @property
    def value(self) -> str:
        if self.lean_type == "EVM.Address":
            return f".address v.{self.name}"
        return f".int (Int.ofNat v.{self.name}.toNat)"

    @property
    def word(self) -> str:
        if self.lean_type == "EVM.Address":
            return f"EVM.Word.ofNat (↑v.{self.name} : Nat)"
        return f"EVM.wordOfInt (Int.ofNat v.{self.name}.toNat)"


@dataclass
class Contract:
    directory: Path
    name: str
    module: str
    namespace: str
    prefix: str
    transitions: list[Transition]
    has_fallback: bool
    has_receive: bool
    immutables: list[Immutable]
    version: tuple[int, int, int]
    external_calls: list[dict]
    runtime: bytes
    has_transient: bool = False
    has_decode_mode: bool = False
    abicoder_v2: bool = False
    compiler_kind: str = "solc"
    block_hyps: dict[str, list[str]] | None = None

    @property
    def code_term(self) -> str:
        return f"deployedRuntime v" if self.immutables else f"{self.prefix}Bytecode"

    @property
    def blocks_ns(self) -> str:
        return f"{rd.lean_ident(self.prefix)}Blocks"

    @property
    def imm_struct(self) -> str:
        return f"{self.name}Immutables"

    @property
    def v_binder(self) -> str:
        return f" (v : {self.imm_struct})" if self.immutables else ""

    @property
    def imm_store_arg(self) -> str:
        return " (immStore v)" if self.immutables else ""


def block_hypotheses(directory: Path) -> dict[str, list[str]] | None:
    """Each runtime block theorem's explicit hypotheses, by name, from the generated
    ``RuntimeBlocks_NNN.lean``; ``None`` before they are generated.  A block proved from the
    listing has no ``hvalid`` when its jump target is a literal JUMPDEST."""
    shards = sorted(directory.glob("RuntimeBlocks_*.lean"))
    if not shards:
        return None
    out: dict[str, list[str]] = {}
    for path in shards:
        for m in re.finditer(r"(?m)^theorem (\S+) [^\n]*\n((?:    \([^\n]*\n)*)",
                             path.read_text(encoding="utf-8")):
            out[m.group(1)] = re.findall(r"(?m)^    \((\w+) :", m.group(2))
    return out


def spec_syntax_info(text: str) -> tuple[dict[str, bool], bool, bool]:
    """(external function name -> payable, has fallback, has receive) from SpecSyntax.lean."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    payable: dict[str, bool] = {}
    for m in re.finditer(r"\bfunction\s+«?([A-Za-z_][A-Za-z0-9_]*)»?\s*\(([^)]*)\)\s*([^{]*)\{", text):
        mods = m.group(3)
        if re.search(r"\b(internal|private)\b", mods):
            continue
        payable[m.group(1)] = bool(re.search(r"\bpayable\b", mods))
    has_fallback = re.search(r"\bfallback\s*\(", text) is not None
    has_receive = re.search(r"\breceive\s*\(", text) is not None
    return payable, has_fallback, has_receive


def load_contract(directory: Path, module: str | None, namespace: str | None, prefix: str | None,
                  explicit_name: str | None) -> Contract:
    name = contract_name(directory, explicit_name)
    build_path = find_build(directory, name)
    build = load_json(build_path) if build_path else {}
    module = module or default_module(directory)
    namespace = namespace or module
    prefix = prefix or lower_camel(name)
    spec_path = directory / "SpecSyntax.lean"
    if not spec_path.exists():
        if build.get("compiler", {}).get("kind") == "vyper":
            raise SystemExit("SpecSyntax.lean is required (draft it with vy2stele.py from the pinned "
                             "annotated AST, then close its holes)")
        raise SystemExit("SpecSyntax.lean is required (write it, or draft it with sol2stele.py)")
    spec_text = spec_path.read_text(encoding="utf-8")
    payable, has_fallback, has_receive = spec_syntax_info(spec_text)
    has_transient = re.search(r"\btransient\s+«?[A-Za-z_]", re.sub(r"--[^\n]*", "", spec_text)) is not None
    has_decode_mode = re.search(r"\bdef\s+abiDecodeMode\s*:\s*(?:ABI\.)?DecodeMode\b",
                                re.sub(r"/-.*?-/|--[^\n]*", "", spec_text, flags=re.S)) is not None
    selectors_path = directory / "Selectors.lean"
    if not selectors_path.exists():
        raise SystemExit("Selectors.lean is required (scaffold.py lean)")
    table = lean_selector_table(selectors_path.read_text(encoding="utf-8"))
    names = overload_names([sig for sig, _ in table])
    transitions = [Transition(i, sig, names[sig], sel, payable.get(sig.split("(", 1)[0], False))
                   for i, (sig, sel) in enumerate(table)]
    immutables = [Immutable(i["name"], i.get("type", "")) for i in build.get("immutables", [])]
    version = (0, 8, 0)
    m = re.search(r"(\d+)\.(\d+)\.(\d+)", build.get("compiler", {}).get("version", ""))
    if m:
        version = (int(m.group(1)), int(m.group(2)), int(m.group(3)))
    spec_json = directory / f"{name}.spec.json"
    external_calls = load_json(spec_json).get("externalCalls", []) if spec_json.exists() else []
    runtime = read_bytecode(directory / "runtime.hex")
    # solc < 0.8 with `pragma abicoder v2` / `pragma experimental ABIEncoderV2` validates calldata
    # like 0.8 does; the legacy decode mode models the old coder's cleanup instead
    ast_path = directory / f"{name}.sol.ast.json"
    abicoder_v2 = False
    if ast_path.exists():
        text = ast_path.read_text(encoding="utf-8")
        abicoder_v2 = '"abicoder", "v2"' in text or '"experimental", "ABIEncoderV2"' in text
    return Contract(directory, name, module, namespace, prefix, transitions, has_fallback, has_receive,
                    immutables, version, external_calls, runtime, has_transient, has_decode_mode, abicoder_v2,
                    build.get("compiler", {}).get("kind", "solc"), block_hypotheses(directory))


# --------------------------------------------------------------------------------------------
# ABI type terms

def abi_type_term(t: str) -> str | None:
    t = t.strip()
    m = re.fullmatch(r"(.+?)\[\]", t)
    if m:
        inner = abi_type_term(m.group(1))
        return f"(.dynamicArray {inner})" if inner else None
    m = re.fullmatch(r"(.+?)\[(\d+)\]", t)
    if m:
        inner = abi_type_term(m.group(1))
        return f"(.array {inner} {m.group(2)})" if inner else None
    if t == "address":
        return "(.elem .address)"
    if t == "bool":
        return "(.elem .bool)"
    m = re.fullmatch(r"uint(\d+)", t)
    if m:
        return f"(.elem (.int (.uint ⟨{m.group(1)}, by decide⟩)))"
    m = re.fullmatch(r"int(\d+)", t)
    if m:
        return f"(.elem (.int (.sint ⟨{m.group(1)}, by decide⟩)))"
    m = re.fullmatch(r"bytes(\d+)", t)
    if m:
        return f"(.elem (.bytes ⟨{int(m.group(1)) - 1}, by decide⟩))"
    if t == "bytes":
        return ".bytes"
    if t == "string":
        return ".string"
    return None


# --------------------------------------------------------------------------------------------
# Spec.lean

def render_spec(c: Contract) -> str:
    vyper = c.compiler_kind == "vyper"
    out = [f"import {c.module}.SpecSyntax", "import Stele.Semantics", "import Stele.SolidityLayout",
           "import Stele.MetaVyperLayout" if vyper else "import Stele.MetaSolidityLayout",
           "import Stele.Refine", ""]
    if c.immutables:
        out.append(f"import {c.module}.Immutables")
    out += ["/-!", f"# {c.name} spec assembly (generated by `scripts/proof_skeleton.py`)", "",
            "The contract is defined by `SpecSyntax.lean`; this file only names its parts: the transition",
            f"handles the proof files unfold, the storage backend ({'Vyper' if vyper else 'solc'} layout, from the",
            "declarations), the external-call ABI, and the `Config`.", "-/", "",
            "open Stele ABI", "", f"namespace {c.namespace}", "",
            "def contract : ContractDecl := Syntax.contractSyntax", "",
            "/-! ## Transition handles, in `contract.transitions` order -/", ""]
    for t in c.transitions:
        out.append(f"abbrev {t.handle} : TransitionDecl := contract.transitions[{t.index}]!  -- {t.signature}")
    if vyper:
        out += ["", "/-! ## Storage backend: Vyper's full-word layout for static declarations.\n"
                "For DynArray, Bytes, or String state, replace this with vyperBoundedStorage!\n"
                "and source-checked VyperStorageDecl capacities. -/", "",
                "def storageBackend : StorageBackend := vyperStorage! [contract.storage]", ""]
    else:
        out += ["", "/-! ## Storage backend: solc's layout for the declared storage -/", "",
                "def storageBackend : StorageBackend := solidityStorage! [contract.structs] [contract.storage]", ""]
    # external-call ABI
    if c.external_calls:
        out += ["/-! ## External-call ABI (from the translator's call facts; check against the callee ABIs) -/", "",
                "def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩", ""]
        encode_arms: list[str] = []
        decode_arms: list[str] = []
        todo: list[str] = []
        for call in c.external_calls:
            params = call.get("params", [])
            rets = call.get("returns", [])
            terms = [abi_type_term(p) for p in params]
            ret_terms = [abi_type_term(r) for r in rets]
            canon = f"{call['name']}({','.join(params)})"
            if any(t is None for t in terms) or any(t is None for t in ret_terms):
                todo.append(canon)
                continue
            sel = selector(canon)
            sel_term = f"(selectorBytes 0x{sel[0]:02x} 0x{sel[1]:02x} 0x{sel[2]:02x} 0x{sel[3]:02x})"
            encode_arms.append(f"    else if name = \"{call['name']}\" then  -- {canon}\n"
                               f"      ABI.encodeCallWithSelector? {sel_term} [{', '.join(terms)}] args")
            if not rets:
                decode_arms.append(f"    else if name = \"{call['name']}\" then some []")
            elif len(rets) == 1:
                decode_arms.append(f"    else if name = \"{call['name']}\" then\n"
                                   f"      (ABI.decodeReturnValueWithMode? DecodeMode.modern {ret_terms[0]} out).map (fun v => [v])")
            else:
                todo.append(canon + " (multiple return values)")
        out += ["def externalABI : ExternalCallABI where", "  encode? := fun name args =>",
                "    if False then none"]
        out += encode_arms
        out += ["    else none", "  decode? := fun name out =>", "    if False then none"]
        out += decode_arms
        out += ["    else none", ""]
        if todo:
            out += ["-- TODO external calls not covered by the generated table: " + "; ".join(todo), ""]
        abi_name = "externalABI"
    else:
        abi_name = "defaultExternalCallABI"
    if vyper:
        decode_mode = ".withMode DecodeMode.vyper"
        out += ["-- If an entry parameter has a Vyper capacity (DynArray, Bytes, String),",
                "-- declare every selector variant as ABI.VyperABIFunction and use",
                "-- withVyperABI functions here; ABI JSON erases capacities.", ""]
    else:
        decode_mode = "" if c.version >= (0, 8, 0) or c.abicoder_v2 else ".withMode DecodeMode.legacySolc05"
    if c.has_decode_mode:
        decode_mode = ".withMode Syntax.abiDecodeMode"
    transient = ("\n    transientBackend := solidityTransientStorage! [contract.structs] [contract.transient]"
                 if c.has_transient and not vyper else "")
    if vyper and c.has_transient:
        raise SystemExit("Vyper transient declarations need an explicit Vyper transient backend; "
                         "automatic Spec generation is not supported for this contract")
    out += ["/-! ## Config -/", "", "def config : Config :=",
            f"  {{ storageBackend := storageBackend\n    externalABI := {abi_name}{decode_mode}{transient}\n"
            f"    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }}", "",
            f"end {c.namespace}", ""]
    return "\n".join(out)


# --------------------------------------------------------------------------------------------
# Common.lean

def nat_repr_facts(c: Contract) -> list[str]:
    widths = sorted({int(w) for t in c.transitions for w in re.findall(r"u?int(\d+)", t.signature)} |
                    {int(w) for t in c.transitions for w in re.findall(r"bytes(\d+)", t.signature)})
    return [f"show Nat.repr {w} = \"{w}\" by decide +kernel" for w in widths]


def render_common(c: Contract) -> str:
    p = c.prefix
    out = [f"import {c.module}.Spec", f"import {c.module}.Bytecode", f"import {c.module}.Selectors",
           "import Reasoning.ABI", "import Reasoning.Constructor", "import Reasoning.Solc",
           "import Reasoning.Storage", "import Reasoning.Dispatch", "import Reasoning.SteleBody",
           "import Reasoning.WordArithmetic", "import Reasoning.Initcode", "import Reasoning.MemCascade",
           "import Mathlib.Tactic.IntervalCases"]
    if c.immutables:
        out += [f"import {c.module}.ImmutableCode", "import Reasoning.Immutables"]
    out += ["", "/-!", f"# {c.name} proof prelude (generated by `scripts/proof_skeleton.py`)", "",
            "Single import point for the proof files; selector bridges, selector-word facts, and the",
            "immutables plumbing.  Contract-specific helpers shared by several proof files go here too.", "-/", "",
            "open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach"]
    if c.immutables:
        out += ["open Reasoning.Immutables", f"open {c.namespace}.Immutables"]
    out += ["", f"namespace {c.namespace}", "", "set_option maxRecDepth 2000000", ""]
    out += common_bridges(c)
    if c.immutables:
        out += render_immutable_plumbing(c)
    else:
        out += jumpdest_wrapper(c)
    out += [f"end {c.namespace}", ""]
    return "\n".join(out)


def common_bridges(c: Contract) -> list[str]:
    """The bytecode size, the transition list and the selector bridges shared by both compilers."""
    p = c.prefix
    out = [f"@[simp] theorem {p}Bytecode_size : {p}Bytecode.size = {len(c.runtime)} := by",
           "  decide +kernel", ""]
    handles = ", ".join(t.handle for t in c.transitions)
    out += ["/-- The transition list as its handles. -/",
            f"theorem transitions_eq : contract.transitions = [{handles}] := by",
            "  first | rfl | simp [contract, Syntax.contractSyntax]", ""]
    out += ["/-! ## Selector bridges: each transition's signature hashes to its table entry -/", ""]
    facts = ", ".join(nat_repr_facts(c))
    for t in c.transitions:
        out += ["set_option maxHeartbeats 0 in", "set_option maxRecDepth 1000000 in",
                f"/-- `selectorOf {t.handle} = {p}SelBytes {t.index}` (`{t.signature}`). -/",
                f"theorem {t.name}SelectorOf : selectorOf {t.handle} = {p}SelBytes {t.index} := by",
                f"  have hsig : transitionSigStr {t.handle} = \"{t.signature}\" := by",
                f"    simp [transitionSigStr, ABI.printSignature, transitionSignature, {t.handle}, contract,",
                f"      Syntax.contractSyntax, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr{', ' + facts if facts else ''}]",
                "      <;> decide +kernel",
                "  unfold selectorOf", "  rw [hsig]", f"  exact {t.name}SelectorFact", ""]
    out += ["/-! ## Selector words as the dispatcher compares them -/", ""]
    for t in c.transitions:
        s = t.selector
        v = int.from_bytes(s, "big")
        out += [f"theorem {t.name}EvmSelector {{cd : ByteArray}} (hsz : 4 ≤ cd.size) :",
                f"    UInt256.eq ⟨{v}⟩ (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)",
                f"      = if ({p}SelBytes {t.index} == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=",
                f"  evmSelectorDecode hsz 0x{s[0]:02x} 0x{s[1]:02x} 0x{s[2]:02x} 0x{s[3]:02x} ⟨{v}⟩ (by decide)", ""]
    return out


def jumpdest_wrapper(c: Contract) -> list[str]:
    """`<prefix>Jumpdest`: a target is a valid jump destination of the code the block summaries
    run over when the listing (`Bytecode.lean`) has a section there that starts with `JUMPDEST`;
    `rfl rfl` proves both hypotheses for a literal target (the lookup, then the test)."""
    p = c.prefix
    doc = ["/-- A jump target is a valid jump destination when the listing has a section there that",
           "starts with `JUMPDEST` (`rfl rfl` for a literal target: the lookup, then the test). -/"]
    hyps = ["    (h : Listing.tree.get? pc.toNat = some s) (hjd : Reasoning.Listing.startsJD s = true) :"]
    if c.immutables and c.compiler_kind != "vyper":
        return [*doc, f"theorem {p}Jumpdest (v : {c.imm_struct}) {{pc : UInt256}} {{s : Reasoning.Listing.Section}}",
                *hyps, "    (D_J (deployedRuntime v) 0).contains pc = true := by",
                "  have hj := Listing.jumpdest_code (wordsOf (immStore v)) h hjd pc.val.isLt",
                "  rw [u256_ofNat_toNat] at hj", "  exact hj", ""]
    # A Vyper runtime with immutables is `template ++ suffix`; the wrapper is about the template
    # (`D_J_contains_append_left` lifts it).
    arg = " ByteArray.empty" if c.immutables else ""
    extra = ", ByteArray.append_empty" if c.immutables else ""
    return [*doc, f"theorem {p}Jumpdest {{pc : UInt256}} {{s : Reasoning.Listing.Section}}",
            *hyps, f"    (D_J {p}Bytecode 0).contains pc = true := by",
            f"  have hj := Listing.jumpdest_code{arg} h hjd pc.val.isLt",
            f"  rw [u256_ofNat_toNat{extra}] at hj", "  exact hj", ""]


def render_immutable_plumbing(c: Contract) -> list[str]:
    p = c.prefix
    out = ["/-! ## Immutables: the valuation's store, its words, and the deployed runtime -/", "",
           "/-- The immutables a contract deployed with `v` runs with. -/",
           f"def immStore (v : {c.imm_struct}) : Store :="]
    store = "(∅ : Store)"
    for imm in c.immutables:
        store = f"({store}.insert \"{imm.name}\" ({imm.value}))"
    out += [f"  {store}", ""]
    for imm in c.immutables:
        out += [f"@[simp] theorem immStore_get_{imm.name} (v : {c.imm_struct}) :",
                f"    (immStore v).get? \"{imm.name}\" = some ({imm.value}) := by",
                "  simp only [immStore, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]",
                "  rfl", "",
                f"@[simp] theorem wordsOf_immStore_{imm.name} (v : {c.imm_struct}) :",
                f"    wordsOf (immStore v) \"{imm.name}\" = {imm.word} :=",
                f"  wordsOf_of_get (immStore_get_{imm.name} v) rfl", ""]
    out += ["/-- The runtime deployed with the immutables `v`. -/",
            f"def deployedRuntime (v : {c.imm_struct}) : ByteArray :=",
            f"  immutableLayout.deployed {p}Bytecode (immStore v)", ""]
    for imm in c.immutables:
        out += [f"theorem evalImmutable_{imm.name} (cfg : Config) (C : ContractDecl) (locals : Store) (evm : EVM.State)",
                f"    (v : {c.imm_struct}) :",
                f"    evalExpr? cfg {{ contract := C, locals := locals, immutables := immStore v }} evm",
                f"      (.immutable \"{imm.name}\") = .ok ({imm.value}) := by",
                f"  simp only [evalExpr?, immStore_get_{imm.name}, EvalResult.ofOption]", ""]
    out += ["/-- Every patch site is a declared immutable. -/",
            "theorem immutableLayout_keys :",
            "    ∀ site ∈ immutableLayout.sites, site.2.2 ∈ contract.immutables.map (·.name) := by",
            "  decide", "",
            "/-- A well-typed immutables store runs as the store of some valuation. -/",
            "theorem restrictImmutables_of_fit {imms : Store} (h : immutablesFit contract imms) :",
            "    ∃ v, restrictImmutables contract imms = immStore v := by",
            "  sorry  -- TODO: case on each immutable's value as in Examples/TinyImmutable/Common.lean", ""]
    return out + jumpdest_wrapper(c)


# --------------------------------------------------------------------------------------------
# Dispatcher path analysis over the runtime

class PathError(Exception):
    pass


@dataclass
class Piece:
    instructions: list[rd.Instruction]
    index: int

    @property
    def pc(self) -> int:
        return self.instructions[0].pc

    @property
    def end_pc(self) -> int:
        last = self.instructions[-1]
        return last.pc + last.size

    @property
    def terminator(self) -> int | None:
        last = self.instructions[-1]
        return last.opcode if last.opcode in rd.TERMINATORS else None


@dataclass
class Step:
    piece: Piece
    branch: str | None       # "taken" | "fallthrough" | None
    conds: list[tuple[str, str]]   # (hypothesis name, term) in summary order
    summary: rd.Summary


@dataclass
class Env:
    callvalue: int | str      # 0 or "cvnz"
    calldatasize: str         # "big" (≥ 4) or "small" (< 4)
    selector: int | str       # concrete or "nomatch"


ZERO = r"(?:\(UInt256\.ofNat 0\)|\(⟨0⟩ : UInt256\))"
W224 = r"(?:\(UInt256\.ofNat 224\)|\(⟨224⟩ : UInt256\))"
SEL_TERM_RE = re.compile(r"\(UInt256\.shiftRight \(uInt256OfByteArray \(ee\.calldata\.readBytes "
                         + ZERO + r"\.toNat 32\)\) " + W224 + r"\)")


class Dispatcher:
    """Follows the compiled dispatcher concretely and composes block summaries along the path."""

    def __init__(self, c: Contract, immutable_sites: dict | None) -> None:
        self.c = c
        body = rd.strip_solidity_metadata(c.runtime)
        self.instructions = rd.disassemble(body)
        self.pieces: list[Piece] = []
        for block in rd.blocks(self.instructions):
            for part in rd.bounded_supported_segments(block, rd.MAX_SUMMARY_INSTRUCTIONS):
                if isinstance(part, rd.Instruction):
                    continue
                self.pieces.append(Piece(part, len(self.pieces)))
        self.by_pc = {p.pc: p for p in self.pieces}
        self.sites = immutable_sites
        self.jump_dests = set(jump_dests(c.runtime))

    def piece_at(self, pc: int) -> Piece:
        piece = self.by_pc.get(pc)
        if piece is None:
            raise PathError(f"no summary starts at pc {pc}")
        return piece

    def summary(self, piece: Piece, branch: str | None) -> rd.Summary:
        return rd.simulate(piece.instructions, branch, "(by native_decide)", None, self.sites, False)

    def theorem_name(self, piece: Piece, branch: str | None) -> str:
        return rd.summary_name(rd.lean_ident(self.c.prefix), piece.instructions, branch)

    # --- concrete interpretation -------------------------------------------------------------

    def run(self, env: Env, stop_at: int | None, revert_blocks_end: bool = True) -> list[Step] | list:
        """Steps from pc 0 until `stop_at` (a pc) or a terminator.  Pivot compares on an unknown
        selector return a Fork."""
        steps: list[Step] = []
        stack: list = []
        pc = 0
        visited = 0
        while True:
            visited += 1
            if visited > 200:
                raise PathError("dispatcher path too long")
            if stop_at is not None and pc == stop_at:
                return steps
            piece = self.piece_at(pc)
            branch, next_pc, stack, fork = self.execute(piece, stack, env)
            if fork is not None:
                return steps + [fork]
            summary = self.summary(piece, branch)
            conds = [(name, term) for name, term in summary.extra_hypotheses]
            steps.append(Step(piece, branch, conds, summary))
            if next_pc is None:
                return steps
            pc = next_pc

    def execute(self, piece: Piece, stack: list, env: Env):
        """Run one piece; returns (branch, next pc or None at a terminator, stack, fork)."""
        for k, ins in enumerate(piece.instructions):
            op = ins.opcode
            last = k == len(piece.instructions) - 1
            if op == 0x5F or 0x60 <= op <= 0x7F:
                stack.insert(0, ins.argument if ins.argument is not None else 0)
            elif 0x80 <= op <= 0x8F:
                stack.insert(0, stack[op - 0x80])
            elif 0x90 <= op <= 0x9F:
                n = op - 0x8F
                stack[0], stack[n] = stack[n], stack[0]
            elif op == 0x50:
                stack.pop(0)
            elif op == 0x5B:
                pass
            elif op == 0x34:
                stack.insert(0, env.callvalue)
            elif op == 0x36:
                stack.insert(0, env.calldatasize)
            elif op == 0x35:
                off = stack.pop(0)
                stack.insert(0, "cdw" if off == 0 else "unk")
            elif op == 0x1C:
                shift, value = stack.pop(0), stack.pop(0)
                stack.insert(0, env.selector if (shift == 224 and value == "cdw") else "unk")
            elif op == 0x04:
                a, b = stack.pop(0), stack.pop(0)
                stack.insert(0, env.selector if (a == "cdw" and b == 2 ** 224) else "unk")
            elif op == 0x16:
                a, b = stack.pop(0), stack.pop(0)
                sel = env.selector
                if (a == sel and b == 0xFFFFFFFF) or (b == sel and a == 0xFFFFFFFF):
                    stack.insert(0, sel)
                elif isinstance(a, int) and isinstance(b, int):
                    stack.insert(0, a & b)
                else:
                    stack.insert(0, "unk")
            elif op == 0x15:
                a = stack.pop(0)
                if isinstance(a, int):
                    stack.insert(0, 1 if a == 0 else 0)
                elif a == "cvnz":
                    stack.insert(0, 0)
                else:
                    stack.insert(0, "unk")
            elif op in (0x14, 0x10, 0x11):
                a, b = stack.pop(0), stack.pop(0)
                stack.insert(0, self.compare(op, a, b, env))
            elif op == 0x52 or op == 0x53:
                stack.pop(0); stack.pop(0)
            elif op == 0x51:
                stack.pop(0); stack.insert(0, "unk")
            elif op == 0x56:
                dest = stack.pop(0)
                if not isinstance(dest, int):
                    raise PathError(f"dynamic JUMP at pc {ins.pc}")
                return None, dest, stack, None
            elif op == 0x57:
                dest, cond = stack.pop(0), stack.pop(0)
                if not isinstance(dest, int):
                    raise PathError(f"dynamic JUMPI at pc {ins.pc}")
                if cond == "pivot":
                    return None, None, stack, Fork(piece, dest, ins.pc)
                if cond == "cvnz":
                    taken = True
                elif isinstance(cond, int):
                    taken = cond != 0
                else:
                    raise PathError(f"undecidable JUMPI at pc {ins.pc}")
                return ("taken", dest, stack, None) if taken else ("fallthrough", piece.end_pc, stack, None)
            elif op in (0x00, 0xF3, 0xFD, 0xFE):
                return None, None, stack, None
            else:
                try:
                    _, pops, pushes = rd.stack_shape(ins)
                except ValueError as error:
                    raise PathError(f"unsupported dispatcher opcode {ins.name} at pc {ins.pc}") from error
                for _ in range(pops):
                    stack.pop(0)
                for _ in range(pushes):
                    stack.insert(0, "unk")
            if last and op not in (0x56, 0x57, 0x00, 0xF3, 0xFD, 0xFE):
                return None, piece.end_pc, stack, None
        return None, piece.end_pc, stack, None

    def compare(self, op: int, a, b, env: Env):
        sel = env.selector
        if isinstance(a, int) and isinstance(b, int):
            return int({0x14: a == b, 0x10: a < b, 0x11: a > b}[op])
        if "cdw" in (a, b) or "unk" in (a, b) or "cvnz" in (a, b):
            raise PathError("comparison on an unknown value")
        # calldatasize against a constant
        for x, y, swapped in ((a, b, False), (b, a, True)):
            if x == "big" and isinstance(y, int) and y <= 4:
                # cds ≥ 4: cds < y false, cds > y true (y ≤ 3), cds == y false (y < 4) / unknown (y == 4)
                if op == 0x14:
                    if y < 4:
                        return 0
                    raise PathError("calldatasize == 4 is undecidable")
                lt = (x < y) if False else None
                if op == 0x10:   # a < b
                    return 0 if not swapped else 1   # cds < y → 0 ; y < cds → 1 (y ≤ 3)
                if op == 0x11:   # a > b
                    return 1 if not swapped else 0
            if x == "small" and isinstance(y, int) and y == 4:
                if op == 0x10:
                    return 1 if not swapped else 0
                if op == 0x11:
                    return 0 if not swapped else 1
                if op == 0x14:
                    return 0
        # selector compares
        if a == "nomatch" or b == "nomatch":
            other = b if a == "nomatch" else a
            if not isinstance(other, int):
                raise PathError("selector compared with an unknown value")
            return 0 if op == 0x14 else "pivot"
        if isinstance(sel, int) and (a == sel or b == sel):
            x = a if a == sel else b
            y = b if a == sel else a
            if not isinstance(y, int):
                raise PathError("selector compared with an unknown value")
            if a == sel:
                return int({0x14: x == y, 0x10: x < y, 0x11: x > y}[op])
            return int({0x14: y == x, 0x10: y < x, 0x11: y > x}[op])
        raise PathError(f"comparison {hex(op)} on symbolic values {a!r} {b!r}")

    def is_revert_block(self, pc: int) -> bool:
        piece = self.by_pc.get(pc)
        if piece is None:
            return False
        return all(ins.opcode in (0x5B, 0x5F, 0x80, 0xFD) or 0x60 <= ins.opcode <= 0x7F
                   for ins in piece.instructions) and piece.instructions[-1].opcode == 0xFD


@dataclass
class Fork:
    piece: Piece
    dest: int
    jumpi_pc: int


# --------------------------------------------------------------------------------------------
# Composition of summaries into a reach lemma

def subst(term: str, env: dict[str, str]) -> str:
    def repl(m: re.Match) -> str:
        return env.get(m.group(0), m.group(0))
    return re.sub(r"(?<![\w'])(?:x\d+|R|mem|aw|σ|rdata|ee)(?![\w'])", repl, term)


@dataclass
class RDState:
    stack: list[str]
    mem: str
    aw: str

    def copy(self) -> "RDState":
        return RDState(list(self.stack), self.mem, self.aw)


def apply_summary(state: RDState, summary: rd.Summary) -> RDState:
    depth = len(summary.stack_in)
    if len(state.stack) < depth:
        raise PathError("stack underflow while composing summaries")
    env = {f"x{i}": state.stack[i] for i in range(depth)}
    env["mem"] = state.mem
    env["aw"] = state.aw
    rest = state.stack[depth:]
    env["R"] = "R"
    new_stack = [subst(e, env) for e in summary.stack_out] + rest
    return RDState(new_stack, subst(summary.mem, env), subst(summary.aw, env))


def lean_list(items: list[str]) -> str:
    return "[" + ", ".join(items) + "]"


class ProofGen:
    def __init__(self, c: Contract, d: Dispatcher, fallback_pc: int | None = None) -> None:
        self.c = c
        self.d = d
        self.fallback_pc = fallback_pc
        self.global_guard = self.detect_global_guard()

    def detect_global_guard(self) -> bool:
        """A global non-payable guard: the dispatcher path branches on `callvalue` before any selector
        compare (solc emits it when no function is payable)."""
        try:
            steps = self.d.run(Env("cvnz", "big", "nomatch"), None)
        except PathError:
            return False
        for step in steps:
            if isinstance(step, Fork):
                return False
            if any("weiValue" in term for _, term in step.conds):
                return True
        return False

    # --- hypothesis discharge ----------------------------------------------------------------

    def lib_spelling(self, term: str) -> str:
        """The summary's term with the selector word and literals in library spelling."""
        term = SEL_TERM_RE.sub("(solcSelectorWord I)", term)
        term = term.replace("ee.", "I.")
        term = re.sub(r"\(UInt256\.ofNat (\d+)\)", r"⟨\1⟩", term)
        term = re.sub(r"\(⟨(\d+)⟩ : UInt256\)", r"⟨\1⟩", term)
        return term

    def cond_proof(self, term: str, kind: str, extra: dict) -> str:
        lib = self.lib_spelling(term)
        if "weiValue" in term:
            return "(by first | (rw [hwv]; decide) | exact isZero_eq_zero_of_ne hwv | exact hwv | simpa using hwv)"
        if "calldata.size" in term:
            return ("(by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort"
                    " | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)"
                    " | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide)"
                    " | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide))")
        if SEL_TERM_RE.search(term):
            if kind == "arm":
                return f"(by simpa [solcSelectorWord] using (show {lib} by rw [hword]; native_decide))"
            if kind == "nomatch":
                m = re.search(r"UInt256\.eq ⟨(\d+)⟩ \(solcSelectorWord I\)", lib)
                if m:
                    value = int(m.group(1))
                    t = next((t for t in self.c.transitions if int.from_bytes(t.selector, "big") == value), None)
                    if t is not None:
                        return (f"(by simpa [solcSelectorWord] using (show {lib} by "
                                f"rw [solcSelectorWord, {t.name}EvmSelector hsz, hnm {t.index} (by omega)]; decide))")
            key = lib.replace(" ≠ ⟨0⟩", " = ⟨0⟩")
            hyp = extra.get("pivots", {}).get(key)
            if hyp:
                return f"(by simpa [solcSelectorWord] using {hyp})"
        return "(by sorry)"

    def valid_proof(self) -> str:
        if self.c.immutables:
            return f"(by exact {self.c.prefix}Jumpdest v rfl rfl)"
        return f"(by exact {self.c.prefix}Jumpdest rfl rfl)"

    def takes(self, name: str, hyp: str) -> bool:
        """Whether the block theorem `name` has the hypothesis `hyp` (from the generated block
        files; assumed when they are not there yet)."""
        hyps = self.c.block_hyps
        return hyps is None or name not in hyps or hyp in hyps[name]

    # --- chains --------------------------------------------------------------------------------

    def chain(self, steps: list[Step], kind: str, start: str, extra: dict | None = None,
              indent: str = "  ", init: RDState | None = None) -> tuple[list[str], str, RDState, str | None, list[str]]:
        """Proof lines applying the summaries; returns (lines, last hypothesis, state, terminal, defs)."""
        extra = extra or {}
        lines: list[str] = []
        state = init.copy() if init is not None else RDState([], "ByteArray.empty", "(UInt256.ofNat 0)")
        defs: list[str] = []
        last = start
        terminal = None
        imm = self.imm_args()
        for n, step in enumerate(steps, 1):
            name = self.d.theorem_name(step.piece, step.branch)
            args = [f"(by simp [{', '.join(defs)}])" if defs else "(by simp)"]
            has_stack_hyp = any(ins.opcode != 0xFE for ins in step.piece.instructions)
            if not has_stack_hyp:
                args = []
            env = {f"x{i}": state.stack[i] for i in range(min(len(state.stack), len(step.summary.stack_in)))}
            env["mem"] = state.mem
            env["aw"] = state.aw
            for hyp, term in step.conds:
                if hyp == "hcond":
                    args.append(self.cond_proof(subst(term, env), kind, extra))
                elif hyp == "hvalid":
                    if self.takes(name, "hvalid"):
                        args.append(self.valid_proof())
                elif hyp == "hperm":
                    args.append("hperm")
                else:
                    args.append("(by sorry)")
            lines.append(f"{indent}have rd{n} := {self.c.blocks_ns}.{name}{imm} {' '.join(args)} {last}")
            last = f"rd{n}"
            if step.summary.terminal:
                terminal = step.summary.terminal
                break
            stack_changed = rd.stack_term(step.summary.stack_out) != rd.stack_term(step.summary.stack_in)
            if stack_changed:
                defs.append(f"{self.c.blocks_ns}.{name}_stack")
            if step.summary.mem != "mem":
                defs.append(f"{self.c.blocks_ns}.{name}_memory")
            state = apply_summary(state, step.summary)
        return lines, last, state, terminal, defs

    def imm_args(self) -> str:
        """The code-suffix argument a summary takes when the contract has immutables."""
        return " (immWords := wordsOf (immStore v))" if self.c.immutables else ""

    def state_terms(self, state: RDState) -> tuple[str, str, str]:
        ren = lambda s: s.replace("ee.", "I.")
        return lean_list([ren(x) for x in state.stack]), ren(state.mem), ren(state.aw)

    def reach_statement(self, pc: int, state: RDState) -> str:
        stack, mem, aw = self.state_terms(state)
        return (f"∃ k C, RD ({self.c.code_term}) I g (initState σ σ₀ g A I) (UInt256.ofNat {pc})\n"
                f"      {stack}\n      {mem}\n      {aw} ByteArray.empty σ k C")

    def finish(self, defs: list[str], last: str, indent: str = "  ") -> str:
        simp_set = defs + (["deployedRuntime"] if self.c.immutables else [])
        return f"{indent}exact ⟨_, _, by simpa [{', '.join(simp_set)}] using {last}⟩"

    def finish_rev(self, defs: list[str], last: str, indent: str = "  ") -> str:
        simp_set = defs + (["deployedRuntime"] if self.c.immutables else [])
        return f"{indent}simpa [{', '.join(simp_set)}] using {last}" if simp_set else f"{indent}exact {last}"

    def hword_lines(self, t: Transition) -> list[str]:
        s = t.selector
        v = int.from_bytes(s, "big")
        return [f"  have hword : solcSelectorWord I = ⟨{v}⟩ :=",
                f"    solcSelectorWord_eq_of_beq I hsz 0x{s[0]:02x} 0x{s[1]:02x} 0x{s[2]:02x} 0x{s[3]:02x} ⟨{v}⟩ (by native_decide)",
                f"      (by simpa [{self.c.prefix}SelBytes] using hsel)"]

    # --- lemmas --------------------------------------------------------------------------------

    def binders(self, with_hwv: bool, size_hyps: str) -> str:
        v = self.c.v_binder
        hwv = " (hwv : I.weiValue = ⟨0⟩)" if with_hwv else ""
        return (f"{{σ σ₀ A I}} {{g : Sat256}}{v}\n    (hcode : I.code = {self.c.code_term}){hwv}"
                f"{size_hyps}")

    def arm_lemma(self, t: Transition, arm_pc: int) -> str:
        p = self.c.prefix
        name = f"{p}Reach{t.cap}Body"
        head = (f"theorem {name} {self.binders(self.global_guard, ' (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)')}\n"
                f"    (hsel : selIs I ({p}SelBytes {t.index})) :")
        try:
            steps = self.d.run(Env(0, "big", int.from_bytes(t.selector, "big")), arm_pc)
            if any(isinstance(s, Fork) for s in steps):
                raise PathError("unexpected fork on an arm path")
            lines, last, state, terminal, defs = self.chain(steps, "arm", "rd0")
            if terminal:
                raise PathError(f"arm path of {t.signature} ends in {terminal}")
            body = self.hword_lines(t) + [
                "  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode", *lines, self.finish(defs, last)]
            return "\n".join([f"/-- Dispatcher path to `{t.signature}` (arm entry pc {arm_pc}). -/", head,
                              f"    {self.reach_statement(arm_pc, state)} := by", *body, ""])
        except PathError as error:
            return "\n".join([f"/-- Dispatcher path to `{t.signature}` (arm entry pc {arm_pc}); "
                              f"path analysis failed: {error}. -/", head,
                              f"    ∃ k C, RD ({self.c.code_term}) I g (initState σ σ₀ g A I) (UInt256.ofNat {arm_pc})\n"
                              f"      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by",
                              "  sorry", ""])

    def rev_lemma(self, name: str, doc: str, binders: str, env: Env, kind: str) -> tuple[str, bool]:
        """A lemma whose path ends in a revert (or at the fallback entry); returns (text, ends in RDrev)."""
        head = f"/-- {doc} -/\ntheorem {name} {binders} :"
        try:
            if self.fallback_pc is not None:
                steps = self.d.run(env, self.fallback_pc)
                if any(isinstance(s, Fork) for s in steps):
                    raise PathError("pivot on the way to the fallback entry (not supported yet)")
                lines, last, state, terminal, defs = self.chain(steps, kind, "rd0")
                if terminal is not None:
                    raise PathError(f"path to the fallback entry ends in {terminal}")
                return "\n".join([head.replace(" -/", f" (runs the fallback at pc {self.fallback_pc}). -/"),
                                  f"    {self.reach_statement(self.fallback_pc, state)} := by",
                                  "  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode",
                                  *lines, self.finish(defs, last), ""]), False
            steps = self.d.run(env, None)
            if any(isinstance(s, Fork) for s in steps):
                return self.fork_lemma(name, doc, binders, env, kind)
            lines, last, state, terminal, defs = self.chain(steps, kind, "rd0")
            if terminal and "RDrev" in terminal:
                return "\n".join([head, f"    RDrev ({self.c.code_term}) g (initState σ σ₀ g A I) := by",
                                  "  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode",
                                  *lines, self.finish_rev(defs, last), ""]), True
            raise PathError(f"path ends in {terminal or 'a non-revert block'}")
        except PathError as error:
            return "\n".join([head.replace(" -/", f"; path analysis failed: {error}. -/"),
                              f"    RDrev ({self.c.code_term}) g (initState σ σ₀ g A I) := by", "  sorry", ""]), True

    def fork_lemma(self, name: str, doc: str, binders: str, env: Env, kind: str) -> tuple[str, bool]:
        """The no-match path of a binary-search dispatcher: nested case splits on the pivots."""
        head = f"/-- {doc} (binary-search dispatcher: case split on each pivot). -/\ntheorem {name} {binders} :"
        body: list[str] = ["  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode"]
        try:
            self.fork_tree(env, kind, body, "  ", 0, [], {})
        except PathError as error:
            return "\n".join([head.replace(" -/", f"; path analysis failed: {error}. -/"),
                              f"    RDrev ({self.c.code_term}) g (initState σ σ₀ g A I) := by", "  sorry", ""]), True
        return "\n".join([head, f"    RDrev ({self.c.code_term}) g (initState σ σ₀ g A I) := by", *body, ""]), True

    def fork_tree(self, env: Env, kind: str, body: list[str], indent: str, depth: int,
                  decisions: list[tuple[int, bool]], pivots: dict[str, str]) -> None:
        steps = self.run_with_decisions(env, decisions)
        if steps and isinstance(steps[-1], Fork):
            fork = steps[-1]
            # the pivot condition is the JUMPI condition of the fork piece, instantiated with the
            # stack reaching it
            state = RDState([], "ByteArray.empty", "(UInt256.ofNat 0)")
            for step in steps[:-1]:
                state = apply_summary(state, step.summary)
            summary_t = self.d.summary(fork.piece, "taken")
            cond_term = next(term for hyp, term in summary_t.extra_hypotheses if hyp == "hcond")
            inst = {f"x{i}": state.stack[i] for i in range(min(len(state.stack), len(summary_t.stack_in)))}
            inst["mem"] = state.mem
            inst["aw"] = state.aw
            lib = self.lib_spelling(subst(cond_term, inst)).replace(" ≠ ⟨0⟩", " = ⟨0⟩")
            hyp = f"hpiv{depth}"
            body.append(f"{indent}by_cases {hyp} : {lib}")
            body.append(f"{indent}· -- pivot at pc {fork.jumpi_pc}: not taken")
            self.fork_tree(env, kind, body, indent + "  ", depth + 1, decisions + [(fork.jumpi_pc, False)],
                           {**pivots, lib: hyp})
            body.append(f"{indent}· -- pivot at pc {fork.jumpi_pc}: taken")
            self.fork_tree(env, kind, body, indent + "  ", depth + 1, decisions + [(fork.jumpi_pc, True)],
                           {**pivots, lib: hyp})
            return
        lines, last, state, terminal, defs = self.chain(steps, kind, "rd0", {"pivots": pivots}, indent)
        body.extend(lines)
        if terminal and "RDrev" in terminal:
            body.append(self.finish_rev(defs, last, indent))
        else:
            raise PathError(f"no-match leaf ends in {terminal or 'a non-revert block'}")

    def run_with_decisions(self, env: Env, decisions: list[tuple[int, bool]]):
        """Like `run`, but resolves pivot forks with the recorded decisions."""
        steps: list[Step] = []
        stack: list = []
        pc = 0
        pending = list(decisions)
        for _ in range(300):
            piece = self.d.piece_at(pc)
            branch, next_pc, stack, fork = self.d.execute(piece, stack, env)
            if fork is not None:
                if pending and pending[0][0] == fork.jumpi_pc:
                    _, taken = pending.pop(0)
                    branch = "taken" if taken else "fallthrough"
                    next_pc = fork.dest if taken else piece.end_pc
                else:
                    return steps + [fork]
            summary = self.d.summary(piece, branch)
            steps.append(Step(piece, branch, list(summary.extra_hypotheses), summary))
            if next_pc is None:
                return steps
            pc = next_pc
        raise PathError("dispatcher path too long")


# --------------------------------------------------------------------------------------------
# Dispatch.lean

def render_dispatch(c: Contract, immutable_sites: dict | None, sorry_dispatch: bool,
                    arms: dict[int, int]) -> tuple[str, dict]:
    p = c.prefix
    d = Dispatcher(c, immutable_sites)
    fallback_pc = None
    if c.has_fallback or c.has_receive:
        from evm_tools import dispatcher as recover_dispatcher
        disp = recover_dispatcher(d.instructions)
        if disp.calldatasize_check and not d.is_revert_block(disp.calldatasize_check[1]):
            fallback_pc = disp.calldatasize_check[1]
    gen = ProofGen(c, d, fallback_pc)
    info = {"global_guard": gen.global_guard, "fallback_pc": fallback_pc}
    shards = sorted(f.stem for f in c.directory.glob("RuntimeBlocks_*.lean"))
    out = [f"import {c.module}.Common"]
    out += [f"import {c.module}.{s}" for s in shards]
    out += ["", "/-!", f"# {c.name} dispatcher (generated by `scripts/proof_skeleton.py`)", "",
            "Stele-side dispatch facts and the runtime dispatcher reach lemmas, composed from the block",
            "summaries along the path the compiled dispatcher takes for each selector.", "-/", "",
            "open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach"]
    if c.immutables:
        out += ["open Reasoning.Immutables", f"open {c.namespace}.Immutables"]
    out += ["", f"namespace {c.namespace}", "", "set_option maxRecDepth 2000000", ""]
    # Stele dispatch facts
    simple = not c.has_fallback and not c.has_receive
    out += stele_dispatch_facts(c, sorry_dispatch, simple)
    # runtime reach lemmas
    out += ["/-! ## Runtime dispatcher paths -/", ""]
    size_hyps = " (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)"
    for t in c.transitions:
        value = int.from_bytes(t.selector, "big")
        arm_pc = arms.get(value)
        if arm_pc is None:
            out += [f"-- no dispatcher arm found for {t.signature} (served by the fallback?)", ""]
            continue
        if sorry_dispatch:
            out += [f"theorem {p}Reach{t.cap}Body {gen.binders(gen.global_guard, size_hyps)}",
                    f"    (hsel : selIs I ({p}SelBytes {t.index})) :",
                    f"    ∃ k C, RD ({c.code_term}) I g (initState σ σ₀ g A I) (UInt256.ofNat {arm_pc})",
                    "      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by",
                    "  sorry", ""]
        else:
            out.append(gen.arm_lemma(t, arm_pc))
    if gen.global_guard:
        text, _ = gen.rev_lemma(f"{p}X_callvalue_ne", "`callvalue ≠ 0` reverts in the global non-payable guard",
                                f"{{σ σ₀ A I}} {{g : Sat256}}{c.v_binder}\n    (hcode : I.code = {c.code_term}) (hwv : I.weiValue ≠ ⟨0⟩)",
                                Env("cvnz", "big", "nomatch"), "nomatch")
        out.append(text if not sorry_dispatch else text.split(":= by")[0] + ":= by\n  sorry\n")
    hwv_b = " (hwv : I.weiValue = ⟨0⟩)" if gen.global_guard else ""
    if simple:
        text, _ = gen.rev_lemma(f"{p}X_short", "Calldata shorter than a selector",
                                f"{{σ σ₀ A I}} {{g : Sat256}}{c.v_binder}\n    (hcode : I.code = {c.code_term}){hwv_b}\n"
                                f"    (hshort : I.calldata.size < 4)", Env(0, "small", "nomatch"), "nomatch")
        out.append(text if not sorry_dispatch else text.split(":= by")[0] + ":= by\n  sorry\n")
        text, _ = gen.rev_lemma(f"{p}X_noMatch", "No selector matches",
                                f"{{σ σ₀ A I}} {{g : Sat256}}{c.v_binder}\n    (hcode : I.code = {c.code_term}){hwv_b}\n"
                                f"    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)\n"
                                f"    (hnm : ∀ i, i < {len(c.transitions)} → ({p}SelBytes i == I.calldata.extract 0 4) = false)",
                                Env(0, "big", "nomatch"), "nomatch")
        out.append(text if not sorry_dispatch else text.split(":= by")[0] + ":= by\n  sorry\n")
    out += [f"end {c.namespace}", ""]
    return "\n".join(out), info


def stele_dispatch_facts(c: Contract, sorry_dispatch: bool, simple: bool) -> list[str]:
    """`dispatchMsg` facts: the transition each selector reaches, and `none` for short or unmatched calldata."""
    p = c.prefix
    out = ["/-! ## Stele dispatch: which transition a selector reaches -/", ""]
    for t in c.transitions:
        pre = [u for u in c.transitions if u.index < t.index]
        post = [u for u in c.transitions if u.index > t.index]
        misses = " ".join(f"(h{u.index} : ¬ selIs I ({p}SelBytes {u.index}))" for u in pre)
        out += [f"theorem {p}Dispatch_{t.name} {{I : ExecutionEnv}} {misses}",
                f"    (hsel : selIs I ({p}SelBytes {t.index})) :",
                f"    dispatchMsg contract I.calldata = some {t.handle} := by"]
        if simple and not sorry_dispatch:
            out += [f"  refine dispatchMsg_eq_some_of_split (contract := contract)",
                    f"    (pre := [{', '.join(u.handle for u in pre)}]) (post := [{', '.join(u.handle for u in post)}])",
                    f"    (ti := {t.handle}) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)",
                    "  · exact transitions_eq",
                    "  · intro u hu"]
            if pre:
                out += ["    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu",
                        "    rcases hu with " + " | ".join(["rfl"] * len(pre))]
                for u in pre:
                    out += [f"    · rw [{u.name}SelectorOf]; exact Bool.eq_false_of_not_eq_true h{u.index}"]
            else:
                out += ["    simp at hu"]
            out += [f"  · rw [{t.name}SelectorOf]; exact hsel", ""]
        else:
            out += ["  sorry  -- TODO: contracts with a fallback/receive route unmatched selectors differently", ""]
    if simple:
        out += [f"theorem {p}Dispatch_none_short {{cd : ByteArray}} (h : cd.size < 4) :",
                "    dispatchMsg contract cd = none := by"]
        if not sorry_dispatch:
            out += ["  rw [dispatchMsg_eq_dispatchList contract cd, transitions_eq]",
                    "  refine dispatchList_none_short _ ?_ h",
                    "  intro t ht",
                    "  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht",
                    "  rcases ht with " + " | ".join(["rfl"] * len(c.transitions))]
            out += [f"  · rw [{t.name}SelectorOf]; rfl" for t in c.transitions]
            out += [""]
        else:
            out += ["  sorry", ""]
        out += [f"theorem {p}Dispatch_none_nomatch {{I : ExecutionEnv}}",
                f"    (hnm : ∀ i, i < {len(c.transitions)} → ({p}SelBytes i == I.calldata.extract 0 4) = false) :",
                "    dispatchMsg contract I.calldata = none := by"]
        if not sorry_dispatch:
            out += ["  refine dispatchMsg_none_of_all_ne (contract := contract) (cd := I.calldata) (by rfl) (by rfl) ?_",
                    "  intro t ht",
                    "  rw [transitions_eq] at ht",
                    "  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht",
                    "  rcases ht with " + " | ".join(["rfl"] * len(c.transitions))]
            for t in c.transitions:
                out += [f"  · rw [{t.name}SelectorOf]; exact hnm {t.index} (by omega)"]
            out += [""]
        else:
            out += ["  sorry", ""]
    return out


# --------------------------------------------------------------------------------------------
# Function stubs, constructor, capstone

def body_signature(c: Contract, t: Transition, global_guard: bool) -> str:
    p = c.prefix
    hwv = "\n    (hwv : I.weiValue = ⟨0⟩)" if global_guard else ""
    return (f"theorem {p}{t.cap}Body {{σ σ₀ A I}} {{g : UInt256}}{c.v_binder}\n"
            f"    (hcode : I.code = {c.code_term}) (hsize : I.calldata.size < UInt256.size){hwv}\n"
            f"    (hsel : selIs I ({p}SelBytes {t.index})) :\n"
            f"    runtimeRefinementFor config contract σ σ₀ g A I{c.imm_store_arg}")


def render_function(c: Contract, t: Transition, global_guard: bool, arm_pc: int | None) -> str:
    p = c.prefix
    out = [f"import {c.module}.Dispatch", "",
           "/-!", f"# {c.name} `{t.signature}`", "",
           "Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the",
           "body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.",
           f"Dispatcher arm entry: pc {arm_pc if arm_pc is not None else '?'}; reach lemma `{p}Reach{t.cap}Body`.", "-/", "",
           "open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach"]
    if c.immutables:
        out += ["open Reasoning.Immutables", f"open {c.namespace}.Immutables"]
    out += ["", f"namespace {c.namespace}", "", "set_option maxRecDepth 2000000", "",
            f"/-- `{t.signature}`: the theorem `Correct.lean` routes selector {t.index} to. -/",
            body_signature(c, t, global_guard) + " := by",
            f"  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I ({p}SelBytes {t.index}) rfl hsel",
            "  sorry", "", f"end {c.namespace}", ""]
    return "\n".join(out)


def render_constructor(c: Contract) -> str:
    p = c.prefix
    runtime_of = f"(immutableLayout.deployed {p}Bytecode)" if c.immutables else f"(fun _ => {p}Bytecode)"
    out = [f"import {c.module}.Common", f"import {c.module}.CreationBytecode", "",
           "/-!", f"# {c.name} constructor correctness", "",
           "Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code",
           "return) against the Stele constructor body, composed from the creation summaries.", "-/", "",
           "open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach"]
    if c.immutables and c.compiler_kind == "vyper":
        out += ["open Reasoning.VyperImmutables"]
    elif c.immutables:
        out += ["open Reasoning.Immutables", f"open {c.namespace}.Immutables"]
    out += ["", f"namespace {c.namespace}", "",
            f"theorem {p}ConstructorCorrect :",
            f"    typedConstructorRefinement config {p}CreationBytecode contract {runtime_of} := by",
            "  sorry", "", f"end {c.namespace}", ""]
    return "\n".join(out)


def render_correct(c: Contract, global_guard: bool) -> str:
    p = c.prefix
    n = len(c.transitions)
    out = [f"import {c.module}.Constructor"]
    out += [f"import {c.module}.{t.cap}" for t in c.transitions]
    out += ["import Stele.Refine", "", "/-!", f"# {c.name} correctness capstone (generated by `scripts/proof_skeleton.py`)", "",
            "Thin top-level: the selector case split routes each selector to its per-function `…Body`",
            "lemma, the shared revert paths close the rest, and the constructor is packaged into the",
            "whole-contract refinement.", "-/", "",
            "open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach"]
    if c.immutables:
        out += ["open Reasoning.Immutables", f"open {c.namespace}.Immutables"]
    out += ["", f"namespace {c.namespace}", "", "set_option maxRecDepth 2000000", ""]
    v = c.v_binder
    vv = " v" if c.immutables else ""
    imm = c.imm_store_arg
    code = c.code_term
    if global_guard:
        out += [f"theorem {p}BodyReverts_nonPayable{v} (t : TransitionDecl)",
                "    (ht : t ∈ contract.transitions) (evm : EVM.State) (callargs : Store)",
                "    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :",
                f"    ExecTransitionBody config contract evm callargs t.body .reverted{imm} := by",
                "  rw [transitions_eq] at ht",
                "  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht",
                "  rcases ht with " + " | ".join(["rfl"] * n) + " <;>",
                "    exact ExecFuncBody.execBlockRevert (blockReverts_nonPayable hwv)", "",
                f"/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/",
                f"theorem {p}NonPayable {{σ σ₀ A I}} {{g : UInt256}}{v}",
                f"    (hcode : I.code = {code}) (hwv : I.weiValue ≠ ⟨0⟩) :",
                f"    runtimeRefinementFor config contract σ σ₀ g A I{imm} := by",
                f"  exact ({p}X_callvalue_ne (g := Sat256.ofUInt256 g){vv} hcode hwv).reEquivElim hcode",
                "    fun _ _ hrev => by",
                "      by_cases hdisp : dispatchMsg contract I.calldata = none",
                "      · exact reEquiv_noDispatch hdisp hrev",
                "      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp",
                "        have htmem : t ∈ contract.transitions := by",
                "          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)] at ht",
                "          exact dispatchList_some_mem ht",
                "        by_cases hdec : config.externalABI.decodeCalldata? (t.params.map Param.name)",
                "            (transitionSignature t).paramTypes I.calldata = none",
                "        · exact reEquiv_decodingFailed ht hdec hrev",
                "        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec",
                "          exact reEquiv_execution ht hca",
                f"            ({p}BodyReverts_nonPayable{vv} t htmem",
                "              (initState σ σ₀ (Sat256.ofUInt256 g) A I)",
                "              callargs (by simp only [initState]; exact hwv))",
                "            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)", ""]
    hwv_b = " (hwv : I.weiValue = ⟨0⟩)" if global_guard else ""
    hwv_a = " hwv" if global_guard else ""
    out += [f"theorem {p}NoDispatch {{σ σ₀ A I}} {{g : UInt256}}{v}",
            f"    (hcode : I.code = {code}) (hsize : I.calldata.size < UInt256.size){hwv_b}",
            f"    (hnm : ∀ i, i < {n} → ({p}SelBytes i == I.calldata.extract 0 4) = false) :",
            f"    runtimeRefinementFor config contract σ σ₀ g A I{imm} := by"]
    if c.has_fallback or c.has_receive:
        out += ["  sorry  -- TODO: refine the fallback/receive execution for unmatched calldata", ""]
    else:
        out += ["  by_cases hsz : 4 ≤ I.calldata.size",
                f"  · exact ({p}X_noMatch (g := Sat256.ofUInt256 g){vv} hcode{hwv_a} hsz hsize hnm)",
                f"      |>.reEquivNoDispatch hcode ({p}Dispatch_none_nomatch hnm)",
                "  · have hshort : I.calldata.size < 4 := by omega",
                f"    exact ({p}X_short (g := Sat256.ofUInt256 g){vv} hcode{hwv_a} hshort)",
                f"      |>.reEquivNoDispatch hcode ({p}Dispatch_none_short hshort)", ""]
    hyps = " ".join(f"(h{t.index} : ¬ selIs I ({p}SelBytes {t.index}))" for t in c.transitions)
    out += [f"theorem {p}NoSelectorMatches {{I : ExecutionEnv}}", f"    {hyps} :",
            f"    ∀ i, i < {n} → ({p}SelBytes i == I.calldata.extract 0 4) = false := by",
            "  intro i hi", "  interval_cases i"]
    out += [f"  · simpa [selIs] using h{t.index}" for t in c.transitions]
    out += [""]
    runtime_name = f"{p}Correct"
    out += [f"theorem {runtime_name}{v} :",
            f"    runtimeRefinement config ({code}) contract{imm} := by",
            "  refine ⟨fun σ σ₀ g A I hcode hsize ↦ ?_⟩"]
    indent = "  "
    if global_guard:
        out += ["  by_cases hwv : I.weiValue = ⟨0⟩"]
        indent = "  · "
    line_indent = indent
    for t in c.transitions:
        prev = " ".join(f"h{u.index}" for u in c.transitions if u.index < t.index)
        out += [f"{line_indent}by_cases h{t.index} : selIs I ({p}SelBytes {t.index})",
                f"{line_indent.replace('·', ' ')}· exact {p}{t.cap}Body{vv} hcode hsize{hwv_a} h{t.index}"]
        line_indent = line_indent.replace("·", " ") + "· "
    all_h = " ".join(f"h{t.index}" for t in c.transitions)
    out += [f"{line_indent}exact {p}NoDispatch{vv} hcode hsize{hwv_a} ({p}NoSelectorMatches {all_h})"]
    if global_guard:
        out += [f"  · exact {p}NonPayable{vv} hcode hwv"]
    out += [""]
    if c.immutables:
        out += [f"theorem {p}RuntimeCorrect (imms : Store) (hfit : immutablesFit contract imms) :",
                f"    runtimeRefinement config (immutableLayout.deployed {p}Bytecode imms) contract",
                "      (restrictImmutables contract imms) := by",
                "  obtain ⟨v, hv⟩ := restrictImmutables_of_fit hfit",
                "  rw [← Reasoning.Immutables.Layout.deployed_restrict immutableLayout_keys, hv]",
                f"  exact {runtime_name} v", "",
                f"theorem {p}ContractCorrect :",
                f"    contractRefinement config {p}CreationBytecode contract :=",
                f"  .of_runtime {p}ConstructorCorrect {p}RuntimeCorrect", ""]
    else:
        out += [f"theorem {p}ContractCorrect :",
                f"    contractRefinement config {p}CreationBytecode contract :=",
                f"  contractRefinement.of_constant {p}ConstructorCorrect {runtime_name}", ""]
    out += [f"end {c.namespace}", ""]
    return "\n".join(out)


# --------------------------------------------------------------------------------------------


# --------------------------------------------------------------------------------------------
# Vyper: the computed dispatcher

VYPER_HEAD_RE = re.compile(rb"\x5f\x35\x60\xe0\x1c\x60\x02\x60(.)\x82(.)\x60\x01\x1b\x61(..)\x01\x60\x1e\x39\x5f\x51\x56", re.S)
SEL_SPELLED = ("(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) "
               "(UInt256.ofNat 224))")


@dataclass
class VyperTable:
    """Vyper 0.4's jump table: `selector % buckets` (or `& mask`) indexes 2-byte entries at `table`."""
    buckets: int
    mask: int | None          # the AND mask, or None for MOD
    table: int
    entries: list[int]

    @property
    def index_term(self) -> str:
        if self.mask is not None:
            return f"(UInt256.land (solcSelectorWord I) (UInt256.ofNat {self.mask}))"
        return f"(UInt256.mod (solcSelectorWord I) (UInt256.ofNat {self.buckets}))"

    @property
    def index_lemma(self) -> str:
        if self.mask is not None:
            b = self.buckets.bit_length() - 1
            return (f"land_eq_ofNat (mask := {self.mask}) (b := {b}) (n := {self.buckets}) (by norm_num) (by norm_num) "
                    "(by decide) hm")
        return "mod_eq_ofNat (by decide) (by decide) hm"


def vyper_table(runtime: bytes) -> VyperTable | None:
    m = VYPER_HEAD_RE.match(runtime)
    if m is None:
        return None
    n, op, table = m.group(1)[0], m.group(2)[0], int.from_bytes(m.group(3), "big")
    if op == 0x06:
        buckets, mask = n, None
    elif op == 0x16 and (n + 1) & n == 0:
        buckets, mask = n + 1, n
    else:
        return None
    entries = [int.from_bytes(runtime[table + 2 * k:table + 2 * k + 2], "big") for k in range(buckets)]
    return VyperTable(buckets, mask, table, entries)


class VyperProofGen(ProofGen):
    """Reach and revert lemmas for the jump-table dispatcher, from the block summaries."""

    def __init__(self, c: Contract, d: Dispatcher, table: VyperTable) -> None:
        super().__init__(c, d)
        self.table = table
        self.global_guard = False
        self.suffix = bool(c.immutables)
        self.code = f"({c.prefix}Bytecode ++ suffix)" if self.suffix else f"{c.prefix}Bytecode"
        self.binder_suffix = " {suffix : ByteArray}" if self.suffix else ""
        self.selectors = {int.from_bytes(t.selector, "big"): t for t in c.transitions}

    # --- the compare chain of a bucket -----------------------------------------------------

    def compare_block(self, pc: int) -> tuple[int, int, int] | None:
        """(selector constant, jump target, fallthrough pc) when `pc` starts `JUMPDEST PUSH4 c DUP2 XOR PUSH2 d JUMPI`."""
        piece = self.d.by_pc.get(pc)
        if piece is None:
            return None
        ops = [ins.opcode for ins in piece.instructions]
        if ops != [0x5B, 0x63, 0x81, 0x18, 0x61, 0x57]:
            return None
        const = piece.instructions[1].argument
        dest = piece.instructions[4].argument
        return const, dest, piece.end_pc

    def chain_of(self, entry: int) -> tuple[list[tuple[int, int, int, int]], int]:
        """The compare blocks from a bucket entry, (pc, constant, target, fallthrough), and the final pc."""
        chain: list[tuple[int, int, int, int]] = []
        pc = entry
        for _ in range(64):
            cmp = self.compare_block(pc)
            if cmp is None:
                return chain, pc
            const, dest, end = cmp
            chain.append((pc, const, dest, end))
            pc = dest
        raise PathError("compare chain too long")

    def arm_of(self, value: int) -> tuple[int, int, list[Step]]:
        """(bucket, arm pc, steps) for a selector value: taken compares until its own, which falls through."""
        m = value % self.table.buckets if self.table.mask is None else value & self.table.mask
        chain, _ = self.chain_of(self.table.entries[m])
        steps: list[Step] = []
        for pc, const, _, end in chain:
            piece = self.d.by_pc[pc]
            branch = "fallthrough" if const == value else "taken"
            summary = self.d.summary(piece, branch)
            steps.append(Step(piece, branch, list(summary.extra_hypotheses), summary))
            if const == value:
                return m, end, steps
        raise PathError(f"selector 0x{value:08x} is not compared in bucket {m}")

    def miss_of(self, m: int) -> list[Step]:
        """Steps of bucket `m` when no selector matches: every compare taken, then the revert block."""
        chain, final = self.chain_of(self.table.entries[m])
        steps: list[Step] = []
        for pc, _, _, _ in chain:
            piece = self.d.by_pc[pc]
            summary = self.d.summary(piece, "taken")
            steps.append(Step(piece, "taken", list(summary.extra_hypotheses), summary))
        piece = self.d.piece_at(final)
        summary = self.d.summary(piece, None)
        if not (summary.terminal and "RDrev" in summary.terminal):
            raise PathError(f"bucket {m} does not end in a revert block (pc {final})")
        steps.append(Step(piece, None, list(summary.extra_hypotheses), summary))
        return steps

    # --- proof pieces ------------------------------------------------------------------------

    def init_state(self, m: int) -> RDState:
        return RDState(["(solcSelectorWord I)"], f"({self.c.prefix}DispatchMem {m})", "(UInt256.ofNat 1)")

    def cond_proof(self, term: str, kind: str, extra: dict) -> str:
        lib = self.lib_spelling(term)
        m = re.search(r"UInt256\.xor \(solcSelectorWord I\) ⟨(\d+)⟩", lib)
        if m is None:
            return super().cond_proof(term, kind, extra)
        value = int(m.group(1))
        if kind == "arm":
            return f"(by simpa [solcSelectorWord] using (show {lib} by rw [hword]; native_decide))"
        if kind == "nomatch":
            t = self.selectors.get(value)
            if t is None:
                return "(by sorry)"
            return (f"(by simpa [solcSelectorWord] using u256_xor_ne_zero_of_ne (selectorWord_ne_of_selector_false "
                    f"(sel := ⟨{value}⟩) hsz (by native_decide) (hnm {t.index} (by omega))))")
        if kind == "short":
            return (f"(by simpa [solcSelectorWord] using u256_xor_ne_zero_of_ne (selectorWord_ne_of_short "
                    f"(sel := ⟨{value}⟩) hshort (by native_decide)))")
        return "(by sorry)"

    def valid_proof(self) -> str:
        if self.suffix:
            return f"(by apply D_J_contains_append_left; exact {self.c.prefix}Jumpdest rfl rfl)"
        return f"(by exact {self.c.prefix}Jumpdest rfl rfl)"

    def imm_args(self) -> str:
        return " (suffix := suffix)" if self.suffix else ""

    def finish(self, defs: list[str], last: str, indent: str = "  ") -> str:
        if defs:
            return f"{indent}exact ⟨_, _, by simpa [{', '.join(defs)}] using {last}⟩"
        return f"{indent}exact ⟨_, _, {last}⟩"

    def finish_rev(self, defs: list[str], last: str, indent: str = "  ") -> str:
        return f"{indent}simpa [{', '.join(defs)}] using {last}" if defs else f"{indent}exact {last}"

    def reach_statement(self, pc: int, state: RDState) -> str:
        stack, mem, aw = self.state_terms(state)
        return (f"∃ k C, RD {self.code} I g (initState σ σ₀ g A I) (UInt256.ofNat {pc})\n"
                f"      {stack} {mem} {aw} ByteArray.empty σ k C")

    def binders(self, with_hwv: bool, size_hyps: str) -> str:
        return f"{{σ σ₀ A I}} {{g : Sat256}}{self.binder_suffix}\n    (hcode : I.code = {self.code}){size_hyps}"

    # --- lemmas --------------------------------------------------------------------------------

    def bucket_lemma(self) -> list[str]:
        c, t = self.c, self.table
        p = c.prefix
        n = t.buckets
        code = self.code
        idx = t.index_term
        spelled_idx = idx.replace("(solcSelectorWord I)", SEL_SPELLED)
        write = (f"{code}.write ((UInt256.ofNat {t.table}) + (UInt256.shiftLeft {{idx}} (UInt256.ofNat 1))).toNat "
                 "ByteArray.empty (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat")
        out = [f"/-! ## The computed dispatcher: `selector {'&' if t.mask is not None else '%'} "
               f"{t.mask if t.mask is not None else n}` indexes {n} two-byte entries at code offset {t.table} -/", "",
               f"/-- Memory after the table lookup of bucket `m`: the entry's two bytes at offset 30. -/",
               f"def {p}DispatchMem (m : Nat) : ByteArray := {p}Bytecode.write ({t.table} + 2 * m) ByteArray.empty 30 2", "",
               "/-- The lookup lands bucket `m` at the entry it names. -/",
               f"theorem {p}Bucket {{σ σ₀ A I}} {{g : Sat256}}{self.binder_suffix} (m : Nat) (entry : UInt256)",
               f"    (hcode : I.code = {code}) (hm : (solcSelectorWord I).toNat % {n} = m)",
               f"    (hload : memLoad ⟨0⟩ ({p}DispatchMem m) = entry)",
               f"    (hvalid : (D_J {p}Bytecode 0).contains entry = true) :",
               f"    ∃ k C, RD {code} I g (initState σ σ₀ g A I) entry",
               f"      [solcSelectorWord I] ({p}DispatchMem m) (UInt256.ofNat 1) ByteArray.empty σ k C := by",
               f"  have hmlt : m < {n} := by rw [← hm]; exact Nat.mod_lt _ (by decide)",
               "  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode",
               f"  have hoff : ((UInt256.ofNat {t.table}) + (UInt256.shiftLeft {idx} (UInt256.ofNat 1))).toNat = {t.table} + 2 * m :=",
               f"    offset_toNat ({t.index_lemma}) (lt_of_lt_of_le (by omega : {t.table} + 2 * m < {t.table + 2 * n + 1}) (by decide))",
               f"  have hmem : {write.format(idx=idx)} = {p}DispatchMem m := by",
               "    rw [hoff, ulit_toNat' 30 (by decide), ulit_toNat' 2 (by decide)]"]
        if self.suffix:
            out += [f"    exact write_append_left_empty _ _ _ _ _ (by decide) (by rw [{p}Bytecode_size]; omega)"]
        else:
            out += ["    rfl"]
        out += [f"  have hmem' : {write.format(idx=spelled_idx)} = {p}DispatchMem m := hmem",
                "  have haw : M (M (UInt256.ofNat 0) (UInt256.ofNat 30) (UInt256.ofNat 2)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256) =",
                "      UInt256.ofNat 1 := by decide",
                f"  have rd1 := {c.blocks_ns}.{p}_block_0{' (suffix := suffix)' if self.suffix else ''} (R := []) (mem := ByteArray.empty)",
                "    (aw := UInt256.ofNat 0) (by simp)",
                "    (by",
                f"      show (D_J {code} 0).contains (memLoad ⟨0⟩ ({write.format(idx=idx)})) = true",
                "      rw [hmem, hload]",
                "      exact D_J_contains_append_left _ _ _ hvalid) rd0" if self.suffix else
                "      exact hvalid) rd0",
                f"  simp only [{c.blocks_ns}.{p}_block_0_stack, {c.blocks_ns}.{p}_block_0_memory] at rd1",
                "  rw [hmem', hload, haw] at rd1",
                "  exact ⟨_, _, rd1⟩", ""]
        for m, entry in enumerate(t.entries):
            out += [f"/-- Bucket {m} enters at pc {entry}. -/",
                    f"theorem {p}Bucket{m} {{σ σ₀ A I}} {{g : Sat256}}{self.binder_suffix}",
                    f"    (hcode : I.code = {code}) (hm : (solcSelectorWord I).toNat % {n} = {m}) :",
                    f"    ∃ k C, RD {code} I g (initState σ σ₀ g A I) (UInt256.ofNat {entry})",
                    f"      [solcSelectorWord I] ({p}DispatchMem {m}) (UInt256.ofNat 1) ByteArray.empty σ k C :=",
                    f"  {p}Bucket {m} (UInt256.ofNat {entry}) hcode hm (by native_decide)",
                    f"    (by exact {p}Jumpdest rfl rfl)", ""]
        return out

    def arm_lemma(self, t: Transition, arm_pc: int) -> str:
        p = self.c.prefix
        value = int.from_bytes(t.selector, "big")
        name = f"{p}Reach{t.cap}Body"
        head = (f"theorem {name} {self.binders(False, ' (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)')}\n"
                f"    (hsel : selIs I ({p}SelBytes {t.index})) :")
        try:
            m, pc, steps = self.arm_of(value)
            lines, last, state, terminal, defs = self.chain(steps, "arm", "rd0", init=self.init_state(m))
            if terminal:
                raise PathError(f"arm path of {t.signature} ends in {terminal}")
            body = self.hword_lines(t) + [
                f"  have hm : (solcSelectorWord I).toNat % {self.table.buckets} = {m} := by rw [hword]; native_decide",
                f"  obtain ⟨_, _, rd0⟩ := {p}Bucket{m} hcode hm", *lines, self.finish(defs, last)]
            return "\n".join([f"/-- Dispatcher path to `{t.signature}` (bucket {m}, arm entry pc {pc}). -/", head,
                              f"    {self.reach_statement(pc, state)} := by", *body, ""])
        except PathError as error:
            return "\n".join([f"/-- Dispatcher path to `{t.signature}`; path analysis failed: {error}. -/", head,
                              f"    ∃ k C, RD {self.code} I g (initState σ σ₀ g A I) (UInt256.ofNat {arm_pc})\n"
                              f"      [solcSelectorWord I] ({p}DispatchMem 0) (UInt256.ofNat 1) ByteArray.empty σ k C := by",
                              "  sorry", ""])

    def miss_lemma(self, name: str, doc: str, kind: str, hyps: str) -> str:
        """`X_noMatch` / `X_short`: every bucket's compare chain is taken down to the revert block."""
        p = self.c.prefix
        n = self.table.buckets
        head = (f"/-- {doc} -/\ntheorem {name} {{σ σ₀ A I}} {{g : Sat256}}{self.binder_suffix}\n"
                f"    (hcode : I.code = {self.code}){hyps} :\n"
                f"    RDrev {self.code} g (initState σ σ₀ g A I) := by")
        body = [f"  have hmlt : (solcSelectorWord I).toNat % {n} < {n} := Nat.mod_lt _ (by decide)",
                f"  generalize hm : (solcSelectorWord I).toNat % {n} = m at hmlt",
                "  interval_cases m"]
        try:
            if kind == "short":
                low_zero = [t.signature for t in self.c.transitions if t.selector[3] == 0]
                if low_zero:
                    raise PathError(f"selector with a zero low byte matches short calldata: {', '.join(low_zero)}")
            for m in range(n):
                steps = self.miss_of(m)
                lines, last, state, terminal, defs = self.chain(steps, kind, "rd0", indent="    ",
                                                                init=self.init_state(m))
                body += [f"  · obtain ⟨_, _, rd0⟩ := {p}Bucket{m} hcode hm", *lines, self.finish_rev(defs, last, "    ")]
        except PathError as error:
            return "\n".join([head.replace(" -/", f"; path analysis failed: {error}. -/"), "  sorry", ""])
        return "\n".join([head, *body, ""])


def render_common_vyper(c: Contract) -> str:
    p = c.prefix
    out = [f"import {c.module}.Spec", f"import {c.module}.Bytecode", f"import {c.module}.Selectors",
           "import Reasoning.ABI", "import Reasoning.Constructor", "import Reasoning.Solc",
           "import Reasoning.Storage", "import Reasoning.Dispatch", "import Reasoning.SteleBody",
           "import Reasoning.WordArithmetic", "import Reasoning.Initcode", "import Reasoning.MemCascade",
           "import Reasoning.ABIViews", "import Reasoning.Vyper", "import Reasoning.VyperDispatch",
           "import Mathlib.Tactic.IntervalCases"]
    if c.immutables:
        out += [f"import {c.module}.Immutables", f"import {c.module}.ImmutableCode", "import Reasoning.VyperImmutables"]
    out += ["", "/-!", f"# {c.name} proof prelude (generated by `scripts/proof_skeleton.py`, Vyper)", "",
            "Single import point for the proof files; selector bridges, selector-word facts, and the",
            "immutables bridge.  Contract-specific helpers shared by several proof files go here too.", "-/", "",
            "open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch"]
    if c.immutables:
        out += ["open Reasoning.VyperImmutables"]
    out += ["", f"namespace {c.namespace}", "", "set_option maxRecDepth 2000000", ""]
    if vyper_wf(c):
        out += [f"/-- The storage precondition the runtime refinement is stated under (`--wf {vyper_wf(c)}`).",
                "Strengthen it to the typed view the proofs need: Vyper returns and compares raw storage",
                "words, so a `bool`/`address` slot must hold a canonical word, a bounded array's length",
                "word must be within its capacity, and the words the body re-reads after an external",
                "call must stay well-formed.  Every writer stores validated words, so the proofs preserve",
                "it; record the final predicate in the hand-off. -/",
                f"def {vyper_wf(c)} : StorageWF := fun _ _ => True", ""]
    out += common_bridges(c)
    out += jumpdest_wrapper(c)
    if c.immutables:
        out += ["/-! ## Immutables: the deployed runtime is the template plus the words of the store -/", "",
                "/-- A well-typed immutables store deploys the template with its words as the code suffix,",
                "the form the block summaries state the code in (the Vyper analogue of",
                "`restrictImmutables_of_fit`). -/",
                "theorem deployed_of_fit {imms : Store} (h : immutablesFit contract imms) :",
                f"    immutableLayout.deployed {p}Bytecode imms =",
                f"      {p}Bytecode ++ immutableLayout.suffixWords (wordsOf imms) := by",
                "  sorry  -- TODO: each declared immutable fits its scalar type (`elemValueFits`), so `scalarBytes?`",
                "         -- yields its 32-byte word; conclude with `deployedRuntime_eq_words` (ImmutableCode.lean)", ""]
    out += [f"end {c.namespace}", ""]
    return "\n".join(out)


def vyper_imm_binders(c: Contract) -> tuple[str, str, str]:
    """(binders, code term, immutables argument) of the runtime theorems."""
    if c.immutables:
        return (" (imms : Store) (hfit : immutablesFit contract imms)",
                f"immutableLayout.deployed {c.prefix}Bytecode imms", " (restrictImmutables contract imms)")
    return "", f"{c.prefix}Bytecode", ""


def vyper_wf(c: Contract) -> str | None:
    """The storage well-formedness predicate the Vyper proofs are stated under (`--wf`), if any.

    Vyper returns and compares raw storage words, so a spec with typed storage (`bool`, `address`,
    bounded arrays) refines the bytecode only on well-formed storage; the proofs then take
    `(hwf : <wf> σ I)` and the capstone is a `runtimeRefinementWithWF <wf> noGasBound`."""
    return getattr(c, "wf", None)


def render_dispatch_vyper(c: Contract, sorry_dispatch: bool) -> tuple[str, dict[int, tuple[int, int] | None]]:
    """Dispatch.lean for a Vyper contract; returns the text and each selector's (bucket, arm pc)."""
    p = c.prefix
    table = vyper_table(c.runtime)
    if table is None:
        raise SystemExit("the runtime does not start with Vyper 0.4's jump-table dispatcher")
    d = Dispatcher(c, None)
    gen = VyperProofGen(c, d, table)
    shards = sorted(f.stem for f in c.directory.glob("RuntimeBlocks_*.lean"))
    out = [f"import {c.module}.Common"]
    out += [f"import {c.module}.{s}" for s in shards]
    out += ["", "/-!", f"# {c.name} dispatcher (generated by `scripts/proof_skeleton.py`, Vyper)", "",
            "Stele-side dispatch facts and the runtime dispatcher reach lemmas: the jump-table lookup of",
            "each bucket (`…Bucket`), then the selector-compare chain of the bucket down to the function's",
            "guard block or to the no-match revert, composed from the block summaries.", "-/", "",
            "open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch", "",
            f"namespace {c.namespace}", "", "set_option maxRecDepth 2000000", ""]
    simple = not c.has_fallback and not c.has_receive
    out += stele_dispatch_facts(c, sorry_dispatch, simple)
    arms: dict[int, tuple[int, int] | None] = {}
    if sorry_dispatch:
        out += ["-- dispatcher reach lemmas left as sorry (--sorry-dispatch)", ""]
    else:
        out += gen.bucket_lemma()
        out += ["/-! ## Runtime dispatcher paths -/", ""]
    for t in c.transitions:
        value = int.from_bytes(t.selector, "big")
        try:
            m, pc, _ = gen.arm_of(value)
            arms[value] = (m, pc)
        except PathError:
            arms[value] = None
        if sorry_dispatch:
            continue
        out.append(gen.arm_lemma(t, arms[value][1] if arms[value] else 0))
    if simple and not sorry_dispatch:
        out.append(gen.miss_lemma(f"{p}X_short", "Calldata shorter than a selector: the padded word matches no bucket entry.",
                                  "short", "\n    (hshort : I.calldata.size < 4)"))
        out.append(gen.miss_lemma(f"{p}X_noMatch", "No selector matches.", "nomatch",
                                  "\n    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)\n"
                                  f"    (hnm : ∀ i, i < {len(c.transitions)} → ({p}SelBytes i == I.calldata.extract 0 4) = false)"))
    elif simple:
        for name, hyps in ((f"{p}X_short", "\n    (hshort : I.calldata.size < 4)"),
                           (f"{p}X_noMatch", "\n    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)\n"
                            f"    (hnm : ∀ i, i < {len(c.transitions)} → ({p}SelBytes i == I.calldata.extract 0 4) = false)")):
            out += [f"theorem {name} {{σ σ₀ A I}} {{g : Sat256}}{gen.binder_suffix}",
                    f"    (hcode : I.code = {gen.code}){hyps} :",
                    f"    RDrev {gen.code} g (initState σ σ₀ g A I) := by", "  sorry", ""]
    out += [f"end {c.namespace}", ""]
    return "\n".join(out), arms


def render_function_vyper(c: Contract, t: Transition, arm: tuple[int, int] | None) -> str:
    p = c.prefix
    binders, code, imm = vyper_imm_binders(c)
    wf_binder = f"\n    (hwf : {vyper_wf(c)} σ I)" if vyper_wf(c) else ""
    where = f"bucket {arm[0]}, arm entry pc {arm[1]}" if arm else "arm not found"
    out = [f"import {c.module}.Dispatch", "",
           "/-!", f"# {c.name} `{t.signature}`", "",
           "Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the",
           "body (its own `calldatasize`/`callvalue` guard first), the Stele body evaluation, and the",
           "`…Body` theorem `Correct.lean` consumes.",
           f"Dispatcher: {where}; reach lemma `{p}Reach{t.cap}Body`.", "-/", "",
           "open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch"]
    if c.immutables:
        out += ["open Reasoning.VyperImmutables"]
    out += ["", f"namespace {c.namespace}", "", "set_option maxRecDepth 2000000", "",
            f"/-- `{t.signature}`: the theorem `Correct.lean` routes selector {t.index} to. -/",
            f"theorem {p}{t.cap}Body {{σ σ₀ A I}} {{g : UInt256}}{binders}{wf_binder}",
            f"    (hcode : I.code = {code}) (hsize : I.calldata.size < UInt256.size)",
            f"    (hsel : selIs I ({p}SelBytes {t.index})) :",
            f"    runtimeRefinementFor config contract σ σ₀ g A I{imm} := by",
            f"  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I ({p}SelBytes {t.index}) rfl hsel"]
    if c.immutables:
        out += [f"  have hcode' : I.code = {p}Bytecode ++ immutableLayout.suffixWords (wordsOf imms) := by",
                "    rw [hcode, deployed_of_fit hfit]"]
    out += ["  sorry", "", f"end {c.namespace}", ""]
    return "\n".join(out)


def render_correct_vyper(c: Contract) -> str:
    p = c.prefix
    n = len(c.transitions)
    binders, code, imm = vyper_imm_binders(c)
    args = " imms hfit" if c.immutables else ""
    out = [f"import {c.module}.Constructor"]
    out += [f"import {c.module}.{t.cap}" for t in c.transitions]
    out += ["import Stele.Refine", "", "/-!", f"# {c.name} correctness capstone (generated by `scripts/proof_skeleton.py`, Vyper)", "",
            "Thin top-level: the selector case split routes each selector to its per-function `…Body`",
            "lemma, the shared revert paths close the rest, and the constructor is packaged into the",
            "whole-contract refinement.", "-/", "",
            "open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch"]
    if c.immutables:
        out += ["open Reasoning.VyperImmutables"]
    out += ["", f"namespace {c.namespace}", "", "set_option maxRecDepth 2000000", ""]
    out += [f"theorem {p}NoDispatch {{σ σ₀ A I}} {{g : UInt256}}{binders}",
            f"    (hcode : I.code = {code}) (hsize : I.calldata.size < UInt256.size)",
            f"    (hnm : ∀ i, i < {n} → ({p}SelBytes i == I.calldata.extract 0 4) = false) :",
            f"    runtimeRefinementFor config contract σ σ₀ g A I{imm} := by"]
    if c.has_fallback or c.has_receive:
        out += ["  sorry  -- TODO: refine the `__default__` execution for unmatched calldata", ""]
    else:
        if c.immutables:
            out += [f"  have hcode' : I.code = {p}Bytecode ++ immutableLayout.suffixWords (wordsOf imms) := by",
                    "    rw [hcode, deployed_of_fit hfit]"]
        h = "hcode'" if c.immutables else "hcode"
        out += ["  by_cases hsz : 4 ≤ I.calldata.size",
                f"  · exact ({p}X_noMatch (g := Sat256.ofUInt256 g) {h} hsz hsize hnm)",
                f"      |>.reEquivNoDispatch {h} ({p}Dispatch_none_nomatch hnm)",
                "  · have hshort : I.calldata.size < 4 := by omega",
                f"    exact ({p}X_short (g := Sat256.ofUInt256 g) {h} hshort)",
                f"      |>.reEquivNoDispatch {h} ({p}Dispatch_none_short hshort)", ""]
    hyps = " ".join(f"(h{t.index} : ¬ selIs I ({p}SelBytes {t.index}))" for t in c.transitions)
    out += [f"theorem {p}NoSelectorMatches {{I : ExecutionEnv}}", f"    {hyps} :",
            f"    ∀ i, i < {n} → ({p}SelBytes i == I.calldata.extract 0 4) = false := by",
            "  intro i hi", "  interval_cases i"]
    out += [f"  · simpa [selIs] using h{t.index}" for t in c.transitions]
    out += [""]
    wf = vyper_wf(c)
    if wf:
        out += [f"/-- Runtime refinement under the storage precondition `{wf}` (`Common.lean`): Vyper returns",
                "and compares raw storage words, so the spec's typed view refines the bytecode on well-formed",
                "storage; every writer stores validated words.  No gas bound. -/",
                f"theorem {p}Correct{binders} :",
                f"    runtimeRefinementWithWF {wf} noGasBound config ({code}) contract{imm} := by",
                "  refine ⟨fun σ σ₀ g A I hcode hsize hwf _ ↦ ?_⟩"]
    else:
        out += [f"theorem {p}Correct{binders} :",
                f"    runtimeRefinement config ({code}) contract{imm} := by",
                "  refine ⟨fun σ σ₀ g A I hcode hsize ↦ ?_⟩"]
    hwf_a = " hwf" if wf else ""
    line_indent = "  "
    for t in c.transitions:
        out += [f"{line_indent}by_cases h{t.index} : selIs I ({p}SelBytes {t.index})",
                f"{line_indent.replace('·', ' ')}· exact {p}{t.cap}Body{args}{hwf_a} hcode hsize h{t.index}"]
        line_indent = line_indent.replace("·", " ") + "· "
    all_h = " ".join(f"h{t.index}" for t in c.transitions)
    out += [f"{line_indent}exact {p}NoDispatch{args} hcode hsize ({p}NoSelectorMatches {all_h})", ""]
    if wf:
        if c.immutables:
            out += [f"/-- Whole-contract refinement under `{wf}` (no gas bound). -/",
                    f"theorem {p}ContractCorrect :",
                    f"    contractRefinementWF {wf} noGasBound config {p}CreationBytecode contract :=",
                    f"  .of_runtime {p}ConstructorCorrect {p}Correct", ""]
        else:
            out += [f"/-- Whole-contract refinement under `{wf}` (no gas bound); no immutables, so the deployed",
                    "code is the constant runtime and the restricted immutables are empty. -/",
                    f"theorem {p}ContractCorrect :",
                    f"    contractRefinementWF {wf} noGasBound config {p}CreationBytecode contract :=",
                    f"  .of_runtime {p}ConstructorCorrect (fun imms _ => by",
                    "    rw [restrictImmutables_noImmutables (by rfl)]",
                    f"    exact {p}Correct)", ""]
    elif c.immutables:
        out += [f"theorem {p}ContractCorrect :",
                f"    contractRefinement config {p}CreationBytecode contract :=",
                f"  .of_runtime {p}ConstructorCorrect {p}Correct", ""]
    else:
        out += [f"theorem {p}ContractCorrect :",
                f"    contractRefinement config {p}CreationBytecode contract :=",
                f"  contractRefinement.of_constant {p}ConstructorCorrect {p}Correct", ""]
    out += [f"end {c.namespace}", ""]
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--dir", type=Path, required=True)
    parser.add_argument("--contract")
    parser.add_argument("--module")
    parser.add_argument("--namespace")
    parser.add_argument("--prefix")
    parser.add_argument("--force", action="store_true", help="overwrite existing generated files")
    parser.add_argument("--sorry-dispatch", action="store_true",
                        help="leave the dispatcher reach lemmas and dispatch facts as sorry")
    parser.add_argument("--only", action="append", default=[],
                        help="generate only these files (Spec, Common, Dispatch, Functions, Constructor, Correct)")
    parser.add_argument("--wf", metavar="NAME",
                        help="Vyper: state the runtime refinement under the storage precondition NAME "
                             "(`runtimeRefinementWithWF NAME noGasBound`); the `…Body` stubs take `(hwf : NAME σ I)` "
                             "and Common.lean declares the placeholder predicate")
    args = parser.parse_args(argv)
    c = load_contract(args.dir, args.module, args.namespace, args.prefix, args.contract)
    if args.wf:
        if c.compiler_kind != "vyper":
            parser.error("--wf is only supported for Vyper contracts")
        c.wf = args.wf
    only = set(args.only)
    want = lambda name: not only or name in only

    if c.compiler_kind == "vyper":
        if want("Spec"):
            write_file(c.directory / "Spec.lean", render_spec(c), args.force)
        if want("Common"):
            write_file(c.directory / "Common.lean", render_common_vyper(c), args.force)
        dispatch_text, vyper_arms = render_dispatch_vyper(c, args.sorry_dispatch)
        if want("Dispatch"):
            write_file(c.directory / "Dispatch.lean", dispatch_text, args.force)
        if want("Functions"):
            for t in c.transitions:
                arm = vyper_arms.get(int.from_bytes(t.selector, "big"))
                write_file(c.directory / f"{t.cap}.lean", render_function_vyper(c, t, arm), args.force)
        if want("Constructor"):
            write_file(c.directory / "Constructor.lean", render_constructor(c), args.force)
        if want("Correct"):
            write_file(c.directory / "Correct.lean", render_correct_vyper(c), args.force)
        print(f"Vyper skeleton for {c.name}: {len(c.transitions)} selectors, "
              f"immutables: {len(c.immutables)}; review storage capacities and calldata bounds in Spec.lean")
        return 0

    # dispatcher arms from the bytecode
    from evm_tools import dispatcher as recover_dispatcher
    body = rd.strip_solidity_metadata(c.runtime)
    disp = recover_dispatcher(rd.disassemble(body))
    arms = {a.selector: a.target for a in disp.arms}
    sites = None
    if c.immutables:
        build = load_json(find_build(c.directory, c.name))
        from scaffold import immutable_sites
        sites = immutable_sites(build, c.runtime)

    if want("Spec"):
        write_file(c.directory / "Spec.lean", render_spec(c), args.force)
    if want("Common"):
        write_file(c.directory / "Common.lean", render_common(c), args.force)
    dispatch_text, info = render_dispatch(c, sites, args.sorry_dispatch, arms)
    if want("Dispatch"):
        write_file(c.directory / "Dispatch.lean", dispatch_text, args.force)
    global_guard = info["global_guard"]
    if want("Functions"):
        for t in c.transitions:
            arm_pc = arms.get(int.from_bytes(t.selector, "big"))
            write_file(c.directory / f"{t.cap}.lean", render_function(c, t, global_guard, arm_pc), args.force)
    if want("Constructor"):
        write_file(c.directory / "Constructor.lean", render_constructor(c), args.force)
    if want("Correct"):
        write_file(c.directory / "Correct.lean", render_correct(c, global_guard), args.force)
    print(f"skeleton for {c.name}: {len(c.transitions)} transitions, global callvalue guard: {global_guard}, "
          f"immutables: {len(c.immutables)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
