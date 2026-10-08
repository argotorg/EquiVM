#!/usr/bin/env python3
"""Draft a Solm specification in `solidity%` surface syntax from the solc AST.

Input is the compact AST solc emits (the ``ast`` map of ``<Name>.build.json`` written by
``scaffold.py compile``, or a single ``<Name>.sol.ast.json``).  Output is a ``SpecSyntax.lean``
draft: storage, structs, constants, immutables, events, the constructor (base constructors and
state-variable initialisers inlined, in linearisation order), every external function (modifiers
inlined, public state-variable getters generated), and the internal functions they reach
(inherited and library functions included, virtual dispatch resolved to the most derived
override).

What the draft encodes mechanically:
  * solc's checked arithmetic as ``(a op b) as T`` from the static type of each operation, and
    ``unchecked`` blocks or pre-0.8 code as wrapping casts ``T(a op b)``;
  * integer bit operations with their width, ``[T]``, fixed-bytes operations unqualified;
  * ``if (c) revert …`` as ``require(!c)``, ``revert``/``assert`` as requires (payloads are not
    modelled);
  * external calls bound as ``var r = x.f{view}(args)`` (view from the callee's mutability),
    ``address.transfer``/``send`` as low-level value calls, with solc's EXTCODESIZE guard where the
    compiler version emits one;
  * calls in expression position hoisted into ``var __cN = …`` bindings before the statement.

What it cannot know goes into HOLES (inline assembly, library calls it cannot inline, ``abi.encode``,
array literals, ``new C()``, function types, …).  Each hole is a ``${hole "…"}`` splice, which fails
to elaborate until replaced; ``--comment-holes`` writes them as comments instead so the rest of the
file can be checked.  The agent's audit against the bytecode report still decides storage read
order, compiler guards, and everything the compiler optimised.

Example:
  scripts/sol2solm.py Benchmarks/Scaffolds/CometRewards --namespace Benchmarks.CompoundIII.CometRewards \
      --output Benchmarks/Scaffolds/CometRewards/SpecSyntax.draft.lean
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

LEAN_RESERVED = {
    "at", "by", "do", "end", "from", "fun", "have", "in", "let", "match", "show", "then", "with",
    "where", "to", "module", "calc", "deriving", "instance", "structure", "theorem", "def", "abbrev",
    "variable", "universe", "namespace", "open", "section", "import", "export", "private",
    "protected", "partial", "mutual", "noncomputable", "axiom", "example", "inductive", "class",
    "extends", "macro", "syntax", "elab", "notation", "infix", "prefix", "postfix", "attribute",
    "local", "scoped", "nomatch", "nofun", "unsafe", "opaque", "omit", "include", "using",
    "initialize", "set_option", "termination_by", "decreasing_by", "obtain", "exact", "intro",
    "if", "else", "while", "for", "return", "break", "continue", "try", "catch", "delete", "this",
    "fun", "Type", "Prop", "Sort", "suffices", "rfl", "sorry", "admit", "lemma", "rename",
}

CHECKED_OPS = {"+", "-", "*", "**"}
COMPARE = {"<", "<=", ">", ">=", "==", "!="}
NEGATE = {"<": ">=", "<=": ">", ">": "<=", ">=": "<", "==": "!=", "!=": "=="}
SUBDENOMINATION = {"wei": 1, "gwei": 10 ** 9, "szabo": 10 ** 12, "finney": 10 ** 15,
                   "ether": 10 ** 18, "seconds": 1, "minutes": 60, "hours": 3600, "days": 86400,
                   "weeks": 604800, "years": 31536000}
CALLDATA_LIMIT = 2 ** 255 + 4


class Hole(Exception):
    """An unsupported construct; the message says what and where."""


def version_tuple(text: str) -> tuple[int, int, int]:
    m = re.search(r"(\d+)\.(\d+)\.(\d+)", text or "")
    return (int(m.group(1)), int(m.group(2)), int(m.group(3))) if m else (0, 8, 0)


def unparen(text: str) -> str:
    """Drop one pair of outer parentheses when they enclose the whole expression."""
    if not (text.startswith("(") and text.endswith(")")):
        return text
    depth = 0
    for i, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and i != len(text) - 1:
                return text
    return text[1:-1]


def ident(name: str) -> str:
    return f"«{name}»" if name in LEAN_RESERVED else name


def walk(node: object):
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from walk(v)
    elif isinstance(node, list):
        for v in node:
            yield from walk(v)


def default_value(t: str) -> str | None:
    """The zero value of a surface type, or None for types without a literal zero."""
    if re.fullmatch(r"u?int\d+", t):
        return "0"
    if t == "bool":
        return "false"
    if t == "address":
        return "address(0)"
    if re.fullmatch(r"bytes\d+", t):
        return f"{t}(0)"
    if t in ("bytes", "string"):
        return "new bytes(0)"
    return None


@dataclass
class Stmts:
    lines: list[str] = field(default_factory=list)

    def add(self, line: str, depth: int) -> None:
        self.lines.append("  " * depth + line)


@dataclass
class FnCtx:
    node: dict | None             # FunctionDefinition (or None for synthesized bodies)
    contract: dict                # contract whose code this is (for super/virtual resolution)
    returns: list[tuple[str, str]]  # (name or "", surface type)
    unchecked: int = 0
    depth: int = 1
    tmp: int = 0
    locals: dict[str, str] = field(default_factory=dict)   # name -> surface type
    renames: dict[int, str] = field(default_factory=dict)  # declaration id -> surface name


class Translator:
    def __init__(self, units: dict[str, dict], contract: str, version: tuple[int, int, int],
                 via_ir: bool, comment_holes: bool, extcodesize: str, calldata_guard: str) -> None:
        self.units = units
        self.version = version
        self.via_ir = via_ir
        self.comment_holes = comment_holes
        self.extcodesize_mode = extcodesize
        self.calldata_guard_mode = calldata_guard
        self.nodes: dict[int, dict] = {}
        for unit in units.values():
            for node in walk(unit):
                if isinstance(node.get("id"), int) and "nodeType" in node:
                    self.nodes[node["id"]] = node
        contracts = [n for n in self.nodes.values()
                     if n.get("nodeType") == "ContractDefinition" and n.get("name") == contract]
        if not contracts:
            raise SystemExit(f"contract {contract} not found in the AST")
        self.contract = contracts[0]
        self.linear = [self.nodes[i] for i in self.contract.get("linearizedBaseContracts", [self.contract["id"]])]
        self.base_first = list(reversed(self.linear))
        self.holes: list[str] = []
        self.notes: list[str] = []
        self.external_calls: dict[str, dict] = {}
        self.fn_names: dict[int, str] = {}      # FunctionDefinition id -> surface name
        self.needed: list[dict] = []            # internal FunctionDefinitions to emit
        self.split_public: set[int] = set()     # public functions also called internally
        self.state_vars = [v for c in self.base_first for v in c["nodes"]
                           if v.get("nodeType") == "VariableDeclaration"]
        self.struct_defs = {n["id"]: n for n in self.nodes.values() if n.get("nodeType") == "StructDefinition"}
        self.enum_defs = {n["id"]: n for n in self.nodes.values() if n.get("nodeType") == "EnumDefinition"}
        self.udvt_defs = {n["id"]: n for n in self.nodes.values()
                          if n.get("nodeType") == "UserDefinedValueTypeDefinition"}
        self.all_functions = [f for c in self.linear for f in c["nodes"] if f.get("nodeType") == "FunctionDefinition"]
        self.modifier_defs = [m for c in self.linear for m in c["nodes"] if m.get("nodeType") == "ModifierDefinition"]

    # ---------------------------------------------------------------- resolution helpers

    def checked(self, ctx: FnCtx) -> bool:
        return self.version >= (0, 8, 0) and ctx.unchecked == 0

    def hole(self, what: str, src: dict | None = None) -> str:
        loc = ""
        if src and src.get("src"):
            loc = f" @{src['src'].split(':')[0]}"
        self.holes.append(what + loc)
        text = (what + loc).replace('"', "'")
        return f"-- HOLE: {text}" if self.comment_holes else f"${{hole \"{text}\"}}"

    def note(self, text: str) -> None:
        if text not in self.notes:
            self.notes.append(text)

    def signature_key(self, fn: dict) -> tuple[str, tuple[str, ...]]:
        params = fn.get("parameters", {}).get("parameters", [])
        return (fn.get("name", ""), tuple(p["typeDescriptions"]["typeString"] for p in params))

    def effective(self, fn: dict, from_contract: dict | None = None, use_super: bool = False) -> dict:
        """The most derived implementation of `fn` for this contract (virtual dispatch)."""
        key = self.signature_key(fn)
        chain = self.linear
        if use_super and from_contract is not None:
            idx = next((i for i, c in enumerate(chain) if c["id"] == from_contract["id"]), -1)
            chain = chain[idx + 1:]
        for c in chain:
            for g in c["nodes"]:
                if g.get("nodeType") == "FunctionDefinition" and self.signature_key(g) == key \
                        and g.get("implemented", True) and g.get("body") is not None:
                    return g
        return fn

    def effective_modifier(self, mod: dict) -> dict:
        for c in self.linear:
            for g in c["nodes"]:
                if g.get("nodeType") == "ModifierDefinition" and g.get("name") == mod.get("name") \
                        and g.get("body") is not None:
                    return g
        return mod

    def owner_contract(self, node_id: int) -> dict | None:
        for c in self.nodes.values():
            if c.get("nodeType") == "ContractDefinition":
                if any(n.get("id") == node_id for n in c.get("nodes", [])):
                    return c
        return None

    def surface_name(self, fn: dict) -> str:
        """Surface name for an internal/library/public function definition, mangling clashes."""
        if fn["id"] in self.fn_names:
            return self.fn_names[fn["id"]]
        base = fn.get("name") or fn.get("kind", "f")
        owner = self.owner_contract(fn["id"])
        name = base
        is_effective = self.effective(fn)["id"] == fn["id"] and owner is not None \
            and owner["id"] in {c["id"] for c in self.linear}
        if not is_effective:
            name = f"{owner['name']}_{base}" if owner else base
        # overloads: same surface name, different parameters
        if any(v == name and self.signature_key(self.nodes[k]) != self.signature_key(fn)
               for k, v in self.fn_names.items()):
            params = self.signature_key(fn)[1]
            name = name + "_" + re.sub(r"[^A-Za-z0-9]+", "_", "_".join(params)).strip("_")
        if fn["id"] in self.split_public:
            name = name + "_body"
        self.fn_names[fn["id"]] = name
        return name

    def require_internal(self, fn: dict) -> str:
        """Mark an internal function as needed in the output and return its surface name."""
        if not any(f["id"] == fn["id"] for f in self.needed):
            if fn.get("body") is None:
                raise Hole(f"call to unimplemented function {fn.get('name')}")
            self.needed.append(fn)
        return self.surface_name(fn)

    # ---------------------------------------------------------------- types

    def stype(self, type_name: dict) -> str:
        """Surface type for a TypeName node."""
        kind = type_name.get("nodeType")
        if kind == "ElementaryTypeName":
            name = type_name["name"]
            if name.startswith("address"):
                return "address"
            if name == "uint":
                return "uint256"
            if name == "int":
                return "int256"
            if name == "byte":
                return "bytes1"
            if name.startswith("fixed") or name.startswith("ufixed"):
                raise Hole(f"fixed-point type {name}")
            return name
        if kind == "UserDefinedTypeName":
            ref = self.nodes.get(type_name.get("referencedDeclaration"))
            if ref is None:
                raise Hole(f"unresolved type {type_name.get('pathNode', {}).get('name')}")
            if ref["nodeType"] == "StructDefinition":
                return ref["name"]
            if ref["nodeType"] == "EnumDefinition":
                return "uint8"
            if ref["nodeType"] == "ContractDefinition":
                return "address"
            if ref["nodeType"] == "UserDefinedValueTypeDefinition":
                return self.stype(ref["underlyingType"])
            raise Hole(f"user-defined type {ref['nodeType']}")
        if kind == "ArrayTypeName":
            base = self.stype(type_name["baseType"])
            length = type_name.get("length")
            if length is None:
                return f"{base}[]"
            value = self.const_value(length)
            return f"{base}[{value}]"
        if kind == "Mapping":
            return f"mapping({self.stype(type_name['keyType'])} => {self.stype(type_name['valueType'])})"
        if kind == "FunctionTypeName":
            raise Hole("function type")
        raise Hole(f"type node {kind}")

    def stype_of_string(self, ts: str) -> str:
        """Surface type for an expression typeString (used for arithmetic widths and ABI casts)."""
        ts = ts.strip()
        for suffix in (" storage ref", " storage pointer", " memory", " calldata", " payable", " ref"):
            if ts.endswith(suffix):
                ts = ts[:-len(suffix)].strip()
        if ts.startswith("contract ") or ts.startswith("address"):
            return "address"
        if ts.startswith("enum "):
            return "uint8"
        if ts.startswith("struct "):
            return ts.split()[1].split(".")[-1]
        if ts == "uint":
            return "uint256"
        if ts == "int":
            return "int256"
        if ts.startswith("int_const"):
            return "uint256"
        if ts.startswith("literal_string"):
            return "string"
        if ts.startswith("user-defined"):
            raise Hole(f"typeString {ts}")
        m = re.fullmatch(r"(.+?)\[(\d*)\]", ts)
        if m:
            return f"{self.stype_of_string(m.group(1))}[{m.group(2)}]"
        return ts

    def int_type(self, ts: str) -> str | None:
        t = self.stype_of_string(ts)
        return t if re.fullmatch(r"u?int\d+", t) else None

    def const_value(self, node: dict) -> int:
        ts = node.get("typeDescriptions", {}).get("typeString", "")
        m = re.fullmatch(r"int_const (-?\d+)", ts)
        if m:
            return int(m.group(1))
        if node.get("nodeType") == "Literal":
            return self.literal_int(node)
        raise Hole("non-constant array length")

    def literal_int(self, node: dict) -> int:
        text = node.get("value", "0").replace("_", "")
        if text.startswith("0x"):
            value = int(text, 16)
        elif re.fullmatch(r"\d+", text):
            value = int(text)
        else:
            m = re.fullmatch(r"(\d+)(?:\.(\d+))?[eE](\d+)", text)
            if not m:
                raise Hole(f"number literal {text}")
            whole, frac, exp = m.group(1), m.group(2) or "", int(m.group(3))
            value = int(whole + frac) * 10 ** (exp - len(frac))
        sub = node.get("subdenomination")
        if sub:
            value *= SUBDENOMINATION[sub]
        return value

    # ---------------------------------------------------------------- constants

    def constant_text(self, var: dict, ctx: FnCtx, pre: Stmts) -> str:
        """A constant's value, inlined: a number, a keccak of a literal, or its translated expression."""
        value = var.get("value")
        if value is None:
            raise Hole(f"constant {var['name']} without a value")
        ts = value.get("typeDescriptions", {}).get("typeString", "")
        m = re.fullmatch(r"int_const (-?\d+)", ts)
        if m:
            declared = self.stype(var["typeName"])
            self.note(f"constant {var['name']} = {m.group(1)} inlined")
            if re.fullmatch(r"bytes\d+", declared):
                return f"{declared}({m.group(1)})"
            return m.group(1)
        if value.get("nodeType") == "FunctionCall" and value["expression"].get("name") == "keccak256":
            arg = value["arguments"][0]
            if arg.get("nodeType") == "Literal" and arg.get("kind") == "string":
                from evm_tools import keccak256
                digest = keccak256(arg["value"].encode()).hex()
                self.note(f"constant {var['name']} = keccak256(\"{arg['value']}\") = 0x{digest} inlined")
                return f"bytes32(0x{digest})"
        inner = Stmts()
        text = self.expr(value, FnCtx(None, self.contract, []), inner)
        if inner.lines:
            raise Hole(f"constant {var['name']} with a call in its initialiser")
        self.note(f"constant {var['name']} = {text} inlined")
        return f"({text})"

    # ---------------------------------------------------------------- expressions

    def expr_Assignment(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        """An assignment used as a value (`require((z = x + y) >= x)`): hoisted, then the target."""
        out = Stmts()
        saved = ctx.depth
        self.assignment(node, ctx, out)
        ctx.depth = saved
        pre.lines.extend(out.lines)
        return self.expr(node["leftHandSide"], ctx, pre)

    def expr(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        kind = node["nodeType"]
        handler = getattr(self, f"expr_{kind}", None)
        if handler is None:
            raise Hole(f"expression {kind}")
        return handler(node, ctx, pre)

    def expr_Literal(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        kind = node.get("kind")
        if kind == "number":
            return str(self.literal_int(node))
        if kind == "bool":
            return node["value"]
        if kind == "string":
            value = node.get("value", "")
            if any(ord(ch) < 32 or ch in '"\\' for ch in value):
                raise Hole("string literal with escapes")
            return f"\"{value}\""
        if kind in ("hexString", "unicodeString"):
            raise Hole(f"{kind} literal")
        raise Hole(f"literal {kind}")

    def expr_Identifier(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        name = node["name"]
        ref = self.nodes.get(node.get("referencedDeclaration"))
        if node.get("referencedDeclaration") in ctx.renames:
            return ctx.renames[node["referencedDeclaration"]]
        if name == "this":
            return "this"
        if name == "now":
            return "block.timestamp"
        if ref is not None and ref.get("nodeType") == "VariableDeclaration" and ref.get("constant"):
            return self.constant_text(ref, ctx, pre)
        if ref is not None and ref.get("nodeType") == "ContractDefinition":
            raise Hole(f"contract name {name} used as a value")
        return ident(name)

    def expr_TupleExpression(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        comps = node.get("components", [])
        if node.get("isInlineArray"):
            raise Hole("inline array literal")
        if len(comps) == 1 and comps[0] is not None:
            inner = self.expr(comps[0], ctx, pre)
            if re.fullmatch(r"[A-Za-z_«»][A-Za-z0-9_«».]*|\d+", inner) or unparen(inner) != inner:
                return inner
            return f"({inner})"
        raise Hole("tuple expression")

    def expr_Conditional(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        c = self.expr(node["condition"], ctx, pre)
        a = self.expr(node["trueExpression"], ctx, pre)
        b = self.expr(node["falseExpression"], ctx, pre)
        return f"({c} ? {a} : {b})"

    def expr_UnaryOperation(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        op = node["operator"]
        sub = node["subExpression"]
        if op in ("++", "--"):
            raise Hole("increment in expression position")
        if op == "delete":
            raise Hole("delete in expression position")
        inner = self.expr(sub, ctx, pre)
        if op == "!":
            return f"!({inner})"
        if op == "-":
            t = self.int_type(node["typeDescriptions"]["typeString"])
            if t and self.checked(ctx):
                return f"((0 - {inner}) as {t})"
            if t:
                return f"{t}(0 - {inner})"
            return f"(-{inner})"
        if op == "~":
            t = self.int_type(node["typeDescriptions"]["typeString"])
            return f"(~[{t}] {inner})" if t else f"(~{inner})"
        raise Hole(f"unary operator {op}")

    def expr_BinaryOperation(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        op = node["operator"]
        ts = node["typeDescriptions"]["typeString"]
        m = re.fullmatch(r"int_const (-?\d+)", ts)
        if m:
            return m.group(1)
        a = self.expr(node["leftExpression"], ctx, pre)
        b = self.expr(node["rightExpression"], ctx, pre)
        if op in COMPARE:
            return f"({a} {op} {b})"
        if op in ("&&", "||"):
            return f"({a} {op} {b})"
        t = self.int_type(ts)
        left_t = self.stype_of_string(node["leftExpression"]["typeDescriptions"]["typeString"])
        if op in CHECKED_OPS and t:
            return f"(({a} {op} {b}) as {t})" if self.checked(ctx) else f"{t}({a} {op} {b})"
        if op in ("/", "%") and t:
            if t.startswith("int"):
                fn = "sdiv" if op == "/" else "srem"
                return f"{fn}({a}, {b})"
            return f"({a} {op} {b})"
        if op in ("&", "|", "^"):
            if t:
                return f"({a} {op}[{t}] {b})"
            return f"({a} {op} {b})"
        if op in ("<<", ">>"):
            lt = self.int_type(node["leftExpression"]["typeDescriptions"]["typeString"]) or t
            if lt:
                return f"({a} {op}[{lt}] {b})"
            return f"({a} {op} {b})"
        if op in CHECKED_OPS or op in ("/", "%"):
            raise Hole(f"arithmetic on non-integer type {ts}")
        raise Hole(f"binary operator {op} on {left_t}")

    def may_revert(self, node: dict) -> bool:
        for n in walk(node):
            if n.get("nodeType") == "FunctionCall":
                return True
            if n.get("nodeType") == "BinaryOperation" and n.get("operator") in ("/", "%", "**", "+", "-", "*"):
                return True
            if n.get("nodeType") == "IndexAccess":
                ts = n.get("baseExpression", {}).get("typeDescriptions", {}).get("typeString", "")
                if "[]" in ts or "bytes" in ts:
                    return True
        return False

    def src_text(self, node: dict) -> str:
        return f"src {node.get('src', '?')}"

    def expr_IndexAccess(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        if node.get("indexExpression") is None:
            raise Hole("index access without index")
        base = self.expr(node["baseExpression"], ctx, pre)
        index = self.expr(node["indexExpression"], ctx, pre)
        return f"{base}[{index}]"

    def expr_IndexRangeAccess(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        base = self.expr(node["baseExpression"], ctx, pre)
        start = self.expr(node["startExpression"], ctx, pre) if node.get("startExpression") else "0"
        if node.get("endExpression") is None:
            raise Hole("open-ended slice")
        end = self.expr(node["endExpression"], ctx, pre)
        return f"{base}[{start} : {end}]"

    def expr_MemberAccess(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        member = node["memberName"]
        base = node["expression"]
        ref = self.nodes.get(node.get("referencedDeclaration"))
        bts = base.get("typeDescriptions", {}).get("typeString", "")
        # enum member
        if ref is not None and ref.get("nodeType") == "EnumValue":
            enum = next((e for e in self.enum_defs.values() if any(m["id"] == ref["id"] for m in e["members"])), None)
            if enum:
                index = next(i for i, m in enumerate(enum["members"]) if m["id"] == ref["id"])
                return str(index)
        if base.get("nodeType") == "Identifier":
            bname = base["name"]
            if bname in ("msg", "tx", "block"):
                if member in ("gas",):
                    raise Hole("msg.gas")
                if bname == "block" and member == "difficulty":
                    return "block.prevrandao"
                return f"{bname}.{member}"
            bref = self.nodes.get(base.get("referencedDeclaration"))
            if bref is not None and bref.get("nodeType") == "ContractDefinition":
                # Library.CONST / Contract.CONST / Interface.f.selector handled by callers
                if ref is not None and ref.get("nodeType") == "VariableDeclaration" and ref.get("constant"):
                    return self.constant_text(ref, ctx, pre)
                raise Hole(f"member {bname}.{member} of a contract name")
            if bref is not None and bref.get("nodeType") == "EnumDefinition":
                raise Hole(f"enum member {bname}.{member}")
        if base.get("nodeType") == "FunctionCall" and base.get("kind") == "typeConversion" \
                and base["expression"].get("nodeType") == "ElementaryTypeNameExpression":
            # address(x).balance / address(this).balance / address(x).code
            inner = base["arguments"][0]
            if member == "balance":
                if inner.get("nodeType") == "Identifier" and inner["name"] == "this":
                    return "address(this).balance"
                return f"{self.expr(inner, ctx, pre)}.balance"
            if member in ("code", "codehash"):
                return f"{self.expr(inner, ctx, pre)}.{member}"
        if bts.startswith("type("):
            # type(T).max/min
            tname = base["arguments"][0]["typeName"]["name"] if base.get("nodeType") == "FunctionCall" \
                and base.get("kind") == "typeConversion" else None
            if base.get("nodeType") == "FunctionCall" and base["expression"].get("name") == "type":
                arg = base["arguments"][0]
                if arg.get("nodeType") == "ElementaryTypeNameExpression":
                    tname = arg["typeName"]["name"]
                    tname = {"uint": "uint256", "int": "int256"}.get(tname, tname)
                    if member in ("max", "min"):
                        return f"type({tname}).{member}"
            if member == "interfaceId" and base.get("nodeType") == "FunctionCall":
                arg = base["arguments"][0]
                iface = self.nodes.get(arg.get("referencedDeclaration"))
                if iface is not None and iface.get("nodeType") == "ContractDefinition":
                    return self.interface_id(iface)
            raise Hole(f"type(…).{member}")
        if member == "length":
            return f"{self.expr(base, ctx, pre)}.length"
        if member == "selector":
            raise Hole("`.selector` outside abi.encodeWithSelector")
        if member in ("balance", "code", "codehash"):
            return f"{self.expr(base, ctx, pre)}.{member}"
        # struct field or tuple component
        return f"{self.expr(base, ctx, pre)}.{ident(member)}"

    def interface_id(self, iface: dict) -> str:
        """EIP-165 id: XOR of the selectors of the functions the interface itself declares."""
        from evm_tools import selector
        acc = 0
        for f in iface.get("nodes", []):
            if f.get("nodeType") == "FunctionDefinition" and f.get("kind") == "function" \
                    and f.get("visibility") in ("external", "public"):
                acc ^= int.from_bytes(selector(self.canonical_signature(f)), "big")
        self.note(f"type({iface['name']}).interfaceId = 0x{acc:08x} inlined")
        return f"bytes4(0x{acc:08x})"

    def callee_function(self, node: dict) -> dict | None:
        """The FunctionDefinition a call expression targets, if any."""
        callee = node["expression"]
        if callee.get("nodeType") in ("Identifier", "MemberAccess"):
            ref = self.nodes.get(callee.get("referencedDeclaration"))
            if ref is not None and ref.get("nodeType") == "FunctionDefinition":
                return ref
        return None

    def call_args(self, node: dict, fn: dict | None) -> list[dict]:
        args = node.get("arguments", [])
        names = node.get("names") or []
        if names and fn is not None:
            params = [p["name"] for p in fn["parameters"]["parameters"]]
            ordered = [None] * len(params)
            for name, arg in zip(names, args):
                ordered[params.index(name)] = arg
            return [a for a in ordered if a is not None]
        return args

    def expr_FunctionCall(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        kind = node.get("kind")
        callee = node["expression"]
        cts = callee.get("typeDescriptions", {}).get("typeString", "")
        if kind == "typeConversion":
            return self.conversion(node, ctx, pre)
        if kind == "structConstructorCall":
            ref = self.nodes.get(callee.get("referencedDeclaration"))
            if ref is None or ref.get("nodeType") != "StructDefinition":
                raise Hole("struct constructor")
            args = node.get("arguments", [])
            names = node.get("names") or [m["name"] for m in ref["members"]]
            fields = ", ".join(f"{ident(n)}: {self.expr(a, ctx, pre)}" for n, a in zip(names, args))
            return f"{ref['name']}({{{fields}}})"
        # builtins by name
        if callee.get("nodeType") == "Identifier":
            name = callee["name"]
            args = node.get("arguments", [])
            if name == "keccak256":
                return f"keccak256({self.expr(args[0], ctx, pre)})"
            if name == "blockhash":
                return f"blockhash({self.expr(args[0], ctx, pre)})"
            if name in ("addmod", "mulmod"):
                a, b, n = (self.expr(x, ctx, pre) for x in args)
                op = "+" if name == "addmod" else "*"
                self.note(f"{name} translated as (a {op} b) % n: differs for n == 0 (EVM gives 0)")
                return f"(({a} {op} {b}) % {n})"
            if name in ("sha256", "ripemd160", "ecrecover", "selfdestruct", "gasleft"):
                raise Hole(f"builtin {name}()")
            if name == "type":
                raise Hole("type(…)")
        if callee.get("nodeType") == "MemberAccess":
            base = callee["expression"]
            member = callee["memberName"]
            if base.get("nodeType") == "Identifier" and base["name"] == "abi":
                return self.abi_builtin(member, node, ctx, pre)
            if member in ("push", "pop") and node.get("nodeType") == "FunctionCall":
                raise Hole("push/pop in expression position")
        fn = self.callee_function(node)
        if fn is not None and "external" not in cts and not (callee.get("nodeType") == "MemberAccess"
                                                             and callee["expression"].get("name") != "super"
                                                             and self.is_external_receiver(callee)):
            # internal call (direct, inherited, library, or super)
            return self.hoist_internal_call(node, fn, ctx, pre)
        if "external" in cts or ("function" in cts and callee.get("nodeType") == "MemberAccess"):
            return self.hoist_external_call(node, ctx, pre)
        raise Hole(f"call {cts}")

    def is_external_receiver(self, callee: dict) -> bool:
        base = callee["expression"]
        bts = base.get("typeDescriptions", {}).get("typeString", "")
        return bts.startswith("contract ") or bts.startswith("address")

    def conversion(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        callee = node["expression"]
        arg = node["arguments"][0]
        if callee.get("nodeType") == "ElementaryTypeNameExpression":
            tname = callee["typeName"]["name"]
            tname = {"uint": "uint256", "int": "int256", "byte": "bytes1"}.get(tname, tname)
            if tname.startswith("address"):
                if arg.get("nodeType") == "Identifier" and arg["name"] == "this":
                    return "address(this)"
                ats = arg.get("typeDescriptions", {}).get("typeString", "")
                if ats.startswith("contract ") or ats.startswith("address"):
                    return self.expr(arg, ctx, pre)   # contract/address → address: identity
                if ats.startswith("int_const"):
                    return f"address({self.expr(arg, ctx, pre)})"
                return f"address({self.expr(arg, ctx, pre)})"
            if tname == "payable":
                return self.expr(arg, ctx, pre)
            if tname in ("bytes", "string"):
                ats = arg.get("typeDescriptions", {}).get("typeString", "")
                if ats.startswith(("bytes ", "string ", "literal_string", "bytes", "string")) and not re.match(r"bytes\d", ats):
                    return self.expr(arg, ctx, pre)   # bytes(s) / string(b): the same byte string
                raise Hole(f"conversion to {tname} from {ats}")
            if re.fullmatch(r"bytes\d+", tname) and arg.get("nodeType") == "Literal" and arg.get("kind") == "number":
                return f"{tname}({self.literal_int(arg)})"
            ats = arg.get("typeDescriptions", {}).get("typeString", "")
            if ats.startswith("bytes memory") or ats.startswith("bytes calldata") or ats.startswith("bytes storage"):
                self.note(f"cast from dynamic bytes to {tname} is not a Solm cast; check — {self.src_text(node)}")
            return f"{tname}({self.expr(arg, ctx, pre)})"
        ref = self.nodes.get(callee.get("referencedDeclaration"))
        cts = callee.get("typeDescriptions", {}).get("typeString", "")
        if ref is None:
            if cts.startswith("type(contract ") or cts.startswith("type(address"):
                return self.expr(arg, ctx, pre)   # IFoo(addr) → addr
            if cts.startswith("type(enum "):
                return f"uint8({self.expr(arg, ctx, pre)})"
        if ref is not None and ref.get("nodeType") == "ContractDefinition":
            return self.expr(arg, ctx, pre)       # IFoo(addr) → addr
        if ref is not None and ref.get("nodeType") == "EnumDefinition":
            return f"uint8({self.expr(arg, ctx, pre)})"
        if ref is not None and ref.get("nodeType") == "UserDefinedValueTypeDefinition":
            return self.expr(arg, ctx, pre)
        if callee.get("nodeType") == "MemberAccess" and callee.get("memberName") in ("wrap", "unwrap"):
            return self.expr(arg, ctx, pre)
        raise Hole("type conversion")

    def abi_builtin(self, member: str, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        args = node.get("arguments", [])
        if member == "encodePacked":
            parts = []
            for a in args:
                t = self.stype_of_string(a["typeDescriptions"]["typeString"])
                if t in ("string", "bytes") or re.fullmatch(r"u?int\d+|address|bool|bytes\d+", t):
                    parts.append(f"{t}({self.expr(a, ctx, pre)})")
                else:
                    raise Hole(f"abi.encodePacked argument of type {t}")
            return f"abi.encodePacked({', '.join(parts)})"
        if member == "encodeWithSelector":
            sel = args[0]
            if sel.get("nodeType") == "MemberAccess" and sel.get("memberName") == "selector":
                fname = sel["expression"].get("memberName") or sel["expression"].get("name")
                if fname:
                    rest = ", ".join(self.expr(a, ctx, pre) for a in args[1:])
                    return f"abi.encodeWithSelector({fname}{', ' if rest else ''}{rest})"
            raise Hole("abi.encodeWithSelector with a non-`.selector` selector")
        if member == "decode":
            data = self.expr(args[0], ctx, pre)
            types = args[1].get("components", [])
            if len(types) == 1 and types[0].get("nodeType") == "ElementaryTypeNameExpression":
                return f"abi.decode({data}, ({types[0]['typeName']['name']}))"
            raise Hole("abi.decode with a non-elementary or multiple types")
        raise Hole(f"abi.{member}")

    def hoist_internal_call(self, node: dict, fn: dict, ctx: FnCtx, pre: Stmts) -> str:
        callee = node["expression"]
        use_super = callee.get("nodeType") == "MemberAccess" and callee["expression"].get("name") == "super"
        target = self.effective(fn, ctx.contract, use_super)
        if target.get("visibility") in ("public", "external") and fn.get("kind") == "function":
            self.split_public.add(target["id"])
            if target["id"] in self.fn_names:
                del self.fn_names[target["id"]]
        name = self.require_internal(target)
        args = [self.expr(a, ctx, pre) for a in self.call_args(node, target)]
        tmp = f"__c{ctx.tmp}"
        ctx.tmp += 1
        pre.add(f"var {tmp} = {name}({', '.join(args)});", ctx.depth)
        rets = target.get("returnParameters", {}).get("parameters", [])
        if not rets:
            return tmp   # void: the binder holds unit; callers in statement position ignore it
        return tmp

    def hoist_external_call(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        callee = node["expression"]
        options: dict[str, str] = {}
        while callee.get("nodeType") == "FunctionCallOptions":
            for name, opt in zip(callee.get("names", []), callee.get("options", [])):
                options[name] = self.expr(opt, ctx, pre)
            callee = callee["expression"]
        if callee.get("nodeType") != "MemberAccess":
            raise Hole("external call without a receiver")
        member = callee["memberName"]
        recv_node = callee["expression"]
        cts = callee.get("typeDescriptions", {}).get("typeString", "")
        is_view = " view " in cts + " " or " pure " in cts + " "
        rts = recv_node.get("typeDescriptions", {}).get("typeString", "")
        if member in ("call", "staticcall", "delegatecall") or \
                (member in ("transfer", "send") and rts.startswith("address")):
            raise Hole(f"low-level {member} in expression position")
        receiver = self.expr(recv_node, ctx, pre)
        if recv_node.get("nodeType") == "Identifier" and recv_node["name"] == "this":
            receiver = "this"
        fn = self.callee_function(node)
        args = [self.expr(a, ctx, pre) for a in self.call_args(node, fn)]
        opts = []
        if "value" in options:
            opts.append(f"value: {options['value']}")
        if "gas" in options:
            self.note(f"call option gas dropped — {self.src_text(node)}")
        if is_view:
            opts.append("view")
        opt_text = f"{{{', '.join(opts)}}}" if opts else ""
        _, ret_types, _ = self.parse_function_type(cts)
        self.record_external_call(member, fn, cts)
        if self.needs_extcodesize_guard(ret_types):
            pre.add(f"require({receiver}.code.length > 0);", ctx.depth)
        tmp = f"__c{ctx.tmp}"
        ctx.tmp += 1
        pre.add(f"var {tmp} = {receiver}.{member}{opt_text}({', '.join(args)});", ctx.depth)
        return tmp

    @staticmethod
    def parse_function_type(cts: str) -> tuple[list[str], list[str], bool]:
        """(parameter types, return types, view) from a `function (…) … returns (…)` typeString."""
        m = re.match(r"function \((.*?)\)(.*)$", cts)
        if not m:
            return [], [], False
        params = [p.strip() for p in m.group(1).split(",") if p.strip()]
        rest = m.group(2)
        view = " view" in rest or " pure" in rest
        r = re.search(r"returns \((.*)\)", rest)
        rets = [p.strip() for p in r.group(1).split(",") if p.strip()] if r else []
        return params, rets, view

    def needs_extcodesize_guard(self, rets: list[str]) -> bool:
        if self.extcodesize_mode == "none":
            return False
        if self.extcodesize_mode == "all":
            return True
        if self.version < (0, 8, 10):
            return True
        return not rets

    def record_external_call(self, name: str, fn: dict | None, cts: str) -> None:
        params, rets, view = self.parse_function_type(cts)
        try:
            params = [self.stype_of_string(p) for p in params]
            rets = [self.stype_of_string(p) for p in rets]
        except Hole:
            pass
        self.external_calls.setdefault(name, {"name": name, "params": params, "returns": rets, "view": view})

    # ---------------------------------------------------------------- statements

    def stmt(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        kind = node["nodeType"]
        handler = getattr(self, f"stmt_{kind}", None)
        try:
            if handler is None:
                raise Hole(f"statement {kind}")
            handler(node, ctx, out)
        except Hole as hole:
            out.add(self.hole(str(hole), node), ctx.depth)

    def block(self, node: dict | None, ctx: FnCtx, out: Stmts) -> None:
        if node is None:
            return
        for s in node.get("statements", []):
            self.stmt(s, ctx, out)

    def stmt_Block(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        self.block(node, ctx, out)

    def stmt_UncheckedBlock(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        ctx.unchecked += 1
        try:
            self.block(node, ctx, out)
        finally:
            ctx.unchecked -= 1

    def stmt_PlaceholderStatement(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        raise Hole("placeholder outside modifier inlining")

    def with_pre(self, ctx: FnCtx, out: Stmts, build) -> None:
        """Translate an expression that may hoist calls; emit the hoisted bindings first."""
        pre = Stmts()
        text = build(pre)
        out.lines.extend(pre.lines)
        if text is not None:
            out.add(text, ctx.depth)

    def stmt_ExpressionStatement(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        e = node["expression"]
        kind = e["nodeType"]
        if kind == "Assignment":
            self.assignment(e, ctx, out)
            return
        if kind == "UnaryOperation" and e["operator"] in ("++", "--"):
            self.increment(e, ctx, out)
            return
        if kind == "UnaryOperation" and e["operator"] == "delete":
            self.with_pre(ctx, out, lambda pre: f"delete {self.expr(e['subExpression'], ctx, pre)};")
            return
        if kind == "FunctionCall":
            self.call_statement(e, ctx, out)
            return
        if kind == "Identifier":
            return  # a bare expression statement with no effect
        raise Hole(f"expression statement {kind}")

    def call_statement(self, e: dict, ctx: FnCtx, out: Stmts) -> None:
        callee = e["expression"]
        if callee.get("nodeType") == "Identifier":
            name = callee["name"]
            args = e.get("arguments", [])
            if name == "require":
                self.with_pre(ctx, out, lambda pre: f"require({unparen(self.expr(args[0], ctx, pre))});")
                return
            if name == "assert":
                self.with_pre(ctx, out, lambda pre: f"require({unparen(self.expr(args[0], ctx, pre))});")
                return
            if name == "revert":
                out.add("require(false);", ctx.depth)
                return
            if name == "selfdestruct":
                raise Hole("selfdestruct")
        if callee.get("nodeType") == "MemberAccess":
            member = callee["memberName"]
            base = callee["expression"]
            bts = base.get("typeDescriptions", {}).get("typeString", "")
            if member == "push" and ("[]" in bts):
                args = e.get("arguments", [])
                def build(pre: Stmts) -> str:
                    target = self.expr(base, ctx, pre)
                    if args:
                        return f"{target}.push({self.expr(args[0], ctx, pre)});"
                    return f"{target}.push();"
                self.with_pre(ctx, out, build)
                return
            if member == "pop" and "[]" in bts:
                self.with_pre(ctx, out, lambda pre: f"{self.expr(base, ctx, pre)}.pop();")
                return
            if member in ("transfer", "send") and (bts.startswith("address")):
                args = e.get("arguments", [])
                def build_transfer(pre: Stmts) -> None:
                    recv = self.expr(base, ctx, pre)
                    value = self.expr(args[0], ctx, pre)
                    pre.add(f"(bool __ok{ctx.tmp}, bytes memory __data{ctx.tmp}) = {recv}.call{{value: {value}}}(new bytes(0));", ctx.depth)
                    if member == "transfer":
                        pre.add(f"require(__ok{ctx.tmp});", ctx.depth)
                    ctx.tmp += 1
                    return None
                self.with_pre(ctx, out, build_transfer)
                return
            if member in ("call", "staticcall", "delegatecall"):
                self.low_level_call(e, ctx, out, binders=None)
                return
        # internal or external call whose result is unused
        if e.get("kind") == "functionCall":
            def build_call(pre: Stmts) -> None:
                self.expr(e, ctx, pre)
                return None
            self.with_pre(ctx, out, build_call)
            return
        raise Hole("call statement")

    def low_level_call(self, e: dict, ctx: FnCtx, out: Stmts, binders: list[str] | None) -> None:
        callee = e["expression"]
        options: dict[str, str] = {}
        pre = Stmts()
        while callee.get("nodeType") == "FunctionCallOptions":
            for name, opt in zip(callee.get("names", []), callee.get("options", [])):
                options[name] = self.expr(opt, ctx, pre)
            callee = callee["expression"]
        member = callee["memberName"]
        recv = self.expr(callee["expression"], ctx, pre)
        arg = e["arguments"][0]
        if arg.get("nodeType") == "Literal" and arg.get("value", "") == "":
            payload = "new bytes(0)"
        else:
            payload = self.expr(arg, ctx, pre)
        names = binders or [f"__ok{ctx.tmp}", f"__data{ctx.tmp}"]
        if binders is None:
            ctx.tmp += 1
        opt = f"{{value: {options['value']}}}" if "value" in options else ""
        if "gas" in options:
            self.note(f"call option gas dropped — {self.src_text(e)}")
        out.lines.extend(pre.lines)
        out.add(f"(bool {names[0]}, bytes memory {names[1]}) = {recv}.{member}{opt}({payload});", ctx.depth)

    def assignment(self, e: dict, ctx: FnCtx, out: Stmts) -> None:
        op = e["operator"]
        lhs = e["leftHandSide"]
        rhs = e["rightHandSide"]
        if lhs.get("nodeType") == "TupleExpression":
            self.tuple_assignment(e, ctx, out)
            return
        def build(pre: Stmts) -> str:
            target = self.expr(lhs, ctx, pre)
            value = self.expr(rhs, ctx, pre)
            if op == "=":
                return f"{target} = {unparen(value)};"
            bop = op[:-1]
            ts = e["typeDescriptions"]["typeString"]
            t = self.int_type(ts)
            if bop in CHECKED_OPS and t:
                return f"{target} = (({target} {bop} {value}) as {t});" if self.checked(ctx) \
                    else f"{target} = {t}({target} {bop} {value});"
            if bop in ("/", "%") and t:
                if t.startswith("int"):
                    return f"{target} = {'sdiv' if bop == '/' else 'srem'}({target}, {value});"
                return f"{target} = ({target} {bop} {value});"
            if bop in ("&", "|", "^", "<<", ">>"):
                return f"{target} = ({target} {bop}[{t}] {value});" if t else f"{target} = ({target} {bop} {value});"
            raise Hole(f"compound assignment {op}")
        self.with_pre(ctx, out, build)

    def tuple_assignment(self, e: dict, ctx: FnCtx, out: Stmts) -> None:
        lhs = e["leftHandSide"]
        rhs = e["rightHandSide"]
        comps = lhs.get("components", [])
        if rhs.get("nodeType") == "FunctionCall":
            callee = rhs["expression"]
            if callee.get("nodeType") == "MemberAccess" and callee["memberName"] in ("call", "staticcall", "delegatecall") \
                    or (callee.get("nodeType") == "FunctionCallOptions"):
                inner = callee
                while inner.get("nodeType") == "FunctionCallOptions":
                    inner = inner["expression"]
                if inner.get("nodeType") == "MemberAccess" and inner["memberName"] in ("call", "staticcall", "delegatecall"):
                    names = [self.expr(c, ctx, Stmts()) if c else f"__unused{i}" for i, c in enumerate(comps)]
                    if len(names) != 2:
                        raise Hole("low-level call with an unexpected number of results")
                    self.low_level_call(rhs, ctx, out, binders=names)
                    return
            def build(pre: Stmts) -> None:
                tmp = self.expr(rhs, ctx, pre)
                for i, c in enumerate(comps):
                    if c is not None:
                        pre.add(f"{self.expr(c, ctx, pre)} = {tmp}.{i};", ctx.depth)
                return None
            self.with_pre(ctx, out, build)
            return
        if rhs.get("nodeType") == "TupleExpression" and len(rhs.get("components", [])) == len(comps):
            def build_pairs(pre: Stmts) -> None:
                # evaluate every right-hand component first (swap idiom), then assign
                temps = []
                for r in rhs["components"]:
                    value = self.expr(r, ctx, pre)
                    name = f"__t{ctx.tmp}"
                    ctx.tmp += 1
                    pre.add(f"var {name} = {unparen(value)};", ctx.depth)
                    temps.append(name)
                for c, name in zip(comps, temps):
                    if c is not None:
                        pre.add(f"{self.expr(c, ctx, pre)} = {name};", ctx.depth)
                return None
            self.with_pre(ctx, out, build_pairs)
            return
        raise Hole("tuple assignment")

    def increment(self, e: dict, ctx: FnCtx, out: Stmts) -> None:
        op = "+" if e["operator"] == "++" else "-"
        t = self.int_type(e["typeDescriptions"]["typeString"]) or "uint256"
        def build(pre: Stmts) -> str:
            target = self.expr(e["subExpression"], ctx, pre)
            if self.checked(ctx):
                return f"{target} = (({target} {op} 1) as {t});"
            return f"{target} = {t}({target} {op} 1);"
        self.with_pre(ctx, out, build)

    def stmt_VariableDeclarationStatement(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        decls = node.get("declarations", [])
        init = node.get("initialValue")
        if len([d for d in decls if d]) > 1 or (len(decls) > 1):
            self.tuple_declaration(node, ctx, out)
            return
        decl = decls[0]
        if decl is None:
            raise Hole("declaration without a variable")
        name = ident(decl["name"])
        t = self.stype(decl["typeName"])
        ctx.locals[decl["name"]] = t
        loc = decl.get("storageLocation", "default")
        if init is None:
            zero = default_value(t)
            if zero is None:
                raise Hole(f"uninitialised local of type {t}")
            mem = " memory" if t in ("bytes", "string") else ""
            out.add(f"{t}{mem} {name} = {zero};", ctx.depth)
            return
        if loc == "storage":
            self.with_pre(ctx, out, lambda pre: f"{t} storage {name} = {self.expr(init, ctx, pre)};")
            return
        if t[0].isupper() and init.get("nodeType") in ("IndexAccess", "Identifier", "MemberAccess"):
            self.note(f"`{decl['name']}` copies a struct from storage in one read; check the bytecode's "
                      f"field read order — {self.src_text(node)}")
        def build(pre: Stmts) -> str:
            value = self.expr(init, ctx, pre)
            if init.get("nodeType") == "FunctionCall" and value.startswith("__c"):
                # a hoisted call: bind under the declared name instead of the temporary
                last = pre.lines[-1]
                if f"var {value} = " in last:
                    pre.lines[-1] = last.replace(f"var {value} = ", f"var {name} = ", 1)
                    return None
            mem = " memory" if loc == "memory" and t not in ("bytes", "string") and not re.fullmatch(r"u?int\d+|address|bool|bytes\d+", t) else ""
            if t in ("bytes", "string"):
                mem = " memory"
            return f"{t}{mem} {name} = {unparen(value)};"
        self.with_pre(ctx, out, build)

    def tuple_declaration(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        decls = node.get("declarations", [])
        init = node.get("initialValue")
        if init is None:
            raise Hole("tuple declaration without initialiser")
        if init.get("nodeType") == "FunctionCall":
            inner = init["expression"]
            while inner.get("nodeType") == "FunctionCallOptions":
                inner = inner["expression"]
            if inner.get("nodeType") == "MemberAccess" and inner["memberName"] in ("call", "staticcall", "delegatecall"):
                names = [ident(d["name"]) if d else f"__unused{i}" for i, d in enumerate(decls)]
                for d in decls:
                    if d:
                        ctx.locals[d["name"]] = self.stype(d["typeName"])
                self.low_level_call(init, ctx, out, binders=names)
                return
        if init.get("nodeType") == "TupleExpression" and len(init.get("components", [])) == len(decls):
            def build_pairs(pre: Stmts) -> None:
                for d, r in zip(decls, init["components"]):
                    value = self.expr(r, ctx, pre)
                    if d is not None:
                        t = self.stype(d["typeName"])
                        ctx.locals[d["name"]] = t
                        pre.add(f"{t} {ident(d['name'])} = {unparen(value)};", ctx.depth)
                return None
            self.with_pre(ctx, out, build_pairs)
            return
        def build(pre: Stmts) -> None:
            tmp = self.expr(init, ctx, pre)
            for i, d in enumerate(decls):
                if d is not None:
                    t = self.stype(d["typeName"])
                    ctx.locals[d["name"]] = t
                    pre.add(f"{t} {ident(d['name'])} = {tmp}.{i};", ctx.depth)
            return None
        self.with_pre(ctx, out, build)

    def stmt_IfStatement(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        cond = node["condition"]
        then = node["trueBody"]
        els = node.get("falseBody")
        # `if (c) revert …;` → require(!c)
        if els is None and self.is_revert(then):
            self.with_pre(ctx, out, lambda pre: f"require({unparen(self.negate(cond, ctx, pre))});")
            return
        pre = Stmts()
        c = unparen(self.expr(cond, ctx, pre))
        out.lines.extend(pre.lines)
        out.add(f"if ({c}) {{", ctx.depth)
        ctx.depth += 1
        self.stmt_or_block(then, ctx, out)
        ctx.depth -= 1
        if els is not None:
            if els.get("nodeType") == "IfStatement":
                out.add("} else {", ctx.depth)
                ctx.depth += 1
                self.stmt(els, ctx, out)
                ctx.depth -= 1
                out.add("}", ctx.depth)
            else:
                out.add("} else {", ctx.depth)
                ctx.depth += 1
                self.stmt_or_block(els, ctx, out)
                ctx.depth -= 1
                out.add("}", ctx.depth)
        else:
            out.add("}", ctx.depth)

    def stmt_or_block(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        if node.get("nodeType") == "Block":
            self.block(node, ctx, out)
        else:
            self.stmt(node, ctx, out)

    def is_revert(self, node: dict) -> bool:
        stmts = node.get("statements", [node]) if node.get("nodeType") == "Block" else [node]
        if len(stmts) != 1:
            return False
        s = stmts[0]
        if s.get("nodeType") == "RevertStatement":
            return True
        if s.get("nodeType") == "ExpressionStatement":
            e = s["expression"]
            return e.get("nodeType") == "FunctionCall" and e["expression"].get("nodeType") == "Identifier" \
                and e["expression"]["name"] == "revert"
        return False

    def negate(self, cond: dict, ctx: FnCtx, pre: Stmts) -> str:
        if cond.get("nodeType") == "UnaryOperation" and cond["operator"] == "!":
            return self.expr(cond["subExpression"], ctx, pre)
        if cond.get("nodeType") == "BinaryOperation" and cond["operator"] in NEGATE:
            a = self.expr(cond["leftExpression"], ctx, pre)
            b = self.expr(cond["rightExpression"], ctx, pre)
            return f"{a} {NEGATE[cond['operator']]} {b}"
        if cond.get("nodeType") == "FunctionCall":
            return f"!{self.expr(cond, ctx, pre)}"
        if cond.get("nodeType") == "TupleExpression" and len(cond.get("components", [])) == 1:
            return self.negate(cond["components"][0], ctx, pre)
        return f"!({self.expr(cond, ctx, pre)})"

    def stmt_WhileStatement(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        pre = Stmts()
        c = unparen(self.expr(node["condition"], ctx, pre))
        if pre.lines:
            raise Hole("while condition with a call")
        out.add(f"while ({c}) {{", ctx.depth)
        ctx.depth += 1
        self.stmt_or_block(node["body"], ctx, out)
        ctx.depth -= 1
        out.add("}", ctx.depth)

    def stmt_DoWhileStatement(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        self.stmt_or_block(node["body"], ctx, out)
        self.stmt_WhileStatement(node, ctx, out)

    def stmt_ForStatement(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        init = node.get("initializationExpression")
        cond = node.get("condition")
        post = node.get("loopExpression")
        init_out = Stmts()
        if init is not None:
            self.stmt(init, ctx, init_out)
        pre = Stmts()
        c = unparen(self.expr(cond, ctx, pre)) if cond is not None else "true"
        if pre.lines:
            raise Hole("for condition with a call")
        post_text = ""
        if post is not None:
            post_out = Stmts()
            self.stmt(post, ctx, post_out)
            if len(post_out.lines) != 1:
                raise Hole("for loop update with several statements")
            post_text = post_out.lines[0].strip().rstrip(";")
        if len(init_out.lines) == 1 and post_text:
            init_text = init_out.lines[0].strip()
            out.add(f"for ({init_text} {c}; {post_text}) {{", ctx.depth)
            ctx.depth += 1
            self.stmt_or_block(node["body"], ctx, out)
            ctx.depth -= 1
            out.add("}", ctx.depth)
            return
        # fall back to a while loop (post appended to the body; `continue` would skip it)
        out.lines.extend(init_out.lines)
        if any("continue;" in l for l in self.body_lines(node["body"], ctx)):
            self.note("for loop lowered to while with a continue in its body — check the update order")
        out.add(f"while ({c}) {{", ctx.depth)
        ctx.depth += 1
        self.stmt_or_block(node["body"], ctx, out)
        if post is not None:
            self.stmt(post, ctx, out)
        ctx.depth -= 1
        out.add("}", ctx.depth)

    def body_lines(self, body: dict, ctx: FnCtx) -> list[str]:
        saved = (ctx.tmp, ctx.depth, dict(ctx.locals))
        tmp = Stmts()
        holes = len(self.holes)
        notes = list(self.notes)
        self.stmt_or_block(body, ctx, tmp)
        ctx.tmp, ctx.depth, ctx.locals = saved[0], saved[1], saved[2]
        del self.holes[holes:]
        self.notes = notes
        return tmp.lines

    def stmt_Return(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        e = node.get("expression")
        if e is None:
            if ctx.returns and all(n for n, _ in ctx.returns):
                names = ", ".join(ident(n) for n, _ in ctx.returns)
                out.add(f"return {names};" if len(ctx.returns) == 1 else f"return ({names});", ctx.depth)
            else:
                out.add("return;", ctx.depth)
            return
        def build(pre: Stmts) -> str:
            if e.get("nodeType") == "TupleExpression" and not e.get("isInlineArray"):
                parts = [self.expr(c, ctx, pre) for c in e.get("components", [])]
                return f"return ({', '.join(parts)});"
            if e.get("nodeType") == "FunctionCall" and e.get("kind") == "structConstructorCall" \
                    and len(ctx.returns) == 1 and ctx.returns[0][1].startswith("("):
                parts = [self.expr(a, ctx, pre) for a in e.get("arguments", [])]
                return f"return tuple({', '.join(parts)});"
            return f"return {unparen(self.expr(e, ctx, pre))};"
        self.with_pre(ctx, out, build)

    def stmt_Break(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        out.add("break;", ctx.depth)

    def stmt_Continue(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        out.add("continue;", ctx.depth)

    def stmt_EmitStatement(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        call = node["eventCall"]
        name = call["expression"].get("name") or call["expression"].get("memberName")
        def build(pre: Stmts) -> str:
            args = ", ".join(self.expr(a, ctx, pre) for a in call.get("arguments", []))
            return f"emit {name}({args});"
        self.with_pre(ctx, out, build)

    def stmt_RevertStatement(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        out.add("require(false);", ctx.depth)

    def stmt_InlineAssembly(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        raise Hole("inline assembly block")

    def stmt_TryStatement(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        call = node["externalCall"]
        clauses = node.get("clauses", [])
        ok = clauses[0]
        catches = clauses[1:]
        pre = Stmts()
        callee = call["expression"]
        options: dict[str, str] = {}
        while callee.get("nodeType") == "FunctionCallOptions":
            for name, opt in zip(callee.get("names", []), callee.get("options", [])):
                options[name] = self.expr(opt, ctx, pre)
            callee = callee["expression"]
        if callee.get("nodeType") != "MemberAccess":
            raise Hole("try on a non-external call")
        recv = self.expr(callee["expression"], ctx, pre)
        fn = self.callee_function(call)
        args = ", ".join(self.expr(a, ctx, pre) for a in self.call_args(call, fn))
        self.record_external_call(callee["memberName"], fn, callee.get("typeDescriptions", {}).get("typeString", ""))
        params = ok.get("parameters", {}).get("parameters", []) if ok.get("parameters") else []
        ret = ident(params[0]["name"]) if params and params[0].get("name") else "__ret"
        err = "__err"
        for c in catches:
            cp = c.get("parameters", {}).get("parameters", []) if c.get("parameters") else []
            if cp and cp[0].get("name"):
                err = ident(cp[0]["name"])
        if len(catches) > 1:
            self.note("try with several catch clauses merged into one")
        opt = f"{{value: {options['value']}}}" if "value" in options else ""
        out.lines.extend(pre.lines)
        out.add(f"try {recv}.{callee['memberName']}{opt}({args}) returns ({ret}) {{", ctx.depth)
        ctx.depth += 1
        self.block(ok.get("block"), ctx, out)
        ctx.depth -= 1
        out.add(f"}} catch ({err}) {{", ctx.depth)
        ctx.depth += 1
        for c in catches:
            self.block(c.get("block"), ctx, out)
        ctx.depth -= 1
        out.add("}", ctx.depth)

    # ---------------------------------------------------------------- functions

    def params_text(self, params: list[dict]) -> str:
        parts = []
        for i, p in enumerate(params):
            name = p.get("name") or f"arg{i}"
            t = self.stype(p["typeName"])
            loc = p.get("storageLocation", "default")
            loc_text = f" {loc}" if loc in ("memory", "calldata") and (t in ("bytes", "string") or "[" in t or t[0].isupper()) else ""
            parts.append(f"{t}{loc_text} {ident(name)}")
        return ", ".join(parts)

    def returns_text(self, rets: list[dict]) -> str:
        types = []
        for p in rets:
            t = self.stype(p["typeName"])
            if t[0].isupper():   # struct → ABI tuple
                struct = next((s for s in self.struct_defs.values() if s["name"] == t), None)
                if struct is None:
                    raise Hole(f"return type {t}")
                members = [self.stype(m["typeName"]) for m in struct["members"]]
                if len(members) < 2:
                    raise Hole(f"struct {t} with fewer than two members as a return type")
                t = f"({', '.join(members)})"
            types.append(t)
        return ", ".join(types)

    def modifier_invocations(self, fn: dict) -> list[dict]:
        return [m for m in fn.get("modifiers", []) if m.get("kind", "modifierInvocation") == "modifierInvocation"
                and self.nodes.get(m["modifierName"].get("referencedDeclaration"), {}).get("nodeType") == "ModifierDefinition"]

    def base_constructor_calls(self, fn: dict | None, contract: dict) -> dict[int, list[dict]]:
        """Base constructor arguments by base contract id, from `is Base(args)` and `constructor() Base(args)`."""
        calls: dict[int, list[dict]] = {}
        for spec in contract.get("baseContracts", []):
            if spec.get("arguments") is not None:
                ref = spec["baseName"].get("referencedDeclaration")
                calls[ref] = spec["arguments"]
        if fn is not None:
            for m in fn.get("modifiers", []):
                ref = self.nodes.get(m["modifierName"].get("referencedDeclaration"))
                if ref is not None and ref.get("nodeType") == "ContractDefinition":
                    calls[ref["id"]] = m.get("arguments") or []
        return calls

    def function_body(self, fn: dict, ctx: FnCtx, out: Stmts) -> None:
        """Body with modifiers inlined (outermost first) and named returns handled."""
        rets = fn.get("returnParameters", {}).get("parameters", [])
        for p in rets:
            if p.get("name"):
                t = self.stype(p["typeName"])
                ctx.locals[p["name"]] = t
                zero = default_value(t)
                if zero is None:
                    out.add(self.hole(f"named return of type {t} needs a default", p), ctx.depth)
                else:
                    mem = " memory" if t in ("bytes", "string") else ""
                    out.add(f"{t}{mem} {ident(p['name'])} = {zero};", ctx.depth)
        mods = self.modifier_invocations(fn)
        self.inline_modifiers(mods, fn, ctx, out)
        if rets and all(p.get("name") for p in rets) and not self.ends_with_return(fn.get("body")):
            names = ", ".join(ident(p["name"]) for p in rets)
            out.add(f"return {names};" if len(rets) == 1 else f"return ({names});", ctx.depth)

    def ends_with_return(self, body: dict | None) -> bool:
        if not body:
            return False
        stmts = body.get("statements", [])
        return bool(stmts) and stmts[-1].get("nodeType") == "Return"

    def inline_modifiers(self, mods: list[dict], fn: dict, ctx: FnCtx, out: Stmts) -> None:
        if not mods:
            self.block(fn.get("body"), ctx, out)
            return
        inv = mods[0]
        mod = self.effective_modifier(self.nodes[inv["modifierName"]["referencedDeclaration"]])
        params = mod.get("parameters", {}).get("parameters", [])
        args = inv.get("arguments") or []
        pre = Stmts()
        for p, a in zip(params, args):
            t = self.stype(p["typeName"])
            # modifier parameters get a unique name: they routinely shadow the function's own
            local = f"{mod['name']}_{p['name']}"
            ctx.locals[local] = t
            ctx.renames[p["id"]] = ident(local)
            value = self.expr(a, ctx, pre)
            pre.add(f"{t} {ident(local)} = {unparen(value)};", ctx.depth)
        out.lines.extend(pre.lines)
        body = mod.get("body")
        if body is None:
            raise Hole(f"modifier {mod.get('name')} without a body")
        placeholders = sum(1 for n in walk(body) if n.get("nodeType") == "PlaceholderStatement")
        if placeholders != 1:
            self.note(f"modifier {mod.get('name')} has {placeholders} placeholders; the body is inlined at each")
        self.inline_modifier_block(body, mods[1:], fn, ctx, out)

    def inline_modifier_block(self, block: dict, rest: list[dict], fn: dict, ctx: FnCtx, out: Stmts) -> None:
        for s in block.get("statements", []):
            if s.get("nodeType") == "PlaceholderStatement":
                self.inline_modifiers(rest, fn, ctx, out)
            elif s.get("nodeType") == "Block":
                self.inline_modifier_block(s, rest, fn, ctx, out)
            elif s.get("nodeType") == "IfStatement" and any(n.get("nodeType") == "PlaceholderStatement" for n in walk(s)):
                raise Hole("modifier placeholder inside a conditional")
            else:
                self.stmt(s, ctx, out)

    def render_function(self, fn: dict, external: bool, name: str | None = None) -> list[str]:
        params = fn["parameters"]["parameters"]
        rets = fn.get("returnParameters", {}).get("parameters", [])
        fname = name or self.surface_name(fn) if not external else (name or fn["name"])
        owner = self.owner_contract(fn["id"]) or self.contract
        ctx = FnCtx(fn, owner, [(p.get("name", ""), self.stype(p["typeName"]) if not self.stype(p["typeName"])[0].isupper()
                                else self.returns_text([p])) for p in rets])
        for p in params:
            if p.get("name"):
                ctx.locals[p["name"]] = self.stype(p["typeName"])
        vis = "external" if external else "internal"
        mods = [vis]
        if fn.get("stateMutability") == "payable" and external:
            mods.append("payable")
        head = f"function {ident(fname)}({self.params_text(params)}) {' '.join(mods)}"
        try:
            ret_text = self.returns_text(rets)
        except Hole as hole:
            ret_text = ""
            self.holes.append(str(hole))
            head = f"{self.hole(str(hole), fn)}\n  " + head
        if ret_text:
            head += f" returns ({ret_text})"
        out = Stmts()
        if external and self.calldata_guard_mode == "on" or (external and self.calldata_guard_mode == "auto" and self.via_ir):
            out.add("bytes __calldata = msg.data;", 1)
            out.add(f"require(__calldata.length < {CALLDATA_LIMIT});", 1)
        if external and fn["id"] in self.split_public:
            body_name = self.surface_name(fn)
            args = ", ".join(ident(p.get("name") or f"arg{i}") for i, p in enumerate(params))
            out.add(f"var __r = {body_name}({args});", 1)
            if rets:
                out.add("return __r;", 1)
        else:
            try:
                self.function_body(fn, ctx, out)
            except Hole as hole:
                out.add(self.hole(str(hole), fn), 1)
        return [f"  {head} {{", *["  " + l for l in out.lines], "  }", ""]

    def render_getter(self, var: dict) -> list[str]:
        name = var["name"]
        t = var["typeName"]
        params: list[str] = []
        path = ident(name)
        depth = 0
        while True:
            if t["nodeType"] == "Mapping":
                params.append(f"{self.stype(t['keyType'])} arg{depth}")
                path += f"[arg{depth}]"
                t = t["valueType"]
                depth += 1
            elif t["nodeType"] == "ArrayTypeName":
                params.append(f"uint256 arg{depth}")
                path += f"[arg{depth}]"
                t = t["baseType"]
                depth += 1
            else:
                break
        ret_t = self.stype(t)
        body: list[str]
        if ret_t[0].isupper():
            struct = next((s for s in self.struct_defs.values() if s["name"] == ret_t), None)
            members = [m for m in struct["members"] if m["typeName"]["nodeType"] not in ("Mapping", "ArrayTypeName")]
            types = [self.stype(m["typeName"]) for m in members]
            ret_text = ", ".join(types)
            fields = ", ".join(f"{path}.{ident(m['name'])}" for m in members)
            body = [f"return ({fields});"] if len(members) > 1 else [f"return {fields};"]
        else:
            ret_text = ret_t
            body = [f"return {path};"]
        head = f"function {ident(name)}({', '.join(params)}) external returns ({ret_text})"
        guard = []
        if self.calldata_guard_mode == "on" or (self.calldata_guard_mode == "auto" and self.via_ir):
            guard = ["bytes __calldata = msg.data;", f"require(__calldata.length < {CALLDATA_LIMIT});"]
        return [f"  {head} {{", *[f"    {l}" for l in guard + body], "  }", ""]

    # ---------------------------------------------------------------- contract

    def external_functions(self) -> list[dict]:
        """Most-derived implementations of every public/external function, in linearisation order."""
        seen: dict[tuple, dict] = {}
        for c in self.linear:
            for f in c["nodes"]:
                if f.get("nodeType") == "FunctionDefinition" and f.get("kind") == "function" \
                        and f.get("visibility") in ("public", "external"):
                    key = self.signature_key(f)
                    if key not in seen:
                        seen[key] = self.effective(f)
        return [f for f in seen.values() if f.get("body") is not None]

    def selector_sort_key(self, sig: str) -> int:
        from evm_tools import selector
        return int.from_bytes(selector(sig), "big")

    def canonical_signature(self, fn: dict) -> str:
        from evm_tools import abi_signatures
        params = []
        for p in fn["parameters"]["parameters"]:
            params.append(self.abi_type_string(p))
        return f"{fn['name']}({','.join(params)})"

    def abi_type_string(self, p: dict) -> str:
        ts = p["typeDescriptions"]["typeString"]
        return self.abi_type_of_string(ts)

    def abi_type_of_string(self, ts: str) -> str:
        t = self.stype_of_string(ts)
        if t[0].isupper():
            struct = next((s for s in self.struct_defs.values() if s["name"] == t), None)
            if struct:
                return "(" + ",".join(self.abi_type_of_string(m["typeDescriptions"]["typeString"]) for m in struct["members"]) + ")"
        m = re.fullmatch(r"(.+?)(\[\d*\])$", t)
        if m:
            return self.abi_type_of_string(m.group(1)) + m.group(2)
        return t

    def getter_signature(self, var: dict) -> str:
        params = []
        t = var["typeName"]
        while True:
            if t["nodeType"] == "Mapping":
                params.append(self.abi_type_of_string(t["keyType"]["typeDescriptions"]["typeString"]))
                t = t["valueType"]
            elif t["nodeType"] == "ArrayTypeName":
                params.append("uint256")
                t = t["baseType"]
            else:
                break
        return f"{var['name']}({','.join(params)})"

    def render(self, namespace: str, order: str) -> str:
        name = self.contract["name"]
        items: list[str] = []
        # structs
        for c in self.base_first:
            for s in c["nodes"]:
                if s.get("nodeType") == "StructDefinition":
                    items.append(f"  struct {s['name']} {{")
                    for m in s["members"]:
                        try:
                            items.append(f"    {self.stype(m['typeName'])} {ident(m['name'])};")
                        except Hole as hole:
                            items.append("    " + self.hole(str(hole), m))
                    items += ["  }", ""]
        # storage, constants, immutables
        for v in self.state_vars:
            try:
                t = self.stype(v["typeName"])
            except Hole as hole:
                items.append("  " + self.hole(str(hole), v))
                continue
            if v.get("constant"):
                continue   # inlined at each use (see NOTES); the surface grammar has no constant item
            elif v.get("mutability") == "immutable":
                items.append(f"  {t} immutable {ident(v['name'])};")
            else:
                items.append(f"  {t} {ident(v['name'])};")
        items.append("")
        # events
        for c in self.base_first:
            for e in c["nodes"]:
                if e.get("nodeType") == "EventDefinition":
                    ps = []
                    for i, p in enumerate(e["parameters"]["parameters"]):
                        try:
                            ps.append(f"{self.stype(p['typeName'])}{' indexed' if p.get('indexed') else ''} {ident(p.get('name') or f'arg{i}')}")
                        except Hole:
                            ps.append(f"uint256 {ident(p.get('name') or f'arg{i}')}")
                    items.append(f"  event {e['name']}({', '.join(ps)});")
        if any(e.get("nodeType") == "EventDefinition" for c in self.base_first for e in c["nodes"]):
            items.append("")
        # external surface (decides which internal functions are needed)
        externals = self.external_functions()
        getters = [v for v in self.state_vars if v.get("visibility") == "public" and not v.get("constant")]
        entries: list[tuple[str, list[str]]] = []
        for v in getters:
            entries.append((self.getter_signature(v), self.render_getter(v)))
        rendered: dict[int, list[str]] = {}
        for f in externals:
            rendered[f["id"]] = self.render_function(f, external=True)
        # functions split because they are also called internally need a second pass
        for f in externals:
            if f["id"] in self.split_public:
                rendered[f["id"]] = self.render_function(f, external=True)
        for f in externals:
            entries.append((self.canonical_signature(f), rendered[f["id"]]))
        if order == "selector":
            entries.sort(key=lambda e: self.selector_sort_key(e[0]))
        # constructor
        ctor_lines = self.render_constructor()
        # internal functions (worklist may grow while rendering)
        internal_lines: list[str] = []
        done: set[int] = set()
        while True:
            pending = [f for f in self.needed if f["id"] not in done]
            if not pending:
                break
            for f in pending:
                done.add(f["id"])
                internal_lines += self.render_function(f, external=False)
        # fallback / receive
        special: list[str] = []
        for c in self.linear:
            for f in c["nodes"]:
                if f.get("nodeType") == "FunctionDefinition" and f.get("kind") in ("receive", "fallback") \
                        and f.get("body") is not None and f["kind"] not in [s.split("(")[0].strip() for s in special]:
                    special += self.render_special(f)
        header = [f"/-!", f"# {name} spec draft (generated by `scripts/sol2solm.py`)", ""]
        header.append(f"Source contract `{name}`, solc {'.'.join(str(v) for v in self.version)}"
                      f"{', via-IR' if self.via_ir else ''}; linearisation: "
                      + " → ".join(c["name"] for c in self.linear) + ".")
        header.append("Transitions are in " + ("selector order (the dispatcher order)." if order == "selector" else "source order."))
        if self.holes:
            header += ["", f"HOLES ({len(self.holes)}):"] + [f"  - {h}" for h in self.holes]
        if self.notes:
            header += ["", "NOTES:"] + [f"  - {n}" for n in self.notes]
        if self.external_calls:
            header += ["", "External calls (for the spec's `ExternalCallABI`):"]
            for call in self.external_calls.values():
                header.append(f"  - {call['name']}({', '.join(call['params'])})"
                              f"{' view' if call['view'] else ''} returns ({', '.join(call['returns'])})")
        header.append("-/")
        body = [*items, *ctor_lines, *internal_lines]
        for _, lines in entries:
            body += lines
        body += special
        text = ["import Solm.Notation", "", *header, "", "open Solm Solm.Notation", "",
                f"namespace {namespace}.Syntax", "",
                f"def contractSyntax : ContractDecl := solidity% contract {name} {{",
                *body, "}", "", f"end {namespace}.Syntax", ""]
        return "\n".join(text)

    def render_special(self, fn: dict) -> list[str]:
        kind = fn["kind"]
        ctx = FnCtx(fn, self.owner_contract(fn["id"]) or self.contract, [])
        out = Stmts()
        try:
            self.function_body(fn, ctx, out)
        except Hole as hole:
            out.add(self.hole(str(hole), fn), 1)
        mods = ["external"]
        if fn.get("stateMutability") == "payable":
            mods.append("payable")
        return [f"  {kind}() {' '.join(mods)} {{", *["  " + l for l in out.lines], "  }", ""]

    def render_constructor(self) -> list[str]:
        ctors = {c["id"]: next((f for f in c["nodes"] if f.get("nodeType") == "FunctionDefinition"
                                and f.get("kind") == "constructor"), None) for c in self.linear}
        main = ctors[self.contract["id"]]
        params = main["parameters"]["parameters"] if main else []
        ctx = FnCtx(main, self.contract, [])
        for p in params:
            if p.get("name"):
                ctx.locals[p["name"]] = self.stype(p["typeName"])
        out = Stmts()
        # base constructor arguments, resolved from the most derived contract downwards
        arg_sources: dict[int, tuple[dict, list[dict]]] = {}
        for c in self.linear:
            for base_id, args in self.base_constructor_calls(ctors[c["id"]], c).items():
                arg_sources.setdefault(base_id, (c, args))
        for c in self.base_first:
            ctor = ctors[c["id"]]
            # state-variable initialisers of this contract
            for v in c["nodes"]:
                if v.get("nodeType") == "VariableDeclaration" and v.get("value") is not None \
                        and not v.get("constant"):
                    try:
                        self.with_pre(ctx, out, lambda pre, v=v: f"{ident(v['name'])} = {self.expr(v['value'], ctx, pre)};")
                    except Hole as hole:
                        out.add(self.hole(f"initialiser of {v['name']}: {hole}", v), 1)
            if ctor is None:
                continue
            if c["id"] != self.contract["id"]:
                base_params = ctor["parameters"]["parameters"]
                source = arg_sources.get(c["id"])
                if base_params and source is None:
                    out.add(self.hole(f"base constructor {c['name']} arguments not found", ctor), 1)
                    continue
                pre = Stmts()
                try:
                    for p, a in zip(base_params, source[1] if source else []):
                        t = self.stype(p["typeName"])
                        ctx.locals[p["name"]] = t
                        pre.add(f"{t} {ident(p['name'])} = {self.expr(a, ctx, pre)};", 1)
                except Hole as hole:
                    pre.add(self.hole(str(hole), ctor), 1)
                out.lines.extend(pre.lines)
            try:
                saved = ctx.contract
                ctx.contract = c
                self.function_body(ctor, ctx, out)
                ctx.contract = saved
            except Hole as hole:
                out.add(self.hole(str(hole), ctor), 1)
        mods = ["payable"] if main and main.get("stateMutability") == "payable" else []
        head = f"  constructor({self.params_text(params)}){' ' + ' '.join(mods) if mods else ''} {{"
        if not out.lines and not params:
            return []   # implicit constructor: the macro synthesises it
        return [head, *["  " + l for l in out.lines], "  }", ""]


def load_units(directory: Path, contract: str | None) -> tuple[dict[str, dict], str, tuple[int, int, int], bool]:
    builds = sorted(directory.glob("*.build.json"))
    if builds:
        build = json.loads(builds[0].read_text(encoding="utf-8"))
        units = {p: a for p, a in build["ast"].items() if a}
        version = version_tuple(build["compiler"]["version"])
        via_ir = bool(build.get("settings", {}).get("viaIR"))
        return units, contract or build["contract"], version, via_ir
    asts = sorted(directory.glob("*.sol.ast.json"))
    if not asts:
        raise SystemExit(f"{directory}: no *.build.json or *.sol.ast.json")
    units = {}
    for path in asts:
        unit = json.loads(path.read_text(encoding="utf-8"))
        units[unit.get("absolutePath", path.name)] = unit
    if contract is None:
        names = [c["name"] for u in units.values() for c in u.get("nodes", [])
                 if c.get("nodeType") == "ContractDefinition" and c.get("contractKind") == "contract"]
        if len(names) != 1:
            raise SystemExit(f"pass --contract; found {names}")
        contract = names[0]
    pragma = next((n for u in units.values() for n in u.get("nodes", []) if n.get("nodeType") == "PragmaDirective"), None)
    version = (0, 8, 0)
    if pragma:
        literals = pragma.get("literals", [])
        m = re.search(r"(\d+)\.(\d+)\.(\d+)", "".join(literals[1:]))
        if m:
            version = (int(m.group(1)), int(m.group(2)), int(m.group(3)))
    return units, contract, version, False


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("directory", type=Path, help="contract directory with *.build.json or *.sol.ast.json")
    parser.add_argument("--contract", help="contract name (default: from the build json)")
    parser.add_argument("--namespace", help="Lean namespace (default: derived from the directory)")
    parser.add_argument("--output", "-o", type=Path, help="output file (default: stdout)")
    parser.add_argument("--order", choices=["selector", "source"], default="selector",
                        help="transition order: by selector (solc dispatcher order) or source order")
    parser.add_argument("--comment-holes", action="store_true",
                        help="write holes as comments instead of failing `${hole …}` splices")
    parser.add_argument("--extcodesize-guards", choices=["auto", "all", "none"], default="auto",
                        help="EXTCODESIZE guards before external calls (auto: by solc version)")
    parser.add_argument("--calldata-guard", choices=["auto", "on", "off"], default="auto",
                        help="via-IR calldata-size guard at every entry (auto: when compiled via-IR)")
    parser.add_argument("--solc-version", help="override the compiler version, e.g. 0.6.12")
    parser.add_argument("--via-ir", action="store_true", help="treat the artifact as via-IR output")
    parser.add_argument("--spec-json", type=Path, help="also write external-call facts as JSON")
    args = parser.parse_args(argv)
    units, contract, version, via_ir = load_units(args.directory, args.contract)
    if args.solc_version:
        version = version_tuple(args.solc_version)
    via_ir = via_ir or args.via_ir
    namespace = args.namespace or ".".join(args.directory.resolve().parts[-2:])
    t = Translator(units, contract, version, via_ir, args.comment_holes,
                   args.extcodesize_guards, "on" if args.calldata_guard == "on" else "off" if args.calldata_guard == "off" else "auto")
    text = t.render(namespace, args.order)
    if args.output:
        args.output.write_text(text, encoding="utf-8")
        print(f"{args.output}: {len(t.holes)} holes, {len(t.notes)} notes")
    else:
        sys.stdout.write(text)
    if args.spec_json:
        args.spec_json.write_text(json.dumps({"contract": contract, "externalCalls": list(t.external_calls.values()),
                                              "holes": t.holes, "notes": t.notes}, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
