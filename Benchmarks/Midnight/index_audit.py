#!/usr/bin/env python3
"""Index the manually reviewed physical ranges; coverage is not a semantic proof."""
from collections import Counter
import json
from pathlib import Path
import re
import sys

directory = Path(__file__).resolve().parent
sys.path.insert(0, str(directory.parents[1] / "scripts"))
from evm_tools import code_and_blocks

notes = {
    "toMarket": "EXTCODECOPY of the ID address, closed size guards, strict Market value decode, tuple return.",
    "setConsumed": "Authorization short circuit; uint128 monotonic consumed write; event.",
    "setIsAuthorized": "Self/authorized caller short circuit; byte bool update preserving other bits; event.",
    "enableLltv": "Configurator; WAD-inclusive cap; bool byte write; event.",
    "enableLiquidationCursor": "Configurator; strict below-WAD cap; bool byte write; event.",
    "setDefaultContinuousFee": "Fee setter; 317097919 cap; uint32 packed update; event.",
    "setMarketContinuousFee": "Fee setter; cap; initialized tick-spacing guard; uint32 packed update; event.",
    "setDefaultSettlementFee": "Fee setter; index <= 6; constant cap; CBP divisibility; packed uint16 update; event.",
    "setMarketSettlementFee": "Same fee guards; initialized market; packed uint16 update selected by index; event.",
    "setMarketTickSpacing": "Tick-spacing setter; uint8 range; initialized market; packed uint8 update; event.",
    "claimSettlementFee": "Fee claimer; checked subtraction/write before event and safeTransfer.",
    "claimContinuousFee": "touchMarket; fee claimer; sequential credit/total/withdrawable uint128 decreases; event; token call.",
    "supplyCollateral": "Authorization; touchMarket; index; prior collateral; conditional oracle/bitmap/popcount; collateral update; event; transferFrom.",
    "withdrawCollateral": "Authorization; touchMarket; checked collateral decrease; conditional bitmap clear; health/lock short circuit; event; safeTransfer.",
    "repay": "Authorization; touchMarket; debt then withdrawable updates; payer default; event; optional callback; transferFrom.",
    "withdraw": "Authorization; touchMarket/updatePosition; conditional pending-fee decrease; credit/withdrawable/total updates; event; safeTransfer.",
    "take": "Offer decode/authorization; market/offer guards; ratifier; price/fees/caps; conditional accrual/gates; ordered position/market/consumed writes; event; lock; callbacks/transfers; unlock/health.",
    "liquidate": "Materialize Market before touchMarket; debt/gate; descending bitmap oracle loop; lock/health/maturity modes; collateral/bad-debt arithmetic and ordered writes; event; transfer/callback/repayment.",
    "flashLoan": "Equal array lengths; address validation while encoding event; transfer loop; magic callback; repayment loop.",
    "multicall": "Lazy nested calldata bytes with wrapping signed bounds; sequential delegatecalls; raw return-size guard; failure reverts whole call.",
    "touchMarket": "Entry Market validation and call to shared touchMarket_body; return ID.",
    "updatePosition": "Entry decode; touchMarket; shared accrual helper; uint128 triple return.",
    "updatePositionView": "Entry decode; shared view helper; uint128 triple return.",
    "settlementFee": "Shared initialized-market fee interpolation helper; uint256 return.",
    "isHealthy": "Shared debt/bitmap/oracle helper; bool return.",
    "liquidationLocked": "Shared full-word transient hash/read; normalize to bool.",
}


def selector_note(name):
    if name in notes:
        return notes[name]
    if name in {"setConfigurator", "setFeeSetter", "setFeeClaimer", "setTickSpacingSetter"}:
        return "Configurator read/guard; low-160-bit role write preserving upper bits; event."
    return "Getter: exact mapping hashes/array index checks/packed field masks; canonical ABI result; no writes."


def helper_note(name):
    if name.startswith("abi_decode") or name.startswith("read_from_calldatat"):
        return "ABI validation and value representation; canonical scalar checks and signed bounds; Model.lean/Spec.lean."
    if name.startswith("abi_encode"):
        return "Value ABI encoding for returns, events, hashing, or call payloads; no separate memory operation in spec."
    if "allocation" in name:
        return "Explicit input/return/code size guards; remaining capacity arithmetic discharged by the gas condition."
    if "array_index" in name or name.startswith("access_calldata_tail"):
        return "Value indexing, length and canonicality guards; Solidity packed-array slot/byte offset."
    if name.startswith("checked_") or name == "mod_uint256":
        return "Checked-width arithmetic and zero-divisor guards; panic payload abstracted to revert."
    mapping = {
        "fun_isHealthy": "isHealthy_body: debt first; descending bitmap; oracle; rounded collateral capacity; compare debt.",
        "fun_touchMarket": "touchMarket_body and IdLib helpers: exact hashes; first-initialization checks; ordered packed writes; CREATE2; event.",
        "fun_settlementFee": "settlementFee_body: packed fee snapshot; seven knots; checked interpolation; upper saturation.",
        "extract_returndata": "Raw call-result bytes; empty result; uint64 size guard; capacity under gas bound.",
        "fun_updatePositionView": "updatePositionView_body: packed snapshots, loss factor, conditional fee arithmetic, truncations and checked uint128 differences.",
        "fun_tGet": "One keccak of key1/address/base; full-word TLOAD; nonzero truth.",
        "fun_safeTransfer": "Code-presence guard; transfer payload; CALL; raw failure/strict bool acceptance.",
        "fun_safeTransferFrom": "Code-presence guard; transferFrom payload; CALL; raw failure/strict bool acceptance.",
        "fun_toUint128": "Explicit uint128 maximum require, then narrowing cast.",
        "fun_updatePosition": "Shared view result; credit write before market loss re-read; ordered packed writes; continuous fee credit; event.",
        "fun_maxSettlementFee": "Seven literal fee caps and bounded value indexing.",
        "fun_mulDivUp_44146": "Checked multiply, checked WAD-1 addition, divide by WAD.",
        "fun_mulDivUp": "Checked multiply; checked divisor-1; checked addition; checked divide.",
        "fun_tExchange": "Same three-word transient hash; TLOAD then TSTORE zero; previous value returned.",
        "fun_maxLif": "Checked WAD subtraction/multiply/subtraction/division; nonzero denominator.",
        "fun_wExp": "Unchecked signed/word arithmetic, recursive negative branch, signed divides, shift, and reciprocal guard.",
    }
    if name.startswith("copy_literal_to_memory"):
        return "Value bytes11 SSTORE2 constructor prefix; no memory model in spec."
    return mapping[name]


report = (directory / "Midnight.report.md").read_text()
arms = [(int(pc), signature, selector) for selector, signature, pc in re.findall(
    r"^\| \d+ \| (0x[0-9a-f]{8}) \| ([^|]+) \| (\d+) \|", report, re.M)
    if "(" in signature]
assert len(arms) == 57
regions = [{"entry": 0, "name": "dispatcher", "note":
    "Short calldata and unmatched selector revert; 57 linear comparisons; no global value guard."}]
regions += [{"entry": pc, "name": sig.split("(")[0], "signature": sig,
             "selector": sel, "note": selector_note(sig.split("(")[0])}
            for pc, sig, sel in arms]
debug = json.loads((directory / "provenance/function-debug.json").read_text())
regions += [{"entry": info["entryPoint"], "name": name, "note": helper_note(name)}
            for name, info in debug.items() if info["entryPoint"] is not None]
regions.append({"entry": 24512, "name": "unreachable INVALID", "note":
    "Executable routines terminate before this data separator; callback constant and metadata follow."})
regions.sort(key=lambda row: row["entry"])
code = bytes.fromhex((directory / "runtime.hex").read_text())
_, ins, blocks = code_and_blocks(code[:24513], keep_metadata=True)
seen = []
for i, row in enumerate(regions):
    stop = regions[i + 1]["entry"] if i + 1 < len(regions) else 24513
    row["lastByte"] = stop - 1
    owned = [b for b in blocks if row["entry"] <= b[0].pc < stop]
    row["blocks"] = [b[0].pc for b in owned]
    row["effects"] = {op: [x.pc for b in owned for x in b if x.name.upper() == op]
                      for op in ["SLOAD", "SSTORE", "TLOAD", "TSTORE", "CALL", "STATICCALL",
                                 "DELEGATECALL", "UNSUPPORTED_F5", "LOG1", "LOG2", "LOG3", "LOG4"]}
    row["effects"] = {k: v for k, v in row["effects"].items() if v}
    seen += row["blocks"]
assert sorted(seen) == [b[0].pc for b in blocks]
assert len(seen) == len(set(seen))
creation = bytes.fromhex((directory / "creation.hex").read_text())
_, _, ctor = code_and_blocks(creation[:83], keep_metadata=True)
record = {"scope": "Physical block index; not a proof or call graph.",
          "runtimeBlocksIncludingInvalid": len(blocks), "runtimeRegions": regions,
          "constructorBlocks": [{"entry": b[0].pc, "lastByte": b[-1].pc + b[-1].size - 1}
                                for b in ctor],
          "constructorNote": "0..9 nonpayable guard; 10..77 configurator packed store, Constructor event, exact runtime return; 78..81 revert; 82 INVALID.",
          "data": [{"start": 24513, "end": 24544, "kind": "callback magic"},
                   {"start": 24545, "end": 24556, "kind": "metadata"}]}
(directory / "provenance/block-audit.json").write_text(json.dumps(record, indent=2) + "\n")
lines = [f"{b[0].pc:5}-{b[-1].pc + b[-1].size - 1:5}: " + " ".join(
    x.name.upper() + (f" 0x{x.argument:x}" if x.argument is not None else "") for x in b)
    for b in blocks]
(directory / "provenance/runtime-blocks.txt").write_text("\n".join(lines) + "\n")
print(f"Indexed {len(arms)} selector arms, {len(debug) - sum(v['entryPoint'] is None for v in debug.values())} helper entries, {len(blocks)} runtime blocks, {len(ctor)} constructor blocks.")
