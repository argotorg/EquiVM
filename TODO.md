# Solm Semantics
- [X] Constructor calls
  + currently we don't have
- [X] Arithmetic overflow handling
  + Option 1: wrap-around arithmetic and explicit overflow checks in the spec
  + Option 2: parameterize with the checked arith semantics of the language
  + [CURRENT] Option 3: unbounded arith, explicit inRange checks, and truncation to bounded arith when storing to storage
- [X] Add low level call in Solm 
- [ ] Study locals (esp. arrays, mappings and structs) and how to model them in Solm
- [ ] Dynamic data (arrays and strings)
 
- [ ] Out of gas
  + currently we treat OOG as equivalent to any spec
  + nonterminting EVM programs are currently equivalent to any spec [OK]

- When writing spec, the reads/writes of mappings (and likely arrays too) should happen in the 
  order they appear in the bytecode. Otherwise, we may need ta add keccak axioms.

- Optimizations on vs off

- Maybe Solidity example with inline assembly

- StorageRef 
  + probably rename with something else, since it is used for locals too. 

- We need to remove the huge eqDec definitions somewhere else so our syntax/semantics files remain readable.

- What we do not have (and may be fine for now)
  + 
  + no delete for memory arrays


- Discuss legacy Solidity issues that came up. 

- Solidity out-of-scope
  + Checked arithmetic (we have unbounded arithmetic with explicit inRange checks)
  + Events
  + Multiple returns 
  + Inheritance and interfaces
  + Memory references
  + Transient storage
  + Revert reasons 
  + memory references
  + fixed-point decimals
  + function pointers
  + Solm's parameter types carry no memory/calldata marker

- Still TODOs
  + string/bytes handling
  + delete for memory arrays
  + StorageRef is not a good name as it is used for locals too.


- When a contract inherits other contracts, that we have already proved correct,
  can we reuse the proofs? 





- gasleft()/tx.gasprice 

- INVALID

- flat multi-value return encoding → returnType : List ABIType

- Dynamic tuple return:

The ABI rule. A function's return data is encoded as if the output list were the argument list of a top-level tuple: encode((T1, T2, …, Tn)). Heads for all outputs come first (static values inline, dynamic values as offset words), tails after. The crucial point: there is no extra nesting level around the outputs. function f() returns (int56[] memory, uint160[] memory) produces:


head:  offset₁ (0x40)   offset₂
tail:  len₁, data₁...,  len₂, data₂...
What the model does. returnType : Option ABIType forces N outputs to be represented as one value of type .tuple [T1, …, Tn]. Encoding goes through encodeReturnValue? ty v = encodeABIValues? [ty] [v] (Encode.lean:163-164) — i.e. a top-level tuple with one member, which is itself your tuple. encodeABIValuesFrom? then asks isDynamicABIType (.tuple …): if any member is dynamic, the whole tuple is dynamic, so it emits a leading offset word 0x20 and shifts every inner offset by 32 (Encode.lean:145-152). Result: one spurious 32-byte prefix and wrong inner offsets versus what solc returns. returnEquiv.returned compares byte-for-byte → unsatisfiable for every successful call.

Why nobody noticed until now. Two coincidences hid it:

A single return value is genuinely a 1-tuple at top level, so encodeABIValues? [ty] [v] is exactly right — including single dynamic values (WETH9's name() string, getOwners()'s address[], which do get a leading 0x20 on-chain too). Those all check out.
A static tuple's members encode inline in the head with no offset word, so "wrapped as one tuple" and "flat outputs" produce identical bytes. All multi-returns in Examples/ and most in these benchmarks (slot0(), positions(), ticks(), burn, swap, mint) are all-static — fine as-is.
It breaks exactly when N > 1 outputs AND at least one is dynamic: Safe's getModulesPaginated → (address[], address) (Spec.lean:226) and Uniswap's observe → (int56[], uint160[]) (Spec.lean:356).

Why you can't just "unwrap" .tuple in the encoder. A Solidity function can also return a struct, whose ABI output list is [tuple(...)] — one output that legitimately gets the offset word. If the model treated every top-level .tuple returnType as "multiple outputs, encode flat", struct returns would become inexpressible. Option ABIType simply can't distinguish "N outputs" from "1 tuple-typed output". (No current benchmark returns a dynamic struct, so a pragmatic unwrap would work today, but it bakes in the ambiguity.)

The clean fix. Make the return type a list: returnType : List ABIType (empty = void), encode with encodeABIValues? types values directly (the function already exists — encodeReturnValues? at Encode.lean:158-160 is sitting there unused for this), and have returnEquiv unpack a Value.tuple into the member values for N > 1. A struct return is then the singleton list [.tuple …], which correctly keeps its offset word. Ripple effects are contained but real: returnEquiv/returnDataEquiv in Equiv.lean, defaultAbiValue (the fallthrough-zero-return case), transitionSignature is unaffected (it's over params), the Stmt.return eval rules unchanged (specs already build Value.tuple via tupleLit), plus mechanical returnType edits in every existing spec and the corresponding proof scripts.

Also worth knowing: the same wrapped-vs-flat question exists on the decode side for abiDecode/checkedCall returns of multiple values — currently abiDecode : ABIType → … has the same single-type shape, so if a spec ever decodes a two-output external call's returndata as .tuple, it inherits the same mismatch. Same fix applies there if/when needed.

Severity check: this is not load-bearing for the hard parts of the benchmarks — both affected functions are view functions — but as long as they're in the ABI surface, the whole-contract theorem demands them, so it's a genuine blocker for the top-level statement.

- Immutables

Parameterized statement (the principled one). Add a trusted patchRuntime : ByteArray → List (Nat × EVM.Word) → ByteArray and the offset table — solc emits exactly this as immutableReferences in its standard-JSON output, so the table is a compiler artifact, not something you reverse-engineer. Then:

Runtime: ∀ vals, runtimeEquivalence!?! cfg (patchRuntime template (offsets vals)) (poolSpec vals) — one proof, universally quantified over instantiations. The proof works exactly like today's, except symbolic PUSH32 operands where the template had zeros.
Constructor: generalize ctorResultEquiv's o = runtimeCode to o = patchRuntime template (offsets (valsOf env solmState)), where the expected values are derived from the same things the spec constructor computed (the parameters() return, env .this). This is a change to the equivalence-statement layer only — Solm syntax and semantics don't move.



- The wordToElem sign-extension bug

This one isn't a missing feature — it's a bug in the trusted storage-load semantics, the same class as the storageLocStore endianness bug you found via the Caller proof.

What solc does. A packed signed field (say int24 slot0.tick at byte offset 20 of slot 0) is stored as its low N bytes in two's complement. On load, solc shifts/masks the field out and applies SIGNEXTEND at the field's width, so stored bytes 0xFFFFFF come back as −1.

What the model does. storageLocLoad (Storage.lean:69-90) extracts exactly the field's loc.size bytes from the slot and rebuilds a word from them — so the word's upper bytes are always zero. Then wordToElem dispatches on the declared type, and for signed ints does:


| .int (.sint _) => .int (EVM.signed w)
(Value.lean:229) — note the _: the declared bit width is ignored, and EVM.signed (EVM/Types.lean:66-71) tests the 256-bit sign bit. Since the extracted word is < 2^(8·size), that sign bit is never set for any packed field narrower than a full slot. So every negative packed signed value loads as a large positive: int24 −1 → +16777215, int128 −1 → +2¹²⁸−1.

Why it's asymmetric (and therefore doesn't round-trip). The store direction is correct: wordOfInt reduces mod 2²⁵⁶ giving full-width two's complement, and the packer keeps the low size bytes — 0xFFFFFF for int24 −1, matching solc. So spec-store then spec-load of −1 yields +16777215. The bug is confined to the load.

Boundary cases that still work, so you know the blast radius precisely:

Full-slot int256: the extracted word is the whole slot, width = 256, EVM.signed is exactly right.
All unsigned fields, addresses, bools, bytesN: unaffected.
Non-negative signed values: unaffected (both interpretations agree).
How it manifests in the benchmark. UniswapV3 reads packed signed fields on essentially every path: slot0.tick (int24), ticks[t].liquidityNet (int128), tickCumulativeOutside/observations[i].tickCumulative (int56). Two failure shapes:

In arithmetic/comparisons: the bytecode SIGNEXTENDs and does SLT; the spec computes with the bogus positive — results diverge, equivalence unprovable on any state with a negative tick (half the tick range).
Even the plain slot0()/ticks() getters fail loudly: encodeABIWord? range-checks signed values (Encode.lean:44-52), and +16777215 is outside int24's [−2²³, 2²³), so encoding returns none and returnEquiv has no witness at all.
One consolation: because the layout code is trusted, this can never prove a false equivalence — it makes true equivalences unprovable. But it would silently poison Proofs/-style theorems about specs (you'd be proving invariants of the wrong load semantics), which is the more insidious direction.

The fix. The width is already sitting in the ignored pattern: .int (.sint bits). Sign-extend at the declared width inside wordToElem:

| .int (.sint bits) =>
    let m := w.toNat % 2 ^ bits.width      -- however IntType exposes it
    .int (if m < 2 ^ (bits.width - 1) then (m : Int) else (m : Int) - 2 ^ bits.width)


- Integer bitwise ops

Add int cases to evalBinaryOp? (small model change, my recommendation). For .int x, .int y with 0 ≤ x, y < 2²⁵⁶: Nat.land/lor/xor on the Nats, and x <<< k as x * 2^k % 2^256, >>> as division; out-of-range or negative operands → .error .typeError (specs on signed values must go through an explicit two's-complement re-encode first, which keeps the semantics honest rather than guessing a signed-bitwise convention). This keeps specs looking like the source. On the proof side it's actually cheaper than route 1: the spec op and the EVM op are now the same function of the same word, so the per-site lemma disappears.

Do the bytesN → int cast regardless of the route — Safe needs it for uint256(r) in signature splitting, and it's a one-arm addition (fixedBytesToNat? already exists).


- The bytes/string header-validation mismatch

So the fix, stated in the terms you've been pushing me toward:

WETH9's own Spec.lean defines its own readValue?/writeValue?/clearValue? functions — hand-written, like the rest of its layout — implementing the 0.5.16 behavior I verified from the disassembly:

len := if header even then (header &&& 0xFF) / 2 else header / 2 — total, never reverts;
short/long form chosen by len < 32;
read = first len bytes of the slot word (short) or of the keccak(slot) data words (long);
write = header word + data words, clearing ⌈oldLen/32⌉ words computed with the same total decode.
That's it. No change to Solm/, no change to SolidityLayout.lean, no mode knob, no precondition — one contract's layout record carries its own compiler-faithful string semantics, which is exactly what the per-contract layout design is for. The trusted surface is those ~30 lines in WETH9's spec, reviewed against the disassembly (the read side I've verified; the write/clear side still deserves the creation.hex check I flagged).

Marking this one resolved: "WETH9 strings: hand-written per-contract layout hooks with total 0.5.16 header semantics."


- EXTCODECOPY — Safe's EIP-7702 probe


The fix — one Expr, exactly the extCodeSize pattern:


| extCodePrefix : Expr /- address -/ -> Nat /- n bytes -/ -> Expr
with the eval rule reading the same source the opcode reads:


| .extCodePrefix e n => do
    match <- evalExpr? cfg solm evm e with
    | .address a =>
        let code := (evm.accountMap.find? a).elim ByteArray.empty (·.code)
        pure (.bytes (padRightZeros (code.extract 0 n) n))   -- EXTCODECOPY zero-pads past the end
    | _ => .error .typeError
The zero-padding is the one semantic detail to get right: EXTCODECOPY pads reads beyond the code size with zero bytes, so an empty/short-code account yields 0x000000, which correctly fails the 0xef0100 comparison. The spec then writes the guard as a comparison against a 3-byte bytesLit. (A more general extCodeSlice addr offset n costs the same to add; offset 0 is all Safe needs.)

Total cost: the Expr constructor + eval case + DecidableEq arm + exprEvalSize case, and — when the Safe proof actually reaches this branch — one opcode-bridge lemma in the Reasoning framework connecting it to EXTCODECOPY, the same shape extCodeSize/EXTCODESIZE already has. No relation change, no config change.

One honest caveat: I've verified the Solidity source and the Solm side; I have not disassembled Safe's runtime.hex to confirm how the optimizer compiled this sequence (e.g. whether the shr(232, …)/eq survives as-is). That check belongs to whoever writes the Safe spec's guard expression, so the spec-side comparison matches the compiled predicate exactly — on the model side, extCodePrefix + eq against a fixedBytesLit/bytesLit is sufficient either way.

