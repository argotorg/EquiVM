# Auction correctness proof

`auctionContractCorrect` in [Correct.lean](Correct.lean) combines the constructor proof with
the runtime proof for all 20 ABI entry points. `auctionCorrect` is the runtime theorem;
`auctionConstructorCorrect` is the constructor theorem. The syntax-level specification also
checks definitionally equal to the AST specification in [SpecSyntax.lean](SpecSyntax.lean).

The bytecode was compiled with Solidity 0.8.23, optimization enabled, Shanghai instructions,
and the metadata hash disabled. The exact compiler command is recorded in Bytecode.lean.
The runtime and creation hex literals match the original scaffold. All artifacts listed in
`sources.sha256` pass their checksum checks.

## Proof layout

- [Correct.lean](Correct.lean), Dispatcher, DispatchReach, and DispatchFacts handle routing.
  Each ABI function has its own file and `BodyCore` theorem.
- [Constructor.lean](Constructor.lean) handles creation and deployment of the runtime bytes.
- [BidRoutine.lean](BidRoutine.lean) connects bid validation, refund, storage writes,
  extension, and events. Its component proofs are in the other `Bid*.lean` files.
- [CreateRoutine.lean](CreateRoutine.lean) handles minting, strict return decoding, creation,
  and the error-string catch branch.
- [SettleRoutine.lean](SettleRoutine.lean) handles settlement, noun transfer or burn,
  payment, and the settlement event.
- [PaymentRoutine.lean](PaymentRoutine.lean) handles the raw ETH call and the WETH fallback.
  [CallBridge.lean](CallBridge.lean) links source calls to the actual opaque EVM call outcome.
- [CallState.lean](CallState.lean) carries account-map equivalence across calls and writes.
  HeapMemory, SparseMemory, SnapshotMemory, and the return-data helpers carry the memory facts
  needed by subsequent bytecode operations.

## Reusable helpers

Potential library additions are marked `LIBRARY CANDIDATE` or `GENERALIZES` next to their
declarations. The main groups are:

- Symbolic memory operations and memory preservation: DynamicMemory, HeapMemory, SparseMemory,
  CopyMemory, BytesMemory, MemoryGrowth, and CallOutput.
- ABI word and return-data decoding: UIntABI, ScalarABI, CalldataHead, UIntReturnDecoder,
  ErrorReturnABI, and ErrorSourceDecode.
- Source arithmetic: RangeSource, WordSourceArithmetic, and ErrorSourceGuards.
- Shared revert encoding: ErrorStringParts and ShortError.
- Call/state correspondence: CallBridge, CallState, and the state transport helpers in
  SettleStorage.
- Two-topic event steps: Log2.

Contract-specific storage and control-flow wrappers remain beside their callers. No files in
the Reasoning library were changed.

## Validation

The final contract build completed successfully with 3652 jobs. The placeholder scan returned
no matches. All proof files are below 2000 lines, and authored proof code uses at most 100
characters per line.

The full, unabridged Lean axiom reports are saved as:

- [Runtime](axioms-runtime.txt): 3035 dependencies, including 3005 native-evaluation facts.
- [Constructor and runtime](axioms-contract.txt): 3061 dependencies, including 3031
  native-evaluation facts.
- [Constructor](axioms-constructor.txt): 29 dependencies, including 26 native-evaluation facts.

The runtime and combined theorem have the same remaining 30 dependencies: the three standard
logical axioms, 20 ABI selector facts, and seven pre-existing EVM precompile output-size
axioms. The constructor's remaining dependencies are only the three logical axioms.
The audit found no dependencies outside the permitted trusted base.
