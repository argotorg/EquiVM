import Examples.Precompiles.Blake2f.Fallback.Setup.Init

/-!
# BLAKE2F fallback `h` parser, setup through word 0
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validRoundsLoadPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨108⟩ [⟨0⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩]
      (tArrayZeroMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 958 := by
  obtain ⟨k0, rd100⟩ := validTArrayPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload160 :
      (if (⟨160⟩ : UInt256).toNat ≥ (tArrayZeroMem I).size
          ∨ (⟨160⟩ : UInt256) ≥ (UInt256.ofNat 38) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((tArrayZeroMem I).readWithPadding 160 32))) =
        inputFirstWord I := by
    unfold inputFirstWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := tArrayZeroMem I) (aw := UInt256.ofNat 38) (off := (⟨160⟩ : UInt256))
      (memSize := 405) (tArrayZeroMem_size I hlen) (by decide) (by decide)
  have rd108 := evm_run rd100 with [
    raw jumpdest (by decide) (by evm_ov),
    swap2,
    raw mload 0 (inputFirstWord I) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload160
      (by native_decide) (by evm_ov),
    push1 ⟨224⟩,
    shr,
    swap3,
    push0 ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd108⟩

/-- First `h` parser iteration: branch into the loop body and compute the unaligned input load
address for `h[0]`.

Source note: for `i = 0`, the compiler computes `input + 0x24 + (i << 3) = 0xa4`, which is the
bytecode form of reading the eight little-endian bytes at EIP-152 offset `4`.  This theorem stops
immediately before the `MLOAD`; the byte-swap bridge is proved separately. -/
theorem validH0LoadAddressPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨558⟩ [⟨164⟩, ⟨644⟩, ⟨0⟩, ⟨1⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩]
      (tArrayZeroMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 1012 := by
  obtain ⟨k0, rd108⟩ := validRoundsLoadPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have rd558 := evm_run rd108 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨542⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨644⟩,
    push1 ⟨36⟩,
    push1 ⟨1⟩,
    swap4,
    push1 ⟨3⟩,
    shl,
    dup6,
    add,
    add ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd558⟩

/-- First `h` parser iteration: load the unaligned input word and run the bytecode's `swap64`
helper for `h[0]`.

Source note: this proves the control/data movement through the compiler-emitted byte-swap routine
at PC `542`.  The result is the bytecode-level expression `h0ParsedWord`; the later model bridge
will prove that this is the trusted `Model.readLE64 calldata 4`. -/
theorem validH0ParsedPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨644⟩ [h0ParsedWord I, ⟨0⟩, ⟨1⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩]
      (tArrayZeroMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 1131 := by
  obtain ⟨k0, rd558⟩ := validH0LoadAddressPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload164 :
      (if (⟨164⟩ : UInt256).toNat ≥ (tArrayZeroMem I).size
          ∨ (⟨164⟩ : UInt256) ≥ (UInt256.ofNat 38) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((tArrayZeroMem I).readWithPadding 164 32))) =
        h0LoadWord I := by
    unfold h0LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := tArrayZeroMem I) (aw := UInt256.ofNat 38) (off := (⟨164⟩ : UInt256))
      (memSize := 405) (tArrayZeroMem_size I hlen) (by decide) (by decide)
  have rd644 := evm_run rd558 with [
    raw mload 0 (h0LoadWord I) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload164
      (by native_decide) (by evm_ov),
    push1 ⟨192⟩,
    shr,
    push8 ⟨18374966859414961920⟩,
    push7 ⟨71777214294589695⟩,
    dup3,
    push1 ⟨8⟩,
    shr,
    and,
    swap2,
    push1 ⟨8⟩,
    shl,
    and,
    or,
    push8 ⟨18446462603027742720⟩,
    push6 ⟨281470681808895⟩,
    dup3,
    push1 ⟨16⟩,
    shr,
    and,
    swap2,
    push1 ⟨16⟩,
    shl,
    and,
    or,
    push8 ⟨18446744069414584320⟩,
    push4 ⟨4294967295⟩,
    dup3,
    push1 ⟨32⟩,
    shr,
    and,
    swap2,
    push1 ⟨32⟩,
    shl,
    and,
    or,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [h0ParsedWord, evmSwap64, GasConstants.Gverylow] using rd644⟩

/-- First `h` parser iteration: store the parsed `h[0]` word and return to the loop head.

Source note: this closes the first unrolled iteration of the `for i in [0:8]` parser loop for
`h`.  It writes `h0ParsedWord` to `h + (0 << 5) = 0x180`, increments the loop index to `1`, and
returns to PC `108`. -/
theorem validH0StoredPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨108⟩ [⟨1⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩]
      (h0StoredMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 1164 := by
  obtain ⟨k0, rd644⟩ := validH0ParsedPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have rd108 := evm_run rd644 with [
    raw jumpdest (by decide) (by evm_ov),
    dup2,
    push1 ⟨5⟩,
    shl,
    dup9,
    add,
    raw mstore 0 (h0StoredMem I) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold h0StoredMem
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨108⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd108⟩

end Blake2f
