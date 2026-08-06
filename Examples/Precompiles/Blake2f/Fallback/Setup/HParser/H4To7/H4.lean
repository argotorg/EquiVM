import Examples.Precompiles.Blake2f.Fallback.Setup.HParser.H0To3

/-!
# BLAKE2F fallback `h` parser, word 4
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validH4StoredPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨108⟩ [⟨5⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩]
      (h4StoredMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 1988 := by
  obtain ⟨k0, rd108⟩ := validH3StoredPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload196 :
      (if (⟨196⟩ : UInt256).toNat ≥ (h3StoredMem I).size
          ∨ (⟨196⟩ : UInt256) ≥ (UInt256.ofNat 38) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((h3StoredMem I).readWithPadding 196 32))) =
        h4LoadWord I := by
    unfold h4LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := h3StoredMem I) (aw := UInt256.ofNat 38) (off := (⟨196⟩ : UInt256))
      (memSize := 512) (h3StoredMem_size I hlen) (by decide) (by decide)
  have rd108' := evm_run rd108 with [
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
    add,
    raw mload 0 (h4LoadWord I) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload196
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
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup2,
    push1 ⟨5⟩,
    shl,
    dup9,
    add,
    raw mstore 0 (h4StoredMem I) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold h4StoredMem
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨108⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [h4ParsedWord, evmSwap64, GasConstants.Gverylow] using rd108'⟩

end Blake2f
