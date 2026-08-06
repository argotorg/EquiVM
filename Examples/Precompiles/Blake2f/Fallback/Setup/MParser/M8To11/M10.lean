import Examples.Precompiles.Blake2f.Fallback.Setup.MParser.M8To11.M9

/-!
# BLAKE2F fallback `m` parser, word 10
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validM10StoredPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨119⟩ [⟨11⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩]
      (m10StoredMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 4899 := by
  obtain ⟨k0, rd119⟩ := validM9StoredPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload308 :
      (if (⟨308⟩ : UInt256).toNat ≥ (m9StoredMem I).size
          ∨ (⟨308⟩ : UInt256) ≥ (UInt256.ofNat 38) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((m9StoredMem I).readWithPadding 308 32))) =
        m10LoadWord I := by
    unfold m10LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := m9StoredMem I) (aw := UInt256.ofNat 38) (off := (⟨308⟩ : UInt256))
      (memSize := 960) (m9StoredMem_size I hlen) (by decide) (by decide)
  have rd119' := evm_run rd119 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨16⟩,
    dup2,
    lt,
    push2 ⟨427⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨529⟩,
    push1 ⟨100⟩,
    push1 ⟨1⟩,
    swap4,
    push1 ⟨3⟩,
    shl,
    dup6,
    add,
    add,
    raw mload 0 (m10LoadWord I) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload308
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
    dup6,
    add,
    raw mstore 0 (m10StoredMem I) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold m10StoredMem
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨119⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [m10ParsedWord, evmSwap64, GasConstants.Gverylow] using rd119'⟩

end Blake2f
