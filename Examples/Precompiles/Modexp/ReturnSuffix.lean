import Examples.Precompiles.Modexp.Dispatcher

/-!
# Exact wrapper return suffix for ModExp

After the internal ModExp implementation returns a Solidity `bytes` pointer to PC 173, the
wrapper executes `return(add(result, 0x20), mload(result))`.  This file packages that suffix as a
small exact `RDxRet` theorem, independent of the algorithm that filled the bytes object.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

private theorem wrapperReturnDecodes :
    [decode runtimeBytecode ⟨173⟩, decode runtimeBytecode ⟨174⟩,
      decode runtimeBytecode ⟨176⟩, decode runtimeBytecode ⟨177⟩,
      decode runtimeBytecode ⟨178⟩, decode runtimeBytecode ⟨179⟩,
      decode runtimeBytecode ⟨180⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.DUP2, .none), some (.MLOAD, .none), some (.SWAP2, .none),
      some (.ADD, .none), some (.RETURN, .none)] := by
  native_decide

theorem wrapperReturnExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {ptr len : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlen : len ≤ 1024)
    (hptr32 : ptr + 32 < 2 ^ 64)
    (hloadActive : ptr + 32 ≤ 32 * aw.toNat)
    (hreturnActive : ptr + 32 + len ≤ 32 * aw.toNat)
    (hheader :
      (if ptr ≥ mem.size ∨ UInt256.ofNat ptr ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding ptr 32))) =
        UInt256.ofNat len)
    (houtput : mem.readWithPadding (ptr + 32) len = output)
    (htail : tail.length ≤ 1021)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨173⟩
      (UInt256.ofNat ptr :: tail) mem aw rdata acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc output
      (C + 16) := by
  have hd := wrapperReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6⟩
  have hptrWord : ptr < UInt256.size := lt_trans (by omega : ptr < 2 ^ 64) (by decide)
  have hptr32Word : ptr + 32 < UInt256.size := lt_trans hptr32 (by decide)
  have hlenWord : len < UInt256.size :=
    lt_trans (lt_of_le_of_lt hlen (by decide : 1024 < 2 ^ 64)) (by decide)
  have hMload : MachineState.M aw.toNat ptr 32 = aw.toNat := by
    apply machineM_eq_of_access
    omega
  have hMret : MachineState.M aw.toNat (ptr + 32) len = aw.toNat := by
    apply machineM_eq_of_access
    omega
  have hptrAdd :
      UInt256.ofNat ptr + (⟨32⟩ : UInt256) = UInt256.ofNat (ptr + 32) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hptrWord,
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      UInt256.toNat_ofNat_of_lt hptr32Word, Nat.mod_eq_of_lt hptr32Word]
  have rd176 := evm_run rd0 with [
    known jumpdest hd0, known push1 hd1 ⟨32⟩, known dup2 hd2]
  have rd178raw := RDx.mload 0 (UInt256.ofNat len) aw rd176 hd3
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [UInt256.toNat_ofNat_of_lt hptrWord, hMload]
      rw [u256_ofNat_toNat]
      omega)
    (by
      rw [UInt256.toNat_ofNat_of_lt hptrWord]
      exact hheader)
    (by
      rw [UInt256.toNat_ofNat_of_lt hptrWord, hMload, u256_ofNat_toNat])
    (by simp only [List.length_cons]; omega)
  have rd180raw := evm_run rd178raw with [
    known swap2 hd4, known add hd5]
  have rd180 := rd180raw.withStack (by rw [hptrAdd])
  have hret := RDx.ret 0 output rd180 hd6
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [UInt256.toNat_ofNat_of_lt hptr32Word,
        UInt256.toNat_ofNat_of_lt hlenWord, hMret]
      rw [u256_ofNat_toNat]
      omega)
    (by
      rw [UInt256.toNat_ofNat_of_lt hptr32Word,
        UInt256.toNat_ofNat_of_lt hlenWord]
      exact houtput)
    (by omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hret

end Modexp
