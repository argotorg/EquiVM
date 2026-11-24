import Benchmarks.CurveVault.StringReturn
import Benchmarks.CurveVault.StringMalformed

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultStringOffsetMemory (mem : ByteArray) (hmem : mem.size ≤ 64) :
    ∃ front : ByteArray, front.size = 64 ∧
      (UInt256.ofNat 32).toByteArray.write 0 mem 64 32 = front ++ (UInt256.ofNat 32).toByteArray := by
  refine ⟨mem ++ ByteArray.zeroes (64 - mem.size), ?_, ?_⟩
  · rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega
  · exact toByteArray_write_eq _ _ _ hmem (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by omega)))

theorem vaultStringRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isName : Bool)
    (hs : SourceState s0 I σ evm) (hpaid : memoryPaidByGas s0)
    (hvalue : I.weiValue = ⟨0⟩) (hcd : I.calldata.size < UInt256.size)
    (hmem : mem.size ≤ 64) (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (vaultStringPc isName 6437) R mem aw rdata σ k C) :
    (∃ bytes out locals',
      ExecTransitionBody fork config contract evm ∅ (vaultStringBody isName)
        (.returned {contract := contract, locals := locals'} evm (some [.bytes bytes])) ∧
      encodeReturnValue? .string (.bytes bytes) = some out ∧ RDret fork vaultBytecode g s0 σ out) ∨
    (ExecTransitionBody fork config contract evm ∅ (vaultStringBody isName) .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let length := codeOwnerStorageWord I σ (vaultStringSlot isName)
  have hstorage : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName) = length :=
    hs.storageRead _
  have hvalueS : evm.executionEnv.weiValue = ⟨0⟩ := by rw [hs.env]; exact hvalue
  obtain ⟨front, hfront, hoff⟩ := vaultStringOffsetMemory mem hmem
  change (⟨32⟩ : UInt256).toByteArray.write 0 mem 64 32 = front ++ (UInt256.ofNat 32).toByteArray at hoff
  have hhead : (front ++ (UInt256.ofNat 32).toByteArray).size = 96 := by
    rw [ByteArray.size_append, hfront, toByteArray_size]
  by_cases hnormal : length.toNat ≤ 64
  · have hcount : (vyperStringWords length).toNat = (length.toNat + 31) / 32 + 1 := by
      rw [vyperStringWords_normal length hnormal]
      omega
    have hn : (length.toNat + 31) / 32 ≤ 2 := by omega
    obtain ⟨aw', k', C', rdEnd⟩ := vaultStringPrefix isName (by change (vyperStringWords length).toNat ≤ 3; rw [hcount]; omega) hstack h
    rw [hcount, hoff,
      vaultStringCopyMemory_header hs _ _ _ hhead hn, hstorage] at rdEnd
    have hret := vaultStringFinish isName (by omega) rdEnd
    have hdata : (vyperReadDataWords evm (vaultStringSlot isName) 0 ((length.toNat + 31) / 32)).size =
        ABI.paddedSize length.toNat := by rw [vyperReadDataWords_size]; rfl
    have hencode := vaultStringOutputNormal I front
      (vyperReadDataWords evm (vaultStringSlot isName) 0 ((length.toNat + 31) / 32)) length
      hcd hfront hnormal hdata
    have hsource := vaultStringSourceReturns (fork := fork) evm isName hvalueS (by rw [hstorage]; exact hnormal)
    simp only [vaultStringBytes, hstorage] at hsource
    exact Or.inl ⟨_, _, _, hsource, hencode, hret⟩
  · by_cases hwrap : UInt256.size - 63 ≤ length.toNat ∧ length.toNat ≤ UInt256.size - 32
    · have hzero : vyperStringWords length = ⟨0⟩ := vyperStringWords_zero length hwrap.1 hwrap.2
      have hcount : (vyperStringWords length).toNat = 0 := by rw [hzero]; rfl
      obtain ⟨aw', k', C', rdEnd⟩ := vaultStringPrefix isName (by change (vyperStringWords length).toNat ≤ 3; rw [hcount]; omega) hstack h
      rw [hcount, vaultStringCopyMemory, hoff] at rdEnd
      have hret := vaultStringFinish isName (by omega) rdEnd
      have hsource := vaultStringSourceWrapped (fork := fork) evm isName hvalueS
        (by rw [hstorage]; exact hwrap.1) (by rw [hstorage]; exact hwrap.2)
      exact Or.inl ⟨_, _, _, hsource, vaultStringOutputEmpty I front hfront, hret⟩
    · have hsource := vaultStringSourceReverts (fork := fork) evm isName hvalueS
        (by rw [hstorage]; omega) (by rw [hstorage]; exact hwrap)
      refine Or.inr ⟨hsource, ?_⟩
      by_cases htop : UInt256.size - 31 ≤ length.toNat
      · have hone : vyperStringWords length = ⟨1⟩ := vyperStringWords_top length htop
        have hcount : (vyperStringWords length).toNat = 1 := by rw [hone]; rfl
        obtain ⟨aw', k', C', rdEnd⟩ := vaultStringPrefix isName (by change (vyperStringWords length).toNat ≤ 3; rw [hcount]; omega) hstack h
        rw [hcount, hoff,
          vaultStringCopyMemory_header hs _ _ 0 hhead (by omega),
          vyperReadDataWords, ByteArray.append_empty, hstorage] at rdEnd
        have hret := vaultStringFinish isName (by omega) rdEnd
        have hlarge := vaultStringOutputTop_large I (front ++ (UInt256.ofNat 32).toByteArray) length hcd hhead htop
        exact Or.inl (rdret_outOfGas_of_large_output hpaid hlarge hret)
      · have hmiddle : length.toNat < UInt256.size - 63 := by omega
        have hlarge := vyperStringWords_oversize length (by omega) hmiddle
        exact vaultStringEntryRevert isName (by omega)
          (ne_of_eq_of_ne (ugt_one hlarge) (by decide +kernel)) h

end Benchmarks.CurveVault
