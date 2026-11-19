import Benchmarks.Midnight.StaticCallGas

/-! Typed source calls with their caller's cumulative gas bound retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem typedStaticCallBridgeMono {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State} {pc : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {evm : EVM.State} {cfg : Config} {name : Ident} {args : List Value}
    {gasArg target inOffset inSize outOffset outSize : UInt256}
    (h : RD code I g s0 pc (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R) mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hcd : cfg.externalABI.encode? name args = some (mem.readWithPadding inOffset.toNat inSize.toNat))
    (hsmall : inSize.toNat ≤ 2 ^ 64)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (k' C' : ℕ),
      typedCallViaEVM cfg evm (AccountAddress.ofUInt256 target) name 0 args (z, evm', out) false ∧
      SourceState s0 I σ' evm' ∧ C ≤ C' ∧
      RD code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat) outOffset.toNat outSize.toNat))
        out σ' k' C' ∧
      out.size < 2 ^ 138 := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', hc, rd⟩ := staticCallDepthLimitMono h hdec hd hov
    refine ⟨{ evm with substate := (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate }, σ, false,
      ByteArray.empty, k', C', ?_, ⟨hs.world, hs.env, hs.accounts⟩, hc, rd, by decide⟩
    refine ⟨_, hcd, callViaEVM.callNotMade rfl rfl ?_⟩
    intro hn
    exact hn.2 (by rw [hs.env]; exact hd)
  · have hdlt : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := fun hv => hd (Fin.ext hv)
      omega
    obtain ⟨σ', z, out, A_in, callGas, k', C', ⟨g'', A', hΘ⟩, hc, rd, _⟩ := staticCallMono h hdec hdlt hov
    have hsize : out.size < 2 ^ 138 :=
      Theta_returnData_size_lt_2pow138_of_eq I.fork _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ
        (le_trans (Ethereum.EVM.ByteArray.readWithPadding_size_le mem inOffset.toNat inSize.toNat)
          (le_trans hsmall Ethereum.EVM.pow_two_64_le_maxReturnDataSizeByGas))
    rw [hs.accounts, ← hs.world, ← hs.env] at hΘ
    have hΘ' : (σ', g'', A', z, out) =
        Ethereum.EVM.Θ evm.executionEnv.fork evm.accountMap evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner)) evm.executionEnv.sender
          (AccountAddress.ofUInt256 target) (toExecute evm.executionEnv.fork evm.accountMap (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOffset.toNat inSize.toNat) (evm.executionEnv.depth + 1)
          evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks
          (false && evm.executionEnv.perm) := by
      rw [Bool.false_and]; exact hΘ
    have hcall := callCoincides (cfg := cfg) (name := name) (args := args) (callPerm := false)
      (by rw [hs.env]; exact hd) rfl hcd hΘ'
    exact ⟨_, σ', z, out, k', C', hcall, ⟨hs.world, hs.env, rfl⟩, hc, rd, hsize⟩


theorem machineWords_covered (words off len : Nat) (h : off + len ≤ 32 * words) :
    MachineState.M words off len = words := by
  unfold MachineState.M
  split
  · rfl
  · exact max_eq_left (by omega)

theorem staticCallMemoryFunding {credit C C' : Nat} {mem out : ByteArray}
    {aw inOffset inSize outOffset outSize : UInt256}
    (hf : MemoryFunding credit mem aw C) (hc : C ≤ C')
    (hin : inOffset.toNat + inSize.toNat ≤ 32 * aw.toNat)
    (hout : outOffset.toNat + outSize.toNat ≤ 32 * aw.toNat) :
    MemoryFunding credit
      (out.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat out.size)).toNat)
      (UInt256.ofNat (MachineState.M
        (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
        outOffset.toNat outSize.toNat)) C' := by
  rw [machineWords_covered _ _ _ hin, machineWords_covered _ _ _ hout, u256_ofNat_toNat]
  refine ⟨(hf.mono hc).paid, ?_⟩
  have hmin : (min outSize (UInt256.ofNat out.size)).toNat ≤ outSize.toNat := by
    change (if outSize ≤ UInt256.ofNat out.size then outSize else UInt256.ofNat out.size).toNat ≤ _
    split
    · exact le_rfl
    · rename_i h
      change ¬ outSize.toNat ≤ (UInt256.ofNat out.size).toNat at h
      omega
  have hs := byteArray_write_size_le out mem 0 outOffset.toNat
    (min outSize (UInt256.ofNat out.size)).toNat
  have hmem := hf.covered
  unfold MemoryCovered at hmem ⊢
  omega

end Benchmarks.Midnight
