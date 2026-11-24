import Benchmarks.CurveVault.TokenSource
import Benchmarks.CurveVault.TokenOutputMemory
import Benchmarks.CurveVault.TokenReturnEVM

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

theorem vaultTokenRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {token sender recipient amount returnPc : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 192 ≤ mem.size)
    (hmt : memLoad (UInt256.ofNat 64) mem = token)
    (hmf : memLoad (UInt256.ofNat 96) mem = sender)
    (hmr : memLoad (UInt256.ofNat 128) mem = recipient)
    (hma : memLoad (UInt256.ofNat 160) mem = amount)
    (htoken : locals.get? "token" = some (.address (AccountAddress.ofUInt256 token)))
    (hf : locals.get? "_from" = some (.int (Int.ofNat sender.toNat)))
    (ht : locals.get? "_to" = some (.int (Int.ofNat recipient.toNat)))
    (ha : locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hperm : I.perm = true) (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7556) (returnPc :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (mem' out : ByteArray) (locals' : Store)
      (aw' : UInt256) (k' C' : Nat),
      ExecFuncBody fork config {contract := contract, locals := locals} evm vaultTokenFunction.body
        (.returned {contract := contract, locals := locals'} evm' none) ∧
      SourceState s0 I σ' evm' ∧ WordMemoryRange mem mem' 352 UInt256.size ∧
      RD fork vaultBytecode I g s0 returnPc R mem' aw' out σ' k' C') ∨
    (ExecFuncBody fork config {contract := contract, locals := locals} evm vaultTokenFunction.body
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  by_cases hzero : amount = ⟨0⟩
  · have rd7680 := vaultBlocks.vault_block_7556_taken
      (by simp only [List.length_cons]; omega) (by rw [hma, hzero]; decide +kernel) (by native_decide) h
    obtain ⟨aw', k', C', rdReturn⟩ := vaultBlocks.vault_block_7680_packed (by omega) hvalid rd7680
    refine Or.inl ⟨evm, σ, mem, rdata, locals, aw', k', C', ?_, hs, WordMemoryRange.refl _ _ _, rdReturn⟩
    apply vaultTokenSourceZero
    simpa only [hzero] using ha
  have hpos : 0 < amount.toNat := by
    by_contra hn
    exact hzero (uint256_toNat_eq_zero (by omega))
  obtain ⟨aw0, k0, C0, rd7565⟩ := vaultBlocks.vault_block_7556_fallthrough_packed
    (by simp only [List.length_cons]; omega) (by rw [hma]; exact isZero_eq_zero_of_ne hzero) h
  obtain ⟨aw1, k1, C1, rd7594⟩ := vaultBlocks.vault_block_7565_packed
    (by simp only [List.length_cons]; omega) rd7565
  dsimp only [vaultBlocks.vault_block_7565_stack] at rd7594
  rw [hmt] at rd7594
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7594)
    (_ :: token :: ⟨0⟩ :: UInt256.ofNat 220 :: UInt256.ofNat 100 ::
      UInt256.ofNat 192 :: UInt256.ofNat 32 :: token :: returnPc :: R)
    (vaultTokenCallMemory mem) aw1 rdata σ k1 C1 at rd7594
  obtain ⟨evm', σ', z, out, k2, C2, hcall, hs', rd7595, hout⟩ := callBridge rd7594 hs hperm
    (by native_decide) (vaultTokenCallMemory_payload mem sender recipient amount hsize hmf hmr hma)
    (by rw [vaultTokenPayload_size]; exact le_trans (by decide +kernel) Ethereum.EVM.pow_two_64_le_maxReturnDataSizeByGas)
    (by simp only [List.length_cons]; omega)
  have hwide : out.size < UInt256.size := lt_trans hout (by decide +kernel)
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7595) ((if z then ⟨1⟩ else ⟨0⟩) :: token :: returnPc :: R)
    (callOutputMem (vaultTokenCallMemory mem) out (UInt256.ofNat 192) (UInt256.ofNat 32)) _ out σ' k2 C2 at rd7595
  cases z with
  | false =>
    have rd7599 := vaultBlocks.vault_block_7595_fallthrough
      (by simp only [List.length_cons]; omega) rfl rd7595
    exact Or.inr ⟨vaultTokenSourceCallFailure evm evm' locals token sender recipient amount out htoken hf ht ha hpos hcall,
      vaultBlocks.vault_block_7599 (by simp only [vaultBlocks.vault_block_7595_fallthrough_stack, List.length_cons]; omega) rd7599⟩
  | true =>
    have rd7606 := vaultBlocks.vault_block_7595_taken
      (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rd7595
    have hload (h32 : 32 ≤ out.size) :
        memLoad (UInt256.ofNat 192)
          (callOutputMem (vaultTokenCallMemory mem) out (UInt256.ofNat 192) (UInt256.ofNat 32)) = retWord out := by
      exact memLoad_callOutput32 out (vaultTokenCallMemory mem) 192 h32 hwide
        (by rw [vaultTokenCallMemory_size]; omega) (by decide +kernel)
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by omega)))
    rcases vaultTokenReturnEVM hwide hload (by omega) hvalid rd7606 with
      ⟨haccept, aw2, k3, C3, rdReturn⟩ | ⟨hreject, hrev⟩
    · obtain ⟨locals', hsource⟩ := vaultTokenSourceSuccess hs' locals token sender recipient amount out
        htoken hf ht ha hpos hcall haccept
      exact Or.inl ⟨evm', σ', vaultTokenResultMemory mem out, out, locals', aw2, k3, C3, hsource,
        hs', vaultTokenResultMemory_frame mem out hwide, rdReturn⟩
    · exact Or.inr ⟨vaultTokenSourceReturnFailure hs' locals token sender recipient amount out
        htoken hf ht ha hpos hcall hreject, hrev⟩

end Benchmarks.CurveVault
