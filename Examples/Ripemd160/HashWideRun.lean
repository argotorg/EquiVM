import Examples.Ripemd160.HashWideBlock

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem hashBlockCountWord_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashBlockCountWord I).toNat = Model.paddedLength I.calldata.size / 64 := by
  unfold hashBlockCountWord
  change (UInt256.shiftRight (calldataSizeWord I + ⟨72⟩)
    (UInt256.ofNat 6)).toNat = Model.paddedLength I.calldata.size / 64
  rw [ushr_ofNat_toNat _ 6 (by omega), Nat.shiftRight_eq_div_pow]
  have hsize : I.calldata.size < UInt256.size :=
    lt_of_le_of_lt hsmall (by native_decide)
  have hadd : (calldataSizeWord I + ⟨72⟩).toNat = I.calldata.size + 72 := by
    rw [uadd_toNat, ulit_toNat' I.calldata.size hsize,
      show (⟨72⟩ : UInt256).toNat = 72 from by decide,
      show UInt256.size = 2 ^ 256 from by decide, Nat.mod_eq_of_lt]
    unfold maxFallbackCalldataSize at hsmall
    omega
  rw [hadd]
  simp [Model.paddedLength]

/-- Iterate the full-range compression trace over a prefix of the block loop. -/
theorem ripemd160X_blocks_wide {cA gh bl σ σ₀ A I} {g : Sat256}
    {initial : RuntimeHashState} {blocks k C : Nat}
    (hblocks : blocks ≤ Model.paddedLength I.calldata.size / 64)
    (hpadded : RuntimePaddedCursor I initial.cursor 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (rd1028 : RD ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I ⟨0⟩ initial.chain)
      initial.cursor.mem initial.cursor.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I (UInt256.ofNat blocks)
        (runtimeHashRun I blocks initial).chain)
      (runtimeHashRun I blocks initial).cursor.mem
      (runtimeHashRun I blocks initial).cursor.aw ByteArray.empty (cA, σ) k' C' ∧
      RuntimePaddedCursor I (runtimeHashRun I blocks initial).cursor 0 := by
  induction blocks with
  | zero =>
      exact ⟨k, C, by simpa [runtimeHashRun] using rd1028,
        by simpa [runtimeHashRun] using hpadded⟩
  | succ block ih =>
      have hprev : block ≤ Model.paddedLength I.calldata.size / 64 := by omega
      obtain ⟨kprev, Cprev, rdprev, hpprev⟩ := ih hprev
      have hblock : block < Model.paddedLength I.calldata.size / 64 := by omega
      have hcount := hashBlockCountWord_toNat I hsmall
      have hblockUint : block < UInt256.size := by
        have hp := (hashPaddedLength_bounds I.calldata.size).2
        rw [show UInt256.size = 2 ^ 256 from by decide]
        unfold maxFallbackCalldataSize at hsmall
        omega
      have hblockWord :
          UInt256.lt (UInt256.ofNat block) (hashBlockCountWord I) = ⟨1⟩ := by
        apply ult_one
        rw [ulit_toNat' block hblockUint, hcount]
        exact hblock
      obtain ⟨knext, Cnext, rdnext, hinv⟩ :=
        ripemd160X_compressBlock_wide hblockWord hpprev hsmall hblock rdprev
      have hnext : UInt256.ofNat block + ⟨1⟩ = UInt256.ofNat (block + 1) := by
        rw [u256_add_comm, u256_one_add_ofNat]
      refine ⟨knext, Cnext, ?_, ?_⟩
      · simpa [runtimeHashRun, runtimeHashStep, hnext] using rdnext
      · simpa [runtimeHashRun, runtimeHashStep] using hinv.padded.weaken (m := 0) (by omega)

end Ripemd160
