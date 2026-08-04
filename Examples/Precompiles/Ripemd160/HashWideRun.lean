import Examples.Precompiles.Ripemd160.HashWideBlock

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

def ripemd160BlocksGas (I : ExecutionEnv) : Nat → RuntimeHashState → Nat
  | 0, _ => 0
  | block + 1, initial =>
      ripemd160BlocksGas I block initial
        + ripemd160CompressBlockGas I block (runtimeHashRun I block initial)

/-- Iterate the full-range compression trace over a prefix of the block loop. -/
theorem ripemd160X_blocks_wideGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {initial : RuntimeHashState} {blocks k C : Nat}
    (hblocks : blocks ≤ Model.paddedLength I.calldata.size / 64)
    (hpadded : RuntimePaddedCursor I initial.cursor 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (rd1028 : RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I ⟨0⟩ initial.chain)
      initial.cursor.mem initial.cursor.aw ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I (UInt256.ofNat blocks)
        (runtimeHashRun I blocks initial).chain)
      (runtimeHashRun I blocks initial).cursor.mem
      (runtimeHashRun I blocks initial).cursor.aw ByteArray.empty (cA, σ) k'
        (C + ripemd160BlocksGas I blocks initial) ∧
      RuntimePaddedCursor I (runtimeHashRun I blocks initial).cursor 0 := by
  induction blocks with
  | zero =>
      exact ⟨k, by simpa [runtimeHashRun, ripemd160BlocksGas] using rd1028,
        by simpa [runtimeHashRun] using hpadded⟩
  | succ block ih =>
      have hprev : block ≤ Model.paddedLength I.calldata.size / 64 := by omega
      obtain ⟨kprev, rdprev, hpprev⟩ := ih hprev
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
      obtain ⟨knext, rdnext, hinv⟩ :=
        ripemd160X_compressBlock_wideGas hblockWord hpprev hsmall hblock rdprev
      have heta : RuntimeHashState.mk (runtimeHashRun I block initial).cursor
          (runtimeHashRun I block initial).chain =
          runtimeHashRun I block initial := by
        cases runtimeHashRun I block initial
        rfl
      rw [heta] at rdnext
      have hnext : UInt256.ofNat block + ⟨1⟩ = UInt256.ofNat (block + 1) := by
        rw [u256_add_comm, u256_one_add_ofNat]
      refine ⟨knext, ?_, ?_⟩
      · have rdExact := RDx.withIndices rdnext
          (C' := C + ripemd160BlocksGas I (block + 1) initial) (by rfl) (by
            simp only [ripemd160BlocksGas]
            omega)
        simpa [runtimeHashRun, runtimeHashStep, hnext] using rdExact
      · simpa [runtimeHashRun, runtimeHashStep] using hinv.padded.weaken (m := 0) (by omega)

theorem ripemd160X_blocks_wide {cA gh bl σ σ₀ A I} {g : Sat256}
    {initial : RuntimeHashState} {blocks k C : Nat}
    (hblocks : blocks ≤ Model.paddedLength I.calldata.size / 64)
    (hpadded : RuntimePaddedCursor I initial.cursor 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (rd1028 : RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I ⟨0⟩ initial.chain)
      initial.cursor.mem initial.cursor.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I (UInt256.ofNat blocks)
        (runtimeHashRun I blocks initial).chain)
      (runtimeHashRun I blocks initial).cursor.mem
      (runtimeHashRun I blocks initial).cursor.aw ByteArray.empty (cA, σ) k' C' ∧
      RuntimePaddedCursor I (runtimeHashRun I blocks initial).cursor 0 := by
  obtain ⟨k', rd', hi⟩ := ripemd160X_blocks_wideGas
    hblocks hpadded hsmall rd1028
  exact ⟨k', _, rd', hi⟩

end Ripemd160
