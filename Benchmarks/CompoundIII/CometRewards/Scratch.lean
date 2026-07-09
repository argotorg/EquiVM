import Benchmarks.CompoundIII.CometRewards.Claim

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.CompoundIII.CometRewards

theorem scratch_claim_transfer_state
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier accrued claimed : UInt256} {baseOut : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3432⟩
      [ accrued, ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hperm : I.perm = true)
    (hbaseSize : baseOut.size < UInt256.size)
    (hlt : claimed.toNat < accrued.toNat) :
    True := by
  have hgtWord : UInt256.gt accrued claimed = ⟨1⟩ := ugt_one hlt
  have rd3436₀ := evm_run rd with [jumpdest, dup7, dup2, gt]
  have rd3436 := rd3436₀
  rw [hgtWord] at rd3436
  have rd3452 := evm_run rd3436 with [
    push2 ⟨3452⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  let rewardsClaimedBaseSlot : UInt256 :=
    ⟨16344734836896974401298970600416103014985972868941485175496275033332075043944⟩
  have rd3459 := evm_run rd3452 with [
    dup10, dup6, swap4, push2 ⟨3498⟩]
  have rd3492pre :=
    RD.pushConst (op := .PUSH32) (width := 32) rd3459 rewardsClaimedBaseSlot
      (by decide) (by native_decide)
      (by evm_ov)
  have rd3241 := evm_run rd3492pre with [
    swap10, dup5, push2 ⟨3241⟩, jump (by jump_dest)]
  have rd3245₀ := evm_run rd3241 with [jumpdest, dup2, dup2, lt]
  have hltWord : UInt256.lt accrued claimed = ⟨0⟩ := ult_zero (le_of_lt hlt)
  have rd3245 := rd3245₀
  rw [hltWord] at rd3245
  have rd3498 := evm_run rd3245 with [
    push2 ⟨3252⟩, jumpiNT (by native_decide),
    sub, swap1, jump (by jump_dest), jumpdest]
  let postDecodeMem := claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut
  let innerMem :=
    twoWordHashMem (UInt256.land (claimCometWord I) solcAddrMask) ⟨2⟩ postDecodeMem
  let outerMem :=
    twoWordHashMem (UInt256.land (claimSrcWord I) solcAddrMask)
      (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask)) innerMem
  have hpostDecodeSize64 : 64 ≤ postDecodeMem.size := by
    dsimp [postDecodeMem, claimBaseTrackingPostDecodeMem]
    rw [writeWord_size]
    · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
      omega
    · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
      have hle :
          64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
        omega
      rw [hle]
      native_decide
  have rd3501 := evm_run rd3498 with [
    swap11, dup2,
    raw mstore 0
      (wordAt0Mem (UInt256.land (claimCometWord I) solcAddrMask) postDecodeMem)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by
        dsimp [postDecodeMem]
        unfold wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3505 := evm_run rd3501 with [
    push1 ⟨2⟩, dup9,
    raw mstore 0 innerMem claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by
        dsimp [innerMem, postDecodeMem]
        unfold twoWordHashMem wordAt32Mem wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have hinnerHash :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((innerMem).readWithPadding 0 64))) =
        solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask) := by
    dsimp [innerMem]
    exact twoWordHashMem_solcMappingSlot_of_ge ⟨2⟩
      (UInt256.land (claimCometWord I) solcAddrMask) hpostDecodeSize64
  have rd3506 := rd3505.keccak256 0
    (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
    claimBaseTrackingPostCallAw (by native_decide) mem_cost
    hinnerHash (by native_decide) (by evm_ov)
  have rd3510 := evm_run rd3506 with [
    dup9, push1 ⟨0⟩,
    raw mstore 0
      (wordAt0Mem (UInt256.land (claimSrcWord I) solcAddrMask) innerMem)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by
        dsimp [innerMem]
        unfold wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3512 := evm_run rd3510 with [
    dup7,
    raw mstore 0 outerMem claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by
        dsimp [outerMem, innerMem]
        unfold twoWordHashMem wordAt32Mem wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have hinnerMemSize64 : 64 ≤ innerMem.size := by
    dsimp [innerMem]
    rw [twoWordHashMem_size_of_ge
      (UInt256.land (claimCometWord I) solcAddrMask) ⟨2⟩ hpostDecodeSize64]
    exact hpostDecodeSize64
  have houterHash :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((outerMem).readWithPadding 0 64))) =
        solcMappingSlot
          (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
          (UInt256.land (claimSrcWord I) solcAddrMask) := by
    dsimp [outerMem]
    exact twoWordHashMem_solcMappingSlot_of_ge
      (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
      (UInt256.land (claimSrcWord I) solcAddrMask) hinnerMemSize64
  have rd3516pre := (evm_run rd3512 with [dup10, push1 ⟨0⟩]).keccak256 0
    (solcMappingSlot
      (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
      (UInt256.land (claimSrcWord I) solcAddrMask))
    claimBaseTrackingPostCallAw (by native_decide) mem_cost
    houterHash (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3518⟩ := rd3516pre.sstore hperm (by native_decide) (by evm_ov)
  have hpostDecodeSize160 : 160 ≤ postDecodeMem.size := by
    dsimp [postDecodeMem, claimBaseTrackingPostDecodeMem]
    rw [writeWord_size]
    · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
      omega
    · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
      have hle :
          64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
        omega
      rw [hle]
      native_decide
  have hinnerMemSize160 : 160 ≤ innerMem.size := by
    dsimp [innerMem]
    rw [twoWordHashMem_size_of_ge
      (UInt256.land (claimCometWord I) solcAddrMask) ⟨2⟩ hpostDecodeSize64]
    exact hpostDecodeSize160
  have houterMemSize160 : 160 ≤ outerMem.size := by
    dsimp [outerMem]
    rw [twoWordHashMem_size_of_ge
      (UInt256.land (claimSrcWord I) solcAddrMask)
      (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
      hinnerMemSize64]
    exact hinnerMemSize160
  have houterMem_read128 :
      outerMem.readWithPadding 128 32 =
        UInt256.toByteArray (rewardConfigTokenFromSlot0 slot0) := by
    dsimp [outerMem, innerMem, postDecodeMem]
    rw [twoWordHashMem_read_above64_of_ge]
    · rw [twoWordHashMem_read_above64_of_ge]
      · exact claimBaseTrackingPostDecodeMem_read128 I slot0 multiplier hbaseSize
      · exact hpostDecodeSize160
      · norm_num
    · exact hinnerMemSize160
    · norm_num
  have houterMem_mload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ outerMem.size
          ∨ (⟨128⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ then
        ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (outerMem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        rewardConfigTokenFromSlot0 slot0 := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨128⟩ : UInt256)) (aw := claimBaseTrackingPostCallAw)
      (v := rewardConfigTokenFromSlot0 slot0)
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        omega)
      (by native_decide)
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact houterMem_read128)
  have rd3530 := evm_run rd3518 with [
    push2 ⟨3531⟩, dup9, dup5, dup5, dup5,
    raw mload 0 (rewardConfigTokenFromSlot0 slot0) claimBaseTrackingPostCallAw
      (by native_decide) mem_cost houterMem_mload128 (by native_decide) (by evm_ov),
    and, push2 ⟨3915⟩, jump (by jump_dest)]
  trivial

end Benchmarks.CompoundIII.CometRewards
