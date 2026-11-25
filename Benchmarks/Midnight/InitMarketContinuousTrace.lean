import Benchmarks.Midnight.InitMarketFeeTrace

variable {fork : Ethereum.Fork}

/-! The final initialization write reads the continuous fee after the settlement writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem wordShiftLeftLand (a b bits : UInt256) :
    UInt256.land (UInt256.shiftLeft a bits) (UInt256.shiftLeft b bits) =
      UInt256.shiftLeft (UInt256.land a b) bits := by
  by_cases hb : bits.toNat < 256
  · have hs (w : UInt256) : (UInt256.shiftLeft w bits).toNat =
        (w.toNat <<< bits.toNat) % 2^256 := by
      unfold UInt256.shiftLeft
      rw [if_neg (show ¬ bits.val ≥ 256 from Nat.not_le.mpr hb)]
      rfl
    apply u256_inj
    rw [uland_toNat, hs, hs, hs, uland_toNat, Nat.shiftLeft_and_distrib, Nat.and_mod_two_pow]
  · unfold UInt256.shiftLeft
    simp only [if_pos (show bits.val ≥ 256 from Nat.le_of_not_gt hb)]
    rfl

theorem initMarketContinuousWord (old value : UInt256) :
    UInt256.lor
      (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 112))
        (UInt256.shiftLeft value (UInt256.ofNat 112)))
      (UInt256.land (UInt256.lnot
        (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 112))) old) =
      setUint32Offset14Word old value := by
  have hs (w : UInt256) : UInt256.shiftLeft w (UInt256.ofNat 112) =
      UInt256.mul w (UInt256.ofNat (2^112)) := by
    apply u256_inj
    rw [u256_mul_toNat]
    unfold UInt256.shiftLeft
    rw [if_neg (show ¬ (UInt256.ofNat 112).val ≥ 256 from by decide)]
    change (w.toNat <<< 112) % UInt256.size = (w.toNat * 2^112) % UInt256.size
    rw [Nat.shiftLeft_eq]
  rw [wordShiftLeftLand, hs]
  simp only [setUint32Offset14Word, u256_land_comm (UInt256.ofNat 4294967295),
    u256_land_comm _ old, u256_lor_comm]
  rfl

set_option maxRecDepth 2000000 in
theorem midnightInitMarketContinuous {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id : UInt256} {k C : Nat} {R : List UInt256}
    (token : AccountAddress) (hstack : R.length + 5 ≤ 1024)
    (hmem : 64 ≤ mem.size) (hperm : evm.executionEnv.perm = true)
    (rd : RD fork midnightBytecode evm.executionEnv g s0 ⟨21514⟩
      (⟨0⟩ :: (solcMappingSlot ⟨1⟩ id + ⟨2⟩) :: R)
      (twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 5) mem)
      aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD fork midnightBytecode evm.executionEnv g s0 ⟨24347⟩
      (UInt256.ofNat 21556 :: R)
      (twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 5) mem)
      aw' rdata (initMarketContinuous evm id token).accountMap k' C' := by
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 5) mem) =
      solcMappingSlot ⟨5⟩ (UInt256.ofNat token.val) := twoWordHashMem_mapSlot_of_ge64 _ _ hmem
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_21514_packed hstack hperm (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_21514_stack, hh, initMarketContinuousWord,
    accountStorageWord_fold] at rd1
  refine ⟨aw1, k1, C1, ?_⟩
  simpa only [initMarketContinuous, marketFeeWord, storageStore_accountMap,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl] using rd1

end Benchmarks.Midnight
