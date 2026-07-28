import Benchmarks.Dss.Flipper.DealEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-! ## Tic-expired EVM helpers for `deal(uint256)` -/

-- LIBRARY CANDIDATE: a 96-byte scratch buffer is determined by its three 32-byte windows.
theorem scratch96_eq_reads (mem : ByteArray) (hmem : mem.size = 96) :
    mem = mem.readWithPadding 0 32 ++ mem.readWithPadding 32 32 ++
      mem.readWithPadding 64 32 := by
  rw [readWithPadding_eq_extract mem 0 (by omega),
      readWithPadding_eq_extract mem 32 (by omega),
      readWithPadding_eq_extract mem 64 (by omega)]
  conv_lhs => rw [← byteArray_extract_self mem]
  rw [hmem]
  norm_num

-- LIBRARY CANDIDATE: repeated writes of the same mapping-hash input are stable on
-- 96-byte scratch memory.
theorem twoWordHashMem_eq_of_size_read64_128 {mem mem' : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) (hmem' : mem'.size = 96)
    (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h64' : mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    twoWordHashMem key slot mem = twoWordHashMem key slot mem' := by
  rw [scratch96_eq_reads (twoWordHashMem key slot mem) (twoWordHashMem_size_96 key slot hmem),
      scratch96_eq_reads (twoWordHashMem key slot mem') (twoWordHashMem_size_96 key slot hmem')]
  rw [twoWordHashMem_read0 key slot hmem, twoWordHashMem_read0 key slot hmem',
      twoWordHashMem_read32 key slot hmem, twoWordHashMem_read32 key slot hmem',
      twoWordHashMem_read64 key slot hmem h64, twoWordHashMem_read64 key slot hmem' h64']

theorem dealHashMem0_size (I : ExecutionEnv) :
    (dealHashMem0 I).size = 96 := by
  unfold dealHashMem0
  exact twoWordHashMem_size_96 (dealId I) ⟨1⟩ solcFreePtrMem_size

theorem dealHashMem0_read64 (I : ExecutionEnv) :
    (dealHashMem0 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealHashMem0
  exact twoWordHashMem_read64 (dealId I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem dealHashMem1_size (I : ExecutionEnv) :
    (dealHashMem1 I).size = 96 := by
  unfold dealHashMem1
  exact twoWordHashMem_size_96 (dealId I) ⟨1⟩ (dealHashMem0_size I)

theorem dealHashMem1_read64 (I : ExecutionEnv) :
    (dealHashMem1 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dealHashMem1
  exact twoWordHashMem_read64 (dealId I) ⟨1⟩ (dealHashMem0_size I) (dealHashMem0_read64 I)

theorem dealHashMem1_eq_dealHashMem2 (I : ExecutionEnv) :
    dealHashMem1 I = dealHashMem2 I := by
  unfold dealHashMem1 dealHashMem2
  exact twoWordHashMem_eq_of_size_read64_128 (dealId I) ⟨1⟩
    (dealHashMem0_size I) (dealHashMem1_size I)
    (dealHashMem0_read64 I) (dealHashMem1_read64 I)

theorem flipperDealX_ticExpired_catMem {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hticNe : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticLt : (bidTicWord (dealId I) σ I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat)
    (h : RD flipperBytecode I g s0 ⟨5365⟩ [dealId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5558⟩ [dealId I, ret, sel]
      (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd5558⟩ := flipperDealX_ticExpired hticNe hticLt h
  exact ⟨k', C', by simpa [dealHashMem1_eq_dealHashMem2 I] using rd5558⟩

end Benchmarks.Dss.Flipper
