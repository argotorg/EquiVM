import Benchmarks.Dss.Flopper.Dent.Part4

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper
set_option maxHeartbeats 1000000 in
theorem flopperDentX_ticZeroOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (h : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1964⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (dentIdWord I) ⟨1⟩
        (twoWordHashMem (dentIdWord I) ⟨1⟩
          (twoWordHashMem (dentIdWord I) ⟨1⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := dentIdWord I
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memTicZero := twoWordHashMem id ⟨1⟩ memTic
  obtain ⟨_, _, rd1806⟩ := flopperDentX_guyOk (g := g) hlive hguy h
  obtain ⟨_, _, rd1843⟩ := flopperDentX_toTicGtGuard rd1806
  have hle :
      (flopperUint48Offset20Word (auctionPackedSlot id) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
    rw [htic]
    exact Nat.zero_le _
  have hgt :
      UInt256.gt (flopperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ugt_zero
    exact hle
  have rd1847 := evm_run rd1843 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw push2 ⟨1883⟩ (by decide +native) (by evm_ov)]
  have rd1848 := rd1847.jumpiNT (by decide +native) hgt (by evm_ov)
  have rd1849 := rd1848.pop (by decide +native) (by evm_ov)
  let memKey := wordAt0Mem id memTic
  let base := solcMappingSlot ⟨1⟩ id
  have rd1853pre := evm_run rd1849 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd1854 := rd1853pre.mstore 0 memKey (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by simp [memKey, memTic, memGuy, id, wordAt0Mem])
    (by decide +native)
    (by evm_ov)
  have rd1858pre := evm_run rd1854 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd1859 := rd1858pre.mstore 0 memTicZero (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memTicZero, memTic, id, twoWordHashMem, wordAt32Mem])
    (by decide +native)
    (by evm_ov)
  have rd1862pre := evm_run rd1859 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTicZero.readWithPadding 0 64))) = base := by
    simpa [base, memTicZero, memTic, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memTic
  have rd1863 := rd1862pre.keccak256 0 base (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      decide +native)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by decide +native)
    (by evm_ov)
  have rd1866pre := evm_run rd1863 with [
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd1866pre
  obtain ⟨k1867, C1867, rd1867raw⟩ := rd1866pre.sload (by decide +native) (by evm_ov)
  have rd1867 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1867⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, dentBidWord I, dentLotWord I,
        id, ⟨334⟩, sel]
      memTicZero (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1867 C1867 := by
    simpa [flopperSlotWord] using rd1867raw
  have rd1882 := evm_run rd1867 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov)]
  have rd1881 := rd1882.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by decide +native)
    (by simp)
  have rd1882' := rd1881.and (by decide +native) (by evm_ov)
  have rd1883pre := rd1882'.iszero (by decide +native) (by evm_ov)
  have hpc1883 :
      (⟨1867⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat (Nat.succ 6) + ⟨1⟩ + ⟨1⟩ =
        ⟨1883⟩ := by
    decide +native
  rw [hpc1883] at rd1883pre
  have hticRaw :
      UInt256.land flopperUint48Mask
          (UInt256.div (flopperSlotWord (auctionPackedSlot id) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        flopperUint48Offset20Word (auctionPackedSlot id) σ I := by
    rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
      from by decide +native]
    rfl
  have rd1883 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1883⟩
      [UInt256.isZero (flopperUint48Offset20Word (auctionPackedSlot id) σ I),
        dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memTicZero (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k1867 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C1867 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3) := by
    simpa [id, hticRaw] using rd1883pre
  have hzeroGuard :
      UInt256.isZero (flopperUint48Offset20Word (auctionPackedSlot id) σ I) ≠
        ⟨0⟩ := by
    rw [htic]
    decide +native
  have rd1884 := rd1883.jumpdest (by decide +native) (by evm_ov)
  have rd1887 := rd1884.push2 ⟨1964⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, by
    simpa [id] using rd1887.jumpiT (by decide +native) hzeroGuard
      (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_toEndGtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (rd1964 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1964⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memEnd := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2001⟩
      [UInt256.gt (flopperUint48Offset26Word (auctionPackedSlot id) σ I)
        (UInt256.ofNat I.header.timestamp), dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memEnd
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd1969pre := evm_run rd1964 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd1970 := rd1969pre.mstore 0 memKey (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by simp [memKey, id, wordAt0Mem])
    (by decide +native)
    (by evm_ov)
  have rd1974pre := evm_run rd1970 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd1975 := rd1974pre.mstore 0 memEnd (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memEnd, id, twoWordHashMem, wordAt32Mem])
    (by decide +native)
    (by evm_ov)
  have rd1978pre := evm_run rd1975 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memEnd.readWithPadding 0 64))) = base := by
    simpa [base, memEnd, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd1979 := rd1978pre.keccak256 0 base (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      decide +native)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by decide +native)
    (by evm_ov)
  have rd1982pre := evm_run rd1979 with [
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd1982pre
  obtain ⟨k1983, C1983, rd1983raw⟩ := rd1982pre.sload (by decide +native) (by evm_ov)
  have rd1983 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1983⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, dentBidWord I, dentLotWord I,
        id, ⟨334⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1983 C1983 := by
    simpa [flopperSlotWord] using rd1983raw
  have rd1992 := evm_run rd1983 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨208⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov)]
  have rd1999 := rd1992.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by decide +native)
    (by simp)
  have rd2000 := rd1999.and (by decide +native) (by evm_ov)
  have rd2001 := rd2000.gt (by decide +native) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flopperUint48Offset26Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ = UInt256.ofNat (256 ^ 26)
      from by decide +native]
      using rd2001⟩

theorem flopperDentX_endFinishedFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memEnd : ByteArray} {k C : ℕ}
    (hendLe :
      (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hmemSize : memEnd.size = 96)
    (hread64 : memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2001 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2001⟩
      [UInt256.gt (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I)
        (UInt256.ofNat I.header.timestamp),
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hgt :
      UInt256.gt (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ugt_zero
    exact hendLe
  have rd2004 := rd2001.push2 ⟨2081⟩ (by decide +native) (by evm_ov)
  have rd2005 := rd2004.jumpiNT (by decide +native) hgt (by evm_ov)
  exact solcErrorStringRevertTailFullWord
    (pc := ⟨2005⟩)
    (len := ⟨28⟩)
    (word :=
      ⟨0x466c6f707065722f616c72656164792d66696e69736865642d656e6400000000⟩)
    rd2005
    (by
      unfold solcErrorStringRevertTailFullWordWf
      repeat' first | apply And.intro | decide +native)
    hmemSize
    hread64
    (by simp)

theorem flopperDentX_endOkFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memEnd : ByteArray} {k C : ℕ}
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (rd2001 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2001⟩
      [UInt256.gt (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I)
        (UInt256.ofNat I.header.timestamp),
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2081⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hgt :
      UInt256.gt (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨1⟩ := by
    apply ugt_one
    exact hendGt
  have rd2004 := rd2001.push2 ⟨2081⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, by
    simpa [hgt] using rd2004.jumpiT (by decide +native)
      (by rw [hgt]; exact one_ne_zero_uint)
      (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_toBidEqGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (rd2081 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2081⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memBid := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2099⟩
      [UInt256.eq (dentBidWord I) (flopperSlotWord (auctionBidSlot id) σ I),
        dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memBid
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2086pre := evm_run rd2081 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd2087 := rd2086pre.mstore 0 memKey (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by simp [memKey, id, wordAt0Mem])
    (by decide +native)
    (by evm_ov)
  have rd2091pre := evm_run rd2087 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd2092 := rd2091pre.mstore 0 memBid (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memBid, id, twoWordHashMem, wordAt32Mem])
    (by decide +native)
    (by evm_ov)
  have rd2095pre := evm_run rd2092 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memBid.readWithPadding 0 64))) = base := by
    simpa [base, memBid, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2096pre := rd2095pre.keccak256 0 base (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      decide +native)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by decide +native)
    (by evm_ov)
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd2096pre
  obtain ⟨k2097, C2097, rd2097raw⟩ := rd2096pre.sload (by decide +native) (by evm_ov)
  have rd2097 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2097⟩
      [flopperSlotWord (auctionBidSlot id) σ I, dentBidWord I, dentLotWord I, id, ⟨334⟩,
        sel]
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2097 C2097 := by
    simpa [flopperSlotWord] using rd2097raw
  have rd2099 := evm_run rd2097 with [
    raw dup2 (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa [id] using rd2099⟩

theorem flopperDentX_bidMismatchFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memBid : ByteArray} {k C : ℕ}
    (hbid : dentBidWord I ≠ flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I)
    (hmemSize : memBid.size = 96)
    (hread64 : memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2099 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2099⟩
      [UInt256.eq (dentBidWord I) (flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I),
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq :
      UInt256.eq (dentBidWord I) (flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I) =
        ⟨0⟩ := by
    apply u256_eq_of_ne
    exact hbid
  have rd2102 := rd2099.push2 ⟨2179⟩ (by decide +native) (by evm_ov)
  have rd2103 := rd2102.jumpiNT (by decide +native) heq (by evm_ov)
  exact solcErrorStringRevertTailFullWord
    (pc := ⟨2103⟩)
    (len := ⟨24⟩)
    (word := ⟨0x466c6f707065722f6e6f742d6d61746368696e672d6269640000000000000000⟩)
    rd2103
    (by
      unfold solcErrorStringRevertTailFullWordWf
      repeat' first | apply And.intro | decide +native)
    hmemSize
    hread64
    (by simp)

theorem flopperDentX_bidOkFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memBid : ByteArray} {k C : ℕ}
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I)
    (rd2099 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2099⟩
      [UInt256.eq (dentBidWord I) (flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I),
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2179⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have heq :
      UInt256.eq (dentBidWord I) (flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I) ≠
        ⟨0⟩ := by
    rw [hbid, u256_eq_refl]
    exact one_ne_zero_uint
  have rd2102 := rd2099.push2 ⟨2179⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2102.jumpiT (by decide +native) heq (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_toLotLtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (rd2179 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2179⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memLot := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2201⟩
      [UInt256.lt (dentLotWord I) (flopperSlotWord (auctionLotSlot id) σ I),
        dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memLot
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2184pre := evm_run rd2179 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd2185 := rd2184pre.mstore 0 memKey (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by simp [memKey, id, wordAt0Mem])
    (by decide +native)
    (by evm_ov)
  have rd2191pre := evm_run rd2185 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd2192 := rd2191pre.mstore 0 memLot (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memLot, id, twoWordHashMem, wordAt32Mem])
    (by decide +native)
    (by evm_ov)
  have rd2196pre := evm_run rd2192 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memLot.readWithPadding 0 64))) = base := by
    simpa [base, memLot, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2197pre := rd2196pre.keccak256 0 base (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      decide +native)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by decide +native)
    (by evm_ov)
  have rd2198pre := rd2197pre.add (by decide +native) (by evm_ov)
  have hlotSlot : base + ⟨1⟩ = auctionLotSlot id := by
    simp [base, auctionLotSlot_eq, id]
  rw [hlotSlot] at rd2198pre
  obtain ⟨k2199, C2199, rd2199raw⟩ := rd2198pre.sload (by decide +native) (by evm_ov)
  have rd2199 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2199⟩
      [flopperSlotWord (auctionLotSlot id) σ I, dentBidWord I, dentLotWord I, id, ⟨334⟩,
        sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2199 C2199 := by
    simpa [flopperSlotWord] using rd2199raw
  have rd2201 := evm_run rd2199 with [
    raw dup3 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa [id] using rd2201⟩

theorem flopperDentX_lotNotLowerFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memLot : ByteArray} {k C : ℕ}
    (hlotLe :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I).toNat ≤
        (dentLotWord I).toNat)
    (hmemSize : memLot.size = 96)
    (hread64 : memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2201 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2201⟩
      [UInt256.lt (dentLotWord I) (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I),
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (dentLotWord I) (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I) =
        ⟨0⟩ := by
    apply ult_zero
    exact hlotLe
  have rd2204 := rd2201.push2 ⟨2273⟩ (by decide +native) (by evm_ov)
  have rd2205 := rd2204.jumpiNT (by decide +native) hlt (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2205⟩)
    (len := ⟨21⟩)
    (rawWord := ⟨0x233637b83832b917b637ba16b737ba16b637bbb2b9⟩)
    (shift := ⟨89⟩)
    (word := ⟨0x466c6f707065722f6c6f742d6e6f742d6c6f7765720000000000000000000000⟩)
    (op := .PUSH21)
    (width := 21)
    rd2205
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide)
    (by decide +native)
    hmemSize
    hread64
    (by simp)

theorem flopperDentX_lotLowerOkFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memLot : ByteArray} {k C : ℕ}
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (rd2201 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2201⟩
      [UInt256.lt (dentLotWord I) (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I),
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2273⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.lt (dentLotWord I) (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I) ≠
        ⟨0⟩ := by
    rw [ult_one hlotLt]
    exact one_ne_zero_uint
  have rd2204 := rd2201.push2 ⟨2273⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2204.jumpiT (by decide +native) hlt (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_toLotOneMulStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (rd2273 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2273⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memLotOne := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4674⟩
      [dentOneWord, flopperSlotWord (auctionLotSlot id) σ I, ⟨2310⟩,
        dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memLotOne
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2278pre := evm_run rd2273 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd2279 := rd2278pre.mstore 0 memKey (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by simp [memKey, id, wordAt0Mem])
    (by decide +native)
    (by evm_ov)
  have rd2285pre := evm_run rd2279 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd2286 := rd2285pre.mstore 0 memLotOne (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memLotOne, id, twoWordHashMem, wordAt32Mem])
    (by decide +native)
    (by evm_ov)
  have rd2290pre := evm_run rd2286 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memLotOne.readWithPadding 0 64))) = base := by
    simpa [base, memLotOne, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2292pre := rd2290pre.keccak256 0 base (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      decide +native)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by decide +native)
    (by evm_ov)
  have rd2293pre := rd2292pre.add (by decide +native) (by evm_ov)
  have hlotSlot : base + ⟨1⟩ = auctionLotSlot id := by
    simp [base, auctionLotSlot_eq, id]
  rw [hlotSlot] at rd2293pre
  obtain ⟨k2293, C2293, rd2293raw⟩ := rd2293pre.sload (by decide +native) (by evm_ov)
  have rd2293 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2293⟩
      [flopperSlotWord (auctionLotSlot id) σ I, dentBidWord I, dentLotWord I, id, ⟨334⟩,
        sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2293 C2293 := by
    simpa [flopperSlotWord, id] using rd2293raw
  have rd2297 := evm_run rd2293 with [
    raw push2 ⟨2310⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd2306 := rd2297.pushConst dentOneWord (width := 8) (op := .PUSH8)
    (by decide : Operation.POp.PUSH8 ≠ .PUSH0)
    (by decide +native)
    (by simp [dentOneWord])
  have rd2309 := rd2306.push2 ⟨4674⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2309.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem flopperDentX_lotOneOverflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memStart : ByteArray} {k C : ℕ}
    (hover :
      UInt256.size ≤
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I).toNat * dentOneWord.toNat)
    (rd2273 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2273⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4674⟩ := flopperDentX_toLotOneMulStart rd2273
  exact RD.flopperCheckedMulOverflowReverts
    (R := [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel])
    (hRlen := by simp)
    (hover := by simpa [dentOneWord] using hover)
    rd4674

theorem flopperDentX_lotOneOk {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memStart : ByteArray} {k C : ℕ}
    (hfit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I).toNat * dentOneWord.toNat <
        UInt256.size)
    (rd2273 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2273⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memLotOne := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2310⟩
      [dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
        dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memLotOne
  obtain ⟨_, _, rd4674⟩ := flopperDentX_toLotOneMulStart rd2273
  obtain ⟨_, _, rd2310⟩ := RD.flopperCheckedMulReturns
    (R := [dentBidWord I, dentLotWord I, id, ⟨334⟩, sel])
    (hRlen := by simp)
    (hret := by decide +native)
    (hfit := by simpa [id, dentOneWord] using hfit)
    rd4674
  exact ⟨_, _, by
    simpa [dentLotOneWord, dentLotStoredWord, flopperSlotWord, initState, id, dentOneWord,
      u256_mul_comm dentOneWord (flopperSlotWord (auctionLotSlot id) σ I)]
      using rd2310⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_toBegLotMulStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memLotOne : ByteArray}
    {k C : ℕ}
    (rd2310 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2310⟩
      [dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4674⟩
      [dentLotWord I, flopperSlotWord ⟨4⟩ σ I, ⟨2322⟩,
        dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2316pre := evm_run rd2310 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨2322⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov)]
  obtain ⟨k2317, C2317, rd2317raw⟩ := rd2316pre.sload (by decide +native) (by evm_ov)
  have rd2317 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2317⟩
      [flopperSlotWord ⟨4⟩ σ I, ⟨2322⟩,
        dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2317 C2317 := by
    simpa [flopperSlotWord] using rd2317raw
  have rd2321 := evm_run rd2317 with [
    raw dup5 (by decide +native) (by evm_ov),
    raw push2 ⟨4674⟩ (by decide +native) (by evm_ov)]
  exact ⟨_, _, rd2321.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem flopperDentX_begLotOverflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memLotOne : ByteArray} {k C : ℕ}
    (hover : UInt256.size ≤ (flopperSlotWord ⟨4⟩ σ I).toNat * (dentLotWord I).toNat)
    (rd2310 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2310⟩
      [dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4674⟩ := flopperDentX_toBegLotMulStart rd2310
  exact RD.flopperCheckedMulOverflowReverts
    (R := [dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
      dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel])
    (hRlen := by simp)
    (hover := by simpa using hover)
    rd4674

theorem flopperDentX_begLotOk {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memLotOne : ByteArray} {k C : ℕ}
    (hfit : (flopperSlotWord ⟨4⟩ σ I).toNat * (dentLotWord I).toNat < UInt256.size)
    (rd2310 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2310⟩
      [dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2322⟩
      [dentBegLotWord (initState cA gh bl σ σ₀ g A I) I,
        dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd4674⟩ := flopperDentX_toBegLotMulStart rd2310
  obtain ⟨_, _, rd2322⟩ := RD.flopperCheckedMulReturns
    (R := [dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
      dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel])
    (hRlen := by simp)
    (hret := by decide +native)
    (hfit := by simpa using hfit)
    rd4674
  exact ⟨_, _, by
    simpa [dentBegLotWord, dentBegWord, flopperSlotWord, initState]
      using rd2322⟩

theorem flopperDentX_insufficientDecreaseFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memLotOne : ByteArray} {k C : ℕ}
    (hinsuff :
      (dentLotOneWord (initState cA gh bl σ σ₀ g A I) I).toNat <
        (dentBegLotWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hmemSize : memLotOne.size = 96)
    (hread64 : memLotOne.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2322 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2322⟩
      [dentBegLotWord (initState cA gh bl σ σ₀ g A I) I,
        dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hgt :
      UInt256.gt (dentBegLotWord (initState cA gh bl σ σ₀ g A I) I)
          (dentLotOneWord (initState cA gh bl σ σ₀ g A I) I) =
        ⟨1⟩ := by
    apply ugt_one
    exact hinsuff
  have rd2328 := evm_run rd2322 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨2405⟩ (by decide +native) (by evm_ov)]
  have hcond :
      UInt256.isZero
          (UInt256.gt (dentBegLotWord (initState cA gh bl σ σ₀ g A I) I)
            (dentLotOneWord (initState cA gh bl σ σ₀ g A I) I)) =
        ⟨0⟩ := by
    rw [hgt]
    decide +native
  have rd2329 := rd2328.jumpiNT (by decide +native) hcond (by evm_ov)
  exact solcErrorStringRevertTailFullWord
    (pc := ⟨2329⟩)
    (len := ⟨29⟩)
    (word := ⟨0x466c6f707065722f696e73756666696369656e742d6465637265617365000000⟩)
    rd2329
    (by
      unfold solcErrorStringRevertTailFullWordWf
      repeat' first | apply And.intro | decide +native)
    hmemSize
    hread64
    (by simp)

theorem flopperDentX_sufficientDecreaseOkFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memLotOne : ByteArray} {k C : ℕ}
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ σ₀ g A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (rd2322 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2322⟩
      [dentBegLotWord (initState cA gh bl σ σ₀ g A I) I,
        dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2405⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hgt :
      UInt256.gt (dentBegLotWord (initState cA gh bl σ σ₀ g A I) I)
          (dentLotOneWord (initState cA gh bl σ σ₀ g A I) I) =
        ⟨0⟩ := by
    apply ugt_zero
    exact hsuff
  have rd2328 := evm_run rd2322 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨2405⟩ (by decide +native) (by evm_ov)]
  have hcond :
      UInt256.isZero
          (UInt256.gt (dentBegLotWord (initState cA gh bl σ σ₀ g A I) I)
            (dentLotOneWord (initState cA gh bl σ σ₀ g A I) I)) ≠
        ⟨0⟩ := by
    rw [hgt]
    decide +native
  exact ⟨_, _, rd2328.jumpiT (by decide +native) hcond (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_toCallerEqGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (rd2405 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2405⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memCaller := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2435⟩
      [UInt256.eq (UInt256.ofNat I.source.val)
        (flopperAddressReturnWord (auctionPackedSlot id) σ I),
        dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memCaller
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2410pre := evm_run rd2405 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd2411 := rd2410pre.mstore 0 memKey (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by simp [memKey, id, wordAt0Mem])
    (by decide +native)
    (by evm_ov)
  have rd2415pre := evm_run rd2411 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd2416 := rd2415pre.mstore 0 memCaller (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memCaller, id, twoWordHashMem, wordAt32Mem])
    (by decide +native)
    (by evm_ov)
  have rd2419pre := evm_run rd2416 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memCaller.readWithPadding 0 64))) = base := by
    simpa [base, memCaller, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2420 := rd2419pre.keccak256 0 base (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      decide +native)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by decide +native)
    (by evm_ov)
  have rd2423pre := evm_run rd2420 with [
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd2423pre
  obtain ⟨k2424, C2424, rd2424raw⟩ := rd2423pre.sload (by decide +native) (by evm_ov)
  have rd2424 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2424⟩
      [flopperSlotWord (auctionPackedSlot id) σ I, dentBidWord I, dentLotWord I, id, ⟨334⟩,
        sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2424 C2424 := by
    simpa [flopperSlotWord] using rd2424raw
  have rd2435raw := evm_run rd2424 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  have hmask :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (flopperSlotWord (auctionPackedSlot id) σ I) =
      flopperAddressReturnWord (auctionPackedSlot id) σ I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
  exact ⟨_, _, by simpa [hmask, id] using rd2435raw⟩

theorem flopperDentX_callerEqOkFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memCaller : ByteArray} {k C : ℕ}
    (hcaller :
      UInt256.ofNat I.source.val =
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I)
    (rd2435 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2435⟩
      [UInt256.eq (UInt256.ofNat I.source.val)
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I),
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I) ≠
        ⟨0⟩ := by
    rw [hcaller, u256_eq_refl]
    exact one_ne_zero_uint
  have rd2438 := rd2435.push2 ⟨2889⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2438.jumpiT (by decide +native) heq (by jump_dest) (by evm_ov)⟩

theorem flopperDentX_callerNeToMove {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memCaller : ByteArray} {k C : ℕ}
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I)
    (rd2435 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2435⟩
      [UInt256.eq (UInt256.ofNat I.source.val)
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I),
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2439⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I) =
        ⟨0⟩ := by
    apply u256_eq_of_ne
    exact hcaller
  have rd2438 := rd2435.push2 ⟨2889⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2438.jumpiNT (by decide +native) heq (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_toMoveExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memCaller : ByteArray}
    {k C : ℕ}
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2439 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2439⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let vat := flopperAddressReturnWord ⟨2⟩ σ I
    let guy := flopperAddressReturnWord (auctionPackedSlot id) σ I
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2529⟩
      (vat :: vat :: dentMoveOutSize :: dentMoveOutPtr :: dentMoveInSize ::
        dentMoveOutPtr :: dentMoveOutSize :: dentMoveEndPtr :: dentMoveSelectorWord ::
        vat :: dentBidWord I :: dentLotWord I :: id :: ⟨334⟩ :: sel :: [])
      (dentMoveCalldataMem src guy (dentBidWord I) memMap)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  intro id memMap src vat guy
  let memKey := wordAt0Mem id memCaller
  let base := solcMappingSlot ⟨1⟩ id
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
  have hread64Map : memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id] using twoWordHashMem_read64 id ⟨1⟩ hmemCaller hread64Caller
  have hmload64Map :
      (if (⟨64⟩ : UInt256).toNat ≥ memMap.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memMap.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemMap]; decide) (by decide) hread64Map
  have hcallMem : (dentMoveCalldataMem src guy (dentBidWord I) memMap).size = 228 :=
    dentMoveCalldataMem_size src guy (dentBidWord I) hmemMap
  have hcallRead64 :
      (dentMoveCalldataMem src guy (dentBidWord I) memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    dentMoveCalldataMem_read64 src guy (dentBidWord I) hmemMap hread64Map
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (dentMoveCalldataMem src guy (dentBidWord I) memMap).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dentMoveCalldataMem src guy (dentBidWord I) memMap).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd2441pre := evm_run rd2439 with [
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨k2443, C2443, rd2443raw⟩ := rd2441pre.sload (by decide +native) (by evm_ov)
  have rd2443 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2443⟩
      (flopperSlotWord ⟨2⟩ σ I :: ⟨2⟩ :: dentBidWord I :: dentLotWord I ::
        id :: ⟨334⟩ :: sel :: [])
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2443 C2443 := by
    simpa [id, flopperSlotWord] using rd2443raw
  have rd2446pre := evm_run rd2443 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd2447 := rd2446pre.mstore 0 memKey (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by simp [memKey, id, wordAt0Mem])
    (by decide +native)
    (by evm_ov)
  have rd2450pre := evm_run rd2447 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd2452 := rd2450pre.mstore 0 memMap (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by decide +native)
    (by evm_ov)
  have rd2456pre := evm_run rd2452 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memCaller
  have rd2457 := rd2456pre.keccak256 0 base (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      decide +native)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by decide +native)
    (by evm_ov)
  have rd2460pre := evm_run rd2457 with [
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd2460pre
  obtain ⟨k2462, C2462, rd2462raw⟩ := rd2460pre.sload (by decide +native) (by evm_ov)
  have rd2462 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2462⟩
      (flopperSlotWord (auctionPackedSlot id) σ I :: ⟨0⟩ ::
        flopperSlotWord ⟨2⟩ σ I :: ⟨64⟩ :: dentBidWord I :: dentLotWord I ::
        id :: ⟨334⟩ :: sel :: [])
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2462 C2462 := by
    simpa [flopperSlotWord] using rd2462raw
  have rd2528 := evm_run rd2462 with [
    raw dup4 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64Map (by decide) (by evm_ov),
    raw push4 dentMoveSelectorWord (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (dentMoveSelectorMem memMap) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (dentMoveSrcMem src memMap) (UInt256.ofNat 6)
      (by decide +native) mem_cost
      (by
        simp [dentMoveSrcMem, src,
          show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 from by decide +native])
      (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (dentMoveGuyMem src guy memMap) (UInt256.ofNat 7)
      (by decide +native) mem_cost
      (by
        simp [dentMoveGuyMem, guy, u256_land_comm,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide,
          show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 from by decide +native])
      (by decide +native) (by evm_ov),
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 3 (dentMoveCalldataMem src guy (dentBidWord I) memMap) (UInt256.ofNat 8)
      (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push4 dentMoveSelectorWord (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 dentMoveInSize (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  have hpc2528 :
      (⟨2462⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨2529⟩ := by
    decide +native
  rw [hpc2528] at rd2528
  exact ⟨_, _, by
    simpa [vat, guy, src, dentMoveSelectorMem, dentMoveSrcMem, dentMoveGuyMem,
      dentMoveCalldataMem, dentMoveSelectorShifted, dentMoveOutPtr, dentMoveOutSize,
      dentMoveInSize, dentMoveEndPtr, flopperAddressReturnWord, flopperSlotWord,
      solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide +native,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide +native,
      show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by decide +native,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + dentMoveInSize =
        dentMoveInSize from by decide +native,
      show (⟨128⟩ : UInt256) + dentMoveInSize = dentMoveEndPtr from by decide +native,
      show dentMoveInSize + dentMoveOutPtr = dentMoveEndPtr from by decide +native]
      using rd2528⟩

theorem flopperDentX_moveNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {memCaller : ByteArray} {k C : ℕ}
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ (flopperAddressReturnWord ⟨2⟩ σ I) =
        ⟨0⟩)
    (rd2439 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2439⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2529⟩ :=
    flopperDentX_toMoveExtcodesizeGuard hmemCaller hread64Caller rd2439
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2529⟩) (okPc := ⟨2541⟩) rd2529
    hnoCode
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp)

theorem flopperDentX_moveCall
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memCaller : ByteArray}
    {k C : ℕ}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flopperAddressReturnWord ⟨2⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2439 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2439⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let vat := flopperAddressReturnWord ⟨2⟩ σ I
    let guy := flopperAddressReturnWord (auctionPackedSlot id) σ I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: dentMoveEndPtr :: dentMoveSelectorWord ::
          vat :: dentBidWord I :: dentLotWord I :: id :: ⟨334⟩ :: sel :: [])
        (dentMoveCalldataMem src guy (dentBidWord I) memMap) (UInt256.ofNat 8)
        out (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
        (EVM.address (AccountAddress.ofNat vat.toNat)) "move" 0
        [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat guy.toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  intro id memMap src vat guy
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    simpa [src, solcSourceWord] using solcSourceWord_canonical I
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, flopperAddressReturnWord] using
      solcAddrMask_result_canonical (flopperSlotWord (auctionPackedSlot id) σ I)
  obtain ⟨_, _, rd2529⟩ :=
    flopperDentX_toMoveExtcodesizeGuard hmemCaller hread64Caller rd2439
  obtain ⟨gasWord, _, _, rd2544⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2529⟩) (okPc := ⟨2541⟩) rd2529
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k2545, C2545, hΘpack, rd2545raw,
      houtsz⟩ :=
    RD.call rd2544 (by decide +native) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k2545, C2545, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          dentMoveOutPtr.toNat dentMoveInSize.toNat)
          dentMoveOutPtr.toNat dentMoveOutSize.toNat) = UInt256.ofNat 8 := by
      unfold dentMoveOutPtr dentMoveInSize dentMoveOutSize
      decide +native
    have hmin : (min dentMoveOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold dentMoveOutSize
      rfl
    have rd2545 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: dentMoveEndPtr :: dentMoveSelectorWord ::
          vat :: dentBidWord I :: dentLotWord I :: id :: ⟨334⟩ :: sel :: [])
        (out.write 0 (dentMoveCalldataMem src guy (dentBidWord I) memMap)
          dentMoveOutPtr.toNat (min dentMoveOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k2545 C2545 :=
      haw ▸ rd2545raw
    rw [hmin, byteArray_write_len_zero] at rd2545
    exact rd2545
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := vat)
      (mem := dentMoveCalldataMem src guy (dentBidWord I) memMap)
      (inOff := dentMoveOutPtr) (inSize := dentMoveInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      flopperAddressWord_address_eq_target
      (dentMoveEncode_eq src guy (dentBidWord I) hmemMap hsrcCanon hguyCanon) ?_
    simpa [initState, hperm] using hΘ

theorem flopperDentX_moveCallDepthLimit
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memCaller : ByteArray}
    {k C : ℕ}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flopperAddressReturnWord ⟨2⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2439 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2439⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dentIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let vat := flopperAddressReturnWord ⟨2⟩ σ I
    let guy := flopperAddressReturnWord (auctionPackedSlot id) σ I
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
      (⟨0⟩ :: dentMoveEndPtr :: dentMoveSelectorWord :: vat ::
        dentBidWord I :: dentLotWord I :: id :: ⟨334⟩ :: sel :: [])
      (dentMoveCalldataMem src guy (dentBidWord I) memMap) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  intro id memMap src vat guy
  obtain ⟨_, _, rd2529⟩ :=
    flopperDentX_toMoveExtcodesizeGuard hmemCaller hread64Caller rd2439
  obtain ⟨gasWord, _, _, rd2544⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2529⟩) (okPc := ⟨2541⟩) rd2529
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  obtain ⟨k2545, C2545, rd2545raw⟩ :=
    RD.callDepthLimit rd2544 (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k2545, C2545, ?_⟩
  have hmin : (min dentMoveOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold dentMoveOutSize
    rfl
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        dentMoveOutPtr.toNat dentMoveInSize.toNat)
        dentMoveOutPtr.toNat dentMoveOutSize.toNat) = UInt256.ofNat 8 := by
    unfold dentMoveOutPtr dentMoveInSize dentMoveOutSize
    decide +native
  simpa [dentMoveOutPtr, dentMoveInSize, dentMoveOutSize, hmin,
    byteArray_write_len_zero, haw] using rd2545raw

theorem flopperDentX_moveCallFailure
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd2545 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
      (⟨0⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem aw out (cA', σ') k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2545⟩) (okPc := ⟨2561⟩) rd2545
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    houtSize (by simp)

set_option maxHeartbeats 1000000 in
theorem flopperDentX_moveSuccessTicNonzeroToTail
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hticNe :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I ≠ ⟨0⟩)
    (rd2545 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
      (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C) :
    ∃ (memGuy : ByteArray) (k' C' : ℕ),
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
        [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
        memGuy (UInt256.ofNat 8) out
        (cA', dentRuntimeAfterGuyMap I.codeOwner σ' I) k' C' := by
  let id := dentIdWord I
  let packedSlot := auctionPackedSlot id
  let memTicKey := wordAt0Mem id mem
  let memTic := twoWordHashMem id ⟨1⟩ mem
  let memGuyKey := wordAt0Mem id memTic
  let memGuy := twoWordHashMem id ⟨1⟩ memTic
  let base := solcMappingSlot ⟨1⟩ id
  let oldPacked := solcSlotWord σ' I packedSlot
  let src := UInt256.ofNat I.source.val
  let σGuy := dentRuntimeAfterGuyMap I.codeOwner σ' I
  obtain ⟨_, _, rd2563⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2545⟩) (okPc := ⟨2561⟩) rd2545
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2565 := evm_run rd2563 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rd2569pre := evm_run rd2565 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd2570 := rd2569pre.mstore 0 memTicKey (UInt256.ofNat 8)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by simp [memTicKey, id, wordAt0Mem])
    (by decide +native)
    (by evm_ov)
  have rd2574pre := evm_run rd2570 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd2575 := rd2574pre.mstore 0 memTic (UInt256.ofNat 8)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memTicKey, memTic, id, twoWordHashMem, wordAt32Mem])
    (by decide +native)
    (by evm_ov)
  have rd2578pre := evm_run rd2575 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTic.readWithPadding 0 64))) = base := by
    simpa [base, memTic, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem
  have rd2579pre := rd2578pre.keccak256 0 base (UInt256.ofNat 8)
    (by decide +native)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      decide +native)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by decide +native)
    (by evm_ov)
  have rd2582pre := evm_run rd2579pre with [
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd2582pre
  obtain ⟨k2583, C2583, rd2583raw⟩ := rd2582pre.sload (by decide +native) (by evm_ov)
  have rd2583 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2583⟩
      [oldPacked, flopperAddressReturnWord ⟨2⟩ σ I, dentBidWord I, dentLotWord I,
        id, ⟨334⟩, sel]
      memTic (UInt256.ofNat 8) out (cA', σ') k2583 C2583 := by
    simpa [oldPacked, packedSlot, solcSlotWord] using rd2583raw
  have rd2602pre := evm_run rd2583 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov)]
  have rd2598 := rd2602pre.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by decide +native)
    (by simp)
  have rd2602 := evm_run rd2598 with [
    raw and (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have hticRaw :
      UInt256.land flopperUint48Mask
          (UInt256.div oldPacked (UInt256.ofNat (256 ^ 20))) =
        flopperUint48Offset20Word packedSlot σ' I := by
    rfl
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (UInt256.land flopperUint48Mask
              (UInt256.div oldPacked (UInt256.ofNat (256 ^ 20))))) ≠
        ⟨0⟩ := by
    rw [hticRaw, isZero_eq_zero_of_ne hticNe]
    decide
  have rd2605 := rd2602.push2 ⟨2855⟩ (by decide +native) (by evm_ov)
  have rd2855 := rd2605.jumpiT (by decide +native) hcond (by jump_dest) (by evm_ov)
  have rd2860pre := evm_run rd2855 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd2861 := rd2860pre.mstore 0 memGuyKey (UInt256.ofNat 8)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by simp [memGuyKey, id, wordAt0Mem])
    (by decide +native)
    (by evm_ov)
  have rd2865pre := evm_run rd2861 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd2866 := rd2865pre.mstore 0 memGuy (UInt256.ofNat 8)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memGuyKey, memGuy, id, twoWordHashMem, wordAt32Mem])
    (by decide +native)
    (by evm_ov)
  have rd2869pre := evm_run rd2866 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have hbaseGuy :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memGuy.readWithPadding 0 64))) = base := by
    simpa [base, memGuy, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memTic
  have rd2870pre := rd2869pre.keccak256 0 base (UInt256.ofNat 8)
    (by decide +native)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      decide +native)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbaseGuy)
    (by decide +native)
    (by evm_ov)
  have rd2873pre := evm_run rd2870pre with [
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  rw [hpacked] at rd2873pre
  have rd2874pre := rd2873pre.dup1 (by decide +native) (by evm_ov)
  obtain ⟨k2875, C2875, rd2875raw⟩ := rd2874pre.sload (by decide +native) (by evm_ov)
  have rd2875 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2875⟩
      [oldPacked, packedSlot, dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memGuy (UInt256.ofNat 8) out (cA', σ') k2875 C2875 := by
    simpa [oldPacked, packedSlot, solcSlotWord] using rd2875raw
  have rd2887pre := evm_run rd2875 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw not (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw or (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  obtain ⟨k2889, C2889, rd2889raw⟩ := rd2887pre.sstore hperm
    (by decide +native) (by evm_ov)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    simpa [src, solcSourceWord] using solcSourceWord_canonical I
  have hsrcClean : UInt256.land src solcAddrMask = src := by
    exact solcAddrMask_clean hsrcCanon
  have hstored :
      UInt256.lor src (UInt256.land (UInt256.lnot solcAddrMask) oldPacked) =
        setAddressOffset0Word oldPacked src := by
    calc
      UInt256.lor src (UInt256.land (UInt256.lnot solcAddrMask) oldPacked) =
          UInt256.lor (UInt256.land oldPacked (UInt256.lnot solcAddrMask)) src := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) oldPacked]
            exact u256_lor_comm _ _
      _ = UInt256.lor (UInt256.land oldPacked (UInt256.lnot solcAddrMask))
            (UInt256.land src solcAddrMask) := by
            rw [hsrcClean]
      _ = setAddressOffset0Word oldPacked src := rfl
  have rd2889 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
      [dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memGuy (UInt256.ofNat 8) out (cA', σGuy) k2889 C2889 := by
    simpa [σGuy, dentRuntimeAfterGuyMap, oldPacked, packedSlot, src, hmask, hstored]
      using rd2889raw
  exact ⟨memGuy, _, _, by simpa [id] using rd2889⟩

end Benchmarks.Dss.Flopper
