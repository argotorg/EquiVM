import Benchmarks.Dss.Flopper.Dent.Part6

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper
set_option maxHeartbeats 1000000 in
theorem flopperDentX_successFromAddOkAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd2932 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2932⟩
      [dentRuntimeTicAddWord I.codeOwner τ I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 8) retData
      (cAcur, dentRuntimeAfterLotMap I.codeOwner τ I) k C) :
    RDret flopperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cAcur, dentRuntimeTailSuccessAccountMap I.codeOwner τ I) ByteArray.empty := by
  let id := dentIdWord I
  let σLot := dentRuntimeAfterLotMap I.codeOwner τ I
  let addWord := dentRuntimeTicAddWord I.codeOwner τ I
  let memStore := twoWordHashMem id ⟨1⟩ memStart
  let base := solcMappingSlot ⟨1⟩ id
  let packedSlot := auctionPackedSlot id
  let oldPacked := solcSlotWord σLot I packedSlot
  let σSuccess := dentRuntimeTailSuccessAccountMap I.codeOwner τ I
  let memKey := wordAt0Mem id memStart
  have rd2937pre := evm_run rd2932 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd2938 := rd2937pre.mstore 0 memKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2942pre := evm_run rd2938 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2943 := rd2942pre.mstore 0 memStore (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2947pre := evm_run rd2943 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memStore.readWithPadding 0 64))) = base := by
    simpa [base, memStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2948pre := rd2947pre.keccak256 0 base (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd2951pre := evm_run rd2948pre with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : (⟨2⟩ : UInt256) + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd2951pre
  have rd2952pre := rd2951pre.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k2953, C2953, rd2953raw⟩ := rd2952pre.sload (by native_decide) (by evm_ov)
  have rd2953 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2953⟩
      [oldPacked, packedSlot, dentBidWord I, dentLotWord I, addWord, ⟨334⟩, sel]
      memStore (UInt256.ofNat 8) retData (cAcur, σLot) k2953 C2953 := by
    simpa [oldPacked, packedSlot, solcSlotWord, addWord, σLot] using rd2953raw
  have rd2960 := rd2953.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd2970pre := evm_run rd2960 with [
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov)]
  have rd2977 := rd2970pre.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd2990pre := evm_run rd2977 with [
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  obtain ⟨k2991, C2991, rd2991raw⟩ := rd2990pre.sstore hperm
    (by native_decide) (by evm_ov)
  have hstoredRaw :
      UInt256.lor
          (UInt256.land oldPacked
            (UInt256.lnot (UInt256.shiftLeft flopperUint48Mask ⟨160⟩)))
          (UInt256.mul (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
            (UInt256.land flopperUint48Mask addWord)) =
        setUint48Offset20Word oldPacked addWord := by
    simpa [setUint48Offset20RawWord] using
      setUint48Offset20RawWord_eq_setUint48Offset20Word oldPacked addWord
  rw [hstoredRaw] at rd2991raw
  have rd2991 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2991⟩
      [dentLotWord I, dentBidWord I, ⟨334⟩, sel]
      memStore (UInt256.ofNat 8) retData (cAcur, σSuccess) k2991 C2991 := by
    simpa [σSuccess, dentRuntimeTailSuccessAccountMap, dentRuntimeTicStoredWord,
      σLot, oldPacked, packedSlot, addWord, id] using rd2991raw
  have rd2993 := evm_run rd2991 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd334 := rd2993.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd335 := rd334.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd335 (by native_decide) (by evm_ov)

theorem flopperDentX_addOverflowFromTailAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner τ I).toNat)
    (rd2889 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 8) retData (cAcur, τ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4740⟩ := flopperDentX_toCheckedAddStartFromTailAw8 hperm rd2889
  exact flopperDentX_addOverflowFromCheckedAddAw8 haddOverflow rd4740

theorem flopperDentX_successFromTailAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner τ I).toNat < 2 ^ 48)
    (rd2889 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 8) retData (cAcur, τ) k C) :
    RDret flopperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cAcur, dentRuntimeTailSuccessAccountMap I.codeOwner τ I) ByteArray.empty := by
  obtain ⟨_, _, rd4740⟩ := flopperDentX_toCheckedAddStartFromTailAw8 hperm rd2889
  obtain ⟨_, _, rd2932⟩ := flopperDentX_addOkFromCheckedAddAw8 haddFit rd4740
  exact flopperDentX_successFromAddOkAw8 hperm rd2932

theorem flopperDentX_toEndGtGuardFromDecoded
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hdecoded : ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (memEnd : ByteArray) (k C : ℕ),
      memEnd.size = 96 ∧
      memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2001⟩
        [UInt256.gt (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I)
          (UInt256.ofNat I.header.timestamp),
          dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
        memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := dentIdWord I
  cases hticOk with
  | inl hticGt =>
      let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
      let memTic := twoWordHashMem id ⟨1⟩ memGuy
      let memEnd := twoWordHashMem id ⟨1⟩ memTic
      have hmemGuy : memGuy.size = 96 := by
        simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
      have hreadGuy : memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memGuy, id] using
          twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
      have hmemTic : memTic.size = 96 := by
        simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
      have hreadTic : memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memTic, memGuy, id] using
          twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
      have hmemEnd : memEnd.size = 96 := by
        simpa [memEnd, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
      have hreadEnd : memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memEnd, memTic, id] using
          twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
      obtain ⟨_, _, rd1964⟩ := flopperDentX_ticGtOk (g := g) hlive hguy hticGt hdecoded
      obtain ⟨_, _, rd2001⟩ := flopperDentX_toEndGtGuard rd1964
      exact ⟨memEnd, _, _, hmemEnd, hreadEnd, by simpa [memEnd, id] using rd2001⟩
  | inr hticZero =>
      let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
      let memTic := twoWordHashMem id ⟨1⟩ memGuy
      let memTicZero := twoWordHashMem id ⟨1⟩ memTic
      let memEnd := twoWordHashMem id ⟨1⟩ memTicZero
      have hmemGuy : memGuy.size = 96 := by
        simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
      have hreadGuy : memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memGuy, id] using
          twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
      have hmemTic : memTic.size = 96 := by
        simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
      have hreadTic : memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memTic, memGuy, id] using
          twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
      have hmemTicZero : memTicZero.size = 96 := by
        simpa [memTicZero, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
      have hreadTicZero :
          memTicZero.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memTicZero, memTic, id] using
          twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
      have hmemEnd : memEnd.size = 96 := by
        simpa [memEnd, memTicZero, id] using
          twoWordHashMem_size_96 id ⟨1⟩ hmemTicZero
      have hreadEnd : memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memEnd, memTicZero, id] using
          twoWordHashMem_read64 id ⟨1⟩ hmemTicZero hreadTicZero
      obtain ⟨_, _, rd1964⟩ :=
        flopperDentX_ticZeroOk (g := g) hlive hguy hticZero hdecoded
      obtain ⟨_, _, rd2001⟩ := flopperDentX_toEndGtGuard rd1964
      exact ⟨memEnd, _, _, hmemEnd, hreadEnd, by simpa [memEnd, id] using rd2001⟩

theorem flopperDentX_toBidEqGuardFromDecoded
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hdecoded : ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (memBid : ByteArray) (k C : ℕ),
      memBid.size = 96 ∧
      memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2099⟩
        [UInt256.eq (dentBidWord I)
          (flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I),
          dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
        memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨memEnd, _, _, hmemEnd, hreadEnd, rd2001⟩ :=
    flopperDentX_toEndGtGuardFromDecoded hlive hguy hticOk hdecoded
  obtain ⟨_, _, rd2081⟩ := flopperDentX_endOkFromGuard hendGt rd2001
  let memBid := twoWordHashMem (dentIdWord I) ⟨1⟩ memEnd
  have hmemBid : memBid.size = 96 := by
    simpa [memBid] using twoWordHashMem_size_96 (dentIdWord I) ⟨1⟩ hmemEnd
  have hreadBid : memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memBid] using twoWordHashMem_read64 (dentIdWord I) ⟨1⟩ hmemEnd hreadEnd
  obtain ⟨_, _, rd2099⟩ := flopperDentX_toBidEqGuard rd2081
  exact ⟨memBid, _, _, hmemBid, hreadBid, by simpa [memBid] using rd2099⟩

theorem flopperDentX_toLotLtGuardFromDecoded
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I)
    (hdecoded : ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (memLot : ByteArray) (k C : ℕ),
      memLot.size = 96 ∧
      memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2201⟩
        [UInt256.lt (dentLotWord I)
          (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I),
          dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
        memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨memBid, _, _, hmemBid, hreadBid, rd2099⟩ :=
    flopperDentX_toBidEqGuardFromDecoded hlive hguy hticOk hendGt hdecoded
  obtain ⟨_, _, rd2179⟩ := flopperDentX_bidOkFromGuard hbid rd2099
  let memLot := twoWordHashMem (dentIdWord I) ⟨1⟩ memBid
  have hmemLot : memLot.size = 96 := by
    simpa [memLot] using twoWordHashMem_size_96 (dentIdWord I) ⟨1⟩ hmemBid
  have hreadLot : memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memLot] using twoWordHashMem_read64 (dentIdWord I) ⟨1⟩ hmemBid hreadBid
  obtain ⟨_, _, rd2201⟩ := flopperDentX_toLotLtGuard rd2179
  exact ⟨memLot, _, _, hmemLot, hreadLot, by simpa [memLot] using rd2201⟩

theorem flopperDentX_toLotLowerOkFromDecoded
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hdecoded : ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (memLot : ByteArray) (k C : ℕ),
      memLot.size = 96 ∧
      memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2273⟩
        [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
        memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨memLot, _, _, hmemLot, hreadLot, rd2201⟩ :=
    flopperDentX_toLotLtGuardFromDecoded hlive hguy hticOk hendGt hbid hdecoded
  obtain ⟨_, _, rd2273⟩ := flopperDentX_lotLowerOkFromGuard hlotLt rd2201
  exact ⟨memLot, _, _, hmemLot, hreadLot, rd2273⟩

theorem flopperDentX_toLotOneOkFromDecoded
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hdecoded : ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (memLotOne : ByteArray) (k C : ℕ),
      memLotOne.size = 96 ∧
      memLotOne.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2310⟩
        [dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
          dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
        memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨memLot, _, _, hmemLot, hreadLot, rd2273⟩ :=
    flopperDentX_toLotLowerOkFromDecoded hlive hguy hticOk hendGt hbid hlotLt hdecoded
  obtain ⟨_, _, rd2310⟩ := flopperDentX_lotOneOk hlotOneFit rd2273
  let memLotOne := twoWordHashMem (dentIdWord I) ⟨1⟩ memLot
  have hmemLotOne : memLotOne.size = 96 := by
    simpa [memLotOne] using twoWordHashMem_size_96 (dentIdWord I) ⟨1⟩ hmemLot
  have hreadLotOne : memLotOne.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memLotOne] using twoWordHashMem_read64 (dentIdWord I) ⟨1⟩ hmemLot hreadLot
  exact ⟨memLotOne, _, _, hmemLotOne, hreadLotOne, by simpa [memLotOne] using rd2310⟩

theorem flopperDentX_toBegLotOkFromDecoded
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hdecoded : ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (memLotOne : ByteArray) (k C : ℕ),
      memLotOne.size = 96 ∧
      memLotOne.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2322⟩
        [dentBegLotWord (initState cA gh bl σ σ₀ g A I) I,
          dentLotOneWord (initState cA gh bl σ σ₀ g A I) I,
          dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
        memLotOne (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨memLotOne, _, _, hmemLotOne, hreadLotOne, rd2310⟩ :=
    flopperDentX_toLotOneOkFromDecoded hlive hguy hticOk hendGt hbid hlotLt
      hlotOneFit hdecoded
  obtain ⟨_, _, rd2322⟩ := flopperDentX_begLotOk hbegFit rd2310
  exact ⟨memLotOne, _, _, hmemLotOne, hreadLotOne, rd2322⟩

theorem flopperDentBodyCoreMoveNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {memStart : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (rd2405 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2405⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hmemStart : memStart.size = 96)
    (hread64Start : memStart.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flopperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    have hword := flopperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hnoCodeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) = ⟨0⟩ :=
    flopperCodeSize_zero_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hnoCode
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_moveNoCode evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hnoCodeSolm)
  obtain ⟨_, _, rd2435⟩ := flopperDentX_toCallerEqGuard rd2405
  let memCaller := twoWordHashMem (dentIdWord I) ⟨1⟩ memStart
  have hmemCaller : memCaller.size = 96 := by
    simpa [memCaller] using twoWordHashMem_size_96 (dentIdWord I) ⟨1⟩ hmemStart
  have hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memCaller] using
      twoWordHashMem_read64 (dentIdWord I) ⟨1⟩ hmemStart hread64Start
  obtain ⟨_, _, rd2439⟩ := flopperDentX_callerNeToMove hcaller rd2435
  have hrev :=
    flopperDentX_moveNoCode
      (g := Sat256.ofUInt256 g) hmemCaller hread64Caller hnoCode rd2439
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreMoveCallFailure
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (rd2545 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2545⟩
      (⟨0⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ_evm I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem aw out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (houtSize : out.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hpostAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flopperAddressReturnWord packedSlot σ_evm I =
        flopperAddressReturnWord packedSlot σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts packedSlot
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address evmSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord packedSlot σ_solm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (false, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, packedSlot, hvatEq, hguyEq, hsrcEq] using
      hcallSolmRaw
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_moveCallFailure evmSolm evmCallSolm I out
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hcodeSizeSolm)
      hcallSolm
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody
    (flopperDentX_moveCallFailure rd2545 houtSize)

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreMoveCallDepthLimit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {memStart : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (rd2405 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2405⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hmemStart : memStart.size = 96)
    (hread64Start : memStart.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let id := dentIdWord I
  let memCaller := twoWordHashMem id ⟨1⟩ memStart
  let memMap := twoWordHashMem id ⟨1⟩ memCaller
  let src := UInt256.ofNat I.source.val
  let vat := flopperAddressReturnWord ⟨2⟩ σ_evm I
  let guy := flopperAddressReturnWord (auctionPackedSlot id) σ_evm I
  let A_move := (evmEvm.addAccessedAccount (EVM.address (AccountAddress.ofNat vat.toNat))).substate
  have hmemCaller : memCaller.size = 96 := by
    simpa [memCaller, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemStart
  have hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memCaller, id] using twoWordHashMem_read64 id ⟨1⟩ hmemStart hread64Start
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, memCaller, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    simpa [src, solcSourceWord] using solcSourceWord_canonical I
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, flopperAddressReturnWord] using
      solcAddrMask_result_canonical (flopperSlotWord (auctionPackedSlot id) σ_evm I)
  have hdepthInit : evmEvm.executionEnv.depth = 1024 := by
    simpa [evmEvm, initState] using hdepth
  have hcallEvm :
      typedCallViaEVM config evmEvm
        (EVM.address (AccountAddress.ofNat vat.toNat)) "move" 0
        [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat guy.toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (false, { evmEvm with substate := A_move }, ByteArray.empty) true := by
    simpa [A_move] using
      (callNotMade_depthLimit (cfg := config) (evm := evmEvm)
        (tgt := EVM.address (AccountAddress.ofNat vat.toNat)) (name := "move")
        (args := [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat guy.toNat),
          .int (Int.ofNat (dentBidWord I).toNat)])
        (callPerm := true)
        (calldata := (dentMoveCalldataMem src guy (dentBidWord I) memMap).readWithPadding
          dentMoveOutPtr.toNat dentMoveInSize.toNat)
        (dentMoveEncode_eq src guy (dentBidWord I) hmemMap hsrcCanon hguyCanon)
        hdepthInit)
  obtain ⟨_, _, rd2435⟩ := flopperDentX_toCallerEqGuard rd2405
  obtain ⟨_, _, rd2439⟩ := flopperDentX_callerNeToMove hcaller rd2435
  obtain ⟨_, _, rd2545⟩ :=
    flopperDentX_moveCallDepthLimit (g := Sat256.ofUInt256 g) hcodeSize hdepth
      hmemCaller hread64Caller rd2439
  exact flopperDentBodyCoreMoveCallFailure
    (cA' := cA) (σ' := σ_evm) (A' := A_move) (out := ByteArray.empty)
    hcode hwv hlive hguy hticOk hendGt hbid hlotLt hbegFit hlotOneFit hsuff
    hcaller hcodeSize rd2545
    (by simpa [evmEvm, A_move, initState] using hcallEvm)
    (by native_decide) hdispatch hdecode hAccounts

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreAshNoCodeMoveCallerNeTicZero
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hticMove :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashNoCode :
      Reasoning.Theory.extCodeSizeWord σ'
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I) = ⟨0⟩)
    (rd2545 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2545⟩
      (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ_evm I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccountsCall⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flopperAddressReturnWord packedSlot σ_evm I =
        flopperAddressReturnWord packedSlot σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts packedSlot
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address evmSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord packedSlot σ_solm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, packedSlot, hvatEq, hguyEq, hsrcEq] using
      hcallSolmRaw
  have hcallEnv : evmCallSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallSolm
    simpa [evmSolm, initState] using h
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hticMoveSolm : dentTicWord evmCallSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I)
      hpostAccountsCall packedSlot
    simpa [evmCallSolm, dentTicWord, packedSlot, hcallEnv, hword] using hticMove
  have hashNoCodeSolm :
      Reasoning.Theory.extCodeSizeWord evmCallSolm.accountMap
        (dentGuyWord evmCallSolm I) = ⟨0⟩ := by
    have hzero :=
      flopperCodeSize_zero_accountMapEquiv_addressSlot
        hpostAccountsCall packedSlot hashNoCode
    simpa [evmCallSolm, dentGuyWord, packedSlot, hcallEnv] using hzero
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_ashNoCode_moveCallerNe_ticZero
      evmSolm evmCallSolm I out
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hcodeSizeSolm)
      hcallSolm hticMoveSolm hashNoCodeSolm
  have hrev :=
    flopperDentX_moveSuccessTicZeroAshNoCode
      (g := Sat256.ofUInt256 g) hmem hread64 hticMove hashNoCode rd2545
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreAshCallFailureMoveCallerNeTicZero
    {cA cA' cAAsh gh bl σ_evm σ_solm σ' σAsh σ₀ A A' AAsh I}
    {g : UInt256} {sel : UInt256} {memAsh outMove outAsh : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hticMove :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd2690 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2690⟩
      (⟨0⟩ :: dentAshEndPtr :: dentAshSelectorWord ::
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I :: ⟨0⟩ ::
        dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ :: sel :: [])
      memAsh aw outAsh (cAAsh, σAsh) k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          outMove) true)
    (hashCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
        "Ash" 0 []
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σAsh, substate := AAsh, createdAccounts := cAAsh },
          outAsh) true)
    (houtAshSize : outAsh.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmCallEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ', substate := A', createdAccounts := cA' }
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccountsCall⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flopperAddressReturnWord packedSlot σ_evm I =
        flopperAddressReturnWord packedSlot σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts packedSlot
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address evmSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord packedSlot σ_solm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallSolm, outMove) true := by
    simpa [evmSolm, evmCallSolm, packedSlot, hvatEq, hguyEq, hsrcEq] using
      hcallSolmRaw
  have hcallEnv : evmCallSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallSolm
    simpa [evmSolm, initState] using h
  let evmCallSolmBase : EVM.State := { evmCallSolm with substate := A' }
  have hcallAshCreated :
      evmCallSolmBase.createdAccounts = evmCallEvm.createdAccounts := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm]
  have hcallAshEnv : evmCallSolmBase.executionEnv = evmCallEvm.executionEnv := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm, evmSolm, initState, hcallEnv]
  obtain ⟨σAshSolm, AAshSolm0, hcallAshSolmBase, _hpostAshAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmCallSolmBase)
      hashCall
      (by simpa [evmCallEvm, evmCallSolmBase, evmCallSolm] using hpostAccountsCall)
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      hcallAshCreated
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallSolmBase])
      hcallAshEnv
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepth
    norm_num at hdepth
  have hdepthNeBase : evmCallSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmCallSolmBase, evmCallSolm, evmSolm, initState, hcallEnv] using hdepthNeI
  obtain ⟨AAshSolm, hcallAshSolmRaw⟩ :=
    dentTypedCallViaEVM_zero_setSubstate hcallAshSolmBase hdepthNeBase
      evmCallSolm.substate
  let evmAshSolm : EVM.State :=
    { evmCallSolm with
        accountMap := σAshSolm, substate := AAshSolm, createdAccounts := cAAsh }
  have hguyMoveEq :
      flopperAddressReturnWord packedSlot σ' I =
        flopperAddressReturnWord packedSlot σ'_solm I :=
    flopperAddressReturnWord_accountMapEquiv hpostAccountsCall packedSlot
  have hcallAshSolm :
      typedCallViaEVM config evmCallSolm
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmCallSolm I).toNat)) "Ash" 0 []
        (false, evmAshSolm, outAsh) true := by
    simpa [evmAshSolm, evmCallSolmBase, evmCallSolm, dentGuyWord, packedSlot, hcallEnv,
      hguyMoveEq] using hcallAshSolmRaw
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hticMoveSolm : dentTicWord evmCallSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I)
      hpostAccountsCall packedSlot
    simpa [evmCallSolm, dentTicWord, packedSlot, hcallEnv, hword] using hticMove
  have hashCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord evmCallSolm.accountMap
        (dentGuyWord evmCallSolm I) ≠ ⟨0⟩ := by
    have hne :=
      flopperCodeSize_ne_accountMapEquiv_addressSlot
        hpostAccountsCall packedSlot hashCodeSize
    simpa [evmCallSolm, dentGuyWord, packedSlot, hcallEnv] using hne
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_ashCallFailure_moveCallerNe_ticZero
      evmSolm evmCallSolm evmAshSolm I outMove outAsh
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hcodeSizeSolm)
      hcallSolm hticMoveSolm hashCodeSizeSolm hcallAshSolm
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody
    (flopperDentX_ashCallFailure rd2690 houtAshSize)

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreAshDecodeShortMoveCallerNeTicZero
    {cA cA' cAAsh gh bl σ_evm σ_solm σ' σAsh σ₀ A A' AAsh I}
    {g : UInt256} {sel : UInt256} {memAsh outMove outAsh : ByteArray}
    {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hticMove :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd2690 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2690⟩
      (⟨1⟩ :: dentAshEndPtr :: dentAshSelectorWord ::
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I :: ⟨0⟩ ::
        dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ :: sel :: [])
      memAsh (UInt256.ofNat 8) outAsh (cAAsh, σAsh) k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          outMove) true)
    (hashCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
        "Ash" 0 []
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σAsh, substate := AAsh, createdAccounts := cAAsh },
          outAsh) true)
    (hashShort : outAsh.size < 32)
    (houtAshSize : outAsh.size < UInt256.size)
    (hmem64 : 64 < memAsh.size)
    (hread64 : memAsh.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmCallEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ', substate := A', createdAccounts := cA' }
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccountsCall⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flopperAddressReturnWord packedSlot σ_evm I =
        flopperAddressReturnWord packedSlot σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts packedSlot
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address evmSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord packedSlot σ_solm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallSolm, outMove) true := by
    simpa [evmSolm, evmCallSolm, packedSlot, hvatEq, hguyEq, hsrcEq] using
      hcallSolmRaw
  have hcallEnv : evmCallSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallSolm
    simpa [evmSolm, initState] using h
  let evmCallSolmBase : EVM.State := { evmCallSolm with substate := A' }
  have hcallAshCreated :
      evmCallSolmBase.createdAccounts = evmCallEvm.createdAccounts := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm]
  have hcallAshEnv : evmCallSolmBase.executionEnv = evmCallEvm.executionEnv := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm, evmSolm, initState, hcallEnv]
  obtain ⟨σAshSolm, AAshSolm0, hcallAshSolmBase, _hpostAshAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmCallSolmBase)
      hashCall
      (by simpa [evmCallEvm, evmCallSolmBase, evmCallSolm] using hpostAccountsCall)
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      hcallAshCreated
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallSolmBase])
      hcallAshEnv
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepth
    norm_num at hdepth
  have hdepthNeBase : evmCallSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmCallSolmBase, evmCallSolm, evmSolm, initState, hcallEnv] using hdepthNeI
  obtain ⟨AAshSolm, hcallAshSolmRaw⟩ :=
    dentTypedCallViaEVM_zero_setSubstate hcallAshSolmBase hdepthNeBase
      evmCallSolm.substate
  let evmAshSolm : EVM.State :=
    { evmCallSolm with
        accountMap := σAshSolm, substate := AAshSolm, createdAccounts := cAAsh }
  have hguyMoveEq :
      flopperAddressReturnWord packedSlot σ' I =
        flopperAddressReturnWord packedSlot σ'_solm I :=
    flopperAddressReturnWord_accountMapEquiv hpostAccountsCall packedSlot
  have hcallAshSolm :
      typedCallViaEVM config evmCallSolm
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmCallSolm I).toNat)) "Ash" 0 []
        (true, evmAshSolm, outAsh) true := by
    simpa [evmAshSolm, evmCallSolmBase, evmCallSolm, dentGuyWord, packedSlot, hcallEnv,
      hguyMoveEq] using hcallAshSolmRaw
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hticMoveSolm : dentTicWord evmCallSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I)
      hpostAccountsCall packedSlot
    simpa [evmCallSolm, dentTicWord, packedSlot, hcallEnv, hword] using hticMove
  have hashCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord evmCallSolm.accountMap
        (dentGuyWord evmCallSolm I) ≠ ⟨0⟩ := by
    have hne :=
      flopperCodeSize_ne_accountMapEquiv_addressSlot
        hpostAccountsCall packedSlot hashCodeSize
    simpa [evmCallSolm, dentGuyWord, packedSlot, hcallEnv] using hne
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_ashDecodeShort_moveCallerNe_ticZero
      evmSolm evmCallSolm evmAshSolm I outMove outAsh
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hcodeSizeSolm)
      hcallSolm hticMoveSolm hashCodeSizeSolm hcallAshSolm hashShort
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody
    (flopperDentX_ashCallSuccessDecodeShort hashShort houtAshSize hmem64 hread64 rd2690)

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreKissNoCodeMoveCallerNeTicZero
    {cA cA' cAAsh gh bl σ_evm σ_solm σ' σAsh σ₀ A A' AAsh I}
    {g : UInt256} {sel : UInt256} {memAsh outMove outAsh : ByteArray}
    {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hticMove :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩)
    (hkissNoCode :
      Reasoning.Theory.extCodeSizeWord σAsh
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σAsh I) = ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd2690 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2690⟩
      (⟨1⟩ :: dentAshEndPtr :: dentAshSelectorWord ::
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I :: ⟨0⟩ ::
        dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ :: sel :: [])
      memAsh (UInt256.ofNat 8) outAsh (cAAsh, σAsh) k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          outMove) true)
    (hashCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
        "Ash" 0 []
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σAsh, substate := AAsh, createdAccounts := cAAsh },
          outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (houtAshSize : outAsh.size < UInt256.size)
    (hmem64 : 64 < memAsh.size)
    (hread64 : memAsh.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hmem128 : 128 < memAsh.size)
    (hread128 : memAsh.readWithPadding dentAshOutPtr.toNat 32 = outAsh.extract 0 32)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmCallEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ', substate := A', createdAccounts := cA' }
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccountsCall⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flopperAddressReturnWord packedSlot σ_evm I =
        flopperAddressReturnWord packedSlot σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts packedSlot
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address evmSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord packedSlot σ_solm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallSolm, outMove) true := by
    simpa [evmSolm, evmCallSolm, packedSlot, hvatEq, hguyEq, hsrcEq] using
      hcallSolmRaw
  have hcallEnv : evmCallSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallSolm
    simpa [evmSolm, initState] using h
  let evmCallSolmBase : EVM.State := { evmCallSolm with substate := A' }
  have hcallAshCreated :
      evmCallSolmBase.createdAccounts = evmCallEvm.createdAccounts := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm]
  have hcallAshEnv : evmCallSolmBase.executionEnv = evmCallEvm.executionEnv := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm, evmSolm, initState, hcallEnv]
  obtain ⟨σAshSolm, AAshSolm0, hcallAshSolmBase, hpostAshAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmCallSolmBase)
      hashCall
      (by simpa [evmCallEvm, evmCallSolmBase, evmCallSolm] using hpostAccountsCall)
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      hcallAshCreated
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallSolmBase])
      hcallAshEnv
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepth
    norm_num at hdepth
  have hdepthNeBase : evmCallSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmCallSolmBase, evmCallSolm, evmSolm, initState, hcallEnv] using hdepthNeI
  obtain ⟨AAshSolm, hcallAshSolmRaw⟩ :=
    dentTypedCallViaEVM_zero_setSubstate hcallAshSolmBase hdepthNeBase
      evmCallSolm.substate
  let evmAshSolm : EVM.State :=
    { evmCallSolm with
        accountMap := σAshSolm, substate := AAshSolm, createdAccounts := cAAsh }
  have hguyMoveEq :
      flopperAddressReturnWord packedSlot σ' I =
        flopperAddressReturnWord packedSlot σ'_solm I :=
    flopperAddressReturnWord_accountMapEquiv hpostAccountsCall packedSlot
  have hcallAshSolm :
      typedCallViaEVM config evmCallSolm
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmCallSolm I).toNat)) "Ash" 0 []
        (true, evmAshSolm, outAsh) true := by
    simpa [evmAshSolm, evmCallSolmBase, evmCallSolm, dentGuyWord, packedSlot, hcallEnv,
      hguyMoveEq] using hcallAshSolmRaw
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hticMoveSolm : dentTicWord evmCallSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I)
      hpostAccountsCall packedSlot
    simpa [evmCallSolm, dentTicWord, packedSlot, hcallEnv, hword] using hticMove
  have hashCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord evmCallSolm.accountMap
        (dentGuyWord evmCallSolm I) ≠ ⟨0⟩ := by
    have hne :=
      flopperCodeSize_ne_accountMapEquiv_addressSlot
        hpostAccountsCall packedSlot hashCodeSize
    simpa [evmCallSolm, dentGuyWord, packedSlot, hcallEnv] using hne
  have hkissNoCodeSolm :
      Reasoning.Theory.extCodeSizeWord evmAshSolm.accountMap
        (dentGuyWord evmAshSolm I) = ⟨0⟩ := by
    have hzero :=
      flopperCodeSize_zero_accountMapEquiv_addressSlot
        hpostAshAccounts packedSlot hkissNoCode
    simpa [evmAshSolm, dentGuyWord, packedSlot, hcallEnv] using hzero
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_kissNoCode_moveCallerNe_ticZero
      evmSolm evmCallSolm evmAshSolm I outMove outAsh
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hcodeSizeSolm)
      hcallSolm hticMoveSolm hashCodeSizeSolm hcallAshSolm houtAsh32 hkissNoCodeSolm
  obtain ⟨_, _, rd2731⟩ :=
    flopperDentX_ashCallSuccessDecodeOk houtAsh32 houtAshSize hmem64 hread64
      hmem128 hread128 rd2690
  obtain ⟨_, _, rd2817⟩ :=
    flopperDentX_ashDecodeOkToKissExtcodesizeGuard hmem128 hread64 rd2731
  have hrev := flopperDentX_kissNoCode hkissNoCode rd2817
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

end Benchmarks.Dss.Flopper
