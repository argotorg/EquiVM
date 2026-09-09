import Benchmarks.Dss.Flopper.Deal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! Runtime tail for `deal(uint256)`: the `gem.mint` call and auction delete. -/

theorem flopperDealX_ticLtReadyToMint
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hticLt :
      (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd3966 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3966⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4159⟩
      [dealIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩
        (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := dealIdWord I
  let mem0 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ mem0
  obtain ⟨_, _, rd3966'⟩ := rd3966
  obtain ⟨_, _, rd4000⟩ := flopperDealX_toTicGuard rd3966'
  obtain ⟨_, _, rd4009⟩ :=
    flopperDealX_ticNonzero_toTicLtStart (g := g) htic (by simpa [id, mem0] using rd4000)
  obtain ⟨_, _, rd4045⟩ := flopperDealX_toTicLtGuard rd4009
  have hticLtWord :
      UInt256.lt (flopperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨1⟩ := by
    apply ult_one
    simpa [id] using hticLt
  have rd4049 := evm_run rd4045 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw push2 ⟨4087⟩ (by decide +native) (by evm_ov)]
  have rd4087 := rd4049.jumpiT (by decide +native)
    (by rw [hticLtWord]; exact one_ne_zero_uint) (by jump_dest) (by evm_ov)
  have rd4088 := rd4087.jumpdest (by decide +native) (by evm_ov)
  have rd4091 := rd4088.push2 ⟨4159⟩ (by decide +native) (by evm_ov)
  have rd4159 := rd4091.jumpiT (by decide +native)
    (by rw [hticLtWord]; exact one_ne_zero_uint) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [id, mem0, memTic, hticLtWord] using rd4159⟩

theorem flopperDealX_endLtReadyToMint
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hticGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat)
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd3966 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3966⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4159⟩
      [dealIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (dealIdWord I) ⟨1⟩
        (twoWordHashMem (dealIdWord I) ⟨1⟩
          (twoWordHashMem (dealIdWord I) ⟨1⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := dealIdWord I
  let mem0 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ mem0
  let memEnd := twoWordHashMem id ⟨1⟩ memTic
  obtain ⟨_, _, rd3966'⟩ := rd3966
  obtain ⟨_, _, rd4000⟩ := flopperDealX_toTicGuard rd3966'
  obtain ⟨_, _, rd4009⟩ :=
    flopperDealX_ticNonzero_toTicLtStart (g := g) htic (by simpa [id, mem0] using rd4000)
  obtain ⟨_, _, rd4045⟩ := flopperDealX_toTicLtGuard rd4009
  have hticLtWord :
      UInt256.lt (flopperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ult_zero
    simpa [id] using hticGe
  have rd4049 := evm_run rd4045 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw push2 ⟨4087⟩ (by decide +native) (by evm_ov)]
  have rd4050 := rd4049.jumpiNT (by decide +native) hticLtWord (by evm_ov)
  have rd4051raw := rd4050.pop (by decide +native) (by evm_ov)
  have hpc4051 : (⟨4045⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ =
      ⟨4051⟩ := by
    decide +native
  rw [hpc4051] at rd4051raw
  obtain ⟨_, _, rd4051⟩ : ∃ k C,
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4051⟩
        [id, ⟨334⟩, sel] memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C :=
    ⟨_, _, by simpa [id, memTic, hticLtWord] using rd4051raw⟩
  obtain ⟨_, _, rd4087⟩ := flopperDealX_toEndLtGuard rd4051
  have hendLtWord :
      UInt256.lt (flopperUint48Offset26Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨1⟩ := by
    apply ult_one
    simpa [id] using hendLt
  have rd4088 := rd4087.jumpdest (by decide +native) (by evm_ov)
  have rd4091 := rd4088.push2 ⟨4159⟩ (by decide +native) (by evm_ov)
  have rd4159 := rd4091.jumpiT (by decide +native)
    (by rw [hendLtWord]; exact one_ne_zero_uint) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [id, mem0, memTic, memEnd, hendLtWord] using rd4159⟩

theorem flopperDealX_readyToMint
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hfinished :
      (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd3966 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3966⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ memStart k C,
      memStart.size = 96 ∧
      memStart.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4159⟩
        [dealIdWord I, ⟨334⟩, sel]
        memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := dealIdWord I
  let mem0 := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ mem0
  let memEnd := twoWordHashMem id ⟨1⟩ memTic
  have hmem0 : mem0.size = 96 := by
    simpa [mem0, id] using
      twoWordHashMem_size_96 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
  have hread0 : mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem0, id] using
      twoWordHashMem_read64 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
        solcFreePtrMem_read64
  have hmemTic : memTic.size = 96 := by
    simpa [memTic, id, mem0] using twoWordHashMem_size_96 id ⟨1⟩ hmem0
  have hreadTic : memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memTic, id, mem0] using twoWordHashMem_read64 id ⟨1⟩ hmem0 hread0
  by_cases hticLt :
      (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat
  · obtain ⟨_, _, rd4159⟩ :=
      flopperDealX_ticLtReadyToMint (g := g) htic hticLt rd3966
    exact ⟨memTic, _, _, hmemTic, hreadTic, by simpa [id, mem0, memTic] using rd4159⟩
  · have hendLt :
        (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
          (UInt256.ofNat I.header.timestamp).toNat := by
      cases hfinished with
      | inl h => exact False.elim (hticLt h)
      | inr h => exact h
    have hticGe :
        (UInt256.ofNat I.header.timestamp).toNat ≤
          (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat :=
      Nat.le_of_not_gt hticLt
    have hmemEnd : memEnd.size = 96 := by
      simpa [memEnd, id, memTic] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
    have hreadEnd : memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [memEnd, id, memTic] using
        twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
    obtain ⟨_, _, rd4159⟩ :=
      flopperDealX_endLtReadyToMint (g := g) htic hticGe hendLt rd3966
    exact ⟨memEnd, _, _, hmemEnd, hreadEnd,
      by simpa [id, mem0, memTic, memEnd] using rd4159⟩

set_option maxHeartbeats 1000000 in
theorem flopperDealX_toMintExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (hmemStart : memStart.size = 96)
    (hread64Start : memStart.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd4159 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4159⟩
      [dealIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memStart
    let gem := flopperAddressReturnWord ⟨3⟩ σ I
    let guy := flopperAddressReturnWord (auctionPackedSlot id) σ I
    let lot := flopperSlotWord (auctionLotSlot id) σ I
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4253⟩
      (gem :: gem :: dealMintOutSize :: dealMintOutPtr :: dealMintInSize ::
        dealMintOutPtr :: dealMintOutSize :: dealMintEndPtr :: dealMintSelectorWord ::
        gem :: id :: ⟨334⟩ :: sel :: [])
      (dealMintCalldataMem guy lot memMap) (UInt256.ofNat 7) ByteArray.empty
      (cA, σ) k' C' := by
  intro id memMap gem guy lot
  let base := solcMappingSlot ⟨1⟩ id
  let memKey := wordAt0Mem id memStart
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemStart
  have hread64Map : memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id] using twoWordHashMem_read64 id ⟨1⟩ hmemStart hread64Start
  have hmload64Map :
      (if (⟨64⟩ : UInt256).toNat ≥ memMap.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memMap.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemMap]; decide) (by decide) hread64Map
  have hcallMem : (dealMintCalldataMem guy lot memMap).size = 196 :=
    dealMintCalldataMem_size guy lot hmemMap
  have hcallRead64 :
      (dealMintCalldataMem guy lot memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    dealMintCalldataMem_read64 guy lot hmemMap hread64Map
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (dealMintCalldataMem guy lot memMap).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dealMintCalldataMem guy lot memMap).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd4162pre := evm_run rd4159 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨3⟩ (by decide +native) (by evm_ov)]
  obtain ⟨k4163, C4163, rd4163raw⟩ := rd4162pre.sload (by decide +native) (by evm_ov)
  have rd4163 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4163⟩
      (flopperSlotWord ⟨3⟩ σ I :: id :: ⟨334⟩ :: [sel])
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4163 C4163 := by
    simpa [id, flopperSlotWord] using rd4163raw
  have rd4166pre := evm_run rd4163 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd4167 := rd4166pre.mstore 0 memKey (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by simp [memKey, id, wordAt0Mem])
    (by decide +native)
    (by evm_ov)
  have rd4173pre := evm_run rd4167 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd4174 := rd4173pre.mstore 0 memMap (UInt256.ofNat 3)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by decide +native))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by decide +native)
    (by evm_ov)
  have rd4178pre := evm_run rd4174 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd4179 := rd4178pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd4183pre := evm_run rd4179 with [
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  have hpackedSlot : base + ⟨2⟩ = auctionPackedSlot id := by
    simp [base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd4183pre
  obtain ⟨k4185, C4185, rd4185raw⟩ := rd4183pre.sload (by decide +native) (by evm_ov)
  have rd4185 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4185⟩
      (flopperSlotWord (auctionPackedSlot id) σ I :: base :: ⟨64⟩ :: ⟨1⟩ ::
        ⟨0⟩ :: flopperSlotWord ⟨3⟩ σ I :: id :: ⟨334⟩ :: [sel])
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4185 C4185 := by
    simpa [flopperSlotWord] using rd4185raw
  have rd4186pre := evm_run rd4185 with [
    raw swap3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  have hlotSlot : ⟨1⟩ + base = auctionLotSlot id := by
    rw [u256_add_comm]
    simp [base, auctionLotSlot, auctionBaseSlot_eq, id]
  rw [hlotSlot] at rd4186pre
  obtain ⟨k4188, C4188, rd4188raw⟩ := rd4186pre.sload (by decide +native) (by evm_ov)
  have rd4188 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4188⟩
      (lot :: ⟨64⟩ :: flopperSlotWord (auctionPackedSlot id) σ I :: ⟨0⟩ ::
        flopperSlotWord ⟨3⟩ σ I :: id :: ⟨334⟩ :: [sel])
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4188 C4188 := by
    simpa [lot, flopperSlotWord] using rd4188raw
  have rd4253 := evm_run rd4188 with [
    raw dup2 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64Map (by decide) (by evm_ov),
    raw push4 dealMintSelectorWord (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (dealMintSelectorMem memMap) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (dealMintGuyMem guy memMap) (UInt256.ofNat 6)
      (by decide +native) mem_cost
      (by
        simp [dealMintGuyMem, guy, u256_land_comm,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide,
          show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 from by decide +native])
      (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw mstore 3 (dealMintCalldataMem guy lot memMap) (UInt256.ofNat 7)
      (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push4 dealMintSelectorWord (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 dealMintInSize (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  have hpc4253 :
      (⟨4188⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨4253⟩ := by
    decide +native
  rw [hpc4253] at rd4253
  exact ⟨_, _, by
    simpa [gem, guy, lot, dealMintSelectorMem, dealMintGuyMem, dealMintCalldataMem,
      dealMintSelectorShifted, dealMintOutPtr, dealMintOutSize, dealMintInSize,
      dealMintEndPtr, flopperAddressReturnWord, flopperSlotWord, solcAddrMask,
      u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide +native,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide +native,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + dealMintInSize =
        dealMintInSize from by decide +native,
      show (⟨128⟩ : UInt256) + dealMintInSize = dealMintEndPtr from by decide +native,
      show dealMintInSize + dealMintOutPtr = dealMintEndPtr from by decide +native]
      using rd4253⟩

theorem flopperDealX_mintNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hfinished :
      (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ (flopperAddressReturnWord ⟨3⟩ σ I) =
        ⟨0⟩)
    (rd3966 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3966⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨memStart, _, _, hmemStart, hread64Start, rd4159⟩ :=
    flopperDealX_readyToMint (g := g) htic hfinished rd3966
  obtain ⟨_, _, rd4253⟩ :=
    flopperDealX_toMintExtcodesizeGuard hmemStart hread64Start rd4159
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4253⟩) (okPc := ⟨1160⟩) rd4253
    hnoCode
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp)

theorem flopperDealX_mintCall
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flopperAddressReturnWord ⟨3⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hfinished :
      (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd3966 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3966⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let gem := flopperAddressReturnWord ⟨3⟩ σ I
    let guy := flopperAddressReturnWord (auctionPackedSlot id) σ I
    let lot := flopperSlotWord (auctionLotSlot id) σ I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (memCall : ByteArray) (k' C' : ℕ),
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: dealMintEndPtr :: dealMintSelectorWord ::
          gem :: id :: ⟨334⟩ :: sel :: [])
        memCall (UInt256.ofNat 7) out (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
        (EVM.address (AccountAddress.ofNat gem.toNat)) "mint" 0
        [.address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat lot.toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  intro id gem guy lot
  obtain ⟨memStart, _, _, hmemStart, hread64Start, rd4159⟩ :=
    flopperDealX_readyToMint (g := g) htic hfinished rd3966
  let memMap := twoWordHashMem id ⟨1⟩ memStart
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemStart
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, flopperAddressReturnWord] using
      solcAddrMask_result_canonical (flopperSlotWord (auctionPackedSlot id) σ I)
  obtain ⟨_, _, rd4253⟩ :=
    flopperDealX_toMintExtcodesizeGuard hmemStart hread64Start rd4159
  obtain ⟨gasWord, _, _, rd1163⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4253⟩) (okPc := ⟨1160⟩) rd4253
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k1164, C1164, hΘpack, rd1164raw,
      houtsz⟩ :=
    RD.call rd1163 (by decide +native) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', dealMintCalldataMem guy lot memMap, k1164, C1164,
    ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          dealMintOutPtr.toNat dealMintInSize.toNat)
          dealMintOutPtr.toNat dealMintOutSize.toNat) = UInt256.ofNat 7 := by
      unfold dealMintOutPtr dealMintInSize dealMintOutSize
      decide +native
    have hmin : (min dealMintOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold dealMintOutSize
      rfl
    have rd1164 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: dealMintEndPtr :: dealMintSelectorWord ::
          gem :: id :: ⟨334⟩ :: sel :: [])
        (out.write 0 (dealMintCalldataMem guy lot memMap) dealMintOutPtr.toNat
          (min dealMintOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 7) out (cA', σ') k1164 C1164 :=
      haw ▸ rd1164raw
    rw [hmin, byteArray_write_len_zero] at rd1164
    exact rd1164
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := gem)
      (mem := dealMintCalldataMem guy lot memMap)
      (inOff := dealMintOutPtr) (inSize := dealMintInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      dealAddressWord_address_eq_target
      (dealMintEncode_eq guy lot hmemMap hguyCanon) ?_
    simpa [initState, hperm] using hΘ

theorem flopperDealX_mintCallDepthLimit
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flopperAddressReturnWord ⟨3⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth = 1024)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I ≠ ⟨0⟩)
    (hfinished :
      (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (rd3966 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3966⟩
      [dealIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := dealIdWord I
    let gem := flopperAddressReturnWord ⟨3⟩ σ I
    ∃ memCall k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
      (⟨0⟩ :: dealMintEndPtr :: dealMintSelectorWord :: gem ::
        id :: ⟨334⟩ :: sel :: [])
      memCall (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
  intro id gem
  obtain ⟨memStart, _, _, hmemStart, hread64Start, rd4159⟩ :=
    flopperDealX_readyToMint (g := g) htic hfinished rd3966
  let memMap := twoWordHashMem id ⟨1⟩ memStart
  let guy := flopperAddressReturnWord (auctionPackedSlot id) σ I
  let lot := flopperSlotWord (auctionLotSlot id) σ I
  obtain ⟨_, _, rd4253⟩ :=
    flopperDealX_toMintExtcodesizeGuard hmemStart hread64Start rd4159
  obtain ⟨gasWord, _, _, rd1163⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4253⟩) (okPc := ⟨1160⟩) rd4253
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  obtain ⟨k1164, C1164, rd1164raw⟩ :=
    RD.callDepthLimit rd1163 (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨dealMintCalldataMem guy lot memMap, k1164, C1164, ?_⟩
  have hmin : (min dealMintOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold dealMintOutSize
    rfl
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
        dealMintOutPtr.toNat dealMintInSize.toNat)
        dealMintOutPtr.toNat dealMintOutSize.toNat) = UInt256.ofNat 7 := by
    unfold dealMintOutPtr dealMintInSize dealMintOutSize
    decide +native
  simpa [gem, guy, lot, memMap, dealMintOutPtr, dealMintInSize, dealMintOutSize, hmin,
    byteArray_write_len_zero, haw] using rd1164raw

theorem flopperDealX_mintCallFailure
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (rd1164 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
      (⟨0⟩ :: dealMintEndPtr :: dealMintSelectorWord ::
        flopperAddressReturnWord ⟨3⟩ σ I :: dealIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 7) out (cA', σ') k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1164⟩) (okPc := ⟨1180⟩) rd1164
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    houtSize (by simp)

theorem flopperDealX_mintCallSuccessDelete
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel status : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hstatus : status ≠ ⟨0⟩)
    (rd1164 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
      (status :: dealMintEndPtr :: dealMintSelectorWord ::
        flopperAddressReturnWord ⟨3⟩ σ I :: dealIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 7) out (cA', σ') k C) :
    RDret flopperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', auctionRuntimeDeleteAccountMap I.codeOwner (dealIdWord I) σ')
      ByteArray.empty := by
  have rd1165 := rd1164.iszero (by decide +native) (by evm_ov)
  have rd1166 := rd1165.dup1 (by decide +native) (by evm_ov)
  have rd1167 := rd1166.iszero (by decide +native) (by evm_ov)
  have rd1170 := rd1167.push2 ⟨1180⟩ (by decide +native) (by evm_ov)
  have hcond : UInt256.isZero (UInt256.isZero status) ≠ ⟨0⟩ := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hstatus]
    decide
  have rd1180 := rd1170.jumpiT (by decide +native) hcond (by jump_dest) (by evm_ov)
  simpa [auctionRuntimeDeleteAccountMap] using
    RD.flopperAuctionDeleteTail hperm
      (by decide +native) (by decide +native) (by decide +native) (by simp) rd1180

theorem flopperDealBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨804⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I ≠ ⟨1⟩ := by
    intro hone
    exact hlive (by
      have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
      rw [hword, hone])
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperDealBodyReverts_notLive evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
  exact (flopperDealX_notLive (g := Sat256.ofUInt256 g) hlive
      (flopperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperDealBodyCoreTicZero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨804⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hticSolm : dealTicWord evmSolm I = ⟨0⟩ := by
    have hword :=
      flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (dealIdWord I))
    simpa [evmSolm, initState, dealTicWord] using (hword ▸ htic)
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperDealBodyReverts_ticZero evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        hticSolm
  obtain ⟨_, _, rd3966⟩ :=
    flopperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
      (flopperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  exact (flopperDealX_ticZero (g := Sat256.ofUInt256 g) htic ⟨_, _, rd3966⟩)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperDealBodyCoreNotFinished
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat)
    (hendGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨804⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hticGeSolm : (dealTimestampWord evmSolm).toNat ≤ (dealTicWord evmSolm I).toNat := by
    simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using hticGe
  have hendGeSolm : (dealTimestampWord evmSolm).toNat ≤ (dealEndWord evmSolm I).toNat := by
    simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using hendGe
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperDealBodyReverts_notFinished evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord hticSolm hticGeSolm hendGeSolm
  obtain ⟨_, _, rd3966⟩ :=
    flopperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
      (flopperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  exact (flopperDealX_notFinished (g := Sat256.ofUInt256 g) htic hticGe hendGe
      ⟨_, _, rd3966⟩)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperDealBodyCoreMintNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hfinished :
      (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨3⟩ σ_evm I) = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨804⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hfinishedSolm :
      (dealTicWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat ∨
      (dealEndWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat := by
    cases hfinished with
    | inl h =>
        left
        simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using h
    | inr h =>
        right
        simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using h
  have hnoCodeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨3⟩ σ_solm I) = ⟨0⟩ :=
    flopperCodeSize_zero_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hnoCode
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperDealBodyReverts_mintNoCode evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord hticSolm hfinishedSolm
        (by simpa [evmSolm, initState] using hnoCodeSolm)
  obtain ⟨_, _, rd3966⟩ :=
    flopperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
      (flopperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  exact (flopperDealX_mintNoCode (g := Sat256.ofUInt256 g) htic hfinished hnoCode
      ⟨_, _, rd3966⟩)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperDealBodyCoreMintCallFailure
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (_hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hfinished :
      (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨3⟩ σ_evm I) ≠ ⟨0⟩)
    (rd1164 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1164⟩
      (⟨0⟩ :: dealMintEndPtr :: dealMintSelectorWord ::
        flopperAddressReturnWord ⟨3⟩ σ_evm I :: dealIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 7) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨3⟩ σ_evm I).toNat))
        "mint" 0
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (houtSize : out.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hpostAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  have hgemEq :
      flopperAddressReturnWord ⟨3⟩ σ_evm I =
        flopperAddressReturnWord ⟨3⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨3⟩
  have hguyEq :
      flopperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_evm I =
        flopperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts (auctionPackedSlot (dealIdWord I))
  have hlotEq :
      flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I =
        flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_solm I :=
    flopperSlotWord_accountMapEquiv hAccounts (auctionLotSlot (dealIdWord I))
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨3⟩ σ_solm I).toNat))
        "mint" 0
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_solm I).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_solm I).toNat)]
        (false, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, hgemEq, hguyEq, hlotEq] using hcallSolmRaw
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hfinishedSolm :
      (dealTicWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat ∨
      (dealEndWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat := by
    cases hfinished with
    | inl h =>
        left
        simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using h
    | inr h =>
        right
        simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using h
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨3⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, evmCallSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperDealBodyReverts_mintCallFailure evmSolm evmCallSolm I out
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord hticSolm hfinishedSolm
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  exact (flopperDealX_mintCallFailure rd1164 houtSize)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperDealBodyCoreMintCallDepthLimit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hfinished :
      (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨3⟩ σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨804⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := dealIdWord I
  let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let gem := flopperAddressReturnWord ⟨3⟩ σ_solm I
  let guy := flopperAddressReturnWord (auctionPackedSlot id) σ_solm I
  let lot := flopperSlotWord (auctionLotSlot id) σ_solm I
  let A_mint := (evmSolm.addAccessedAccount (EVM.address (AccountAddress.ofNat gem.toNat))).substate
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using
      twoWordHashMem_size_96 (dealIdWord I) ⟨1⟩ solcFreePtrMem_size
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, flopperAddressReturnWord] using
      solcAddrMask_result_canonical (flopperSlotWord (auctionPackedSlot id) σ_solm I)
  have hdepthInit : evmSolm.executionEnv.depth = 1024 := by
    simpa [evmSolm, initState] using hdepth
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat gem.toNat)) "mint" 0
        [.address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat lot.toNat)]
        (false, { evmSolm with substate := A_mint }, ByteArray.empty) true := by
    simpa [A_mint] using
      (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
        (tgt := EVM.address (AccountAddress.ofNat gem.toNat)) (name := "mint")
        (args := [.address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat lot.toNat)])
        (callPerm := true)
        (calldata := (dealMintCalldataMem guy lot memMap).readWithPadding
          dealMintOutPtr.toNat dealMintInSize.toNat)
        (dealMintEncode_eq guy lot hmemMap hguyCanon)
        hdepthInit)
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hfinishedSolm :
      (dealTicWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat ∨
      (dealEndWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat := by
    cases hfinished with
    | inl h =>
        left
        simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using h
    | inr h =>
        right
        simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using h
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨3⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body .reverted := by
    simpa [evmSolm, gem, guy, lot, id, flopperSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      flopperDealBodyReverts_mintCallFailure evmSolm
        { evmSolm with substate := A_mint } I ByteArray.empty
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord hticSolm hfinishedSolm
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  obtain ⟨_, _, rd3966⟩ :=
    flopperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
      (flopperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  obtain ⟨_, _, _, rd1164⟩ :=
    flopperDealX_mintCallDepthLimit (g := Sat256.ofUInt256 g) hcodeSize hdepth htic
      hfinished ⟨_, _, rd3966⟩
  exact (flopperDealX_mintCallFailure rd1164 (by decide +native))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperDealBodyCoreMintCallSuccess
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (_hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hfinished :
      (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat ∨
      (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨3⟩ σ_evm I) ≠ ⟨0⟩)
    (rd1164 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1164⟩
      (⟨1⟩ :: dealMintEndPtr :: dealMintSelectorWord ::
        flopperAddressReturnWord ⟨3⟩ σ_evm I :: dealIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 7) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨3⟩ σ_evm I).toNat))
        "mint" 0
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
        (transitionSignature dealTransition).paramTypes I.calldata = some (dealLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostCallAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  have hgemEq :
      flopperAddressReturnWord ⟨3⟩ σ_evm I =
        flopperAddressReturnWord ⟨3⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨3⟩
  have hguyEq :
      flopperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_evm I =
        flopperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts (auctionPackedSlot (dealIdWord I))
  have hlotEq :
      flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I =
        flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_solm I :=
    flopperSlotWord_accountMapEquiv hAccounts (auctionLotSlot (dealIdWord I))
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨3⟩ σ_solm I).toNat))
        "mint" 0
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dealIdWord I)) σ_solm I).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_solm I).toNat)]
        (true, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, hgemEq, hguyEq, hlotEq] using hcallSolmRaw
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hticEq :=
    flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hendEq :=
    flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (dealIdWord I))
  have hticSolm : dealTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    exact htic (by rw [hticEq]; simpa [evmSolm, initState, dealTicWord] using hzero)
  have hfinishedSolm :
      (dealTicWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat ∨
      (dealEndWord evmSolm I).toNat < (dealTimestampWord evmSolm).toNat := by
    cases hfinished with
    | inl h =>
        left
        simpa [evmSolm, initState, dealTicWord, dealTimestampWord, hticEq] using h
    | inr h =>
        right
        simpa [evmSolm, initState, dealEndWord, dealTimestampWord, hendEq] using h
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨3⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (dealLocals I)
        dealTransition.body
        (.returned { contract := contract, locals := dealMintLocals I }
          (auctionDeletePostState (dealIdWord I) evmCallSolm) none) := by
    simpa [evmSolm, evmCallSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperDealBodyReturns_mintCallSuccess evmSolm evmCallSolm I out
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord hticSolm hfinishedSolm
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  have hret :=
    flopperDealX_mintCallSuccessDelete
      (g := Sat256.ofUInt256 g) (σ := σ_evm) (sel := sel) hperm
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) rd1164
  have hRuntimeDeleteEquiv :
      accountMapEquiv (auctionRuntimeDeleteAccountMap I.codeOwner (dealIdWord I) σ')
        (auctionRuntimeDeleteAccountMap I.codeOwner (dealIdWord I) σ'_solm) := by
    unfold auctionRuntimeDeleteAccountMap
    exact accountMapEquiv_sstoreAccountMap_three I.codeOwner I.codeOwner I.codeOwner
      (auctionBidSlot (dealIdWord I)) ⟨0⟩
      (auctionLotSlot (dealIdWord I)) ⟨0⟩
      (auctionPackedSlot (dealIdWord I)) ⟨0⟩
      hpostCallAccounts
  have hDeleteSolm :
      accountMapEquiv (auctionRuntimeDeleteAccountMap I.codeOwner (dealIdWord I) σ'_solm)
        (auctionDeletePostState (dealIdWord I) evmCallSolm).accountMap := by
    simpa [evmCallSolm] using
      auctionDeletePostState_accountMapEquiv (dealIdWord I) evmCallSolm I.codeOwner
        (by simp [evmCallSolm, evmSolm, initState])
  have hFinalAccounts :
      accountMapEquiv (auctionRuntimeDeleteAccountMap I.codeOwner (dealIdWord I) σ')
        (auctionDeletePostState (dealIdWord I) evmCallSolm).accountMap :=
    accountMapEquiv.trans hRuntimeDeleteEquiv hDeleteSolm
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by
      simp [auctionDeletePostState, auctionDeleteAfterTic, auctionDeleteAfterGuy,
        auctionDeleteAfterLot, auctionDeleteAfterBid, evmCallSolm, evmSolm, initState,
        storageStore_createdAccounts])
    (by simpa using hFinalAccounts)
    (by
      simpa [dealTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by decide +native) (by decide +native)))

theorem flopperDealBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some dealTransition)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨804⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flopperDealX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flopperDecode_deal_none_short hsz4 hshort)

theorem flopperDealBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flopperDispatchDeal hsel
  have hreach := flopperReachDealBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := flopperDecode_deal_ok (I := I) hsz36
    by_cases hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩
    · by_cases hticZero :
          flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I = ⟨0⟩
      · exact flopperDealBodyCoreTicZero hcode hsize hwv hsz36 hlive hticZero
          hdispatch hdecode hreach hAccounts
      · have htic :
            flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I ≠ ⟨0⟩ :=
          hticZero
        by_cases hticLt :
            (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
              (UInt256.ofNat I.header.timestamp).toNat
        · let hfinished :
              (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
                (UInt256.ofNat I.header.timestamp).toNat ∨
              (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
                (UInt256.ofNat I.header.timestamp).toNat := Or.inl hticLt
          by_cases hcodeSize :
              Reasoning.Theory.extCodeSizeWord σ_evm
                (flopperAddressReturnWord ⟨3⟩ σ_evm I) = ⟨0⟩
          · exact flopperDealBodyCoreMintNoCode hcode hsize hwv hsz36 hlive htic
              hfinished hcodeSize hdispatch hdecode hreach hAccounts
          · by_cases hdepthEq : I.depth = 1024
            · exact flopperDealBodyCoreMintCallDepthLimit hcode hsize hwv hsz36 hlive
                htic hfinished hcodeSize hdepthEq hdispatch hdecode hreach hAccounts
            · have hdepthLt : I.depth.val < 1024 := by
                have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                by_contra hn
                have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hn
                have hval : I.depth.val = 1024 := by omega
                apply hdepthEq
                apply Fin.ext
                exact hval
              obtain ⟨_, _, rd3966⟩ :=
                flopperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
                  (flopperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
              obtain ⟨cA', σ', z, out, A', memCall, k1164, C1164, rd1164, hcall,
                  houtSize⟩ :=
                flopperDealX_mintCall (g := Sat256.ofUInt256 g) hperm hcodeSize
                  hdepthLt htic hfinished ⟨_, _, rd3966⟩
              by_cases hz : z = true
              · have rd1164True : RD flopperBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1164⟩
                    (⟨1⟩ :: dealMintEndPtr :: dealMintSelectorWord ::
                      flopperAddressReturnWord ⟨3⟩ σ_evm I ::
                      dealIdWord I :: ⟨334⟩ :: flopperSelWord I :: [])
                    memCall (UInt256.ofNat 7) out (cA', σ') k1164 C1164 := by
                  simpa [hz] using rd1164
                have hcallTrue :
                    typedCallViaEVM config
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (EVM.address (AccountAddress.ofNat
                        (flopperAddressReturnWord ⟨3⟩ σ_evm I).toNat))
                      "mint" 0
                      [.address (AccountAddress.ofNat
                        (flopperAddressReturnWord (auctionPackedSlot (dealIdWord I))
                          σ_evm I).toNat),
                      .int (Int.ofNat
                        (flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
                      (true,
                        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                            accountMap := σ', substate := A', createdAccounts := cA' },
                        out) true := by
                  simpa [hz] using hcall
                exact flopperDealBodyCoreMintCallSuccess hcode hsize hperm hwv hsz36
                  hlive htic hfinished hcodeSize rd1164True hcallTrue hdispatch hdecode hAccounts
              · have hzFalse : z = false := Bool.eq_false_iff.mpr hz
                have rd1164False : RD flopperBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1164⟩
                    (⟨0⟩ :: dealMintEndPtr :: dealMintSelectorWord ::
                      flopperAddressReturnWord ⟨3⟩ σ_evm I ::
                      dealIdWord I :: ⟨334⟩ :: flopperSelWord I :: [])
                    memCall (UInt256.ofNat 7) out (cA', σ') k1164 C1164 := by
                  simpa [hzFalse] using rd1164
                have hcallFalse :
                    typedCallViaEVM config
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (EVM.address (AccountAddress.ofNat
                        (flopperAddressReturnWord ⟨3⟩ σ_evm I).toNat))
                      "mint" 0
                      [.address (AccountAddress.ofNat
                        (flopperAddressReturnWord (auctionPackedSlot (dealIdWord I))
                          σ_evm I).toNat),
                      .int (Int.ofNat
                        (flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
                      (false,
                        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                            accountMap := σ', substate := A', createdAccounts := cA' },
                        out) true := by
                  simpa [hzFalse] using hcall
                exact flopperDealBodyCoreMintCallFailure hcode hsize hwv hsz36 hlive
                  htic hfinished hcodeSize rd1164False hcallFalse houtSize hdispatch hdecode
                  hAccounts
        · have hticGe :
              (UInt256.ofNat I.header.timestamp).toNat ≤
                (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat :=
            Nat.le_of_not_gt hticLt
          by_cases hendLt :
              (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
                (UInt256.ofNat I.header.timestamp).toNat
          · let hfinished :
                (flopperUint48Offset20Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
                  (UInt256.ofNat I.header.timestamp).toNat ∨
                (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat <
                  (UInt256.ofNat I.header.timestamp).toNat := Or.inr hendLt
            by_cases hcodeSize :
                Reasoning.Theory.extCodeSizeWord σ_evm
                  (flopperAddressReturnWord ⟨3⟩ σ_evm I) = ⟨0⟩
            · exact flopperDealBodyCoreMintNoCode hcode hsize hwv hsz36 hlive htic
                hfinished hcodeSize hdispatch hdecode hreach hAccounts
            · by_cases hdepthEq : I.depth = 1024
              · exact flopperDealBodyCoreMintCallDepthLimit hcode hsize hwv hsz36 hlive
                  htic hfinished hcodeSize hdepthEq hdispatch hdecode hreach hAccounts
              · have hdepthLt : I.depth.val < 1024 := by
                  have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                  by_contra hn
                  have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hn
                  have hval : I.depth.val = 1024 := by omega
                  apply hdepthEq
                  apply Fin.ext
                  exact hval
                obtain ⟨_, _, rd3966⟩ :=
                  flopperDealX_liveOk (g := Sat256.ofUInt256 g) hlive
                    (flopperDealX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
                obtain ⟨cA', σ', z, out, A', memCall, k1164, C1164, rd1164, hcall,
                    houtSize⟩ :=
                  flopperDealX_mintCall (g := Sat256.ofUInt256 g) hperm hcodeSize
                    hdepthLt htic hfinished ⟨_, _, rd3966⟩
                by_cases hz : z = true
                · have rd1164True : RD flopperBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1164⟩
                      (⟨1⟩ :: dealMintEndPtr :: dealMintSelectorWord ::
                        flopperAddressReturnWord ⟨3⟩ σ_evm I ::
                        dealIdWord I :: ⟨334⟩ :: flopperSelWord I :: [])
                      memCall (UInt256.ofNat 7) out (cA', σ') k1164 C1164 := by
                    simpa [hz] using rd1164
                  have hcallTrue :
                      typedCallViaEVM config
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (EVM.address (AccountAddress.ofNat
                          (flopperAddressReturnWord ⟨3⟩ σ_evm I).toNat))
                        "mint" 0
                        [.address (AccountAddress.ofNat
                          (flopperAddressReturnWord (auctionPackedSlot (dealIdWord I))
                            σ_evm I).toNat),
                        .int (Int.ofNat
                          (flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
                        (true,
                          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                              accountMap := σ', substate := A', createdAccounts := cA' },
                          out) true := by
                    simpa [hz] using hcall
                  exact flopperDealBodyCoreMintCallSuccess hcode hsize hperm hwv hsz36
                    hlive htic hfinished hcodeSize rd1164True hcallTrue hdispatch hdecode
                    hAccounts
                · have hzFalse : z = false := Bool.eq_false_iff.mpr hz
                  have rd1164False : RD flopperBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1164⟩
                      (⟨0⟩ :: dealMintEndPtr :: dealMintSelectorWord ::
                        flopperAddressReturnWord ⟨3⟩ σ_evm I ::
                        dealIdWord I :: ⟨334⟩ :: flopperSelWord I :: [])
                      memCall (UInt256.ofNat 7) out (cA', σ') k1164 C1164 := by
                    simpa [hzFalse] using rd1164
                  have hcallFalse :
                      typedCallViaEVM config
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (EVM.address (AccountAddress.ofNat
                          (flopperAddressReturnWord ⟨3⟩ σ_evm I).toNat))
                        "mint" 0
                        [.address (AccountAddress.ofNat
                          (flopperAddressReturnWord (auctionPackedSlot (dealIdWord I))
                            σ_evm I).toNat),
                        .int (Int.ofNat
                          (flopperSlotWord (auctionLotSlot (dealIdWord I)) σ_evm I).toNat)]
                        (false,
                          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                              accountMap := σ', substate := A', createdAccounts := cA' },
                          out) true := by
                    simpa [hzFalse] using hcall
                  exact flopperDealBodyCoreMintCallFailure hcode hsize hwv hsz36 hlive
                    htic hfinished hcodeSize rd1164False hcallFalse houtSize hdispatch hdecode
                    hAccounts
          · have hendGe :
                (UInt256.ofNat I.header.timestamp).toNat ≤
                  (flopperUint48Offset26Word (auctionPackedSlot (dealIdWord I)) σ_evm I).toNat :=
              Nat.le_of_not_gt hendLt
            exact flopperDealBodyCoreNotFinished hcode hsize hwv hsz36 hlive htic
              hticGe hendGe hdispatch hdecode hreach hAccounts
    · exact flopperDealBodyCoreNotLive hcode hsize hwv hsz36 hlive
        hdispatch hdecode hreach hAccounts
  · exact flopperDealBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flopper
