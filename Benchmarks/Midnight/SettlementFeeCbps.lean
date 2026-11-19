import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ScalarDecode
import Benchmarks.Midnight.SettlementFields
import Benchmarks.Midnight.WordArray
import Benchmarks.Midnight.Allocation
import Benchmarks.Midnight.MappingMemory

/-!
# Midnight `settlementFeeCbps(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 17792; reach lemma `midnightReachSettlementFeeCbpsBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def settlementFeeWords (word : UInt256) : List UInt256 :=
  (List.range 7).map (settlementFeeWord word)

theorem settlementFeeReturnEncoding (word : UInt256) :
    encodeReturnValue? (.array (.elem (.int (.uint ⟨16, by decide⟩))) 7)
      (.array (wordArrayValues (settlementFeeWords word))) =
      some (wordArrayBytes (settlementFeeWords word)) := by
  have h := uintWordArrayReturnEncoding ⟨16, by decide⟩ (settlementFeeWords word) (by
    intro w hw
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
    exact settlementFeeWord_lt word i)
  simpa only [settlementFeeWords, List.length_map, List.length_range] using h

def feePartialMemory (base : ByteArray) (word : UInt256) : ByteArray :=
  writeWordArray base 1056 ((List.range 6).map (settlementFeeWord word))

def feePreparedMemory (base : ByteArray) (id word : UInt256) : ByteArray :=
  writeWord (twoWordHashMem id ⟨1⟩ (feePartialMemory base word)) 1248 (settlementFeeWord word 6)

theorem feePartialMemory_size {base : ByteArray} (word : UInt256) (hsize : base.size = 832) :
    (feePartialMemory base word).size = 1248 := by
  change (writeWordArray base 1056
    [settlementFeeWord word 0, settlementFeeWord word 1, settlementFeeWord word 2,
     settlementFeeWord word 3, settlementFeeWord word 4, settlementFeeWord word 5]).size = _
  simp only [writeWordArray, writeWord_sparse_size, hsize]
  rfl

theorem feePreparedMemory_size {base : ByteArray} (id word : UInt256) (hsize : base.size = 832) :
    (feePreparedMemory base id word).size = 1280 := by
  rw [feePreparedMemory, writeWord_sparse_size, twoWordHashMem_size_of_ge_64 _ _
    (by rw [feePartialMemory_size _ hsize]; decide), feePartialMemory_size _ hsize]
  rfl

theorem feePreparedMemory_freePtr {base : ByteArray} (id word : UInt256)
    (hsize : base.size = 832) (hfp : memLoad (UInt256.ofNat 64) base = ⟨1280⟩) :
    memLoad (UInt256.ofNat 64) (feePreparedMemory base id word) = ⟨1280⟩ := by
  rw [feePreparedMemory, memLoad_writeWord_preserved _ _ _ _
      (by rw [twoWordHashMem_size_of_ge_64 _ _
        (by rw [feePartialMemory_size _ hsize]; decide), feePartialMemory_size _ hsize]; decide)
      (Or.inl (by decide)),
    memLoad_twoWordHashMem _ _ _ (by decide) (by rw [feePartialMemory_size _ hsize]; decide)]
  exact (memLoad_writeWordArray_below base 1056 (UInt256.ofNat 64) _
    (by rw [hsize]; decide) (by decide)).trans hfp

theorem feePreparedMemory_read {base : ByteArray} (id word : UInt256) (hsize : base.size = 832)
    (i : Fin 7) :
    (feePreparedMemory base id word).readWithPadding (1056 + 32 * i.val) 32 =
      (settlementFeeWord word i.val).toByteArray := by
  by_cases hi : i.val < 6
  · rw [feePreparedMemory, writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
      rw [twoWordHashMem_size_of_ge_64 _ _ (by rw [feePartialMemory_size _ hsize]; decide),
        feePartialMemory_size _ hsize]
      omega⟩)]
    rw [twoWordHashMem_read32_above64 _ _ (by omega) (by rw [feePartialMemory_size _ hsize]; omega)]
    have hr := writeWordArray_read_index base 1056
      ((List.range 6).map (settlementFeeWord word)) ⟨i.val, by simpa using hi⟩
    simpa [feePartialMemory] using hr
  · have heq : i.val = 6 := by omega
    rw [heq]
    exact writeWord_sparse_read_back _ _ _

theorem evalSettlementFeeField (evm : EVM.State) (id : UInt256) (i : Fin 7) :
    evalExpr? config (calldataFrame contract ((∅ : Store).insert "id" (wordBytes32Value id)) ∅ evm)
      evm (.storage { base := "marketState", steps := [.mindex (.var "id"),
        .field ("settlementFeeCbp" ++ toString i.val)] }) =
      .ok (.int (Int.ofNat (settlementFeeWord
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ id + ⟨2⟩))
        i.val).toNat)) := by
  apply evalBytes32MappingField (t := .int (.uint ⟨16, by decide⟩))
    (loc := settlementFeeFieldLoc id i) evm id rfl ?_ ?_ ?_
    (by decide) (by decide) (by decide)
  · rw [settlementFeeFieldNames i]
    rcases i with ⟨i, hi⟩
    interval_cases i <;> rfl
  · exact settlementFeeField_layout id i
  · exact settlementFeeField_load evm id i

theorem settlementFeeCbpsBodyReturns (evm : EVM.State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm ((∅ : Store).insert "id" (wordBytes32Value id))
      settlementFeeCbpsTransition.body
      (.returned (calldataFrame contract ((∅ : Store).insert "id" (wordBytes32Value id)) ∅ evm)
        evm (some [.array (wordArrayValues (settlementFeeWords
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ id + ⟨2⟩))))])) := by
  apply guardedReturnBody hwv hhi
  change evalExpr? _ _ _ (.arrayLit _) = _
  rw [evalExpr?]
  have hfields : ∀ is : List Nat, (∀ i ∈ is, i < 7) →
      evalExprList? config
        (calldataFrame contract ((∅ : Store).insert "id" (wordBytes32Value id)) ∅ evm) evm
        (is.map (fun i ↦ .storage { base := "marketState", steps := [.mindex (.var "id"),
          .field ("settlementFeeCbp" ++ toString i)] })) =
        .ok (wordArrayValues (is.map (settlementFeeWord
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ id + ⟨2⟩))))) := by
    intro is hi
    induction is with
    | nil => simp only [List.map_nil, evalExprList?, wordArrayValues, pure]
    | cons i is ih =>
      simp only [List.map_cons, evalExprList?, evalSettlementFeeField evm id ⟨i, hi i List.mem_cons_self⟩,
        ih (fun j hj ↦ hi j (List.mem_cons_of_mem _ hj)), bind, EvalResult.bind, wordArrayValues]
      rfl
  rw [hfields _ (fun _ hi ↦ List.mem_range.mp hi)]
  rfl

theorem settlementFeeCbpsAllocated {σ σ₀ A I} {g : Sat256} {k C : Nat}
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 17810)
      [solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 17843)
      [calldataWord I.calldata 4, ⟨1056⟩, solcSelectorWord I]
      (writeWord (writeWord midnightEntryMemory 64 ⟨1056⟩) 64 ⟨1280⟩)
      aw' ByteArray.empty σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_17810 (by simp) (by jump_dest) rd
  have hfp0 : memLoad (UInt256.ofNat 64) midnightEntryMemory = ⟨832⟩ := midnightEntryMemory_freePtr
  simp only [midnightBlocks.midnight_block_17810_stack, hfp0] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightAllocate (by simp) (by decide +kernel) (by jump_dest) rd1
  have hend : allocationEnd ⟨832⟩ (UInt256.ofNat 224) = ⟨1056⟩ := by decide +kernel
  rw [hend] at rd2
  have rd3 := midnightBlocks.midnight_block_17827 (by simp) (by jump_dest) rd2
  have hm : (writeWord midnightEntryMemory 64 ⟨1056⟩).size = 832 := by
    rw [writeWord_sparse_size, midnightEntryMemory_size]; rfl
  have hzero : I.calldata.write (UInt256.ofNat I.calldata.size).toNat
      (writeWord midnightEntryMemory 64 ⟨1056⟩) (⟨832⟩ : UInt256).toNat
        (UInt256.ofNat 224).toNat = writeWord midnightEntryMemory 64 ⟨1056⟩ := by
    rw [UInt256.toNat_ofNat_of_lt hsize]
    change I.calldata.write I.calldata.size _ 832 224 = _
    rw [← hm]
    exact writePastSourceAtEnd _ _ _
  simp only [midnightBlocks.midnight_block_17827_stack,
    midnightBlocks.midnight_block_17827_memory, hzero] at rd3
  have hfp : memLoad (UInt256.ofNat 64) (writeWord midnightEntryMemory 64 ⟨1056⟩) = ⟨1056⟩ :=
    memLoad_writeWord midnightEntryMemory (UInt256.ofNat 64) ⟨1056⟩
  rw [hfp] at rd3
  obtain ⟨aw4, k4, C4, rd4⟩ := midnightAllocate224 (by simp) (by decide +kernel) (by jump_dest) rd3
  exact ⟨_, _, _, rd4⟩

theorem settlementFeeCbpsPrepared {σ σ₀ A I} {g : Sat256} {k C : Nat}
    {mem : ByteArray} {aw : UInt256} {id : UInt256}
    (hsize : mem.size = 832) (hfp : memLoad (UInt256.ofNat 64) mem = ⟨1280⟩)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 17843)
      [id, ⟨1056⟩, solcSelectorWord I] mem aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 17950)
      [⟨1280⟩, ⟨0⟩, ⟨1056⟩, ⟨1280⟩, solcSelectorWord I]
      (feePreparedMemory (twoWordHashMem id ⟨1⟩ mem) id
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I)) aw' ByteArray.empty σ k' C' := by
  let word := solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) mem) =
      solcMappingSlot ⟨1⟩ id := twoWordHashMem_mapSlot_of_ge64 id _ (by rw [hsize]; decide)
  obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_17843 (by simp) rd
  simp only [midnightBlocks.midnight_block_17843_stack, midnightBlocks.midnight_block_17843_memory,
    show (UInt256.ofNat 32).toNat = 32 from rfl, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    wordAt0_fold, twoWordHash_fold, hh, u256_add_comm (UInt256.ofNat 2),
    u256_land_comm (UInt256.ofNat 65535)] at rd1
  have rd2 := midnightBlocks.midnight_block_17917 (by simp) rd1
  simp only [midnightBlocks.midnight_block_17917_stack, midnightBlocks.midnight_block_17917_memory,
    u256_land_comm (UInt256.ofNat 65535)] at rd2
  let buffer : ByteArray :=
      (UInt256.land (UInt256.shiftRight word (UInt256.ofNat 96)) (UInt256.ofNat 65535)).toByteArray.write 0
        ((UInt256.ofNat 1).toByteArray.write 0
          (id.toByteArray.write 0
            ((settlementFeeWord word 5).toByteArray.write 0
              ((settlementFeeWord word 4).toByteArray.write 0
                ((settlementFeeWord word 3).toByteArray.write 0
                  ((settlementFeeWord word 2).toByteArray.write 0
                    ((settlementFeeWord word 1).toByteArray.write 0
                      ((UInt256.land word (UInt256.ofNat 65535)).toByteArray.write 0
                        (twoWordHashMem id ⟨1⟩ mem) 1056 32) 1088 32) 1120 32) 1152 32)
                1184 32) 1216 32) 0 32) 32 32) 1248 32
  have hmem : buffer =
        feePreparedMemory (twoWordHashMem id ⟨1⟩ mem) id word := by
    dsimp only [buffer]
    rw [← settlementFeeWord_zero word]
    rfl
  change RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 17950)
    [memLoad (UInt256.ofNat 64) buffer, ⟨0⟩, ⟨1056⟩, memLoad (UInt256.ofNat 64) buffer, solcSelectorWord I]
    buffer _ ByteArray.empty σ _ _ at rd2
  rw [hmem] at rd2
  have hs : (twoWordHashMem id ⟨1⟩ mem).size = 832 := by
    rw [twoWordHashMem_size_of_ge_64 _ _ (by rw [hsize]; decide), hsize]
  have hfp' : memLoad (UInt256.ofNat 64) (twoWordHashMem id ⟨1⟩ mem) = ⟨1280⟩ := by
    rw [memLoad_twoWordHashMem _ _ _ (by decide) (by rw [hsize]; decide), hfp]
  rw [feePreparedMemory_freePtr id word hs hfp'] at rd2
  exact ⟨_, _, _, rd2⟩

theorem settlementFeeCopyStep {σ σ₀ A I} {g : Sat256} {k C : Nat}
    {mem : ByteArray} {aw : UInt256} (i : Fin 7) (word : UInt256)
    (hlt : word.toNat < EVM.twoPow 16)
    (hread : memLoad (UInt256.ofNat (1056 + 32 * i.val)) mem = word)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 17950)
      [UInt256.ofNat (1280 + 32 * i.val), UInt256.ofNat i.val,
        UInt256.ofNat (1056 + 32 * i.val), ⟨1280⟩, solcSelectorWord I]
      mem aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 17950)
      [UInt256.ofNat (1280 + 32 * (i.val + 1)), UInt256.ofNat (i.val + 1),
        UInt256.ofNat (1056 + 32 * (i.val + 1)), ⟨1280⟩, solcSelectorWord I]
      (writeWord mem (1280 + 32 * i.val) word) aw' ByteArray.empty σ k' C' := by
  have hiword : i.val < UInt256.size := Nat.lt_trans i.isLt (by decide)
  have hc : UInt256.lt (UInt256.ofNat i.val) (UInt256.ofNat 7) ≠ ⟨0⟩ := by
    rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt hiword]; exact i.isLt)]
    decide
  have rd1 := midnightBlocks.midnight_block_17950_taken (by simp) hc (by jump_dest) rd
  have rd2 := midnightBlocks.midnight_block_17963 (by simp) (by jump_dest) rd1
  have hf : ∀ j : Fin 7,
      UInt256.ofNat (1280 + 32 * j.val) + UInt256.ofNat 32 = UInt256.ofNat (1280 + 32 * (j.val + 1)) ∧
      UInt256.ofNat j.val + UInt256.ofNat 1 = UInt256.ofNat (j.val + 1) ∧
      UInt256.ofNat (1056 + 32 * j.val) + UInt256.ofNat 32 = UInt256.ofNat (1056 + 32 * (j.val + 1)) :=
    by decide +kernel
  simp only [midnightBlocks.midnight_block_17963_stack, midnightBlocks.midnight_block_17963_memory,
    hread, u256LandMaskCleanOfToNat word (UInt256.ofNat 65535) (by decide) hlt,
    (hf i).1, (hf i).2.1, (hf i).2.2,
    UInt256.toNat_ofNat_of_lt (show 1280 + 32 * i.val < UInt256.size from by
      have := i.isLt; change 1280 + 32 * i.val < 2^256; omega)] at rd2
  exact ⟨_, _, _, rd2⟩

def feeCopyMemory (base : ByteArray) (id word : UInt256) (n : Nat) : ByteArray :=
  writeWordArray (feePreparedMemory base id word) 1280
    ((List.range n).map (settlementFeeWord word))

theorem feeCopyMemory_succ (base : ByteArray) (id word : UInt256) (n : Nat) :
    feeCopyMemory base id word (n + 1) =
      writeWord (feeCopyMemory base id word n) (1280 + 32 * n) (settlementFeeWord word n) := by
  simp only [feeCopyMemory, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    writeWordArray_append, List.length_map, List.length_range, writeWordArray]

theorem feeCopyMemory_source {base : ByteArray} (id word : UInt256) (n : Nat)
    (hsize : base.size = 832) (i : Fin 7) :
    memLoad (UInt256.ofNat (1056 + 32 * i.val)) (feeCopyMemory base id word n) =
      settlementFeeWord word i.val := by
  have haddr : 1056 + 32 * i.val < UInt256.size := by
    have := i.isLt
    change 1056 + 32 * i.val < 2^256
    omega
  rw [feeCopyMemory, memLoad_writeWordArray_below _ _ _ _
    (by rw [UInt256.toNat_ofNat_of_lt haddr, feePreparedMemory_size id word hsize]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt haddr]; omega)]
  apply mloadWordValue_of_readWithPadding
  · rw [UInt256.toNat_ofNat_of_lt haddr, feePreparedMemory_size id word hsize]
    omega
  · rw [UInt256.toNat_ofNat_of_lt haddr]
    exact feePreparedMemory_read id word hsize i

theorem settlementFeeCopyLoop {σ σ₀ A I} {g : Sat256} {k C : Nat}
    {base : ByteArray} {aw : UInt256} (id word : UInt256) (hsize : base.size = 832)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 17950)
      [⟨1280⟩, ⟨0⟩, ⟨1056⟩, ⟨1280⟩, solcSelectorWord I]
      (feePreparedMemory base id word) aw ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I) σ (wordArrayBytes (settlementFeeWords word)) := by
  have hloop : ∀ n, n ≤ 7 → ∃ aw' k' C',
      RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 17950)
        [UInt256.ofNat (1280 + 32 * n), UInt256.ofNat n,
          UInt256.ofNat (1056 + 32 * n), ⟨1280⟩, solcSelectorWord I]
        (feeCopyMemory base id word n) aw' ByteArray.empty σ k' C' := by
    intro n
    induction n with
    | zero => intro; exact ⟨_, _, _, rd⟩
    | succ n ih =>
      intro hn
      obtain ⟨aw1, k1, C1, rd1⟩ := ih (by omega)
      obtain ⟨aw2, k2, C2, rd2⟩ := settlementFeeCopyStep ⟨n, by omega⟩ (settlementFeeWord word n)
        (settlementFeeWord_lt word n) (feeCopyMemory_source id word n hsize ⟨n, by omega⟩) rd1
      rw [← feeCopyMemory_succ base id word n] at rd2
      exact ⟨_, _, _, rd2⟩
  obtain ⟨aw7, k7, C7, rd7⟩ := hloop 7 (by decide)
  have rd8 := midnightBlocks.midnight_block_17950_fallthrough (by simp) (by decide +kernel) rd7
  have hr := midnightBlocks.midnight_block_17959 (by simp) rd8
  have hm : (feeCopyMemory base id word 7).readWithPadding 1280 224 =
      wordArrayBytes (settlementFeeWords word) :=
    writeWordArray_read _ _ _ (by rw [feePreparedMemory_size id word hsize])
  exact hm ▸ hr

theorem settlementFeeCbpsTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat}
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 17810)
      [solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I) σ
      (wordArrayBytes (settlementFeeWords
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I))) := by
  obtain ⟨aw1, k1, C1, rd1⟩ := settlementFeeCbpsAllocated hsize rd
  have hm : (writeWord (writeWord midnightEntryMemory 64 ⟨1056⟩) 64 ⟨1280⟩).size = 832 := by
    simp only [writeWord_sparse_size, midnightEntryMemory_size]
    rfl
  obtain ⟨aw2, k2, C2, rd2⟩ := settlementFeeCbpsPrepared hm (memLoad_writeWord _ (UInt256.ofNat 64) _) rd1
  exact settlementFeeCopyLoop _ _
    (by rw [twoWordHashMem_size_of_ge_64 _ _ (by rw [hm]; decide), hm]) rd2

/-- `settlementFeeCbps(bytes32)`: the theorem `Correct.lean` routes selector 3 to. -/
theorem midnightSettlementFeeCbpsBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 3) rfl hsel
  have hd : dispatchMsg contract I.calldata = some settlementFeeCbpsTransition := by
    apply midnightDispatch_settlementFeeCbps <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSettlementFeeCbpsBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_17792_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_17798_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have hret := settlementFeeCbpsTraceReturn hsize rd2
        have hdec := midnightDecodeBytes32 "id" (by decide) (by decide) h36 hhi hsize
        have hbody := settlementFeeCbpsBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (calldataWord I.calldata 4) hwv hhi
        exact hret.reEquivExecution hcode hd hdec hbody
          (returnEquiv_of_encode (settlementFeeReturnEncoding _))
      · have rd2 := midnightBlocks.midnight_block_17798_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 32) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h36) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeScalar_none_short "id" (.bytes abiBytes32Width)
            hsz (Nat.lt_of_not_ge h36) hsize)
    · have rd2 := midnightBlocks.midnight_block_17798_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 32) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeScalar_none_huge "id" (.bytes abiBytes32Width)
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_17792_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (settlementFeeCbpsTransition.params.map Param.name)
        (transitionSignature settlementFeeCbpsTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
