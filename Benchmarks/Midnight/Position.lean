import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.PairDecode
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.PositionStorage
import Benchmarks.Midnight.NestedStorage
import Benchmarks.Midnight.WordTuple

/-!
# Midnight `position(bytes32,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9045; reach lemma `midnightReachPositionBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def positionTupleArguments (id user : UInt256) : Store :=
  nestedMappingArguments (wordBytes32Value id) (.address (AccountAddress.ofNat user.toNat))

def positionReturnWords (load : UInt256 → UInt256) (id user : UInt256) : List UInt256 :=
  [UInt256.land (load (positionSlot id user)) (UInt256.ofNat (2^128 - 1)),
   UInt256.shiftRight (load (positionSlot id user)) (UInt256.ofNat 128),
   UInt256.land (load (positionSlot id user + ⟨1⟩)) (UInt256.ofNat (2^128 - 1)),
   UInt256.shiftRight (load (positionSlot id user + ⟨1⟩)) (UInt256.ofNat 128),
   UInt256.land (load (positionSlot id user + ⟨2⟩)) (UInt256.ofNat (2^128 - 1)),
   UInt256.shiftRight (load (positionSlot id user + ⟨2⟩)) (UInt256.ofNat 128)]

theorem positionReturnEncoding (load : UInt256 → UInt256) (id user : UInt256) :
    encodeReturnValues? positionTransition.returnType
      (wordArrayValues (positionReturnWords load id user)) =
        some (wordArrayBytes (positionReturnWords load id user)) := by
  apply uintWordTupleReturnEncoding
    ((positionReturnWords load id user).map (fun w ↦ (⟨128, by decide⟩, w)))
  intro entry he
  simp only [positionReturnWords, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only [Prod.fst, Prod.snd] <;>
    first | exact u256LandMaskToNatLtOfToNat _ _ (by decide) | exact shiftRight128_lt _

theorem positionBodyReturns (evm : EVM.State) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm (positionTupleArguments id user)
      positionTransition.body
      (.returned (calldataFrame contract (positionTupleArguments id user) ∅ evm) evm
        (some (wordArrayValues (positionReturnWords
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner) id user)))) := by
  apply guardedReturnsBody hwv hhi
  have hbase : (calldataFrame contract (positionTupleArguments id user) ∅ evm).locals.get?
      "position" = none := by simp [calldataFrame, positionTupleArguments, nestedMappingArguments]
  have hid := calldataNestedArg0 contract (wordBytes32Value id)
    (.address (AccountAddress.ofNat user.toNat)) evm
  have huser := calldataNestedArg1 contract (wordBytes32Value id)
    (.address (AccountAddress.ofNat user.toNat)) evm
  have h0 : evalExpr? config (calldataFrame contract (positionTupleArguments id user) ∅ evm) evm
      (.storage { base := "position", steps :=
        [.mindex (.var "arg0"), .mindex (.var "arg1"), .field "credit"] }) =
      .ok (.int (Int.ofNat (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id user)) (UInt256.ofNat (2^128 - 1))).toNat)) := by
    apply evalNestedBytes32AddressField
      (loc := {
        slot := positionSlot id user, offset := 0, size := 16,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      evm id user hbase hid huser rfl rfl ?_ ?_
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot
          (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
          (keyValueToWord (.address (AccountAddress.ofNat user.toNat))),
        offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
        keyValueToWord_address_of_canonical user hcanon]
      rfl
    · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)
  have h1 : evalExpr? config (calldataFrame contract (positionTupleArguments id user) ∅ evm) evm
      (.storage { base := "position", steps :=
        [.mindex (.var "arg0"), .mindex (.var "arg1"), .field "pendingFee"] }) =
      .ok (.int (Int.ofNat (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id user)) (UInt256.ofNat 128)).toNat)) := by
    apply evalNestedBytes32AddressField
      (loc := {
        slot := positionSlot id user, offset := 16, size := 16,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      evm id user hbase hid huser rfl rfl ?_ ?_
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot
          (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
          (keyValueToWord (.address (AccountAddress.ofNat user.toNat))),
        offset := 16, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
        keyValueToWord_address_of_canonical user hcanon]
      rfl
    · exact storageLocLoad_uint128_high evm _
  have h2 : evalExpr? config (calldataFrame contract (positionTupleArguments id user) ∅ evm) evm
      (.storage { base := "position", steps :=
        [.mindex (.var "arg0"), .mindex (.var "arg1"), .field "lastLossFactor"] }) =
      .ok (.int (Int.ofNat (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id user + ⟨1⟩)) (UInt256.ofNat (2^128 - 1))).toNat)) := by
    apply evalNestedBytes32AddressField
      (loc := {
        slot := positionSlot id user + ⟨1⟩, offset := 0, size := 16,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      evm id user hbase hid huser rfl rfl ?_ ?_
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot
          (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
          (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨1⟩,
        offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
        keyValueToWord_address_of_canonical user hcanon]
      rfl
    · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)
  have h3 : evalExpr? config (calldataFrame contract (positionTupleArguments id user) ∅ evm) evm
      (.storage { base := "position", steps :=
        [.mindex (.var "arg0"), .mindex (.var "arg1"), .field "lastAccrual"] }) =
      .ok (.int (Int.ofNat (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id user + ⟨1⟩)) (UInt256.ofNat 128)).toNat)) := by
    apply evalNestedBytes32AddressField
      (loc := {
        slot := positionSlot id user + ⟨1⟩, offset := 16, size := 16,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      evm id user hbase hid huser rfl rfl ?_ ?_
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot
          (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
          (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨1⟩,
        offset := 16, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
        keyValueToWord_address_of_canonical user hcanon]
      rfl
    · exact storageLocLoad_uint128_high evm _
  have h4 : evalExpr? config (calldataFrame contract (positionTupleArguments id user) ∅ evm) evm
      (.storage { base := "position", steps :=
        [.mindex (.var "arg0"), .mindex (.var "arg1"), .field "debt"] }) =
      .ok (.int (Int.ofNat (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id user + ⟨2⟩)) (UInt256.ofNat (2^128 - 1))).toNat)) := by
    apply evalNestedBytes32AddressField
      (loc := {
        slot := positionSlot id user + ⟨2⟩, offset := 0, size := 16,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      evm id user hbase hid huser rfl rfl ?_ ?_
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot
          (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
          (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨2⟩,
        offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
        keyValueToWord_address_of_canonical user hcanon]
      rfl
    · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)
  have h5 : evalExpr? config (calldataFrame contract (positionTupleArguments id user) ∅ evm) evm
      (.storage { base := "position", steps :=
        [.mindex (.var "arg0"), .mindex (.var "arg1"), .field "collateralBitmap"] }) =
      .ok (.int (Int.ofNat (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id user + ⟨2⟩)) (UInt256.ofNat 128)).toNat)) := by
    apply evalNestedBytes32AddressField
      (loc := {
        slot := positionSlot id user + ⟨2⟩, offset := 16, size := 16,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      evm id user hbase hid huser rfl rfl ?_ ?_
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot
          (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
          (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨2⟩,
        offset := 16, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
        keyValueToWord_address_of_canonical user hcanon]
      rfl
    · exact storageLocLoad_uint128_high evm _
  change evalExprs? config (calldataFrame contract (positionTupleArguments id user) ∅ evm) evm
    _ = .ok _
  simp only [evalExprs?, h0, h1, h2, h3, h4, h5, bind, pure, EvalResult.bind,
    positionReturnWords, wordArrayValues, List.map_cons, List.map_nil]

theorem positionTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {user : UInt256}
    (hcanon : user.toNat < EVM.addressModulus)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 9070)
      [user, solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I) σ
      (wordArrayBytes (positionReturnWords (fun slot ↦ solcSlotWordAt slot σ I)
        (calldataWord I.calldata 4) user)) := by
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_9070_packed (by simp) rd
  simp only [midnightBlocks.midnight_block_9070_stack,
    midnightBlocks.midnight_block_9070_memory, addressMask_computed, uint128Mask_computed,
    solcAddrMask_clean hcanon, midnightEntryMemory_zero] at rd1
  simp only [show (UInt256.ofNat 32).toNat = 32 from rfl,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, wordAt0_fold, midnightWordAt0_zero,
    twoWordHash_fold, mappingMemory_fold, mappingMemory_zero, mappingMemory_hash,
    nestedMappingMemory_fold, nestedMappingMemory_hash, nestedMappingMemory_freePtr] at rd1
  have hr := midnightBlocks.midnight_block_9160 (by simp) rd1
  simp only [uint128Mask_computed] at hr
  change RDret _ _ _ _
    ((writeWordArray (nestedMappingMemory (calldataWord I.calldata 4) user ⟨0⟩) 832
      (positionReturnWords (fun slot ↦ solcSlotWordAt slot σ I)
        (calldataWord I.calldata 4) user)).readWithPadding 832 192) at hr
  rw [show 192 = 32 * (positionReturnWords (fun slot ↦ solcSlotWordAt slot σ I)
      (calldataWord I.calldata 4) user).length from rfl,
    writeWordArray_read _ _ _ (by rw [nestedMappingMemory_size])] at hr
  exact hr

/-- `position(bytes32,address)`: the theorem `Correct.lean` routes selector 27 to. -/
theorem midnightPositionBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 27)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 27) rfl hsel
  have hd : dispatchMsg contract I.calldata = some positionTransition := by
    apply midnightDispatch_position <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachPositionBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_9045_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h68 : 68 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_9051_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 64) h68 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_9063 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_9063_stack] at rd3
        by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress36_ok (by simp) (by jump_dest) hcanon rd3
          have hret := positionTraceReturn hcanon rd4
          have hdec := midnightDecodeBytes32Address "arg0" "arg1"
            (by decide) (by decide) (by decide) (by decide) h68 hhi hsize hcanon
          have hbody := positionBodyReturns
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (calldataWord I.calldata 4) (calldataWord I.calldata 36) hcanon hwv hhi
          exact hret.reEquivExecution hcode hd hdec hbody
            (returnEquiv.returned rfl (positionReturnEncoding _ _ _))
        · have hr := midnightAddress36_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeBytes32Address_none_noncanon "arg0" "arg1" h68 hhi hsize hcanon)
      · have rd2 := midnightBlocks.midnight_block_9051_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 64) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h68) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodePair_none_short "arg0" "arg1" (.bytes abiBytes32Width) .address
            hsz (Nat.lt_of_not_ge h68) hsize)
    · have rd2 := midnightBlocks.midnight_block_9051_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 64) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodePair_none_huge "arg0" "arg1" (.bytes abiBytes32Width) .address
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_9045_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (positionTransition.params.map Param.name)
        (transitionSignature positionTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)




end Benchmarks.Midnight
