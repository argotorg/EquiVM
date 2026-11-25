import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ScalarDecode
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.PackedFields
import Benchmarks.Midnight.WordTuple

variable {fork : Ethereum.Fork}

/-!
# Midnight `marketState(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2117; reach lemma `midnightReachMarketStateBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def marketStateReturnEntries (load : UInt256 → UInt256) (key : UInt256) :
    List (BitWidth × UInt256) :=
  [(⟨128, by decide⟩, UInt256.land (load (solcMappingSlot ⟨1⟩ key)) (UInt256.ofNat (2^128 - 1))),
   (⟨128, by decide⟩, UInt256.shiftRight (load (solcMappingSlot ⟨1⟩ key)) (UInt256.ofNat 128)),
   (⟨128, by decide⟩, UInt256.land (load (solcMappingSlot ⟨1⟩ key + ⟨1⟩)) (UInt256.ofNat (2^128 - 1))),
   (⟨128, by decide⟩, UInt256.shiftRight (load (solcMappingSlot ⟨1⟩ key + ⟨1⟩)) (UInt256.ofNat 128)),
   (⟨16, by decide⟩, UInt256.land (load (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat (2^16 - 1))),
   (⟨16, by decide⟩, UInt256.land (UInt256.shiftRight (load (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 16)) (UInt256.ofNat (2^16 - 1))),
   (⟨16, by decide⟩, UInt256.land (UInt256.shiftRight (load (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 32)) (UInt256.ofNat (2^16 - 1))),
   (⟨16, by decide⟩, UInt256.land (UInt256.shiftRight (load (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 48)) (UInt256.ofNat (2^16 - 1))),
   (⟨16, by decide⟩, UInt256.land (UInt256.shiftRight (load (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 64)) (UInt256.ofNat (2^16 - 1))),
   (⟨16, by decide⟩, UInt256.land (UInt256.shiftRight (load (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 80)) (UInt256.ofNat (2^16 - 1))),
   (⟨16, by decide⟩, UInt256.land (UInt256.shiftRight (load (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 96)) (UInt256.ofNat (2^16 - 1))),
   (⟨32, by decide⟩, UInt256.land (UInt256.shiftRight (load (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 112)) (UInt256.ofNat (2^32 - 1))),
   (⟨8, by decide⟩, UInt256.land (UInt256.shiftRight (load (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 144)) (UInt256.ofNat (2^8 - 1)))]

def marketStateReturnWords (load : UInt256 → UInt256) (key : UInt256) : List UInt256 :=
  (marketStateReturnEntries load key).map Prod.snd

theorem marketStateReturnEncoding (load : UInt256 → UInt256) (key : UInt256) :
    encodeReturnValues? marketStateTransition.returnType
      (wordArrayValues (marketStateReturnWords load key)) =
        some (wordArrayBytes (marketStateReturnWords load key)) := by
  apply uintWordTupleReturnEncoding (marketStateReturnEntries load key)
  intro entry he
  simp only [marketStateReturnEntries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only [Prod.fst, Prod.snd] <;>
    first | exact u256LandMaskToNatLtOfToNat _ _ (by decide) | exact shiftRight128_lt _

theorem marketStateBodyReturns (evm : EVM.State) (key : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork config contract evm ((∅ : Store).insert "arg0" (wordBytes32Value key))
      marketStateTransition.body
      (.returned (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm)
        evm (some (wordArrayValues (marketStateReturnWords
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner) key)))) := by
  apply guardedReturnsBody hwv hhi
  have h0 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "totalUnits"] }) =
      .ok (.int (Int.ofNat (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key)) (UInt256.ofNat (2^128 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key, offset := 0, size := 16,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))),
        offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)
  have h1 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "lossFactor"] }) =
      .ok (.int (Int.ofNat (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key)) (UInt256.ofNat 128)).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key, offset := 16, size := 16,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))),
        offset := 16, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · exact storageLocLoad_uint128_high evm _
  have h2 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "withdrawable"] }) =
      .ok (.int (Int.ofNat (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨1⟩)) (UInt256.ofNat (2^128 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨1⟩, offset := 0, size := 16,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨1⟩,
        offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)
  have h3 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "continuousFeeCredit"] }) =
      .ok (.int (Int.ofNat (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨1⟩)) (UInt256.ofNat 128)).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨1⟩, offset := 16, size := 16,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨1⟩,
        offset := 16, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · exact storageLocLoad_uint128_high evm _
  have h4 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "settlementFeeCbp0"] }) =
      .ok (.int (Int.ofNat (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat (2^16 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨2⟩, offset := 0, size := 2,
        hbound := by decide, type := .int (.uint ⟨16, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨2⟩,
        offset := 0, size := 2, hbound := by decide, type := .int (.uint ⟨16, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · exact storageLocLoad_uint_offset0 evm _ 2 ⟨16, by decide⟩ (by decide) (by decide)
  have h5 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "settlementFeeCbp1"] }) =
      .ok (.int (Int.ofNat (UInt256.land (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 16)) (UInt256.ofNat (2^16 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨2⟩, offset := 2, size := 2,
        hbound := by decide, type := .int (.uint ⟨16, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨2⟩,
        offset := 2, size := 2, hbound := by decide, type := .int (.uint ⟨16, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · rw [storageLocLoad_uint_offset evm _ 2 2 ⟨16, by decide⟩
        (by decide) (by decide) (by decide), div_byteOffset_eq_shiftRight]
      rfl
  have h6 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "settlementFeeCbp2"] }) =
      .ok (.int (Int.ofNat (UInt256.land (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 32)) (UInt256.ofNat (2^16 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨2⟩, offset := 4, size := 2,
        hbound := by decide, type := .int (.uint ⟨16, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨2⟩,
        offset := 4, size := 2, hbound := by decide, type := .int (.uint ⟨16, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · rw [storageLocLoad_uint_offset evm _ 4 2 ⟨16, by decide⟩
        (by decide) (by decide) (by decide), div_byteOffset_eq_shiftRight]
      rfl
  have h7 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "settlementFeeCbp3"] }) =
      .ok (.int (Int.ofNat (UInt256.land (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 48)) (UInt256.ofNat (2^16 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨2⟩, offset := 6, size := 2,
        hbound := by decide, type := .int (.uint ⟨16, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨2⟩,
        offset := 6, size := 2, hbound := by decide, type := .int (.uint ⟨16, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · rw [storageLocLoad_uint_offset evm _ 6 2 ⟨16, by decide⟩
        (by decide) (by decide) (by decide), div_byteOffset_eq_shiftRight]
      rfl
  have h8 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "settlementFeeCbp4"] }) =
      .ok (.int (Int.ofNat (UInt256.land (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 64)) (UInt256.ofNat (2^16 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨2⟩, offset := 8, size := 2,
        hbound := by decide, type := .int (.uint ⟨16, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨2⟩,
        offset := 8, size := 2, hbound := by decide, type := .int (.uint ⟨16, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · rw [storageLocLoad_uint_offset evm _ 8 2 ⟨16, by decide⟩
        (by decide) (by decide) (by decide), div_byteOffset_eq_shiftRight]
      rfl
  have h9 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "settlementFeeCbp5"] }) =
      .ok (.int (Int.ofNat (UInt256.land (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 80)) (UInt256.ofNat (2^16 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨2⟩, offset := 10, size := 2,
        hbound := by decide, type := .int (.uint ⟨16, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨2⟩,
        offset := 10, size := 2, hbound := by decide, type := .int (.uint ⟨16, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · rw [storageLocLoad_uint_offset evm _ 10 2 ⟨16, by decide⟩
        (by decide) (by decide) (by decide), div_byteOffset_eq_shiftRight]
      rfl
  have h10 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "settlementFeeCbp6"] }) =
      .ok (.int (Int.ofNat (UInt256.land (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 96)) (UInt256.ofNat (2^16 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨2⟩, offset := 12, size := 2,
        hbound := by decide, type := .int (.uint ⟨16, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨2⟩,
        offset := 12, size := 2, hbound := by decide, type := .int (.uint ⟨16, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · rw [storageLocLoad_uint_offset evm _ 12 2 ⟨16, by decide⟩
        (by decide) (by decide) (by decide), div_byteOffset_eq_shiftRight]
      rfl
  have h11 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "continuousFee"] }) =
      .ok (.int (Int.ofNat (UInt256.land (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 112)) (UInt256.ofNat (2^32 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨2⟩, offset := 14, size := 4,
        hbound := by decide, type := .int (.uint ⟨32, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨2⟩,
        offset := 14, size := 4, hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · exact storageLocLoad_uint32_offset14 evm _
  have h12 : evalExpr? config
      (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := "marketState", steps := [.mindex (.var "arg0"), .field "tickSpacing"] }) =
      .ok (.int (Int.ofNat (UInt256.land (UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨2⟩)) (UInt256.ofNat 144)) (UInt256.ofNat (2^8 - 1))).toNat)) := by
    apply evalBytes32MappingField
      (loc := {
        slot := solcMappingSlot ⟨1⟩ key + ⟨2⟩, offset := 18, size := 1,
        hbound := by decide, type := .int (.uint ⟨8, by decide⟩) })
      evm key rfl rfl ?_ ?_ (by decide) (by decide) (by decide)
    · change some (StorageAddr.leaf {
        slot := solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨2⟩,
        offset := 18, size := 1, hbound := by decide, type := .int (.uint ⟨8, by decide⟩) }) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
    · exact storageLocLoad_uint8_offset18 evm _
  change evalExprs? config
    (calldataFrame contract ((∅ : Store).insert "arg0" (wordBytes32Value key)) ∅ evm) evm _ = .ok _
  simp only [evalExprs?, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, bind, pure, EvalResult.bind,
    marketStateReturnWords, marketStateReturnEntries, wordArrayValues, List.map_cons, List.map_nil]

theorem marketStateTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat}
    (rd : RD fork midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 2135)
      [solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret fork midnightBytecode g (initState σ σ₀ g A I) σ
      (wordArrayBytes (marketStateReturnWords (fun slot ↦ solcSlotWordAt slot σ I)
        (calldataWord I.calldata 4))) := by
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_2135_packed (by simp) rd
  simp only [midnightBlocks.midnight_block_2135_stack,
    midnightBlocks.midnight_block_2135_memory, uint128Mask_computed, midnightEntryMemory_zero,
    show (UInt256.ofNat 32).toNat = 32 from rfl,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    wordAt0_fold, twoWordHash_fold, mappingMemory_fold, mappingMemory_zero,
    mappingMemory_hash, mappingMemory_freePtr] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightBlocks.midnight_block_2226_packed (by simp) rd1
  simp only [midnightBlocks.midnight_block_2226_stack,
    midnightBlocks.midnight_block_2226_memory] at rd2
  have hr := midnightBlocks.midnight_block_2325 (by simp) rd2
  change RDret fork _ _ _ _
    ((writeWordArray (mappingMemory (calldataWord I.calldata 4) ⟨1⟩) 832
      (marketStateReturnWords (fun slot ↦ solcSlotWordAt slot σ I)
        (calldataWord I.calldata 4))).readWithPadding 832 416) at hr
  rw [show 416 = 32 * (marketStateReturnWords (fun slot ↦ solcSlotWordAt slot σ I)
      (calldataWord I.calldata 4)).length from rfl,
    writeWordArray_read _ _ _ (by rw [mappingMemory_size])] at hr
  exact hr

/-- `marketState(bytes32)`: the theorem `Correct.lean` routes selector 50 to. -/
theorem midnightMarketStateBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 50)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 50) rfl hsel
  have hd : dispatchMsg contract I.calldata = some marketStateTransition := by
    apply midnightDispatch_marketState <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachMarketStateBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_2117_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_2123_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have hret := marketStateTraceReturn rd2
        have hdec := midnightDecodeBytes32 "arg0" (by decide) (by decide) h36 hhi hsize
        have hbody := marketStateBodyReturns (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (calldataWord I.calldata 4) hwv hhi
        exact hret.reEquivExecution hcode hd hdec hbody
          (returnEquiv.returned rfl (marketStateReturnEncoding _ _))
      · have rd2 := midnightBlocks.midnight_block_2123_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 32) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h36) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeScalar_none_short "arg0" (.bytes abiBytes32Width)
            hsz (Nat.lt_of_not_ge h36) hsize)
    · have rd2 := midnightBlocks.midnight_block_2123_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 32) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeScalar_none_huge "arg0" (.bytes abiBytes32Width)
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_2117_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (marketStateTransition.params.map Param.name)
        (transitionSignature marketStateTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)


end Benchmarks.Midnight
