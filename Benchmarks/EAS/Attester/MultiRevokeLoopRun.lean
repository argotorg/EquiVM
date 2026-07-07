import Benchmarks.EAS.Attester.MultiRevokeContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeOuterInitFreeInv_to_outerLoopInv
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {callargs : Store} {schemas schemaUids : List Value}
    {evm : EVM.State}
    {a : AttesterMultiOuterArrayInitState}
    (hSchemas : callargs.get? "schemas" = some (.array schemas))
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hSchemasLen :
      schemas.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hSchemaUidsLen :
      schemaUids.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hoff0 : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hoff1 : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hSchemasLenMax : schemas.length ≤ solcMaxU64)
    (hOuter : attesterMultiRevokeOuterInitFreeInv I 0 a) :
    let L1 := callargs.insert "schemaLength" (.int (Int.ofNat schemas.length))
    let L2 := L1.insert "multiRequests"
      (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
    let L3 := L2.insert "i" (.int 0)
    let cursor : AttesterMultiRevokeOuterLoopCursor :=
      { idx := ⟨0⟩,
        outerBase := ⟨128⟩,
        schemaLen := attesterFirstArrayLengthWord I,
        secondLen := attesterSecondArrayLengthWord I,
        secondPayload := attesterSecondArrayPayloadStartWord I,
        schemaPayload := (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ret := ⟨97⟩,
        selector := solcSelectorWord I,
        mem := attesterMultiOuterArrayInitFinalMem a,
        aw := attesterMultiOuterArrayInitFinalAw a,
        acc := (cA, σ) }
    AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids schemas.length cursor L3 evm := by
  intro L1 L2 L3 cursor
  rcases hOuter with
    ⟨harem, habound, hale, hawGe, hawMul, hbaseGe, hbase160, hbaseBound, hbaseSpare,
      hslotGe, hslot160, hslotBound, hslotSpare, hread128, hmem128, hfreeExact⟩
  let oldFree := attesterMultiOuterArrayInitFreeWord a.mem a.aw
  have hlenWordToNat :
      (attesterFirstArrayLengthWord I).toNat = schemas.length := by
    rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0]
    exact hSchemasLen.symm
  have hsecondWordToNat :
      (attesterSecondArrayLengthWord I).toNat = schemaUids.length := by
    rw [attesterSecondArrayLengthWord_toNat (I := I) hoff1]
    exact hSchemaUidsLen.symm
  have hlenPosWord : 0 < (attesterFirstArrayLengthWord I).toNat := by
    rw [hlenWordToNat]
    omega
  have houterStepAw :=
    attesterMultiOuterArrayInitStepAw_bounds
      (slot := a.slot) (mem := a.mem) (aw := a.aw)
      hawGe hawMul
      (by
        have h : oldFree.toNat + 95 < UInt256.size := by
          have hspare : oldFree.toNat + 64 + 160 + 160 * solcMaxU64 < UInt256.size := by
            simpa [oldFree] using hbaseSpare
          omega
        exact h)
      (by
        have h : a.slot.toNat + 63 < UInt256.size := by
          omega
        exact h)
  have holdFree32 : oldFree.toNat + 32 < UInt256.size := by
    have h : oldFree.toNat + 64 < UInt256.size := by
      simpa [oldFree] using hbaseBound
    omega
  have hoffsetToNat :
      (attesterMultiOuterArrayInitOffsetWord a.mem a.aw).toNat =
        oldFree.toNat + 32 := by
    unfold oldFree attesterMultiOuterArrayInitOffsetWord
    exact uadd_word_lit32_toNat
      (attesterMultiOuterArrayInitFreeWord a.mem a.aw) holdFree32
  have hoffset160 :
      128 + 32 ≤ (attesterMultiOuterArrayInitOffsetWord a.mem a.aw).toNat := by
    rw [hoffsetToNat]
    have h : 128 + 32 ≤ oldFree.toNat := by
      simpa [oldFree] using hbase160
    omega
  have hfinalRead128 :
      (attesterMultiOuterArrayInitFinalMem a).readWithPadding 128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
    change
      (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw).readWithPadding
          128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I)
    simpa using
      (attesterMultiOuterArrayInitStep_readWithPadding_nat
        (base := (⟨128⟩ : UInt256)) (slot := a.slot)
        (len := attesterFirstArrayLengthWord I) (mem := a.mem) (aw := a.aw)
        (by simpa using hmem128)
        (by simpa using hread128)
        (by decide)
        (by simpa using hbase160)
        (by simpa using hoffset160)
        (by simpa using hslot160))
  have hfinalMem128 :
      128 + 32 ≤ (attesterMultiOuterArrayInitFinalMem a).size := by
    change 128 + 32 ≤
      (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw).size
    exact le_trans hmem128 attesterMultiOuterArrayInitStep_size_ge
  have hfinalFreeToNat :
      (attesterInnerArrayAllocFreeWord
          (attesterMultiOuterArrayInitFinalMem a)
          (attesterMultiOuterArrayInitFinalAw a)).toNat =
        oldFree.toNat + 64 := by
    change
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw)
          (attesterMultiOuterArrayInitStepAw a.slot a.mem a.aw)).toNat =
        oldFree.toNat + 64
    exact attesterMultiOuterArrayInitStep_freeWord_toNat
      (slot := a.slot) (mem := a.mem) (aw := a.aw)
      (by simpa [oldFree] using hbaseGe)
      (by
        rw [hoffsetToNat]
        have h : 64 + 32 ≤ oldFree.toNat := by
          simpa [oldFree] using hbaseGe
        omega)
      hslotGe houterStepAw.2 houterStepAw.1
      (by simpa [oldFree] using hbaseBound)
  have hfreeBudget :
      (attesterInnerArrayAllocFreeWord
          (attesterMultiOuterArrayInitFinalMem a)
          (attesterMultiOuterArrayInitFinalAw a)).toNat +
          attesterMultiRevokeEncoderOutputBudget schemas.length + 128 +
        attesterMultiRevokeOuterLoopBudgetChunk * schemas.length < UInt256.size := by
    rw [hfinalFreeToNat, hfreeExact]
    rw [hlenWordToNat]
    let n := schemas.length
    have hnpos : 0 < n := by
      dsimp [n]
      omega
    have hprefixLe :
        160 + 32 * n + 64 * (n - 1) + 64 + 128 ≤ 288 + 96 * n := by
      have hsubEq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
      have hmulSub : 64 * (n - 1) + 64 = 64 * n := by
        nlinarith
      nlinarith
    have htotalLe :
        160 + 32 * n + 64 * (n - 1) + 64 +
            attesterMultiRevokeEncoderOutputBudget n + 128 +
            attesterMultiRevokeOuterLoopBudgetChunk * n ≤
          356 + (96 + attesterMultiRevokeOuterLoopBudgetChunk +
              attesterMultiRevokeOuterLoopBudgetChunk) * solcMaxU64 := by
      have hmulLe :
          (96 + attesterMultiRevokeOuterLoopBudgetChunk +
              attesterMultiRevokeOuterLoopBudgetChunk) * n ≤
            (96 + attesterMultiRevokeOuterLoopBudgetChunk +
              attesterMultiRevokeOuterLoopBudgetChunk) * solcMaxU64 :=
        Nat.mul_le_mul_left (96 + attesterMultiRevokeOuterLoopBudgetChunk +
          attesterMultiRevokeOuterLoopBudgetChunk)
          (by simpa [n] using hSchemasLenMax)
      have hcombine :
          356 + 96 * n + attesterMultiRevokeOuterLoopBudgetChunk * n +
              attesterMultiRevokeOuterLoopBudgetChunk * n =
            356 + (96 + attesterMultiRevokeOuterLoopBudgetChunk +
              attesterMultiRevokeOuterLoopBudgetChunk) * n := by
        ring
      unfold attesterMultiRevokeEncoderOutputBudget
      calc
        160 + 32 * n + 64 * (n - 1) + 64 + (4 + 64 +
              attesterMultiRevokeOuterLoopBudgetChunk * n) + 128 +
            attesterMultiRevokeOuterLoopBudgetChunk * n
            ≤ 288 + 96 * n + 68 +
                attesterMultiRevokeOuterLoopBudgetChunk * n +
                attesterMultiRevokeOuterLoopBudgetChunk * n := by
              omega
        _ = 356 + (96 + attesterMultiRevokeOuterLoopBudgetChunk +
              attesterMultiRevokeOuterLoopBudgetChunk) * n := by
              calc
                288 + 96 * n + 68 + attesterMultiRevokeOuterLoopBudgetChunk * n +
                    attesterMultiRevokeOuterLoopBudgetChunk * n
                    = 356 + 96 * n + attesterMultiRevokeOuterLoopBudgetChunk * n +
                        attesterMultiRevokeOuterLoopBudgetChunk * n := by
                      omega
                _ = 356 + (96 + attesterMultiRevokeOuterLoopBudgetChunk +
                    attesterMultiRevokeOuterLoopBudgetChunk) * n := by
                      rw [hcombine]
        _ ≤ 356 + (96 + attesterMultiRevokeOuterLoopBudgetChunk +
              attesterMultiRevokeOuterLoopBudgetChunk) * solcMaxU64 := by
              omega
    have hcap :
        356 + (96 + attesterMultiRevokeOuterLoopBudgetChunk +
            attesterMultiRevokeOuterLoopBudgetChunk) * solcMaxU64 <
          UInt256.size := by
      native_decide
    exact lt_of_le_of_lt (by simpa [n] using htotalLe) hcap
  have hschemasL1 : L1.get? "schemas" = some (.array schemas) := by
    simpa [L1] using
      (attesterStoreGetInsertOfNe (locals := callargs) (name := "schemas")
        (other := "schemaLength") (value := .int (Int.ofNat schemas.length))
        hSchemas (by decide))
  have hschemaUidsL1 : L1.get? "schemaUids" = some (.array schemaUids) := by
    simpa [L1] using
      (attesterStoreGetInsertOfNe (locals := callargs) (name := "schemaUids")
        (other := "schemaLength") (value := .int (Int.ofNat schemas.length))
        hSchemaUids (by decide))
  have hschemaLengthL1 : L1.get? "schemaLength" =
      some (.int (Int.ofNat schemas.length)) := by
    simp [L1]
  have hschemasL2 : L2.get? "schemas" = some (.array schemas) := by
    simpa [L2] using
      (attesterStoreGetInsertOfNe (locals := L1) (name := "schemas")
        (other := "multiRequests")
        (value := .array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
        hschemasL1 (by decide))
  have hschemaUidsL2 : L2.get? "schemaUids" = some (.array schemaUids) := by
    simpa [L2] using
      (attesterStoreGetInsertOfNe (locals := L1) (name := "schemaUids")
        (other := "multiRequests")
        (value := .array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
        hschemaUidsL1 (by decide))
  have hschemaLengthL2 : L2.get? "schemaLength" =
      some (.int (Int.ofNat schemas.length)) := by
    simpa [L2] using
      (attesterStoreGetInsertOfNe (locals := L1) (name := "schemaLength")
        (other := "multiRequests")
        (value := .array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
        hschemaLengthL1 (by decide))
  have hrequestsL2 :
      L2.get? "multiRequests" =
        some (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault)) := by
    simp [L2]
  have hschemasL3 : L3.get? "schemas" = some (.array schemas) := by
    simpa [L3] using
      (attesterStoreGetInsertOfNe (locals := L2) (name := "schemas")
        (other := "i") (value := .int 0) hschemasL2 (by decide))
  have hschemaUidsL3 : L3.get? "schemaUids" = some (.array schemaUids) := by
    simpa [L3] using
      (attesterStoreGetInsertOfNe (locals := L2) (name := "schemaUids")
        (other := "i") (value := .int 0) hschemaUidsL2 (by decide))
  have hschemaLengthL3 : L3.get? "schemaLength" =
      some (.int (Int.ofNat schemas.length)) := by
    simpa [L3] using
      (attesterStoreGetInsertOfNe (locals := L2) (name := "schemaLength")
        (other := "i") (value := .int 0) hschemaLengthL2 (by decide))
  have hrequestsL3 :
      L3.get? "multiRequests" =
        some (.array (attesterMultiRevokeRequestValuesPrefix 0 schemas schemaUids)) := by
    have hraw : L3.get? "multiRequests" =
        some (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault)) := by
      simpa [L3] using
        (attesterStoreGetInsertOfNe (locals := L2) (name := "multiRequests")
          (other := "i") (value := .int 0) hrequestsL2 (by decide))
    simpa [attesterMultiRevokeRequestValuesPrefix_zero] using hraw
  have hiL3 : L3.get? "i" = some (.int 0) := by
    simp [L3]
  refine ⟨0, hschemasL3, hschemaUidsL3, hschemaLengthL3, hrequestsL3, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hiL3
  · omega
  · omega
  · intro idx _value hlt _hlookup
    omega
  · change 0 < UInt256.size
    norm_num [UInt256.size]
  · change (⟨0⟩ : UInt256) = UInt256.ofNat 0
    native_decide
  · simp [cursor]
  · simp [cursor]
  · simp [cursor]
  · simpa [cursor] using hlenWordToNat
  · simp [cursor]
  · simpa [cursor] using hsecondWordToNat
  · simp [cursor, attesterSecondArrayPayloadStartWord]
  · simp [cursor]
  · simp [cursor]
  · simp [cursor]
  · simp [cursor]
  · simpa [cursor] using houterStepAw.1
  · simpa [cursor] using houterStepAw.2
  · simpa [cursor] using hfinalRead128
  · simpa [cursor] using hfinalMem128
  · change 64 + 32 ≤ (⟨128⟩ : UInt256).toNat
    decide
  · rw [hfinalFreeToNat]
    have h : 64 + 32 ≤ oldFree.toNat := by
      simpa [oldFree] using hbaseGe
    omega
  · constructor
    · rw [hfinalFreeToNat]
      change (⟨128⟩ : UInt256).toNat + 32 ≤ oldFree.toNat + 64
      have h : 64 + 32 ≤ oldFree.toNat := by
        simpa [oldFree] using hbaseGe
      have h128 : (⟨128⟩ : UInt256).toNat = 128 := by decide
      rw [h128]
      omega
    · constructor
      · have hfreeFinalLower :
            160 + 32 * schemas.length ≤
              (attesterInnerArrayAllocFreeWord
                (attesterMultiOuterArrayInitFinalMem a)
                (attesterMultiOuterArrayInitFinalAw a)).toNat := by
          rw [hfinalFreeToNat, hfreeExact, hlenWordToNat]
          omega
        have hcursorOuterBaseToNat : cursor.outerBase.toNat = 128 := by
          change (⟨128⟩ : UInt256).toNat = 128
          decide
        rw [hcursorOuterBaseToNat]
        omega
      · constructor
        · intro idx hidx
          omega
        · simpa [cursor] using hfreeBudget

theorem attesterX_multiRevokeOuterInitToLoopInv
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {callargs : Store} {schemas schemaUids : List Value}
    (hSchemas : callargs.get? "schemas" = some (.array schemas))
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hSchemasLen :
      schemas.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hSchemaUidsLen :
      schemaUids.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hoff0 : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hoff1 : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hSchemasLenMax : schemas.length ≤ solcMaxU64)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
          (attesterMultiRevokeOuterArrayInitExitStack I ⟨128⟩
            (attesterFirstArrayLengthWord I) a')
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a')
          ByteArray.empty (cA, σ) k C) :
    let L1 := callargs.insert "schemaLength" (.int (Int.ofNat schemas.length))
    let L2 := L1.insert "multiRequests"
      (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
    let L3 := L2.insert "i" (.int 0)
    ∃ cursor L k C,
      L = L3 ∧
      AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids schemas.length cursor L
        (initState cA gh bl σ σ₀ g A I) ∧
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterLoopStack cursor) cursor.mem cursor.aw ByteArray.empty
        cursor.acc k C := by
  intro L1 L2 L3
  rcases hprogress with ⟨a', k, C, _hrem, hOuter, rd⟩
  let cursor : AttesterMultiRevokeOuterLoopCursor :=
    { idx := ⟨0⟩,
      outerBase := ⟨128⟩,
      schemaLen := attesterFirstArrayLengthWord I,
      secondLen := attesterSecondArrayLengthWord I,
      secondPayload := attesterSecondArrayPayloadStartWord I,
      schemaPayload := (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
      ret := ⟨97⟩,
      selector := solcSelectorWord I,
      mem := attesterMultiOuterArrayInitFinalMem a',
      aw := attesterMultiOuterArrayInitFinalAw a',
      acc := (cA, σ) }
  have hInv :
      AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids schemas.length cursor L3
        (initState cA gh bl σ σ₀ g A I) := by
    simpa [cursor, L1, L2, L3] using
      (attesterMultiRevokeOuterInitFreeInv_to_outerLoopInv
        (cA := cA) (σ := σ) (I := I) (callargs := callargs)
        (schemas := schemas) (schemaUids := schemaUids) (a := a')
        hSchemas hSchemaUids hSchemasLen hSchemaUidsLen hoff0 hoff1
        hSchemasLenMax hOuter)
  exact ⟨cursor, L3, k, C, rfl, hInv, by
    simpa [cursor, attesterMultiRevokeOuterLoopStack,
      attesterMultiRevokeOuterArrayInitExitStack] using rd⟩

set_option maxHeartbeats 1000000 in
theorem AttesterMultiRevokeOuterLoopInv.run_or_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {callargs : Store} {schemas schemaUids : List Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemas : callargs.get? "schemas" = some (.array schemas))
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hoff0 : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hoff1 : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsizeSigned : I.calldata.size < 2 ^ 255)
    (hschemasBound : schemas.length < 2 ^ 256)
    (hschemasLenMax : schemas.length ≤ solcMaxU64)
    (hlenEq : schemaUids.length = schemas.length)
    (hschemaNorm : ∀ {idx schema}, lookupNth? schemas idx = some schema →
      normalizeRawBoolWord? schema = .ok schema)
    (huidssShape : ∀ {idx value}, lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid)) :
    ∀ {fuel : Nat} {a : AttesterMultiRevokeOuterLoopCursor} {L : Store}
      {evm : EVM.State},
      AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids fuel a L evm →
      ∀ k C,
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k C →
      (∃ a' L' evm' k' C',
        ExecStmt (config v) { contract := contract v, locals := L } evm
          (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
          (.ok { contract := contract v, locals := L' } evm') ∧
        AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids 0 a' L' evm' ∧
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨698⟩ : UInt256)
          (attesterMultiRevokeOuterLoopStack a') a'.mem a'.aw ByteArray.empty a'.acc k' C') ∨
      (ExecStmt (config v) { contract := contract v, locals := L } evm
          (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
          .reverted ∧
        RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I)) := by
  intro fuel a L evm hInv k C rd
  refine
    (attesterMultiRevokeOuterLoop_from_headerBodyOutcome_or_revert
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids)
      ?_ ?_ ?_ ?_) fuel a L evm hInv k C rd
  · intro a L evm hInv
    rcases hInv with
      ⟨i, _hschemas, _hSchemaUids, hschemaLength, _hrequests, hi, hvariant, _hile,
        _hprocessed, _hisize, _hidx, _hidxToNat, _houterBase, _hschemaLen,
        _hschemaLenToNat, _hsecondLen, _hsecondLenToNat, _hsecondPayload,
        _hschemaPayload, _hret, _hselector, _hacc, _hawGe, _hawMul, _houterRead,
        _houterMemSize, _houter64, _hbaseGe, _houterBeforeBase,
        _houterSlotsBeforeBase, _hreadLayout, _hfreeBudget⟩
    exact attesterMultiRevokeOuterSourceLoopCondFalse v evm hschemaLength hi (by omega)
  · intro a L evm hInv k C rd
    have hlt :
        UInt256.lt a.idx a.schemaLen = ⟨0⟩ :=
      AttesterMultiRevokeOuterLoopInv.cond_false
        (cA := cA) (σ := σ) (I := I) (schemas := schemas)
        (schemaUids := schemaUids) (a := a) (L := L) (evm := evm) hInv
    rcases hInv with
      ⟨_i, _hschemas, _hSchemaUids, _hschemaLength, _hrequests, _hi, _hvariant,
        _hile, _hprocessed, _hisize, _hidx, _hidxToNat, _houterBase,
        _hschemaLen, _hschemaLenToNat, _hsecondLen, _hsecondLenToNat,
        _hsecondPayload, _hschemaPayload, _hret, _hselector, hacc, _hawGe,
        _hawMul, _houterRead, _houterMemSize, _houter64, _hbaseGe,
        _houterBeforeBase, _houterSlotsBeforeBase, _hreadLayout, _hfreeBudget⟩
    obtain ⟨k', C', rd'⟩ := attesterX_multiRevokeOuterSourceLoopExit
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hlt
      (by simpa [attesterMultiRevokeOuterLoopStack, hacc] using rd)
    exact ⟨k', C', by simpa [attesterMultiRevokeOuterLoopStack, hacc] using rd'⟩
  · intro fuel a L evm hInv
    rcases hInv with
      ⟨i, _hschemas, _hSchemaUids, hschemaLength, _hrequests, hi, hvariant, _hile,
        _hprocessed, _hisize, _hidx, _hidxToNat, _houterBase, _hschemaLen,
        _hschemaLenToNat, _hsecondLen, _hsecondLenToNat, _hsecondPayload,
        _hschemaPayload, _hret, _hselector, _hacc, _hawGe, _hawMul, _houterRead,
        _houterMemSize, _houter64, _hbaseGe, _houterBeforeBase,
        _houterSlotsBeforeBase, _hreadLayout, _hfreeBudget⟩
    exact attesterMultiRevokeOuterSourceLoopCondTrue v evm hschemaLength hi (by omega)
  · intro fuel a L evm hInv k C rd
    exact AttesterMultiRevokeOuterLoopInv.body_or_revert
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hdec hSchemas hSchemaUids hoff0 hoff1 hsizeSigned
      hschemasBound hschemasLenMax hlenEq hschemaNorm huidssShape hInv k C rd

theorem AttesterMultiRevokeOuterLoopInv.done_shape
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {schemas schemaUids : List Value}
    {a : AttesterMultiRevokeOuterLoopCursor} {L : Store} {evm : EVM.State}
    (hInv : AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids 0 a L evm) :
    L.get? "schemas" = some (.array schemas) ∧
    L.get? "schemaUids" = some (.array schemaUids) ∧
    L.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) ∧
    L.get? "multiRequests" =
      some (.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) ∧
    L.get? "i" = some (.int (Int.ofNat schemas.length)) ∧
    a.idx = UInt256.ofNat schemas.length ∧
    a.idx.toNat = schemas.length ∧
    a.outerBase = (⟨128⟩ : UInt256) ∧
    a.schemaLen = attesterFirstArrayLengthWord I ∧
    a.schemaLen.toNat = schemas.length ∧
    a.secondLen = attesterSecondArrayLengthWord I ∧
    a.secondLen.toNat = schemaUids.length ∧
    a.secondPayload = attesterSecondArrayPayloadStartWord I ∧
    a.schemaPayload = (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩ ∧
    a.ret = (⟨97⟩ : UInt256) ∧
    a.selector = solcSelectorWord I ∧
    a.acc = (cA, σ) ∧
    3 ≤ a.aw.toNat ∧
    a.aw.toNat * 32 < UInt256.size ∧
    a.mem.readWithPadding a.outerBase.toNat 32 = UInt256.toByteArray a.schemaLen ∧
    a.outerBase.toNat + 32 ≤ a.mem.size ∧
    64 + 32 ≤ a.outerBase.toNat ∧
    64 + 32 ≤ (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat ∧
    a.outerBase.toNat + 32 ≤ (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat ∧
    (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat + 128 < UInt256.size := by
  rcases hInv with
    ⟨i, hschemas, hschemaUids, hschemaLength, hrequests, hi, hvariant, _hile,
      _hprocessed, _hisize, hidx, hidxToNat, houterBase, hschemaLen,
      hschemaLenToNat, hsecondLen, hsecondLenToNat, hsecondPayload,
      hschemaPayload, hret, hselector, hacc, hawGe, hawMul, houterRead,
      houterMemSize, houter64, hbaseGe, houterBeforeBase,
      _houterSlotsBeforeBase, _hreadLayout, hfreeBudget⟩
  have hidone : i = schemas.length := by omega
  subst hidone
  have hfreeLt :
      (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat + 128 < UInt256.size := by
    omega
  exact
    ⟨hschemas, hschemaUids, hschemaLength, hrequests, hi, hidx, hidxToNat,
      houterBase, hschemaLen, hschemaLenToNat, hsecondLen, hsecondLenToNat,
      hsecondPayload, hschemaPayload, hret, hselector, hacc, hawGe, hawMul,
      houterRead, houterMemSize, houter64, hbaseGe, houterBeforeBase, hfreeLt⟩

theorem AttesterMultiRevokeOuterLoopInv.done_readLayout
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {schemas schemaUids : List Value}
    {a : AttesterMultiRevokeOuterLoopCursor} {L : Store} {evm : EVM.State}
    (hInv : AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids 0 a L evm) :
    AttesterMultiRevokeRequestsReadLayoutBounded schemas schemaUids schemas.length
      a.mem a.outerBase
      (a.outerBase.toNat + 32 + 32 * schemas.length)
      (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat := by
  rcases hInv with
    ⟨i, _hschemas, _hschemaUids, _hschemaLength, _hrequests, _hi, hvariant,
      _hile, _hprocessed, _hisize, _hidx, hidxToNat, _houterBase, _hschemaLen,
      _hschemaLenToNat, _hsecondLen, _hsecondLenToNat, _hsecondPayload,
      _hschemaPayload, _hret, _hselector, _hacc, _hawGe, _hawMul, _houterRead,
      _houterMemSize, _houter64, _hbaseGe, _houterBeforeBase,
      _houterSlotsBeforeBase, hreadLayout, _hfreeBudget⟩
  have hidone : i = schemas.length := by omega
  subst i
  intro idx hidx
  exact hreadLayout (by
    rw [hidone]
    omega)

theorem AttesterMultiRevokeOuterLoopInv.done_uidss_ok
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {schemas schemaUids : List Value}
    {a : AttesterMultiRevokeOuterLoopCursor} {L : Store} {evm : EVM.State}
    (hlenEq : schemaUids.length = schemas.length)
    (hInv : AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids 0 a L evm) :
    ∀ {idx value}, lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length ≠ 0 ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid) := by
  rcases hInv with
    ⟨i, _hschemas, _hschemaUids, _hschemaLength, _hrequests, _hi, hvariant,
      _hile, hprocessed, _hisize, _hidx, _hidxToNat, _houterBase, _hschemaLen,
      _hschemaLenToNat, _hsecondLen, _hsecondLenToNat, _hsecondPayload,
      _hschemaPayload, _hret, _hselector, _hacc, _hawGe, _hawMul, _houterRead,
      _houterMemSize, _houter64, _hbaseGe, _houterBeforeBase,
      _houterSlotsBeforeBase, _hreadLayout, _hfreeBudget⟩
  have hidone : i = schemas.length := by omega
  subst i
  intro idx value hlookup
  have hidxLtSchemaUids : idx < schemaUids.length :=
    lookupNth?_some_length hlookup
  rcases hprocessed (by omega) hlookup with
    ⟨uids, hvalue, hne, _hmax, hbound, hnorm⟩
  exact ⟨uids, hvalue, hne, hbound, hnorm⟩

theorem AttesterMultiRevokeOuterLoopInv.done_uidss_bounded
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {schemas schemaUids : List Value}
    {a : AttesterMultiRevokeOuterLoopCursor} {L : Store} {evm : EVM.State}
    (hlenEq : schemaUids.length = schemas.length)
    (hInv : AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids 0 a L evm) :
    ∀ {idx value}, lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length ≠ 0 ∧
        uids.length ≤ solcMaxU64 ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid) := by
  rcases hInv with
    ⟨i, _hschemas, _hschemaUids, _hschemaLength, _hrequests, _hi, hvariant,
      _hile, hprocessed, _hisize, _hidx, _hidxToNat, _houterBase, _hschemaLen,
      _hschemaLenToNat, _hsecondLen, _hsecondLenToNat, _hsecondPayload,
      _hschemaPayload, _hret, _hselector, _hacc, _hawGe, _hawMul, _houterRead,
      _houterMemSize, _houter64, _hbaseGe, _houterBeforeBase,
      _houterSlotsBeforeBase, _hreadLayout, _hfreeBudget⟩
  have hidone : i = schemas.length := by omega
  subst i
  intro idx value hlookup
  have hidxLtSchemaUids : idx < schemaUids.length :=
    lookupNth?_some_length hlookup
  exact hprocessed (by omega) hlookup

end Benchmarks.EAS.Attester
