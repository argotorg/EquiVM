import Benchmarks.Dss.Clipper.TakeCallback
import Benchmarks.Dss.Clipper.TakeChost
import Benchmarks.Dss.Clipper.TakeChostVatFluxSource
import Benchmarks.Dss.Clipper.TakeDogDigs
import Benchmarks.Dss.Clipper.TakeEvent
import Benchmarks.Dss.Clipper.ExternalCall
import Benchmarks.Dss.Clipper.TakePostDogSource
import Benchmarks.Dss.Clipper.TakeNoAdjustPostDogSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

-- LIBRARY CANDIDATE: generalizes `Reasoning.Theory.wordAt0Mem_size_96` beyond 96 bytes.
theorem wordAt0Mem_size_of_ge_32 {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

-- LIBRARY CANDIDATE: generalizes `Reasoning.Theory.wordAt32Mem_size_96` beyond 96 bytes.
theorem wordAt32Mem_size_of_ge_64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt32Mem word mem).size = mem.size := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

-- LIBRARY CANDIDATE: generalizes `Reasoning.Theory.twoWordHashMem_size_96`.
theorem twoWordHashMem_size_of_ge_64' {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem
  rw [wordAt32Mem_size_of_ge_64 slot]
  exact wordAt0Mem_size_of_ge_32 key (by omega)
  rw [wordAt0Mem_size_of_ge_32 key (by omega)]
  exact hmem

-- LIBRARY CANDIDATE: preserves the solc free-pointer word across a write at scratch offset 0.
theorem wordAt0Mem_read64_of_ge_96 {mem : ByteArray} (word : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt0Mem word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega)
    (by omega) (by omega)]
  exact hread64

-- LIBRARY CANDIDATE: preserves the solc free-pointer word across a write at scratch offset 32.
theorem wordAt32Mem_read64_of_ge_96 {mem : ByteArray} (word : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt32Mem word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size]) (by omega)
    (by omega) (by omega)]
  exact hread64

-- LIBRARY CANDIDATE: generalizes `Reasoning.Theory.twoWordHashMem_read64`.
theorem twoWordHashMem_read64_of_ge_96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem
  exact wordAt32Mem_read64_of_ge_96 slot
    (by rw [wordAt0Mem_size_of_ge_32 key (by omega)]; omega)
    (wordAt0Mem_read64_of_ge_96 key hmem hread64)

theorem RD.clipperTakeOweGtTabToVatFluxExtcodesizeGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd :
      RD code ee g s0 ⟨8686⟩
        (price :: slice :: ⟨4057⟩ :: slice :: ⟨0⟩ :: tab :: lot :: price :: tic ::
          packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmul : price.toNat * slice.toNat < UInt256.size)
    (hgt : tab.toNat < (price.mul slice).toNat)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C',
      RD code ee g s0 ⟨4380⟩
        (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
          ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
            clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
              lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
                dataStart :: who :: max :: amt :: id :: R)
        (clipperTakeVatFluxCalldataMem v ee who (tab.div price) mem) (UInt256.ofNat 9)
        rdata (cA, σ) k' C' := by
  obtain ⟨kMul, CMul, rd4057⟩ :=
    RD.clipperTakeOwe0MulSuccess (v := v) (hpatch := hpatch) rd hmul (by omega)
  obtain ⟨kJoin, CJoin, rd4223⟩ :=
    RD.clipperTakeOweGtTabToJoin (v := v) (hpatch := hpatch) rd4057 hgt (by omega)
  exact RD.clipperTakeVatFluxExtcodesizeGuard (v := v) (hpatch := hpatch) rd4223
    hmem hread64 (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeOweGtTabVatFluxPostCall {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} (v : ClipperImmutables)
    {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd :
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨8686⟩
        (price :: slice :: ⟨4057⟩ :: slice :: ⟨0⟩ :: tab :: lot :: price :: tic ::
          packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        baseMem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmul : price.toNat * slice.toNat < UInt256.size)
    (hgt : tab.toNat < (price.mul slice).toNat)
    (hbaseMem : baseMem.size = 196)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_vat : Batteries.RBSet AccountAddress compare) (σ_vat : AccountMap)
      (zVat : Bool) (outVat : ByteArray) (A_vat : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        (outVat.write 0 (clipperTakeVatFluxCalldataMem v I who (tab.div price) baseMem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outVat (cA_vat, σ_vat) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (zVat,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_vat
            substate := A_vat
            createdAccounts := cA_vat },
          outVat) true ∧
      outVat.size < UInt256.size := by
  obtain ⟨k4380, C4380, rd4380⟩ :=
    RD.clipperTakeOweGtTabToVatFluxExtcodesizeGuard (v := v) (hpatch := hpatch)
      rd hmul hgt hbaseMem hread64 (by omega)
  exact RD.clipperTakeVatFluxPostCall (v := v) (hpatch := hpatch) rd4380
    hbaseMem hcodeSizeVat hdepth hperm (by omega)

theorem RD.clipperTakeOweGtTabVatFluxNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd :
      RD code ee g s0 ⟨8686⟩
        (price :: slice :: ⟨4057⟩ :: slice :: ⟨0⟩ :: tab :: lot :: price :: tic ::
          packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmul : price.toNat * slice.toNat < UInt256.size)
    (hgt : tab.toNat < (price.mul slice).toNat)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨k4380, C4380, rd4380⟩ :=
    RD.clipperTakeOweGtTabToVatFluxExtcodesizeGuard (v := v) (hpatch := hpatch)
      rd hmul hgt hmem hread64 (by omega)
  exact RD.clipperTakeVatFluxNoCode (v := v) (hpatch := hpatch) rd4380
    hcodeSizeVat (by omega)

theorem clipperTakeOweGtTabSourceMul_of_post_lot {I : ExecutionEnv}
    {evmPrice : EVM.State} {price lot : UInt256}
    (hlot : lot = clipperTakeSalesLotEVMWord evmPrice I)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size) :
    (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I)).toNat *
      price.toNat < UInt256.size := by
  simpa [hlot, clipperMinWord_comm, Nat.mul_comm] using hmul

theorem clipperTakeOweGtTabSourceGt_of_post_words {I : ExecutionEnv}
    {evmPrice : EVM.State} {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPrice I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPrice I)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat) :
    (clipperTakeSalesTabEVMWord evmPrice I).toNat <
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I))
        price).toNat := by
  simpa [← htab, ← hlot, clipperMinWord_comm,
    u256_mul_comm price (clipperMinWord lot (clipperTakeAmtWord I)),
    u256_mul_comm (clipperMinWord (clipperTakeAmtWord I) lot) price] using hgt

theorem clipperTakeOweGtTabSourceDivLeLot_of_post_words {I : ExecutionEnv}
    {evmPrice : EVM.State} {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPrice I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPrice I)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat) :
    (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat ≤
      (clipperTakeSalesLotEVMWord evmPrice I).toNat := by
  have hsliceLot : (clipperMinWord (clipperTakeAmtWord I) lot).toNat ≤ lot.toNat :=
    clipperMinWord_le_right (clipperTakeAmtWord I) lot
  have hbase :=
    clipperTakeTabDivPrice_le_lot_of_owe_gt
      (tab := tab) (price := price) (slice := clipperMinWord (clipperTakeAmtWord I) lot)
      (lot := lot)
      (by simpa [Nat.mul_comm] using hmul)
      (by simpa [u256_mul_comm price (clipperMinWord (clipperTakeAmtWord I) lot)] using hgt)
      hsliceLot
  simpa [← htab, ← hlot] using hbase

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCodeTailBlock
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hgt :
      (clipperTakeSalesTabEVMWord evmRead I).toNat <
        (UInt256.mul slice price).toNat)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat)]
        (true, evmVat, outVat) true)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hnoVatCode :
      (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v ++
        ([ .letDecl "dog_" (some addr) (.storage dogRef),
          .ite
            (.binary .and
              (.binary .gt (bytesLength "data") (.intLit 0))
              (.binary .and
                (.binary .ne (.var "who") (vatExpr v))
                (.binary .ne (.var "who") (.var "dog_"))))
            (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
              [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
            [] ] ++
          checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet"))
      .reverted := by
  let owe0 := UInt256.mul slice price
  let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
    (clipperTakeSalesTabEVMWord evmRead I)
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
  let sliceFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let fluxFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe0 slice'
        tabNew lotNew)
  have hflux :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            clipperTakeOweAdjustmentStmt ] ++
          clipperTakePostOweFluxStmts v)
        (.ok fluxFrame evmVat) := by
    simpa [sliceFrame, fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeOweGtTabVatFluxCallSuccessTailBlock v evmLoc evmRead evmVat I price
        slice hmul hgt hsliceLot hvatCode hcallVat
  have hmove :
      ExecBlock (config v) fluxFrame evmVat
        ([ .letDecl "dog_" (some addr) (.storage dogRef),
          .ite
            (.binary .and
              (.binary .gt (bytesLength "data") (.intLit 0))
              (.binary .and
                (.binary .ne (.var "who") (vatExpr v))
                (.binary .ne (.var "who") (.var "dog_"))))
            (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
              [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
            [] ] ++
          checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet")
        .reverted := by
    simpa [fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeVatMoveNoCodeBlock v evmLoc evmRead evmVat I price slice owe0 owe0
        slice' tabNew lotNew hdataLen hnoVatCode
  simpa [sliceFrame, fluxFrame, List.append_assoc] using execBlockAppendOk hflux hmove

theorem clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveCallFailureTailBlock
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice : UInt256) {outVat outMove : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hgt :
      (clipperTakeSalesTabEVMWord evmRead I).toNat <
        (UInt256.mul slice price).toNat)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat)]
        (true, evmVat, outVat) true)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hvatMoveCode :
      0 <
        (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (false, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v ++
        ([ .letDecl "dog_" (some addr) (.storage dogRef),
          .ite
            (.binary .and
              (.binary .gt (bytesLength "data") (.intLit 0))
              (.binary .and
                (.binary .ne (.var "who") (vatExpr v))
                (.binary .ne (.var "who") (.var "dog_"))))
            (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
              [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
            [] ] ++
          checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet"))
      .reverted := by
  let owe0 := UInt256.mul slice price
  let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
    (clipperTakeSalesTabEVMWord evmRead I)
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
  let sliceFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let fluxFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe0 slice'
        tabNew lotNew)
  have hflux :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            clipperTakeOweAdjustmentStmt ] ++
          clipperTakePostOweFluxStmts v)
        (.ok fluxFrame evmVat) := by
    simpa [sliceFrame, fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeOweGtTabVatFluxCallSuccessTailBlock v evmLoc evmRead evmVat I price
        slice hmul hgt hsliceLot hvatCode hcallVat
  have hmove :
      ExecBlock (config v) fluxFrame evmVat
        ([ .letDecl "dog_" (some addr) (.storage dogRef),
          .ite
            (.binary .and
              (.binary .gt (bytesLength "data") (.intLit 0))
              (.binary .and
                (.binary .ne (.var "who") (vatExpr v))
                (.binary .ne (.var "who") (.var "dog_"))))
            (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
              [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
            [] ] ++
          checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet")
        .reverted := by
    simpa [fluxFrame, owe0, slice', tabNew, lotNew] using
      clipperTakeVatMoveCallFailureBlock v evmLoc evmRead evmVat evmMove I price
        slice owe0 owe0 slice' tabNew lotNew hdataLen hvatMoveCode hcallMove
  simpa [sliceFrame, fluxFrame, List.append_assoc] using execBlockAppendOk hflux hmove

theorem clipperTakeOweGtTabVatFluxNoCodeRevertEquivCore
    (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPriceSolm : EVM.State} {price : UInt256}
    (hrev :
      RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hsrcMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size)
    (hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
            (clipperTakeAmtWord I)) price).toNat)
    (hsrcSliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceSolm I).toNat)
    (hnoVatCodeSolm :
      (UInt256.ofNat ((evmPriceSolm.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat = 0)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    exact
      clipperTakeOweGtTabVatFluxNoCodeSourceReverts
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm price hmax
        hsrcMul hsrcGt hsrcSliceLot hnoVatCodeSolm hstatus
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabVatFluxNoCodeRevertEquivFromPostWords
    (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPriceSolm : EVM.State} {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hrev :
      RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hnoVatCodeSolm :
      (UInt256.ofNat ((evmPriceSolm.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat = 0)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact
    clipperTakeOweGtTabVatFluxNoCodeRevertEquivCore v hcode hwv hdispatch hdec
      hlockedSolm hstoppedSolmLt husrSolm hrev hmax
      (clipperTakeOweGtTabSourceMul_of_post_lot hlot hmul)
      (clipperTakeOweGtTabSourceGt_of_post_words htab hlot hgt)
      (clipperTakeOweGtTabSourceDivLeLot_of_post_words htab hlot hmul hgt)
      hnoVatCodeSolm hstatus

theorem clipperTakeOweGtTabVatFluxNoCodeRevertEquivFromPostAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost σPostSolm : AccountMap} {evmPriceSolm : EVM.State}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (rd :
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨8686⟩
        (price :: slice :: ⟨4057⟩ :: slice :: ⟨0⟩ :: tab :: lot :: price :: tic ::
          packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        mem (UInt256.ofNat 7) rdata (cAPost, σPost) k C)
    (hAccountsPost : accountMapEquiv σPost σPostSolm)
    (hevmPriceAccounts : evmPriceSolm.accountMap = σPostSolm)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hslice : slice = clipperMinWord (clipperTakeAmtWord I) lot)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * slice.toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price slice).toNat)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hnoVatCodeEvm :
      Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev :
      RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.clipperTakeOweGtTabVatFluxNoCode (v := v) (hpatch := hpatch) rd hmul hgt
      hmem hread64 hnoVatCodeEvm hov
  have hnoVatCodeSolm :
      (UInt256.ofNat
        ((evmPriceSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
        (σ := σPost) (τ := σPostSolm) (target := clipperTakeVatTarget v)
        (addr := v.vat) hAccountsPost (clipperTakeVatTargetAddress v).symm
        hnoVatCodeEvm
  exact
    clipperTakeOweGtTabVatFluxNoCodeRevertEquivFromPostWords v hcode hwv hdispatch
      hdec hlockedSolm hstoppedSolmLt husrSolm htab hlot hrev hmax
      (by simpa [hslice] using hmul)
      (by simpa [hslice] using hgt)
      hnoVatCodeSolm hstatus

theorem clipperTakeOweGtTabVatFluxCallFailureRevertEquivCore
    (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPriceSolm evmVatSolm : EVM.State} {outVat : ByteArray} {price : UInt256}
    (hrev :
      RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hsrcMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
        (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size)
    (hsrcGt :
      (clipperTakeSalesTabEVMWord evmPriceSolm I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
            (clipperTakeAmtWord I)) price).toNat)
    (hsrcSliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPriceSolm I).toNat)
    (hvatCodeSolm :
      0 <
        (UInt256.ofNat ((evmPriceSolm.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallVatSolm :
      typedCallViaEVM (config v) evmPriceSolm (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPriceSolm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat)]
        (false, evmVatSolm, outVat) true)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    exact
      clipperTakeOweGtTabVatFluxCallFailureSourceReverts
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm price hmax
        hsrcMul hsrcGt hsrcSliceLot hvatCodeSolm hcallVatSolm hstatus
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

theorem clipperTakeOweGtTabVatFluxCallFailureRevertEquivFromPostWords
    (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPriceSolm evmVatSolm : EVM.State} {outVat : ByteArray} {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hrev :
      RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCodeSolm :
      0 <
        (UInt256.ofNat ((evmPriceSolm.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallVatSolm :
      typedCallViaEVM (config v) evmPriceSolm (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPriceSolm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat)]
        (false, evmVatSolm, outVat) true)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact
    clipperTakeOweGtTabVatFluxCallFailureRevertEquivCore v hcode hwv hdispatch hdec
      hlockedSolm hstoppedSolmLt husrSolm hrev hmax
      (clipperTakeOweGtTabSourceMul_of_post_lot hlot hmul)
      (clipperTakeOweGtTabSourceGt_of_post_words htab hlot hgt)
      (clipperTakeOweGtTabSourceDivLeLot_of_post_words htab hlot hmul hgt)
      hvatCodeSolm hcallVatSolm hstatus

theorem clipperTakeOweGtTabVatFluxCallFailureRevertEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost σPostSolm σVat : AccountMap} {cAVat : Batteries.RBSet AccountAddress compare}
    {AVat : Substate} {evmPriceSolm : EVM.State}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {zVat : Bool}
    {R : List UInt256} {mem outVat : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (rd :
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw outVat (cAVat, σVat) k C)
    (hcallVatEvm :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost, createdAccounts := cAPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (zVat,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true)
    (hzVat : zVat = false)
    (houtVat : outVat.size < UInt256.size)
    (hAccountsPost : accountMapEquiv σPost σPostSolm)
    (hevmPriceAccounts : evmPriceSolm.accountMap = σPostSolm)
    (hevmPriceSigma0 : evmPriceSolm.σ₀ = σ₀)
    (hevmPriceCreated : evmPriceSolm.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPriceSolm.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPriceSolm.blocks = bl)
    (hevmPriceEnv : evmPriceSolm.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceSolm I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceSolm I)
    (hwho : who = (clipperTakeWhoWord I).land solcAddrMask)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat * (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCodeEvm :
      Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hov : R.length + 32 ≤ 1024)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPriceSolm)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  subst zVat
  have hrev :
      RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.clipperTakeVatFluxCallFailure (v := v) (hpatch := hpatch)
      (by simpa using rd) houtVat (by simp only [List.length_cons]; omega)
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          ((evmPriceSolm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
        (σ := σPost) (τ := σPostSolm) (target := clipperTakeVatTarget v)
        (addr := v.vat) hAccountsPost (clipperTakeVatTargetAddress v).symm hvatCodeEvm
  let evmPostEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σPost, createdAccounts := cAPost }
  have hAccountsState : accountMapEquiv evmPostEvm.accountMap evmPriceSolm.accountMap := by
    simpa [evmPostEvm, hevmPriceAccounts] using hAccountsPost
  obtain ⟨σVatSolm, AVatSolm, hcallVatSolmRaw, _hAccountsVat⟩ :=
    typedCallViaEVM_accountMapEquiv_noSubstate
      (evm_solm := evmPriceSolm) (hcall := hcallVatEvm) hAccountsState
      (by simpa [evmPostEvm, initState] using hevmPriceSigma0.symm)
      (by simpa [evmPostEvm, initState] using hevmPriceCreated)
      (by simpa [evmPostEvm, initState] using hevmPriceGenesis)
      (by simpa [evmPostEvm, initState] using hevmPriceBlocks)
      (by simpa [evmPostEvm, initState] using hevmPriceEnv)
  let evmVatSolm : EVM.State :=
    { evmPriceSolm with
      accountMap := σVatSolm
      substate := AVatSolm
      createdAccounts := cAVat }
  have hcallVatSolm :
      typedCallViaEVM (config v) evmPriceSolm (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPriceSolm.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceSolm I) price).toNat)]
        (false, evmVatSolm, outVat) true := by
    simpa [evmVatSolm, hevmPriceEnv, htab, hwho] using hcallVatSolmRaw
  exact
    clipperTakeOweGtTabVatFluxCallFailureRevertEquivFromPostWords v
      hcode hwv hdispatch hdec hlockedSolm hstoppedSolmLt husrSolm
      htab hlot hrev hmax hmul hgt hvatCodeSolm hcallVatSolm hstatus

theorem RD.clipperTakeOweGtTabVatFluxCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zVat : Bool}
    (rd :
      RD code ee g s0 ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o acc k C)
    (hzVat : zVat = false)
    (hosz : o.size < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  subst zVat
  exact RD.clipperTakeVatFluxCallFailure (v := v) (hpatch := hpatch)
    (by simpa using rd) hosz (by simp only [List.length_cons]; omega)

theorem RD.clipperTakeOweGtTabVatFluxCallSuccessToPostGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zVat : Bool}
    (rd :
      RD code ee g s0 ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o acc k C)
    (hzVat : zVat = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C',
      RD code ee g s0 ⟨4414⟩
        (⟨260⟩ :: clipperTakeVatFluxSelectorWord :: clipperTakeVatTarget v ::
          tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
            tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt ::
              id :: R)
        mem aw o acc k' C' := by
  subst zVat
  exact RD.clipperTakeVatFluxCallSuccessToPostGuard (v := v) (hpatch := hpatch)
    (by simpa using rd) (by omega)

theorem RD.clipperTakeOweGtTabVatFluxSuccessSkipWhoVat {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zVat : Bool}
    (rd :
      RD code ee g s0 ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzVat : zVat = true)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hwhoVat : UInt256.land who solcAddrMask = clipperTakeVatTarget v)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C',
      RD code ee g s0 ⟨4701⟩
        (UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask ::
          tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
            tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt ::
              id :: R)
        mem aw o (cA, σ) k' C' := by
  obtain ⟨k4414, C4414, rd4414⟩ :=
    RD.clipperTakeOweGtTabVatFluxCallSuccessToPostGuard (v := v) (hpatch := hpatch)
      rd hzVat (by omega)
  exact RD.clipperTakeSkipClipperCallWhoVat (v := v) (hpatch := hpatch) rd4414
    hdataLen hwhoVat (by omega)

theorem RD.clipperTakeOweGtTabVatFluxSuccessSkipWhoDog {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zVat : Bool}
    (rd :
      RD code ee g s0 ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzVat : zVat = true)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hwhoVat : UInt256.land who solcAddrMask ≠ clipperTakeVatTarget v)
    (hwhoDog : UInt256.land who solcAddrMask = UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C',
      RD code ee g s0 ⟨4701⟩
        (UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask ::
          tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
            tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt ::
              id :: R)
        mem aw o (cA, σ) k' C' := by
  obtain ⟨k4414, C4414, rd4414⟩ :=
    RD.clipperTakeOweGtTabVatFluxCallSuccessToPostGuard (v := v) (hpatch := hpatch)
      rd hzVat (by omega)
  exact RD.clipperTakeSkipClipperCallWhoDog (v := v) (hpatch := hpatch) rd4414
    hdataLen hwhoVat hwhoDog (by omega)

theorem clipperTakeVatFluxPostCallAw_eq :
    UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      UInt256.ofNat 9 := by
  native_decide

theorem clipperTakeVatFluxPostCallMem_size (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {baseMem out : ByteArray}
    (hbaseMem : baseMem.size = 196) :
    (out.write 0 (clipperTakeVatFluxCalldataMem v I who slice baseMem)
      128 (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat).size = 260 := by
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      show (0 : Nat) ≤ (UInt256.ofNat out.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  rw [hmin, byteArray_write_len_zero]
  exact clipperTakeVatFluxCalldataMem_size v I who slice hbaseMem

theorem clipperTakeVatFluxPostCallMem_read64 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {baseMem out : ByteArray}
    (hbaseMem : baseMem.size = 196)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (out.write 0 (clipperTakeVatFluxCalldataMem v I who slice baseMem)
      128 (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      show (0 : Nat) ≤ (UInt256.ofNat out.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  rw [hmin, byteArray_write_len_zero]
  exact clipperTakeVatFluxCalldataMem_read64 v I who slice hbaseMem hread64

theorem RD.clipperTakeOweGtTabVatFluxSuccessWhoVatToVatMoveExtcodesizeGuard
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zVat : Bool}
    (rd :
      RD code ee g s0 ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hwhoVat : UInt256.land who solcAddrMask = clipperTakeVatTarget v)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C',
      RD code ee g s0 ⟨4813⟩
        (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
          ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
            clipperTakeVatTarget v :: UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask ::
              tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
                tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt ::
                  id :: R)
        (clipperTakeVatMoveCalldataMem σ ee tab mem) (UInt256.ofNat 9) o (cA, σ) k' C' := by
  subst aw
  obtain ⟨k4701, C4701, rd4701⟩ :=
    RD.clipperTakeOweGtTabVatFluxSuccessSkipWhoVat (v := v) (hpatch := hpatch)
      rd hzVat hdataLen hwhoVat (by omega)
  exact RD.clipperTakeVatMoveExtcodesizeGuard (v := v) (hpatch := hpatch) rd4701
    hmem hread64 (by omega)

theorem RD.clipperTakeOweGtTabVatFluxSuccessWhoDogToVatMoveExtcodesizeGuard
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zVat : Bool}
    (rd :
      RD code ee g s0 ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hwhoVat : UInt256.land who solcAddrMask ≠ clipperTakeVatTarget v)
    (hwhoDog : UInt256.land who solcAddrMask = UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C',
      RD code ee g s0 ⟨4813⟩
        (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
          ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
            clipperTakeVatTarget v :: UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask ::
              tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
                tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt ::
                  id :: R)
        (clipperTakeVatMoveCalldataMem σ ee tab mem) (UInt256.ofNat 9) o (cA, σ) k' C' := by
  subst aw
  obtain ⟨k4701, C4701, rd4701⟩ :=
    RD.clipperTakeOweGtTabVatFluxSuccessSkipWhoDog (v := v) (hpatch := hpatch)
      rd hzVat hdataLen hwhoVat hwhoDog (by omega)
  exact RD.clipperTakeVatMoveExtcodesizeGuard (v := v) (hpatch := hpatch) rd4701
    hmem hread64 (by omega)

theorem RD.clipperTakeOweGtTabVatFluxSuccessWhoVatVatMoveNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zVat : Bool}
    (rd :
      RD code ee g s0 ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hwhoVat : UInt256.land who solcAddrMask = clipperTakeVatTarget v)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  subst aw
  obtain ⟨k4701, C4701, rd4701⟩ :=
    RD.clipperTakeOweGtTabVatFluxSuccessSkipWhoVat (v := v) (hpatch := hpatch)
      rd hzVat hdataLen hwhoVat (by omega)
  exact RD.clipperTakeVatMoveNoCode (v := v) (hpatch := hpatch) rd4701
    hmem hread64 hcodeSizeVat (by omega)

theorem RD.clipperTakeOweGtTabVatFluxSuccessWhoDogVatMoveNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zVat : Bool}
    (rd :
      RD code ee g s0 ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hwhoVat : UInt256.land who solcAddrMask ≠ clipperTakeVatTarget v)
    (hwhoDog : UInt256.land who solcAddrMask = UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  subst aw
  obtain ⟨k4701, C4701, rd4701⟩ :=
    RD.clipperTakeOweGtTabVatFluxSuccessSkipWhoDog (v := v) (hpatch := hpatch)
      rd hzVat hdataLen hwhoVat hwhoDog (by omega)
  exact RD.clipperTakeVatMoveNoCode (v := v) (hpatch := hpatch) rd4701
    hmem hread64 hcodeSizeVat (by omega)

theorem RD.clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMoveNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zVat : Bool}
    (rd :
      RD code ee g s0 ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hdataLen : dataLen = ⟨0⟩)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  subst aw
  subst zVat
  obtain ⟨k4414, C4414, rd4414⟩ :=
    RD.clipperTakeVatFluxCallSuccessToPostGuard (v := v) (hpatch := hpatch)
      (by simpa using rd) (by omega)
  obtain ⟨k4701, C4701, rd4701⟩ :=
    RD.clipperTakeSkipClipperCallDataEmpty (v := v) (hpatch := hpatch)
      rd4414 hdataLen (by omega)
  exact RD.clipperTakeVatMoveNoCode (v := v) (hpatch := hpatch) rd4701
    hmem hread64 hcodeSizeVat (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeOweGtTabVatFluxSuccessDataEmptyVatMovePostCall
    {cA0 cA gh bl σ₀ σStart σ I} {g : Sat256} {A : Substate} {k C : ℕ}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {zVat : Bool}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd :
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hdataLen : dataLen = ⟨0⟩)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_vat : Batteries.RBSet AccountAddress compare) (σ_vat : AccountMap)
      (zMove : Bool) (outMove : ByteArray) (A_vat : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: UInt256.land (solcSlotWord σ I ⟨1⟩) solcAddrMask ::
            tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
              tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt ::
                id :: R)
        (outMove.write 0 (clipperTakeVatMoveCalldataMem σ I tab mem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outMove.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outMove (cA_vat, σ_vat) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "move" 0
        [.address I.source, .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
          .int (Int.ofNat tab.toNat)]
        (zMove,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_vat
            substate := A_vat
            createdAccounts := cA_vat },
          outMove) true ∧
      outMove.size < UInt256.size := by
  subst aw
  subst zVat
  obtain ⟨k4414, C4414, rd4414⟩ :=
    RD.clipperTakeVatFluxCallSuccessToPostGuard (v := v) (hpatch := hpatch)
      (by simpa using rd) (by omega)
  obtain ⟨k4701, C4701, rd4701⟩ :=
    RD.clipperTakeSkipClipperCallDataEmpty (v := v) (hpatch := hpatch)
      rd4414 hdataLen (by omega)
  obtain ⟨k4813, C4813, rd4813⟩ :=
    RD.clipperTakeVatMoveExtcodesizeGuard (v := v) (hpatch := hpatch)
      rd4701 hmem hread64 (by omega)
  exact RD.clipperTakeVatMovePostCall (v := v) (hpatch := hpatch)
    rd4813 hmem hcodeSizeVat hdepth hperm (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeOweGtTabVatFluxSuccessWhoVatVatMovePostCall
    {cA0 cA gh bl σ₀ σStart σ I} {g : Sat256} {A : Substate} {k C : ℕ}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {zVat : Bool}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd :
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hwhoVat : UInt256.land who solcAddrMask = clipperTakeVatTarget v)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_vat : Batteries.RBSet AccountAddress compare) (σ_vat : AccountMap)
      (zMove : Bool) (outMove : ByteArray) (A_vat : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: UInt256.land (solcSlotWord σ I ⟨1⟩) solcAddrMask ::
            tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
              tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt ::
                id :: R)
        (outMove.write 0 (clipperTakeVatMoveCalldataMem σ I tab mem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outMove.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outMove (cA_vat, σ_vat) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "move" 0
        [.address I.source, .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
          .int (Int.ofNat tab.toNat)]
        (zMove,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_vat
            substate := A_vat
            createdAccounts := cA_vat },
          outMove) ∧
      outMove.size < UInt256.size := by
  obtain ⟨k4813, C4813, rd4813⟩ :=
    RD.clipperTakeOweGtTabVatFluxSuccessWhoVatToVatMoveExtcodesizeGuard
      (v := v) (hpatch := hpatch) rd hzVat haw hdataLen hwhoVat hmem hread64 (by omega)
  exact RD.clipperTakeVatMovePostCall (v := v) (hpatch := hpatch) rd4813
    hmem hcodeSizeVat hdepth hperm (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeOweGtTabVatFluxSuccessWhoDogVatMovePostCall
    {cA0 cA gh bl σ₀ σStart σ I} {g : Sat256} {A : Substate} {k C : ℕ}
    {price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {zVat : Bool}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd :
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzVat : zVat = true)
    (haw : aw = UInt256.ofNat 9)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hwhoVat : UInt256.land who solcAddrMask ≠ clipperTakeVatTarget v)
    (hwhoDog : UInt256.land who solcAddrMask = UInt256.land (solcSlotWord σ I ⟨1⟩) solcAddrMask)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_vat : Batteries.RBSet AccountAddress compare) (σ_vat : AccountMap)
      (zMove : Bool) (outMove : ByteArray) (A_vat : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: UInt256.land (solcSlotWord σ I ⟨1⟩) solcAddrMask ::
            tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
              tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt ::
                id :: R)
        (outMove.write 0 (clipperTakeVatMoveCalldataMem σ I tab mem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outMove.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outMove (cA_vat, σ_vat) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "move" 0
        [.address I.source, .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
          .int (Int.ofNat tab.toNat)]
        (zMove,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_vat
            substate := A_vat
            createdAccounts := cA_vat },
          outMove) ∧
      outMove.size < UInt256.size := by
  obtain ⟨k4813, C4813, rd4813⟩ :=
    RD.clipperTakeOweGtTabVatFluxSuccessWhoDogToVatMoveExtcodesizeGuard
      (v := v) (hpatch := hpatch) rd hzVat haw hdataLen hwhoVat hwhoDog hmem hread64
      (by omega)
  exact RD.clipperTakeVatMovePostCall (v := v) (hpatch := hpatch) rd4813
    hmem hcodeSizeVat hdepth hperm (by omega)

theorem RD.clipperTakeOweGtTabVatMoveCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {dog price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zMove : Bool}
    (rd :
      RD code ee g s0 ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o acc k C)
    (hzMove : zMove = false)
    (hosz : o.size < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  subst zMove
  exact RD.clipperTakeVatMoveCallFailure (v := v) (hpatch := hpatch)
    (by simpa using rd) hosz (by simp only [List.length_cons]; omega)

theorem RD.clipperTakeOweGtTabVatMoveCallSuccessToDogDigs {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {dog price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zMove : Bool}
    (rd :
      RD code ee g s0 ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o acc k C)
    (hzMove : zMove = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C',
      RD code ee g s0 ⟨4850⟩
        (dog :: tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
          tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        mem aw o acc k' C' := by
  subst zMove
  exact RD.clipperTakeVatMoveCallSuccessToDogDigs (v := v) (hpatch := hpatch)
    (by simpa using rd) (by omega)

theorem RD.clipperTakeOweGtTabDogDigsCallSetupNonzero {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zMove : Bool}
    (rd :
      RD code ee g s0 ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzMove : zMove = true)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlotNew : lot.sub (tab.div price) ≠ ⟨0⟩)
    (haw : aw = UInt256.ofNat 9)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4964⟩
      (UInt256.land solcAddrMask dog :: UInt256.land solcAddrMask dog :: ⟨0⟩ ::
        ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ ::
        clipperDogDigsSelectorWord :: UInt256.land solcAddrMask dog ::
        dog :: tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who :: max ::
        amt :: id :: R)
      (clipperDogDigsCalldataMem v tab mem) (UInt256.ofNat 9) o (cA, σ) k' C' := by
  subst aw
  obtain ⟨k4850, C4850, rd4850⟩ :=
    RD.clipperTakeOweGtTabVatMoveCallSuccessToDogDigs
      (v := v) (hpatch := hpatch) rd hzMove (by omega)
  exact RD.clipperTakeDogDigsOweCallSetupNonzero (v := v) (hpatch := hpatch)
    rd4850 hmem hread64 hlotNew (by omega)

theorem RD.clipperTakeOweGtTabDogDigsCallSetupZero {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {zMove : Bool}
    (rd :
      RD code ee g s0 ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem aw o (cA, σ) k C)
    (hzMove : zMove = true)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlotNew : lot.sub (tab.div price) = ⟨0⟩)
    (haw : aw = UInt256.ofNat 9)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4964⟩
      (UInt256.land solcAddrMask dog :: UInt256.land solcAddrMask dog :: ⟨0⟩ ::
        ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ ::
        clipperDogDigsSelectorWord :: UInt256.land solcAddrMask dog ::
        dog :: tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who :: max ::
        amt :: id :: R)
      (clipperDogDigsCalldataMem v tab mem) (UInt256.ofNat 9) o (cA, σ) k' C' := by
  subst aw
  obtain ⟨k4850, C4850, rd4850⟩ :=
    RD.clipperTakeOweGtTabVatMoveCallSuccessToDogDigs
      (v := v) (hpatch := hpatch) rd hzMove (by omega)
  exact RD.clipperTakeDogDigsOweCallSetupZero (v := v) (hpatch := hpatch)
    rd4850 hmem hread64 hlotNew (u256_sub_self tab) (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeOweGtTabDogDigsPostCallNonzero {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {dog price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} (v : ClipperImmutables)
    {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {zMove : Bool}
    (rd :
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        baseMem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hzMove : zMove = true)
    (hbaseMem : baseMem.size = 260)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlotNew : lot.sub (tab.div price) ≠ ⟨0⟩)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ (UInt256.land solcAddrMask dog) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_dog : Batteries.RBSet AccountAddress compare) (σ_dog : AccountMap)
      (zDog : Bool) (outDog : ByteArray) (A_dog : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4980⟩
        ((if zDog then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ ::
          clipperDogDigsSelectorWord :: UInt256.land solcAddrMask dog :: dog ::
            tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) ::
              price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
                max :: amt :: id :: R)
        (outDog.write 0 (clipperDogDigsCalldataMem v tab baseMem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outDog (cA_dog, σ_dog) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask dog))) "digs" 0
        [v.ilk, .int (Int.ofNat tab.toNat)]
        (zDog,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true ∧
      outDog.size < UInt256.size := by
  obtain ⟨k4964, C4964, rd4964⟩ :=
    RD.clipperTakeOweGtTabDogDigsCallSetupNonzero
      (v := v) (hpatch := hpatch) rd hzMove hbaseMem hread64 hlotNew rfl (by omega)
  exact RD.clipperTakeDogDigsPostCall (v := v) (hpatch := hpatch)
    rd4964 hbaseMem hcodeSizeDog hdepth hperm (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeOweGtTabDogDigsPostCallZero {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {dog price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} (v : ClipperImmutables)
    {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {zMove : Bool}
    (rd :
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        baseMem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hzMove : zMove = true)
    (hbaseMem : baseMem.size = 260)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlotNew : lot.sub (tab.div price) = ⟨0⟩)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ (UInt256.land solcAddrMask dog) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_dog : Batteries.RBSet AccountAddress compare) (σ_dog : AccountMap)
      (zDog : Bool) (outDog : ByteArray) (A_dog : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4980⟩
        ((if zDog then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ ::
          clipperDogDigsSelectorWord :: UInt256.land solcAddrMask dog :: dog ::
            tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) ::
              price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
                max :: amt :: id :: R)
        (outDog.write 0 (clipperDogDigsCalldataMem v tab baseMem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outDog (cA_dog, σ_dog) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask dog))) "digs" 0
        [v.ilk, .int (Int.ofNat tab.toNat)]
        (zDog,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true ∧
      outDog.size < UInt256.size := by
  obtain ⟨k4964, C4964, rd4964⟩ :=
    RD.clipperTakeOweGtTabDogDigsCallSetupZero
      (v := v) (hpatch := hpatch) rd hzMove hbaseMem hread64 hlotNew rfl (by omega)
  exact RD.clipperTakeDogDigsPostCall (v := v) (hpatch := hpatch)
    rd4964 hbaseMem hcodeSizeDog hdepth hperm (by omega)

theorem RD.clipperTakeOweGtTabDogDigsNoCodeNonzero {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {k C : ℕ} {zMove : Bool}
    (rd :
      RD code ee g s0 ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem (UInt256.ofNat 9) o (cA, σ) k C)
    (hzMove : zMove = true)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlotNew : lot.sub (tab.div price) ≠ ⟨0⟩)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ (UInt256.land solcAddrMask dog) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨k4964, C4964, rd4964⟩ :=
    RD.clipperTakeOweGtTabDogDigsCallSetupNonzero
      (v := v) (hpatch := hpatch) rd hzMove hmem hread64 hlotNew rfl (by omega)
  exact RD.clipperTakeDogDigsNoCode (v := v) (hpatch := hpatch)
    rd4964 hcodeSizeDog (by omega)

theorem RD.clipperTakeOweGtTabDogDigsNoCodeZero {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {k C : ℕ} {zMove : Bool}
    (rd :
      RD code ee g s0 ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        mem (UInt256.ofNat 9) o (cA, σ) k C)
    (hzMove : zMove = true)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlotNew : lot.sub (tab.div price) = ⟨0⟩)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ (UInt256.land solcAddrMask dog) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨k4964, C4964, rd4964⟩ :=
    RD.clipperTakeOweGtTabDogDigsCallSetupZero
      (v := v) (hpatch := hpatch) rd hzMove hmem hread64 hlotNew rfl (by omega)
  exact RD.clipperTakeDogDigsNoCode (v := v) (hpatch := hpatch)
    rd4964 hcodeSizeDog (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeOweGtTabDogDigsPostCallCasesNonzero
    {cA0 cA gh bl σ₀ σStart σ I} {g : Sat256} {A : Substate} {k C : ℕ}
    {dog price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} (v : ClipperImmutables)
    {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {zMove : Bool}
    (rd :
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        baseMem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hzMove : zMove = true)
    (hbaseMem : baseMem.size = 260)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlotNew : lot.sub (tab.div price) ≠ ⟨0⟩)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ (UInt256.land solcAddrMask dog) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_dog : Batteries.RBSet AccountAddress compare) (σ_dog : AccountMap)
      (zDog : Bool) (outDog : ByteArray) (A_dog : Substate),
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask dog))) "digs" 0
        [v.ilk, .int (Int.ofNat tab.toNat)]
        (zDog,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true ∧
      outDog.size < UInt256.size ∧
      (zDog = false → RDrev code g (initState cA0 gh bl σStart σ₀ g A I)) ∧
      (zDog = true →
        ∃ k' C',
          RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨5003⟩
            (tab :: tab.sub tab :: lot.sub (tab.div price) :: price :: tic :: packed ::
              stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
            (outDog.write 0 (clipperDogDigsCalldataMem v tab baseMem)
              128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat)
            (UInt256.ofNat
              (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
                (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
                (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
            outDog (cA_dog, σ_dog) k' C') := by
  obtain ⟨cA_dog, σ_dog, zDog, outDog, A_dog, k4980, C4980, rd4980,
      hcallDog, houtDog⟩ :=
    RD.clipperTakeOweGtTabDogDigsPostCallNonzero (v := v) (hpatch := hpatch)
      rd hzMove hbaseMem hread64 hlotNew hcodeSizeDog hdepth hperm hov
  refine ⟨cA_dog, σ_dog, zDog, outDog, A_dog, hcallDog, houtDog, ?_, ?_⟩
  · intro hzDog
    subst zDog
    exact RD.clipperTakeDogDigsCallFailure (v := v) (hpatch := hpatch)
      (by simpa using rd4980) houtDog (by simp only [List.length_cons]; omega)
  · intro hzDog
    subst zDog
    exact RD.clipperTakeDogDigsCallSuccessToPostDog (v := v) (hpatch := hpatch)
      (by simpa using rd4980) (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeOweGtTabDogDigsPostCallCasesZero
    {cA0 cA gh bl σ₀ σStart σ I} {g : Sat256} {A : Substate} {k C : ℕ}
    {dog price tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} (v : ClipperImmutables)
    {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {zMove : Bool}
    (rd :
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4829⟩
        ((if zMove then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: tab.div price :: tab :: tab.sub tab ::
            lot.sub (tab.div price) :: price :: tic :: packed :: stopped :: dataLen ::
              dataStart :: who :: max :: amt :: id :: R)
        baseMem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hzMove : zMove = true)
    (hbaseMem : baseMem.size = 260)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlotNew : lot.sub (tab.div price) = ⟨0⟩)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ (UInt256.land solcAddrMask dog) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_dog : Batteries.RBSet AccountAddress compare) (σ_dog : AccountMap)
      (zDog : Bool) (outDog : ByteArray) (A_dog : Substate),
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask dog))) "digs" 0
        [v.ilk, .int (Int.ofNat tab.toNat)]
        (zDog,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true ∧
      outDog.size < UInt256.size ∧
      (zDog = false → RDrev code g (initState cA0 gh bl σStart σ₀ g A I)) ∧
      (zDog = true →
        ∃ k' C',
          RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨5003⟩
            (tab :: tab.sub tab :: lot.sub (tab.div price) :: price :: tic :: packed ::
              stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
            (outDog.write 0 (clipperDogDigsCalldataMem v tab baseMem)
              128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat)
            (UInt256.ofNat
              (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
                (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
                (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
            outDog (cA_dog, σ_dog) k' C') := by
  obtain ⟨cA_dog, σ_dog, zDog, outDog, A_dog, k4980, C4980, rd4980,
      hcallDog, houtDog⟩ :=
    RD.clipperTakeOweGtTabDogDigsPostCallZero (v := v) (hpatch := hpatch)
      rd hzMove hbaseMem hread64 hlotNew hcodeSizeDog hdepth hperm hov
  refine ⟨cA_dog, σ_dog, zDog, outDog, A_dog, hcallDog, houtDog, ?_, ?_⟩
  · intro hzDog
    subst zDog
    exact RD.clipperTakeDogDigsCallFailure (v := v) (hpatch := hpatch)
      (by simpa using rd4980) houtDog (by simp only [List.length_cons]; omega)
  · intro hzDog
    subst zDog
    exact RD.clipperTakeDogDigsCallSuccessToPostDog (v := v) (hpatch := hpatch)
      (by simpa using rd4980) (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakePostDogLotZeroToRemoveJoin {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5003⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      mem aw o (cA, σ) k C)
    (hid : id = clipperYankArgWord ee)
    (hlotNew : lotNew = ⟨0⟩)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (heq :
      let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
      clipperYankArgWord ee = solcSlotWord σ ee (clipperYankActiveSlot lastIndex))
    (hov : R.length + 45 ≤ 1024) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
    let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
    let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
    let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
    ∃ k' C', RD code ee g s0 ⟨8379⟩
      (move :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price ::
        tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      activeMem aw2 o (cA, σ) k' C' := by
  intro lastIndex activeMem aw1 aw2 move
  obtain ⟨k8274, C8274, rd8274⟩ :=
    RD.clipperTakePostDogLotZeroToRemove (v := v) (hpatch := hpatch) rd hlotNew
      (by omega)
  exact RD.clipperYankRemoveIdEqMoveToJoinGeneric (v := v) (hpatch := hpatch)
    (ret := (⟨5020⟩ : UInt256))
    (R := owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
      dataStart :: who :: max :: amt :: id :: R)
    (by simpa [hid] using rd8274)
    hlen heq (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeRemoveJoinToEventTail {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {move owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8379⟩
      (move :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price ::
        tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
        [⟨502⟩, sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hactiveMemSize : 64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) mem).size)
    (hperm : ee.perm = true) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
    let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
    let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
    let saleHashMem := twoWordHashMem (clipperYankArgWord ee) ⟨12⟩ activeMem
    let aw3 := UInt256.ofNat (MachineState.M aw2.toNat 0 32)
    let aw4 := UInt256.ofNat (MachineState.M aw3.toNat 32 32)
    let aw5 := UInt256.ofNat (MachineState.M aw4.toNat 0 64)
    ∃ k' C', RD code ee g s0 ⟨5250⟩
      [owe, tabNew, lotNew, price, tic, packed, stopped, dataLen, dataStart, who, max,
        amt, id, ⟨502⟩, sel]
      saleHashMem aw5 o (cA, clipperYankRemoveAccountMap σ ee lastIndex) k' C' := by
  intro lastIndex activeMem aw1 aw2 saleHashMem aw3 aw4 aw5
  obtain ⟨k5020, C5020, rd5020⟩ :=
    RD.clipperYankRemoveJoinToReturn (v := v) (hpatch := hpatch)
      (ret := (⟨5020⟩ : UInt256))
      (R := owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      rd hlen hactiveMemSize hperm (clipperTakeJumpDest5020 v hpatch)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.clipperTakeRemoveReturnToEventTail (v := v) (hpatch := hpatch)
    (by simpa using rd5020)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeRemoveJoinToReturnSuccess {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {move owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8379⟩
      (move :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price ::
        tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
        [⟨502⟩, sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (haw : aw = UInt256.ofNat 9)
    (hperm : ee.perm = true) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner (clipperYankRemoveAccountMap σ ee lastIndex)
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  intro lastIndex
  obtain ⟨k5250, C5250, rd5250⟩ :=
    RD.clipperTakeRemoveJoinToEventTail (v := v) (hpatch := hpatch) rd hlen
      (by rw [wordAt0Mem_size_of_ge_32 (⟨11⟩ : UInt256) (by omega)]; omega)
      hperm
  refine RD.clipperTakeEventTailSuccess (v := v) (hpatch := hpatch)
    (σ := clipperYankRemoveAccountMap σ ee lastIndex) (owe := owe) (tabNew := tabNew)
    (lotNew := lotNew) (price := price) (tic := tic) (packed := packed)
    (stopped := stopped) (dataLen := dataLen) (dataStart := dataStart) (who := who)
    (max := max) (amt := amt) (id := id) (sel := sel)
    (mem := twoWordHashMem (clipperYankArgWord ee) ⟨12⟩ (wordAt0Mem ⟨11⟩ mem))
    (o := o) (k := k5250) (C := C5250) ?_ ?_ ?_ hperm
  · simpa [lastIndex, haw] using rd5250
  · rw [twoWordHashMem_size_of_ge_64']
    · rw [wordAt0Mem_size_of_ge_32 (⟨11⟩ : UInt256) (by omega), hmem]
    · rw [wordAt0Mem_size_of_ge_32 (⟨11⟩ : UInt256) (by omega), hmem]
      omega
  · exact twoWordHashMem_read64_of_ge_96 (clipperYankArgWord ee) ⟨12⟩
      (by rw [wordAt0Mem_size_of_ge_32 (⟨11⟩ : UInt256) (by omega), hmem]; omega)
      (wordAt0Mem_read64_of_ge_96 (⟨11⟩ : UInt256) (by omega) hread64)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakePostDogLotNonzeroTabNonzeroToEventTail {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel : UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5025⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem (UInt256.ofNat 9) o (cA, σ) k C)
    (htabNew : tabNew ≠ ⟨0⟩)
    (hmem : mem.size = 260)
    (hperm : ee.perm = true) :
    ∃ k' C', RD code ee g s0 ⟨5250⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 9) o
      (cA,
        sstoreAccountMap ee.codeOwner
          (sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨12⟩ id + ⟨1⟩) tabNew)
          (solcMappingSlot ⟨12⟩ id + ⟨2⟩) lotNew)
      k' C' := by
  have h5222 : (D_J code 0).contains (⟨5222⟩ : UInt256) = true := by
    apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 6000) hpatch
    unfold patches patchesFrom offsets immValues
    simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
    cases hIlk : wordBytes? v.ilk with
    | none =>
        simp [hIlk]
        native_decide
    | some bs =>
        simp [hIlk]
        native_decide
  have rd5030pre := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5222⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd5222 := rd5030pre.jumpiT (by clipper_runtime_decode) htabNew h5222 (by evm_ov)
  have rd5227pre := evm_run rd5222 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup14 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5227 := rd5227pre.mstore 0 (wordAt0Mem id mem) (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd5232pre := evm_run rd5227 with [
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd5232 := rd5232pre.mstore 0 (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hsalesBase :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem id ⟨12⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨12⟩ id := by
    rw [clipperYankTwoWordHashMem_read0_64_of_ge id ⟨12⟩ (by omega)]
    unfold solcMappingSlot
    exact mappingSlot_single id ⟨12⟩
  have rd5236pre := evm_run rd5232 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd5236 := rd5236pre.keccak256 0 (solcMappingSlot ⟨12⟩ id)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost hsalesBase
    (by native_decide) (by evm_ov)
  have rd5243pre := evm_run rd5236 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k5244, C5244, rd5244raw⟩ :=
    rd5243pre.sstore hperm (by clipper_runtime_decode) (by evm_ov)
  have rd5244 : RD code ee g s0 ⟨5244⟩
      (solcMappingSlot ⟨12⟩ id :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
        [⟨502⟩, sel])
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 9) o
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨12⟩ id + ⟨1⟩) tabNew)
      k5244 C5244 := by
    simpa using rd5244raw
  have rd5249pre := evm_run rd5244 with [
    raw push1 ⟨2⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k5250, C5250, rd5250raw⟩ :=
    rd5249pre.sstore hperm (by clipper_runtime_decode) (by evm_ov)
  rw [u256_add_comm ⟨2⟩ (solcMappingSlot ⟨12⟩ id)] at rd5250raw
  exact ⟨k5250, C5250, by simpa using rd5250raw⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakePostDogLotZeroToReturnSuccess {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5003⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw o (cA, σ) k C)
    (hid : id = clipperYankArgWord ee)
    (hlotNew : lotNew = ⟨0⟩)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (heq :
      let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
      clipperYankArgWord ee = solcSlotWord σ ee (clipperYankActiveSlot lastIndex))
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (haw : aw = UInt256.ofNat 9)
    (hperm : ee.perm = true) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner (clipperYankRemoveAccountMap σ ee lastIndex)
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  intro lastIndex
  obtain ⟨k8379, C8379, rd8379⟩ :=
    RD.clipperTakePostDogLotZeroToRemoveJoin (v := v) (hpatch := hpatch)
      rd hid hlotNew hlen heq
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.clipperTakeRemoveJoinToReturnSuccess (v := v) (hpatch := hpatch)
    (move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex))
    (rd := by simpa [lastIndex] using rd8379) hlen
    (by rw [wordAt0Mem_size_of_ge_32 (⟨11⟩ : UInt256) (by omega), hmem])
    (wordAt0Mem_read64_of_ge_96 (⟨11⟩ : UInt256) (by omega) hread64)
    (by subst aw; native_decide) hperm

end Benchmarks.Dss.Clipper
