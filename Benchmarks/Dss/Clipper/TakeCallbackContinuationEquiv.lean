import Benchmarks.Dss.Clipper.TakeCallbackContinuationSource
import Benchmarks.Dss.Clipper.TakeCallbackEquiv
import Benchmarks.Dss.Clipper.TakeDynamicRemove
import Benchmarks.Dss.Clipper.TakeDynamicPostDog

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTypedCallViaEVM_preservesBase {cfg : Config}
    {evm evm' : EVM.State} {tgt : EVM.Address} {name : Ident}
    {value : ℤ} {args : List Value} {z : Bool} {out : ByteArray}
    {callPerm : Bool}
    (hcall : typedCallViaEVM cfg evm tgt name value args
      (z, evm', out) callPerm) :
    evm'.σ₀ = evm.σ₀ ∧
      evm'.genesisBlockHeader = evm.genesisBlockHeader ∧
      evm'.blocks = evm.blocks ∧
      evm'.executionEnv = evm.executionEnv := by
  obtain ⟨_calldata, _hencode, hraw⟩ := hcall
  cases hraw with
  | callMade _hvalue _hTheta hevm' _hvalue' _hdepth =>
      subst hevm'
      exact ⟨rfl, rfl, rfl, rfl⟩
  | callNotMade _hsubstate hevm' _hvalue =>
      subst hevm'
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem clipperTypedCallSyncFromState {cfg : Config}
    {evmEvm evmSolm evmEvm' : EVM.State}
    {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value}
    {z : Bool} {out : ByteArray} {callPerm : Bool}
    (hAccounts : accountMapEquiv evmEvm.accountMap evmSolm.accountMap)
    (hSigma0 : evmSolm.σ₀ = evmEvm.σ₀)
    (hCreated : evmSolm.createdAccounts = evmEvm.createdAccounts)
    (hGenesis : evmSolm.genesisBlockHeader = evmEvm.genesisBlockHeader)
    (hBlocks : evmSolm.blocks = evmEvm.blocks)
    (hEnv : evmSolm.executionEnv = evmEvm.executionEnv)
    (hcall : typedCallViaEVM cfg evmEvm tgt name value args
      (z, evmEvm', out) callPerm) :
    ∃ evmSolm',
      typedCallViaEVM cfg evmSolm tgt name value args
        (z, evmSolm', out) callPerm ∧
      accountMapEquiv evmEvm'.accountMap evmSolm'.accountMap ∧
      evmSolm'.σ₀ = evmEvm'.σ₀ ∧
      evmSolm'.createdAccounts = evmEvm'.createdAccounts ∧
      evmSolm'.genesisBlockHeader = evmEvm'.genesisBlockHeader ∧
      evmSolm'.blocks = evmEvm'.blocks ∧
      evmSolm'.executionEnv = evmEvm'.executionEnv := by
  have hbase := clipperTypedCallViaEVM_preservesBase hcall
  obtain ⟨σSolm', ASolm', hcallSolm, hAccounts'⟩ :=
    typedCallViaEVM_accountMapEquiv_noSubstate hcall hAccounts hSigma0.symm
      hCreated hGenesis hBlocks hEnv
  let evmSolm' : EVM.State :=
    { evmSolm with
      accountMap := σSolm'
      substate := ASolm'
      createdAccounts := evmEvm'.createdAccounts }
  exact ⟨evmSolm', by simpa [evmSolm'] using hcallSolm, by simpa [evmSolm'],
    by simpa [evmSolm'] using hSigma0.trans hbase.1.symm, by simp [evmSolm'],
    by simpa [evmSolm'] using hGenesis.trans hbase.2.1.symm,
    by simpa [evmSolm'] using hBlocks.trans hbase.2.2.1.symm,
    by simpa [evmSolm'] using hEnv.trans hbase.2.2.2.symm⟩

set_option maxHeartbeats 1000000 in
theorem clipperTakeOweGtTabCallbackTailRevertEquivFromPostWords
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
    {evmPrice evmVat evmCb : EVM.State} {outVat : ByteArray}
    {callbackFrame : Frame} {price tab lot : UInt256}
    (htab : tab = clipperTakeSalesTabEVMWord evmPrice I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPrice I)
    (hrev : RDrev code (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat *
      (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat <
      (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evmPrice.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat : typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
      [v.ilk, .address evmPrice.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
        .int (Int.ofNat
          (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat)]
      (true, evmVat, outVat) true)
    (hcallback :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      let slice := clipperMinWord
        (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I)
      let owe0 := UInt256.mul slice price
      let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price
      let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmPrice I)
        (clipperTakeSalesTabEVMWord evmPrice I)
      let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmPrice I) slice'
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLock evmPrice evmVat I price slice owe0 owe0
            slice' tabNew lotNew))
        evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
        (.ok callbackFrame evmCb))
    (htail : ExecBlock (config v) callbackFrame evmCb
      (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet" ++
        clipperTakeAfterMoveStmts v) .reverted)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v)
        { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok (Frame.mk (contract v)
          (clipperTakeLocalsSt evmLock I false price)) evmPrice)) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLock := Solm.EVM.storageStore evm0
    evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let slice := clipperMinWord
    (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I)
  have hsrcMul : slice.toNat * price.toNat < UInt256.size := by
    simpa [slice] using
      (clipperTakeOweGtTabSourceMul_of_post_lot
        (I := I) (evmPrice := evmPrice) (price := price)
        (lot := lot) hlot hmul)
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPrice I).toNat <
        (UInt256.mul slice price).toNat := by
    simpa [slice] using
      (clipperTakeOweGtTabSourceGt_of_post_words
        (I := I) (evmPrice := evmPrice) (price := price)
        (tab := tab) (lot := lot) htab hlot hgt)
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPrice I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words
      (I := I) (evmPrice := evmPrice) (price := price)
      (tab := tab) (lot := lot) htab hlot hmul hgt
  have hafter : ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsSlice evmLock evmPrice I false price slice))
      evmPrice (clipperTakeAfterSliceStmts v) .reverted := by
    exact clipperTakeOweGtTabCallbackTailSource v evmLock evmPrice
      evmVat evmCb I price slice hsrcMul hsrcGt hsliceLot hvatCode hcallVat
      (by simpa [evm0, evmLock, slice] using hcallback) htail
  have hbody := clipperTakeSourceRevertsOfAfterSlice
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (evmPrice := evmPrice)
    v price hwv hlockedSolm hstoppedSolmLt husrSolm hmax hstatus
    (by simpa [evm0, evmLock, slice] using hafter)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

end Benchmarks.Dss.Clipper
