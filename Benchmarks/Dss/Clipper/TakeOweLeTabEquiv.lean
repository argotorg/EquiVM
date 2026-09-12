import Benchmarks.Dss.Clipper.TakeArithmeticElim
import Benchmarks.Dss.Clipper.TakeNoAdjustEquiv
import Benchmarks.Dss.Clipper.TakeChostNonzeroEquiv
import Benchmarks.Dss.Clipper.TakeChostAdjustedNonzeroEquiv
import Benchmarks.Dss.Clipper.TakeLotZeroContinuationEquiv
import Benchmarks.Dss.Clipper.TakeTabZeroContinuationEquiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- End-to-end refinement of the arithmetic half of `take` where the initial
   purchase value does not exceed the tab.  The case split is shared by the
   bytecode and source proofs, so the large body proof only supplies the state
   correspondence established by the preceding `status` call. -/
set_option maxHeartbeats 10000000 in
theorem clipperTakeOweLeTabEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost : AccountMap} {evmPrice : EVM.State}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id sel : UInt256}
    {baseMem rdata : ByteArray} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
      (List.map Param.name (takeTransition v).params)
      (transitionSignature (takeTransition v)).paramTypes I.calldata =
        some (clipperTakeStore I))
    (rd8686 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨8686⟩
      (price :: slice :: ⟨4057⟩ :: slice :: ⟨0⟩ :: tab :: lot :: price ::
        tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
        [⟨502⟩, sel])
      baseMem (UInt256.ofNat 7) rdata (cAPost, σPost) k C)
    (hbaseSize : baseMem.size = 196)
    (hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hAccountsPost : accountMapEquiv σPost evmPrice.accountMap)
    (hevmPriceSigma0 : evmPrice.σ₀ = σ₀)
    (hevmPriceCreated : evmPrice.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPrice.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPrice.blocks = bl)
    (hevmPriceEnv : evmPrice.executionEnv = I)
    (hdataLenEq : dataLen = clipperTakeDataLenWord I)
    (hdataStartEq : dataStart.toNat = 32 + (4 + (clipperTakeDataOffsetWord I).toNat))
    (hlenMax : dataLen.toNat ≤ 4294967296)
    (hpayload : (((I.calldata.toList.drop 4).drop
      ((clipperTakeDataOffsetWord I).toNat + 32)).take
      (clipperTakeDataLenWord I).toNat).length = (clipperTakeDataLenWord I).toNat)
    (hwhoClean : UInt256.land who solcAddrMask = who)
    (hwhoWord : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hidWord : id = clipperTakeIdWord I)
    (hpackedWord : packed = clipperTakeSalesUsrWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPrice I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPrice I)
    (hslice : slice = clipperMinWord
      (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I))
    (hmul : price.toNat * slice.toNat < UInt256.size)
    (howeLe : (UInt256.mul price slice).toNat ≤ tab.toNat)
    (hlocked : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstopped : (solcSlotWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr : clipperTakeSalesUsrWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) (Frame.mk (contract v) (clipperTakeLocalsTic evmLock I))
        evmLock (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok (Frame.mk (contract v) (clipperTakeLocalsSt evmLock I false price)) evmPrice))
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd4057⟩ := RD.clipperTakeOwe0MulSuccess v hpatch rd8686 hmul (by simp)
  have hsliceLe : slice.toNat ≤ lot.toNat := by
    simpa [hslice, hlot, clipperMinWord_comm] using
      clipperMinWord_le_right (clipperTakeAmtWord I)
        (clipperTakeSalesLotEVMWord evmPrice I)
  refine RD.clipperTakeOweLeTabElim v hpatch rd4057 howeLe hbaseSize hbaseRead64
    (by simp) ?_ ?_ ?_ ?_ ?_
  · intro hge hrd
    obtain ⟨_, _, rd4223⟩ := hrd
    have hite := clipperTakeOweEqTabIte v
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPrice I price slice
      (by simpa [htab, u256_mul_comm] using howeLe)
      (by simpa [htab, u256_mul_comm] using hge)
    have htabZero : UInt256.sub tab (UInt256.mul price slice) = ⟨0⟩ := by
      apply Reasoning.Theory.u256_inj
      rw [usub_toNat howeLe]
      simp
      omega
    by_cases hlotZero : UInt256.sub lot slice = ⟨0⟩
    · exact clipperTakeNoAdjustEquiv v hpatch hcode hwv hdispatch hdec rd4223
        hbaseSize hbaseRead64 hAccountsPost hevmPriceSigma0 hevmPriceCreated
        hevmPriceGenesis hevmPriceBlocks hevmPriceEnv hdataLenEq
        hdataStartEq hlenMax hpayload hwhoClean hwhoWord hpackedWord htab hlot
        hslice (by simpa [Nat.mul_comm] using hmul) howeLe hsliceLe
        (by simpa [u256_mul_comm] using hite)
        hlocked hstopped husr hmax hstatus
        (clipperTakeLotZeroContinuation v hpatch hcode hdispatch hdec hidWord
          hlotZero hdepth hperm)
        hdepth hperm
    · exact clipperTakeNoAdjustEquiv v hpatch hcode hwv hdispatch hdec rd4223
        hbaseSize hbaseRead64 hAccountsPost hevmPriceSigma0 hevmPriceCreated
        hevmPriceGenesis hevmPriceBlocks hevmPriceEnv hdataLenEq
        hdataStartEq hlenMax hpayload hwhoClean hwhoWord hpackedWord htab hlot
        hslice (by simpa [Nat.mul_comm] using hmul) howeLe hsliceLe
        (by simpa [u256_mul_comm] using hite)
        hlocked hstopped husr hmax hstatus
        (clipperTakeTabZeroContinuation v hpatch hcode hdispatch hdec hidWord
          htabZero hlotZero hdepth hperm)
        hdepth hperm
  · intro hlt hsliceGe hrd
    obtain ⟨_, _, rd4223⟩ := hrd
    have hsliceEq : slice = lot := Reasoning.Theory.u256_inj (by omega)
    have hlotZero : UInt256.sub lot slice = ⟨0⟩ := by
      rw [hsliceEq]
      exact u256_sub_self lot
    have hite := clipperTakeOweLtTabSliceGeLotIte v
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPrice I price slice
      (by simpa [htab, u256_mul_comm] using howeLe)
      (by simpa [htab, u256_mul_comm] using hlt)
      (by simpa [hlot] using hsliceGe)
    exact clipperTakeNoAdjustEquiv v hpatch hcode hwv hdispatch hdec rd4223
      hbaseSize hbaseRead64 hAccountsPost hevmPriceSigma0 hevmPriceCreated
      hevmPriceGenesis hevmPriceBlocks hevmPriceEnv hdataLenEq
      hdataStartEq hlenMax hpayload hwhoClean hwhoWord hpackedWord htab hlot
      hslice (by simpa [Nat.mul_comm] using hmul) howeLe hsliceLe
      (by simpa [u256_mul_comm] using hite)
      hlocked hstopped husr hmax hstatus
      (clipperTakeLotZeroContinuation v hpatch hcode hdispatch hdec hidWord
        hlotZero hdepth hperm)
      hdepth hperm
  · intro hlt hsliceLt hchostLe hrd
    obtain ⟨_, _, rd4223⟩ := hrd
    exact clipperTakeChostNoAdjustNonzeroEquiv v hpatch hcode hwv hdispatch hdec
      rd4223 hbaseSize hbaseRead64 hAccountsPost hevmPriceSigma0
      hevmPriceCreated hevmPriceGenesis hevmPriceBlocks hevmPriceEnv
      hdataLenEq hdataStartEq hlenMax hpayload hwhoClean hwhoWord hidWord
      hpackedWord htab hlot hslice (by simpa [Nat.mul_comm] using hmul) howeLe hlt
      hsliceLt hchostLe hlocked
      hstopped husr hmax hstatus hdepth hperm
  · intro hlt hsliceLt hremainingLt hchostTab hprice hrd
    obtain ⟨_, _, rd4223⟩ := hrd
    have hmulNat : (UInt256.mul price slice).toNat =
        price.toNat * slice.toNat := by
      rw [u256_mul_toNat, Nat.mod_eq_of_lt hmul]
    have hchostLe : (solcSlotWord σPost I ⟨9⟩).toNat ≤ tab.toNat :=
      Nat.le_of_lt hchostTab
    have hremainingNat : (UInt256.sub tab (UInt256.mul price slice)).toNat =
        tab.toNat - (UInt256.mul price slice).toNat := usub_toNat howeLe
    have hadjustedOweNat :
        (UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).toNat =
          tab.toNat - (solcSlotWord σPost I ⟨9⟩).toNat :=
      usub_toNat hchostLe
    have hadjustedOweLt :
        (UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).toNat <
          (UInt256.mul price slice).toNat := by
      rw [hadjustedOweNat]
      rw [hremainingNat] at hremainingLt
      omega
    have hsliceAdjustedLtSlice :
        ((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price).toNat <
          slice.toNat := by
      rw [udiv_toNat]
      apply Nat.div_lt_of_lt_mul
      simpa [hmulNat, Nat.mul_comm] using hadjustedOweLt
    have hsliceAdjustedLt :
        ((UInt256.sub tab (solcSlotWord σPost I ⟨9⟩)).div price).toNat <
          lot.toNat := lt_trans hsliceAdjustedLtSlice hsliceLt
    exact clipperTakeChostAdjustNonzeroEquiv v hpatch hcode hwv hdispatch hdec
      rd4223 hbaseSize hbaseRead64 hAccountsPost hevmPriceSigma0
      hevmPriceCreated hevmPriceGenesis hevmPriceBlocks hevmPriceEnv
      hdataLenEq hdataStartEq hlenMax hpayload hwhoClean hwhoWord hidWord
      hpackedWord htab hlot hslice (by simpa [Nat.mul_comm] using hmul) howeLe hlt
      hsliceLt hremainingLt
      hchostTab hprice hsliceAdjustedLt hlocked hstopped husr hmax hstatus
      hdepth hperm
  · intro hlt hsliceLt hremainingLt htabLeChost hrev
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
    have hchostEq :
        Solm.EVM.storageLoad evmPrice evmPrice.executionEnv.codeOwner ⟨9⟩ =
          solcSlotWord σPost I ⟨9⟩ := by
      have hslot := accountMapEquiv_storage_findD hAccountsPost I.codeOwner ⟨9⟩ ⟨0⟩
      simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hevmPriceEnv, hslot]
    have hpref := clipperTakeOwe0MulSuccessBlock v evmLock evmPrice I price slice
      (by simpa [Nat.mul_comm] using hmul)
    have hadjust := clipperTakeOweLtTabSliceLtLotChostRequireReverts v
      evmLock evmPrice I price slice
      (by simpa [htab, u256_mul_comm] using howeLe)
      (by simpa [htab, u256_mul_comm] using hlt)
      (by simpa [hlot] using hsliceLt)
      (by simpa [htab, hchostEq, u256_mul_comm] using hremainingLt)
      (by simpa [htab, hchostEq] using htabLeChost)
    have hprefix := execBlockAppendOk hpref
      (ExecBlock.consRevert (stmts := []) hadjust)
    have htail := execBlockAppendReverted
      (suff := clipperTakePostOweFluxStmts v ++ clipperTakeAfterFluxStmts v ++
        clipperTakeAfterMoveStmts v) hprefix
    have hbody : ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
      apply clipperTakeSourceRevertsOfAfterSlice
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmPrice := evmPrice)
        v price hwv hlocked hstopped husr hmax hstatus
      simpa [evm0, evmLock, hslice, clipperTakeAfterSliceStmts,
        List.append_assoc] using htail
    exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

end Benchmarks.Dss.Clipper
