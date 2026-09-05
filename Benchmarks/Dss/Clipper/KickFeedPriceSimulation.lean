import Benchmarks.Dss.Clipper.KickCallEquiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false

/-! Coupled outcomes for the compiler and source executions of the three calls
inside `getFeedPrice`.  Each intermediate constructor records only the facts
needed by the following call. -/

inductive ClipperKickIlksOutcome (v : ClipperImmutables) (code : ByteArray)
    (g : UInt256) (s0 : EVM.State) (I : ExecutionEnv)
    (callerLocals : Store) (sourceEvm : EVM.State)
    (ret scratch lot tab : UInt256) (R : List UInt256) : Prop
  | reverted
      (hsource : ExecStmt (config v) { contract := contract v, locals := callerLocals }
        sourceEvm (.internalCall "getFeedPrice" [] "feedPrice") .reverted)
      (hevm : RDrev code (Sat256.ofUInt256 g) s0)
  | ready
      (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap)
      (outIlks : ByteArray) (evmIlks : EVM.State) (mem : ByteArray) (k C : ℕ)
      (hcode : 0 < (UInt256.ofNat ((sourceEvm.lookupAccount
        (clipperGetFeedPriceSpotterAddress sourceEvm)).option 0
          (fun acc => acc.code.size))).toNat)
      (hcall : typedCallViaEVM (config v) sourceEvm
        (EVM.address (clipperGetFeedPriceSpotterAddress sourceEvm))
        "spotterIlks" 0 [v.ilk] (true, evmIlks, outIlks))
      (hdec : (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
      (halign : ClipperKickCallAligned s0 cA σ I evmIlks)
      (hout : outIlks.size < UInt256.size)
      (hlo : 64 ≤ outIlks.size)
      (hrd : RD code I (Sat256.ofUInt256 g) s0 ⟨8937⟩
        (clipperSpotterIlksPipTarget outIlks ::
          clipperSpotterIlksPipTarget outIlks :: ⟨0⟩ :: ⟨128⟩ :: ⟨4⟩ ::
          ⟨128⟩ :: ⟨64⟩ :: ⟨132⟩ :: clipperPipPeekSelectorWord ::
          clipperSpotterIlksPipTarget outIlks :: ⟨0⟩ :: ⟨0⟩ ::
          clipperSpotterIlksPipWord outIlks :: ⟨0⟩ :: ret :: scratch :: lot ::
          tab :: R)
        mem (UInt256.ofNat 6) outIlks (cA, σ) k C)
      (hmem : mem.size = 192)
      (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
      (hcalldata : (config v).externalABI.encode? "peek" [] =
        some (mem.readWithPadding 128 4))

theorem clipperKickSimulateSpotterIlks
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {g : UInt256} {s0 sourceEvm : EVM.State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {callerLocals : Store}
    {ret scratch lot tab : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (hrd : RD code I (Sat256.ofUInt256 g) s0 ⟨8728⟩
      (ret :: scratch :: lot :: tab :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (halign : ClipperKickCallAligned s0 cA σ I sourceEvm)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 101 ≤ 1024) :
    ClipperKickIlksOutcome v code g s0 I callerLocals sourceEvm
      ret scratch lot tab R := by
  by_cases hspotter : extCodeSizeWord σ (clipperSpotterTarget σ I) = ⟨0⟩
  · have hevm := RD.clipperKickGetFeedPriceSpotterIlksNoCode
      v hpatch hrd hspotter hmem hread64 (by omega)
    have haddr := clipperKickSpotterAddress_eq_of_aligned halign
    have hnoCode := clipperKickNoCode_of_aligned halign haddr hspotter
    exact .reverted
      (clipperGetFeedPriceCallRevertsSpotterIlksNoCode
        v sourceEvm callerLocals "feedPrice" hnoCode)
      hevm
  · obtain ⟨cAIlks, σIlks, zIlks, outIlks, AIlks, k8840, C8840,
        rd8840, hcallIlks, houtIlks⟩ :=
      RD.clipperKickGetFeedPriceSpotterIlksPostCall
        v hpatch hrd hspotter hdepth hperm hmem hread64 (by omega)
    cases zIlks
    · have hevm := RD.clipperGetFeedPriceSpotterIlksCallFailure
        v hpatch (by simpa using rd8840) houtIlks
          (by simp only [List.length_cons, List.length_nil]; omega)
      obtain ⟨σIlksSolm, AIlksSolm, evmIlks, hevmeq, hcallIlksSolm,
          halignIlks⟩ := clipperKickCallAligned_transport halign hcallIlks
      have haddr := clipperKickSpotterAddress_eq_of_aligned halign
      have hcodeSolm := clipperKickHasCode_of_aligned halign haddr hspotter
      have hsource := clipperGetFeedPriceCallRevertsSpotterIlksCallFailure
        v callerLocals "feedPrice" hcodeSolm (by simpa [haddr] using hcallIlksSolm)
      exact .reverted hsource hevm
    · obtain ⟨k8861, C8861, rd8861⟩ :=
        RD.clipperGetFeedPriceSpotterIlksCallSuccessToDecode
          v hpatch (by simpa using rd8840) (by omega)
      by_cases hshort : outIlks.size < 64
      · have hevm := RD.clipperKickGetFeedPriceSpotterIlksDecodeShortReverts
          v hpatch rd8861 hmem hread64 hshort houtIlks (by omega)
        obtain ⟨σIlksSolm, AIlksSolm, evmIlks, hevmeq, hcallIlksSolm,
            halignIlks⟩ := clipperKickCallAligned_transport halign hcallIlks
        have haddr := clipperKickSpotterAddress_eq_of_aligned halign
        have hcodeSolm := clipperKickHasCode_of_aligned halign haddr hspotter
        have hdec := clipperSpotterIlksDecode_none_short (v := v) hshort
        have hsource := clipperGetFeedPriceCallRevertsSpotterIlksDecode
          v callerLocals "feedPrice" hcodeSolm
            (by simpa [haddr] using hcallIlksSolm) hdec
        exact .reverted hsource hevm
      · have hlo : 64 ≤ outIlks.size := by omega
        obtain ⟨k8937, C8937, rd8937⟩ :=
          RD.clipperKickGetFeedPriceSpotterIlksDecodeOkToPipPeekExtcodesizeGuard
            v hpatch rd8861 hmem hread64 hlo houtIlks (by omega)
        obtain ⟨σIlksSolm, AIlksSolm, evmIlks, hevmeq, hcallIlksSolm,
            halignIlks⟩ := clipperKickCallAligned_transport halign hcallIlks
        have haddr := clipperKickSpotterAddress_eq_of_aligned halign
        have hcodeSolm := clipperKickHasCode_of_aligned halign haddr hspotter
        let memPeek := clipperPipPeekSelectorMem
          (clipperSpotterIlksPostCallMem v mem outIlks)
        have hmemPost := clipperKickSpotterIlksPostCallMem_size_long
          v hmem hlo houtIlks
        have hmemPeek : memPeek.size = 192 := by
          simpa [memPeek] using clipperKickPipPeekSelectorMem_size hmemPost
        have hreadPost := clipperKickSpotterIlksPostCallMem_read64
          v hmem hread64 houtIlks
        have hreadPeek : memPeek.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memPeek] using clipperKickPipPeekSelectorMem_read64 hmemPost hreadPost
        have hcalldata : (config v).externalABI.encode? "peek" [] =
            some (memPeek.readWithPadding 128 4) := by
          simpa [memPeek] using clipperPipPeekEncode_eq v (by omega : 132 ≤
            (clipperSpotterIlksPostCallMem v mem outIlks).size)
        exact .ready cAIlks σIlks outIlks evmIlks memPeek k8937 C8937
          hcodeSolm (by simpa [haddr] using hcallIlksSolm)
          (clipperSpotterIlksDecode_ok hlo)
          (by simpa [hevmeq] using halignIlks) houtIlks hlo
          (by simpa [memPeek] using rd8937) hmemPeek hreadPeek hcalldata

inductive ClipperKickPeekOutcome (v : ClipperImmutables) (code : ByteArray)
    (g : UInt256) (s0 : EVM.State) (I : ExecutionEnv)
    (callerLocals : Store) (sourceEvm : EVM.State)
    (ret scratch lot tab : UInt256) (R : List UInt256) : Prop
  | reverted
      (hsource : ExecStmt (config v) { contract := contract v, locals := callerLocals }
        sourceEvm (.internalCall "getFeedPrice" [] "feedPrice") .reverted)
      (hevm : RDrev code (Sat256.ofUInt256 g) s0)
  | ready
      (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap)
      (outIlks outPeek : ByteArray) (evmPeek : EVM.State)
      (mem : ByteArray) (k C : ℕ)
      (hprefix : ExecBlock (config v) { contract := contract v, locals := ∅ }
        sourceEvm (clipperGetFeedPriceSuccessPrefixStmts v)
        (.ok (Frame.mk (contract v)
          (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek))
      (halign : ClipperKickCallAligned s0 cA σ I evmPeek)
      (hout : outPeek.size < UInt256.size)
      (hlo : 64 ≤ outPeek.size)
      (hrd : RD code I (Sat256.ofUInt256 g) s0 ⟨9079⟩
        (clipperPipPeekHasWord outPeek :: clipperPipPeekValueWord outPeek ::
          clipperSpotterIlksPipWord outIlks :: ⟨0⟩ :: ret :: scratch :: lot :: tab :: R)
        mem (UInt256.ofNat 6) outPeek (cA, σ) k C)
      (hmem : mem.size = 192)
      (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)

theorem clipperKickSimulatePipPeek
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {g : UInt256} {s0 sourceEvm : EVM.State} {I : ExecutionEnv}
    {callerLocals : Store} {ret scratch lot tab : UInt256} {R : List UInt256}
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 101 ≤ 1024)
    (hilks : ClipperKickIlksOutcome v code g s0 I callerLocals sourceEvm
      ret scratch lot tab R) :
    ClipperKickPeekOutcome v code g s0 I callerLocals sourceEvm
      ret scratch lot tab R := by
  cases hilks with
  | reverted hsource hevm => exact .reverted hsource hevm
  | ready cA σ outIlks evmIlks mem k C hcodeIlks hcallIlks hdecIlks
      halign houtIlks hloIlks hrd hmem hread64 hcalldata =>
    by_cases hpip : extCodeSizeWord σ (clipperSpotterIlksPipTarget outIlks) = ⟨0⟩
    · have hevm := RD.clipperGetFeedPricePipPeekNoCode
        v hpatch hrd hpip (by simp only [List.length_cons]; omega)
      have hnoCode := clipperKickNoCode_of_aligned halign
        (clipperSpotterIlksPipAddress_eq_target outIlks) hpip
      have hsource := clipperGetFeedPriceCallRevertsPipPeekNoCode
        v callerLocals "feedPrice" hcodeIlks hcallIlks hdecIlks hnoCode
      exact .reverted hsource hevm
    · obtain ⟨cAPeek, σPeek, zPeek, outPeek, APeek, k8953, C8953,
          rd8953, hcallPeek, houtPeek⟩ :=
        RD.clipperKickGetFeedPricePipPeekPostCall
          v hpatch hrd hpip hdepth hperm hcalldata
            (clipperSpotterIlksPipAddress_eq_target outIlks).symm
            (by simp only [List.length_cons, List.length_nil]; omega)
      cases zPeek
      · have hevm := RD.clipperGetFeedPricePipPeekCallFailure
          v hpatch (by simpa using rd8953) houtPeek
            (by simp only [List.length_cons, List.length_nil]; omega)
        obtain ⟨σPeekSolm, APeekSolm, evmPeek, hevmeq, hcallPeekSolm,
            halignPeek⟩ := clipperKickCallAligned_transport halign hcallPeek
        have hcodePip := clipperKickHasCode_of_aligned halign
          (clipperSpotterIlksPipAddress_eq_target outIlks) hpip
        have hsource := clipperGetFeedPriceCallRevertsPipPeekCallFailure
          v callerLocals "feedPrice" hcodeIlks hcallIlks hdecIlks hcodePip
            (by simpa using hcallPeekSolm)
        exact .reverted hsource hevm
      · obtain ⟨k8974, C8974, rd8974⟩ :=
          RD.clipperGetFeedPricePipPeekCallSuccessToDecode
            v hpatch (by simpa using rd8953)
              (by simp only [List.length_cons, List.length_nil]; omega)
        by_cases hshort : outPeek.size < 64
        · have hevm := RD.clipperKickGetFeedPricePipPeekDecodeShortReverts
            v hpatch rd8974
              (clipperKickPipPeekPostCallMem_size hmem houtPeek)
              (clipperKickPipPeekPostCallMem_read64 hmem hread64 houtPeek)
              hshort houtPeek
                (by simp only [List.length_cons, List.length_nil]; omega)
          obtain ⟨σPeekSolm, APeekSolm, evmPeek, hevmeq, hcallPeekSolm,
              halignPeek⟩ := clipperKickCallAligned_transport halign hcallPeek
          have hcodePip := clipperKickHasCode_of_aligned halign
            (clipperSpotterIlksPipAddress_eq_target outIlks) hpip
          have hdecPeek := clipperPipPeekDecode_none_short (v := v) hshort
          have hsource := clipperGetFeedPriceCallRevertsPipPeekDecode
            v callerLocals "feedPrice" hcodeIlks hcallIlks hdecIlks hcodePip
              (by simpa using hcallPeekSolm) hdecPeek
          exact .reverted hsource hevm
        · have hlo : 64 ≤ outPeek.size := by omega
          let memPost := clipperPipPeekPostCallMem mem outPeek
          have hmemPost : memPost.size = 192 := by
            simpa [memPost] using clipperKickPipPeekPostCallMem_size hmem houtPeek
          have hreadPost : memPost.readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ := by
            simpa [memPost] using
              clipperKickPipPeekPostCallMem_read64 hmem hread64 houtPeek
          have hread128 : memPost.readWithPadding 128 32 = outPeek.extract 0 32 := by
            simpa [memPost] using
              clipperKickPipPeekPostCallMem_read128_long hmem hlo houtPeek
          have hread160 : memPost.readWithPadding 160 32 = outPeek.extract 32 64 := by
            simpa [memPost] using
              clipperKickPipPeekPostCallMem_read160_long hmem hlo houtPeek
          by_cases hhas : clipperPipPeekHasWord outPeek = ⟨0⟩
          · have hevm := RD.clipperKickGetFeedPricePipPeekHasFalseReverts
              v hpatch rd8974 hmemPost hreadPost hread128 hread160 hlo houtPeek
                hhas (by simp only [List.length_cons, List.length_nil]; omega)
            obtain ⟨σPeekSolm, APeekSolm, evmPeek, hevmeq, hcallPeekSolm,
                halignPeek⟩ := clipperKickCallAligned_transport halign hcallPeek
            have hcodePip := clipperKickHasCode_of_aligned halign
              (clipperSpotterIlksPipAddress_eq_target outIlks) hpip
            have hdecPeek := clipperPipPeekDecode_ok (v := v) hlo
            have hsource := clipperGetFeedPriceCallRevertsPipPeekHasFalse
              v callerLocals "feedPrice" hcodeIlks hcallIlks hdecIlks hcodePip
                (by simpa using hcallPeekSolm) hdecPeek hhas
            exact .reverted hsource hevm
          · obtain ⟨k9079, C9079, rd9079⟩ :=
              RD.clipperKickGetFeedPricePipPeekHasTrueToValBln
                v hpatch rd8974 hmemPost hreadPost hread128 hread160 hlo
                  houtPeek hhas
                    (by simp only [List.length_cons, List.length_nil]; omega)
            obtain ⟨σPeekSolm, APeekSolm, evmPeek, hevmeq, hcallPeekSolm,
                halignPeek⟩ := clipperKickCallAligned_transport halign hcallPeek
            have hcodePip := clipperKickHasCode_of_aligned halign
              (clipperSpotterIlksPipAddress_eq_target outIlks) hpip
            have hdecPeek := clipperPipPeekDecode_ok (v := v) hlo
            have hprefix := clipperGetFeedPricePrefixToHas
              v hcodeIlks hcallIlks hdecIlks hcodePip
                (by simpa using hcallPeekSolm) hdecPeek hhas
            exact .ready cAPeek σPeek outIlks outPeek evmPeek memPost k9079 C9079
              (by simpa [hevmeq] using hprefix)
              (by simpa [hevmeq] using halignPeek) houtPeek hlo
              (by simpa [memPost] using rd9079) hmemPost hreadPost

inductive ClipperKickFeedPriceOutcome (v : ClipperImmutables) (code : ByteArray)
    (g : UInt256) (s0 : EVM.State) (I : ExecutionEnv)
    (callerLocals : Store) (sourceEvm : EVM.State)
    (ret scratch lot tab : UInt256) (R : List UInt256) : Prop
  | reverted
      (hsource : ExecStmt (config v) (Frame.mk (contract v) callerLocals)
        sourceEvm (.internalCall "getFeedPrice" [] "feedPrice") .reverted)
      (hevm : RDrev code (Sat256.ofUInt256 g) s0)
  | invalid
      (hsource : ExecStmt (config v) (Frame.mk (contract v) callerLocals)
        sourceEvm (.internalCall "getFeedPrice" [] "feedPrice") .reverted)
      (hevm : RDinvalid code (Sat256.ofUInt256 g) s0)
  | returned
      (feedPrice : UInt256)
      (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap)
      (sourceAfter : EVM.State) (mem : ByteArray) (out : ByteArray) (k C : ℕ)
      (hsource : ExecStmt (config v) (Frame.mk (contract v) callerLocals)
        sourceEvm (.internalCall "getFeedPrice" [] "feedPrice")
        (.ok (Frame.mk (contract v) (callerLocals.insert "feedPrice"
          (.int (Int.ofNat feedPrice.toNat)))) sourceAfter))
      (halign : ClipperKickCallAligned s0 cA σ I sourceAfter)
      (hrd : RD code I (Sat256.ofUInt256 g) s0 ret
        (feedPrice :: scratch :: lot :: tab :: R)
        mem (UInt256.ofNat 6) out (cA, σ) k C)
      (hmem : mem.size = 192)
      (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)

theorem clipperKickFinishFeedPrice
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {g : UInt256} {s0 sourceEvm : EVM.State} {I : ExecutionEnv}
    {callerLocals : Store} {ret scratch lot tab : UInt256} {R : List UInt256}
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 101 ≤ 1024)
    (hpeek : ClipperKickPeekOutcome v code g s0 I callerLocals sourceEvm
      ret scratch lot tab R) :
    ClipperKickFeedPriceOutcome v code g s0 I callerLocals sourceEvm
      ret scratch lot tab R := by
  cases hpeek with
  | reverted hsource hevm => exact .reverted hsource hevm
  | ready cA σ outIlks outPeek evmPeek mem k C hprefix halign houtPeek
      hloPeek hrd hmem hread64 =>
    by_cases hoverVal : UInt256.size ≤
        (clipperPipPeekValueWord outPeek).toNat * (⟨1000000000⟩ : UInt256).toNat
    · have hevm := RD.clipperGetFeedPriceValBlnOverflowReverts
        v hpatch hrd hoverVal
          (by simp only [List.length_cons, List.length_nil]; omega)
      have htail := clipperGetFeedPriceTailRevertsValBlnOverflow
        v evmPeek outIlks outPeek (by omega) hoverVal
      have hsource := clipperGetFeedPriceSuccessCallRevertsOfTail
        v callerLocals "feedPrice" hprefix htail
      exact .reverted hsource hevm
    · have hmulVal :
          (clipperPipPeekValueWord outPeek).toNat *
            (⟨1000000000⟩ : UInt256).toNat < UInt256.size := by omega
      obtain ⟨k9164, C9164, rd9164⟩ :=
        RD.clipperKickGetFeedPriceValBlnToParExtcodesizeGuard
          v hpatch hrd hmulVal hmem hread64
            (by simp only [List.length_cons, List.length_nil]; omega)
      by_cases hspotter : extCodeSizeWord σ (clipperSpotterTarget σ I) = ⟨0⟩
      · have hevm := RD.clipperGetFeedPriceParNoCode
          v hpatch rd9164 hspotter
            (by simp only [List.length_cons, List.length_nil]; omega)
        have haddr := clipperKickSpotterAddress_eq_of_aligned halign
        have hnoCode := clipperKickNoCode_of_aligned halign haddr hspotter
        have htail := clipperGetFeedPriceTailRevertsParNoCode
          v evmPeek outIlks outPeek (by omega) hmulVal hnoCode
        have hsource := clipperGetFeedPriceSuccessCallRevertsOfTail
          v callerLocals "feedPrice" hprefix htail
        exact .reverted hsource hevm
      · let memPar := clipperSpotterParSelectorMem mem
        have hmemPar : memPar.size = 192 := by
          simpa [memPar] using clipperKickSpotterParSelectorMem_size hmem
        have hreadPar : memPar.readWithPadding 64 32 =
            UInt256.toByteArray ⟨128⟩ := by
          simpa [memPar] using clipperKickSpotterParSelectorMem_read64 hmem hread64
        have hcalldata : (config v).externalABI.encode? "par" [] =
            some (memPar.readWithPadding 128 4) := by
          simpa [memPar] using clipperKickSpotterParEncode_eq v hmem
        obtain ⟨cAPar, σPar, zPar, outPar, APar, k9180, C9180,
            rd9180, hcallPar, houtPar⟩ :=
          RD.clipperKickGetFeedPriceParPostCall
            v hpatch rd9164 hspotter hdepth hperm hcalldata rfl
              (by simp only [List.length_cons, List.length_nil]; omega)
        cases zPar
        · have hevm := RD.clipperGetFeedPriceParCallFailure
            v hpatch (by simpa using rd9180) houtPar
              (by simp only [List.length_cons, List.length_nil]; omega)
          obtain ⟨σParSolm, AParSolm, evmPar, hevmeq, hcallParSolm,
              halignPar⟩ := clipperKickCallAligned_transport halign hcallPar
          have haddr := clipperKickSpotterAddress_eq_of_aligned halign
          have hcodePar := clipperKickHasCode_of_aligned halign haddr hspotter
          have htail := clipperGetFeedPriceTailRevertsParCallFailure
            v outIlks outPeek (by omega) hmulVal hcodePar
              (by simpa [haddr] using hcallParSolm)
          have hsource := clipperGetFeedPriceSuccessCallRevertsOfTail
            v callerLocals "feedPrice" hprefix htail
          exact .reverted hsource hevm
        · obtain ⟨k9201, C9201, rd9201⟩ :=
            RD.clipperGetFeedPriceParCallSuccessToDecode
              v hpatch (by simpa using rd9180)
                (by simp only [List.length_cons, List.length_nil]; omega)
          by_cases hshort : outPar.size < 32
          · have hevm := RD.clipperKickGetFeedPriceParDecodeShortReverts
              v hpatch rd9201
                (clipperKickSpotterParPostCallMem_size hmemPar houtPar)
                (clipperKickSpotterParPostCallMem_read64 hmemPar hreadPar houtPar)
                hshort houtPar
                (by simp only [List.length_cons, List.length_nil]; omega)
            obtain ⟨σParSolm, AParSolm, evmPar, hevmeq, hcallParSolm,
                halignPar⟩ := clipperKickCallAligned_transport halign hcallPar
            have haddr := clipperKickSpotterAddress_eq_of_aligned halign
            have hcodePar := clipperKickHasCode_of_aligned halign haddr hspotter
            have hdec := clipperSpotterParDecode_none_short (v := v) hshort
            have htail := clipperGetFeedPriceTailRevertsParDecode
              v outIlks outPeek (by omega) hmulVal hcodePar
                (by simpa [haddr] using hcallParSolm) hdec
            have hsource := clipperGetFeedPriceSuccessCallRevertsOfTail
              v callerLocals "feedPrice" hprefix htail
            exact .reverted hsource hevm
          · have hlo : 32 ≤ outPar.size := by omega
            let memPost := clipperSpotterParPostCallMem memPar outPar
            have hmemPost : memPost.size = 192 := by
              simpa [memPost] using
                clipperKickSpotterParPostCallMem_size hmemPar houtPar
            have hreadPost : memPost.readWithPadding 64 32 =
                UInt256.toByteArray ⟨128⟩ := by
              simpa [memPost] using
                clipperKickSpotterParPostCallMem_read64 hmemPar hreadPar houtPar
            have hread128 : memPost.readWithPadding 128 32 = outPar.extract 0 32 := by
              simpa [memPost] using
                clipperKickSpotterParPostCallMem_read128_long hmemPar hlo houtPar
            obtain ⟨k9290, C9290, rd9290⟩ :=
              RD.clipperKickGetFeedPriceParDecodeOkToRdiv
                v hpatch rd9201 hmemPost hreadPost hread128 hlo houtPar
                  (by simp only [List.length_cons, List.length_nil]; omega)
            obtain ⟨σParSolm, AParSolm, evmPar, hevmeq, hcallParSolm,
                halignPar⟩ := clipperKickCallAligned_transport halign hcallPar
            have haddr := clipperKickSpotterAddress_eq_of_aligned halign
            have hcodePar := clipperKickHasCode_of_aligned halign haddr hspotter
            have hdec := clipperSpotterParDecode_ok (v := v) hlo
            let valBln := UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩
            by_cases hoverRdiv : UInt256.size ≤ valBln.toNat * clipperRayWord.toNat
            · have hevm := RD.clipperGetFeedPriceRdivOverflowReverts
                v hpatch (by simpa [valBln] using rd9290) hoverRdiv
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have hrdiv := clipperGetFeedPriceRdivRevertsMul
                v evmPar outIlks outPeek outPar (by simpa [valBln] using hoverRdiv)
              have htail := clipperGetFeedPriceTailOfParSuccess
                v outIlks outPeek (by omega) hmulVal hcodePar
                  (by simpa [haddr] using hcallParSolm) hdec hrdiv
              have hsource := clipperGetFeedPriceSuccessCallRevertsOfTail
                v callerLocals "feedPrice" hprefix htail
              exact .reverted hsource hevm
            · have hmulRdiv : valBln.toNat * clipperRayWord.toNat < UInt256.size := by
                omega
              by_cases hzero : clipperSpotterParWord outPar = ⟨0⟩
              · have hevm := RD.clipperGetFeedPriceRdivZeroInvalid
                  v hpatch (by simpa [valBln] using rd9290) hmulRdiv hzero
                    (by simp only [List.length_cons, List.length_nil]; omega)
                have hrdiv := clipperGetFeedPriceRdivRevertsDivZero
                  v evmPar outIlks outPeek outPar (by simpa [valBln] using hmulRdiv)
                    hzero
                have htail := clipperGetFeedPriceTailOfParSuccess
                  v outIlks outPeek (by omega) hmulVal hcodePar
                    (by simpa [haddr] using hcallParSolm) hdec hrdiv
                have hsource := clipperGetFeedPriceSuccessCallRevertsOfTail
                  v callerLocals "feedPrice" hprefix htail
                exact .invalid hsource hevm
              · obtain ⟨kret, Cret, rdret⟩ := RD.clipperGetFeedPriceRdivSuccess
                  v hpatch (by simpa [valBln] using rd9290) hmulRdiv hzero hret
                    (by simp only [List.length_cons, List.length_nil]; omega)
                let feedPrice := UInt256.div (UInt256.mul valBln clipperRayWord)
                  (clipperSpotterParWord outPar)
                have hrdiv := clipperGetFeedPriceRdivReturns
                  v evmPar outIlks outPeek outPar (by simpa [valBln] using hmulRdiv)
                    hzero
                have htail := clipperGetFeedPriceTailOfParSuccess
                  v outIlks outPeek (by omega) hmulVal hcodePar
                    (by simpa [haddr] using hcallParSolm) hdec hrdiv
                have hsourceRaw := clipperGetFeedPriceSuccessCallReturnsOfTail
                  v callerLocals "feedPrice" hprefix htail
                have hsource : ExecStmt (config v)
                    (Frame.mk (contract v) callerLocals) sourceEvm
                    (.internalCall "getFeedPrice" [] "feedPrice")
                    (.ok (Frame.mk (contract v) (callerLocals.insert "feedPrice"
                      (.int (Int.ofNat feedPrice.toNat)))) evmPar) := by
                  simpa [feedPrice, valBln, collapseReturns] using hsourceRaw
                exact .returned feedPrice cAPar σPar evmPar memPost outPar kret Cret
                  hsource (by simpa [hevmeq] using halignPar)
                  (by simpa [feedPrice, valBln, memPost] using rdret)
                  hmemPost hreadPost

theorem clipperKickSimulateGetFeedPrice
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {g : UInt256} {s0 sourceEvm : EVM.State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {callerLocals : Store}
    {ret scratch lot tab : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (hrd : RD code I (Sat256.ofUInt256 g) s0 ⟨8728⟩
      (ret :: scratch :: lot :: tab :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (halign : ClipperKickCallAligned s0 cA σ I sourceEvm)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 101 ≤ 1024) :
    ClipperKickFeedPriceOutcome v code g s0 I callerLocals sourceEvm
      ret scratch lot tab R := by
  have hilks := clipperKickSimulateSpotterIlks v hpatch
    (callerLocals := callerLocals) hrd halign hdepth hperm hmem hread64 hov
  have hpeek := clipperKickSimulatePipPeek v hpatch hdepth hperm hov hilks
  exact clipperKickFinishFeedPrice v hpatch hdepth hperm hret hov hpeek

end Benchmarks.Dss.Clipper
