import Benchmarks.Dss.Jug.DripBodyAddReturnsTactic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Jug

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem jugDripBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (jugSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (jugSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dripTransition :=
    jugDispatchDrip hsel
  have hreach := jugReachDripBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hnow :
        (UInt256.ofNat I.header.timestamp).toNat <
          (jugSlotWord (fileDutyRhoSlotFor I) σ_evm I).toNat
    · exact jugDripBodyCoreInvalidNow hcode hsize hwv hsz36 hnow hdispatch
        (jugDecode_drip_ok hsz36) hreach hAccounts
    · have hle :
          (jugSlotWord (fileDutyRhoSlotFor I) σ_evm I).toNat ≤
            (UInt256.ofNat I.header.timestamp).toNat := by
        omega
      by_cases hvatCode :
          Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (dripVatTargetWord σ_evm I) = ⟨0⟩
      · exact jugDripBodyCoreVatIlksNoCode hcode hsize hwv hsz36 hle hdispatch
          (jugDecode_drip_ok hsz36) hreach hAccounts hvatCode
      · by_cases hdepth : I.depth.val < 1024
        · obtain ⟨_, _, hdecoded⟩ := jugDripX_decoded (g := Sat256.ofUInt256 g)
            hsz36 hsize hreach
          obtain ⟨_, _, hnowOk⟩ := jugDripX_nowOk (I := I) hsz36 hle hdecoded
          obtain ⟨gasWord, _, _, rd1399⟩ := RD.jugDripVatIlksCallReady hnowOk hvatCode
          obtain ⟨cA', σ', z, out, Ain, callGas, _, _, hΘ, rd1400, hout⟩ :=
            RD.jugDripVatIlksPostCall rd1399 hdepth
          cases z
          · exact jugDripBodyCoreVatIlksCallFailed
              (cA' := cA') (σ' := σ') (Ain := Ain) (gasWord := callGas)
              hcode hsize hperm hwv hsz36 hle hdispatch (jugDecode_drip_ok hsz36)
              hAccounts hvatCode hdepth (by simpa using rd1400) hΘ hout
          · by_cases hshort : out.size < 64
            · exact jugDripBodyCoreVatIlksReturnDecodeShort
                (cA' := cA') (σ' := σ') (Ain := Ain) (gasWord := callGas)
                hcode hsize hperm hwv hsz36 hle hdispatch (jugDecode_drip_ok hsz36)
                hAccounts hvatCode hdepth (by simpa using rd1400) hΘ hshort hout
            · have hlo : 64 ≤ out.size := by omega
              have _hdecOut := dripVatIlksDecode_ok (out := out) hlo
              obtain ⟨_, _, rd1418⟩ := RD.jugDripVatIlksCallSucceeded (by simpa using rd1400)
              obtain ⟨_, _, _rd1446⟩ := RD.jugDripVatIlksReturnDecodeOk rd1418 hlo hout
              obtain ⟨_, _, _rd1465⟩ := RD.jugDripLoadBaseDuty _rd1446 hsz36 hlo hout
              obtain ⟨_, _, _rd2131⟩ := RD.jugDripToAddRoutine _rd1465
              by_cases haddOverflow :
                  UInt256.size ≤ (jugSlotWord ⟨4⟩ σ' I).toNat +
                    (jugSlotWord (fileDutyDutySlotFor I) σ' I).toNat
              · exact jugDripBodyCoreVatIlksAddOverflow
                  (cA' := cA') (σ' := σ') (Ain := Ain) (callGas := callGas)
                  (out := out)
                  hcode hsize hperm hwv hsz36 hle hdispatch (jugDecode_drip_ok hsz36)
                  hAccounts hvatCode hdepth (by simpa using _rd2131) hΘ _hdecOut
                  haddOverflow
              · jug_drip_add_returns_tac
        · rw [not_lt] at hdepth
          have hdepthEq : I.depth = 1024 := by
            apply Fin.ext
            have hleDepth : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
            omega
          obtain ⟨_, _, hdecoded⟩ := jugDripX_decoded (g := Sat256.ofUInt256 g)
            hsz36 hsize hreach
          obtain ⟨_, _, hnowOk⟩ := jugDripX_nowOk (I := I) hsz36 hle hdecoded
          obtain ⟨gasWord, _, _, rd1399⟩ := RD.jugDripVatIlksCallReady hnowOk hvatCode
          obtain ⟨_, _, rd1400⟩ := RD.jugDripVatIlksCallDepthLimit rd1399 hdepthEq
          exact jugDripBodyCoreVatIlksCallDepthLimit hcode hsize hperm hwv hsz36 hle
            hdispatch (jugDecode_drip_ok hsz36) hAccounts hvatCode hdepthEq rd1400
  · exact jugDripBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Jug
