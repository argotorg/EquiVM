import Reasoning.SolmRpow
import Benchmarks.Dss.Jug.DripBodyCore
import Benchmarks.Dss.Jug.DripSourceGenericFold
import Benchmarks.Dss.Jug.DripSourceGenericRpow
import Benchmarks.Dss.Jug.RpowGeneric
import Mathlib.Util.ParseCommand
import Lean.Elab.Tactic

open Lean Elab Tactic
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

open Reasoning.Theory.RpowB

namespace Benchmarks.Dss.Jug

set_option maxHeartbeats 1000000

private def jugDripGenericAgeScript : String := r#"
let locals := dripLocals I
let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
have hrhoWord :
    solcSlotWordAt (fileDutyRhoSlotFor I) σ I =
      solcSlotWordAt (fileDutyRhoSlotFor I) σ I :=
  rfl
have hleSolm :
    (solcSlotWordAt (fileDutyRhoSlotFor I) σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat := by
  rw [← hrhoWord]
  exact hle
have hcodeSizeSolm :
    Reasoning.Theory.extCodeSizeWord σ
        (dripVatTargetWord σ I) ≠ ⟨0⟩ :=
  hvatCode
have hvatCodeSolm :
    0 <
      (UInt256.ofNat
        (((initState σ σ₀
          (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0
              (fun acc => acc.code.size))).toNat :=
  dripVatCode_pos_of_codeSize_ne_zero
    (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hcodeSizeSolm
rcases hΘ with ⟨g'', A', hΘ'⟩
have hΘE :
    (σ', g'', A', true, out) =
      Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
        (AccountAddress.ofUInt256
          (UInt256.ofNat evm.executionEnv.codeOwner))
        evm.executionEnv.sender
        (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
        (toExecute evm.accountMap
          (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
        callGas (UInt256.ofNat evm.executionEnv.gasPrice)
        ⟨0⟩ ⟨0⟩
        ((dripVatIlksCalldataMem I
          (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
        (evm.executionEnv.depth + 1)
        (evm.executionEnv.header) (evm.executionEnv.blobVersionedHashes) (evm.executionEnv.blocks) true := by
  simpa [evm, initState, hperm] using hΘ'
let σ'_solm := σ'
let A'_solm := A'
have hcallSolm :
    typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
      [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
      (true, { evm with accountMap := σ', substate := A' }, out) true := by
  simpa [evm] using
    callCoincides
      (initStateDepth_ne_1024_of_lt
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hdepth)
      (by
        rw [dripVatAddress_eq_target σ I]
        exact address_of_val _)
      (dripVatIlksEncode_eq I hsz36) hΘE
let evmVatS :=
  { evm with
    accountMap := σ'_solm,
    substate := A'_solm }
have hbaseWord : solcSlotWordAt ⟨4⟩ σ' I =
    solcSlotWordAt ⟨4⟩ σ'_solm I := by rfl
have hdutyWord :
    solcSlotWordAt (fileDutyDutySlotFor I) σ' I =
      solcSlotWordAt (fileDutyDutySlotFor I) σ'_solm I :=
  by rfl
have haddNoSolm :
    ¬ UInt256.size ≤ (solcSlotWordAt ⟨4⟩ σ'_solm I).toNat +
      (solcSlotWordAt (fileDutyDutySlotFor I) σ'_solm I).toNat := by
  intro hbad
  exact haddOverflow (by
    simpa [hbaseWord, hdutyWord] using hbad)
have hfeeNZSolm :
    solcSlotWordAt ⟨4⟩ σ'_solm I +
        solcSlotWordAt (fileDutyDutySlotFor I) σ'_solm I ≠
      ⟨0⟩ := by
  intro hbad
  exact hfeeZero (by
    simpa [fee, hbaseWord, hdutyWord] using hbad)
have hrhoPostWord :
    solcSlotWordAt (fileDutyRhoSlotFor I) σ' I =
      solcSlotWordAt (fileDutyRhoSlotFor I) σ'_solm I :=
  by rfl
have hageEvm :
    UInt256.sub (UInt256.ofNat I.header.timestamp)
      (solcSlotWordAt (fileDutyRhoSlotFor I) σ' I) = age := by
  simp [age]
have hageSolm :
    UInt256.sub (UInt256.ofNat I.header.timestamp)
      (solcSlotWordAt (fileDutyRhoSlotFor I) σ'_solm I) = age := by
  simpa [hrhoPostWord] using hageEvm
have hfeeSolmEq :
    solcSlotWordAt ⟨4⟩ σ'_solm I +
        solcSlotWordAt (fileDutyDutySlotFor I) σ'_solm I =
      fee := by
  simpa [fee, hbaseWord, hdutyWord]
have hfeeEqSolm :
    fee =
      solcSlotWordAt ⟨4⟩ σ'_solm I +
        solcSlotWordAt (fileDutyDutySlotFor I) σ'_solm I :=
  hfeeSolmEq.symm
have rd2153Generic := by
  simpa [fee, age] using _rd2153
have hRayNZ : jugRay ≠ ⟨0⟩ := by
  native_decide
have hrpowCoupled :=
  rpowFunctionCoupled
    (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (x := fee) (n := age) (b := jugRay) (evm := evmVatS)
    (R := [⟨1530⟩, dripVatIlksPrevWord out, ⟨0⟩,
      fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
    (mem :=
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
        (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
          (dripVatIlksPostCallMem I out))))
    (out := out) (acc := σ') (hRlen := by simp)
    hfeeZero hRayNZ rd2153Generic
cases hrpowCoupled with
| inl hret =>
    rcases hret with
      ⟨xFinal, pow, rpowLocals, kRpow, CRpow, hstore, hrpowBody, rd1524⟩
    by_cases hRmulOverflow :
        UInt256.size ≤ pow.toNat * (dripVatIlksPrevWord out).toNat
    · have hbody :
          ExecTransitionBody config contract evm locals
            dripTransition.body .reverted := by
        simpa [evm, locals, initState, solcSlotWordAt] using
          (jugDripSourceBodyVatIlksRmulOverflowRevertsGeneric
            (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (evmVat := evmVatS) (out := out) (age := age)
            (pow := pow) (rpowLocals := rpowLocals)
            hwv hsz36 hleSolm hvatCodeSolm
            (by simpa [evm, evmVatS] using hcallSolm) _hdecOut
            (by
              simpa [evmVatS, evm, initState, solcSlotWordAt] using
                haddNoSolm)
            (by
              simpa [evmVatS, evm, initState, solcSlotWordAt] using
                hageSolm)
            (by
              simpa [evmVatS, evm, initState, solcSlotWordAt, hfeeEqSolm] using
                hrpowBody)
            hRmulOverflow)
      have hrev := RD.jugDripRmulOverflowReverts
        (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
        (by simp) hRmulOverflow rd1524
      exact hrev.reEquivExecutionRevert hcode hdispatch
        (jugDecode_drip_ok hsz36) hbody
    · have hfitRmul :
          pow.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size := by
        omega
      let rate := UInt256.div (dripVatIlksPrevWord out * pow) jugRay
      by_cases hrateMax : (rate.toNat : Int) ≤ Reasoning.Theory.maxInt256
      · by_cases hprevMax :
            ((dripVatIlksPrevWord out).toNat : Int) ≤ Reasoning.Theory.maxInt256
        · by_cases hfoldNoCode :
              Reasoning.Theory.extCodeSizeWord σ'
                (dripVatTargetWord σ' I) = ⟨0⟩
          · have hfoldCodeSolm :
                Reasoning.Theory.extCodeSizeWord σ'_solm
                    (dripVatTargetWord σ'_solm I) = ⟨0⟩ :=
              by simpa [σ'_solm] using hfoldNoCode
            have hfoldNoCodeSolmRaw :
                (UInt256.ofNat
                  ((σ'_solm.get? (dripVatAddress σ'_solm I)).option
                    0 (fun acc => acc.code.size))).toNat = 0 :=
              extCodeSizeWord_zero_lookup_code_zero
                (σ := σ'_solm)
                (target := dripVatTargetWord σ'_solm I)
                (addr := dripVatAddress σ'_solm I)
                (dripVatAddress_eq_target σ'_solm I) hfoldCodeSolm
            have hbody :
                ExecTransitionBody config contract evm locals
                  dripTransition.body .reverted := by
              simpa [evm, locals, initState, solcSlotWordAt] using
                (jugDripSourceBodyVatFoldNoCodeRevertsGeneric
                  (σ := σ)
                  (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (evmVat := evmVatS) (out := out) (age := age)
                  (pow := pow) (rpowLocals := rpowLocals)
                  hwv hsz36 hleSolm hvatCodeSolm
                  (by simpa [evm, evmVatS] using hcallSolm) _hdecOut
                  (by
                    simpa [evmVatS, evm, initState, solcSlotWordAt] using
                      haddNoSolm)
                  (by
                    simpa [evmVatS, evm, initState, solcSlotWordAt] using
                      hageSolm)
                  (by
                    simpa [evmVatS, evm, initState, solcSlotWordAt, hfeeEqSolm] using
                      hrpowBody)
                  hfitRmul
                  (by simpa [rate] using hrateMax)
                  hprevMax
                  (by
                    simpa [evmVatS, evm, initState, State.lookupAccount] using
                      hfoldNoCodeSolmRaw))
            obtain ⟨_, _, rd1530Raw⟩ :=
              RD.jugDripRmulReturns
                (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
                (by simp) hfitRmul rd1524
            have rd1530 := by
              simpa [rate] using rd1530Raw
            obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530
            obtain ⟨_, _, rd1570⟩ := RD.jugDiffReturns
              (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
                dripVatFoldSelectorWord, dripVatTargetWord σ' I,
                dripVatIlksPrevWord out, rate, fileDutyIlkWord I,
                ⟨357⟩, jugSelWord I])
              (g := g) (rate := rate)
              (prev := dripVatIlksPrevWord out)
              (by simp) hrateMax hprevMax (by simpa using rd2397)
            let foldBaseMem :=
              twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                  (dripVatIlksPostCallMem I out))
            have hpostSize :
                (dripVatIlksPostCallMem I out).size = 192 :=
              dripVatIlksPostCallMem_size_long I out hlo hout
            have hpostRead64 :
                (dripVatIlksPostCallMem I out).readWithPadding 64 32 =
                  UInt256.toByteArray ⟨128⟩ :=
              dripVatIlksPostCallMem_read64_long I out hlo hout
            have hinnerSize :
                (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                  (dripVatIlksPostCallMem I out)).size = 192 := by
              rw [twoWordHashMem_size_of_ge64
                (fileDutyIlkWord I) (⟨1⟩ : UInt256)
                (by rw [hpostSize]; omega), hpostSize]
            have hinnerRead64 :
                (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                  (dripVatIlksPostCallMem I out)).readWithPadding
                    64 32 = UInt256.toByteArray ⟨128⟩ :=
              twoWordHashMem_read64_of_ge_96
                (fileDutyIlkWord I) (⟨1⟩ : UInt256)
                (by rw [hpostSize]; omega) hpostRead64
            have hfoldBaseSize : foldBaseMem.size = 192 := by
              dsimp [foldBaseMem]
              rw [twoWordHashMem_size_of_ge64
                (fileDutyIlkWord I) (⟨1⟩ : UInt256)
                (by rw [hinnerSize]; omega), hinnerSize]
            have hfoldBaseRead64 :
                foldBaseMem.readWithPadding 64 32 =
                  UInt256.toByteArray ⟨128⟩ := by
              dsimp [foldBaseMem]
              exact twoWordHashMem_read64_of_ge_96
                (fileDutyIlkWord I) (⟨1⟩ : UInt256)
                (by rw [hinnerSize]; omega) hinnerRead64
            have hrev := RD.jugDripVatFoldNoCode hfoldBaseSize
              hfoldBaseRead64 hfoldNoCode rd1570
            exact hrev.reEquivExecutionRevert hcode hdispatch
              (jugDecode_drip_ok hsz36) hbody
          · obtain ⟨_, _, rd1530Raw⟩ :=
              RD.jugDripRmulReturns
                (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
                (by simp) hfitRmul rd1524
            have rd1530 := by
              simpa [rate] using rd1530Raw
            obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530
            obtain ⟨_, _, rd1570⟩ := RD.jugDiffReturns
              (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
                dripVatFoldSelectorWord, dripVatTargetWord σ' I,
                dripVatIlksPrevWord out, rate, fileDutyIlkWord I,
                ⟨357⟩, jugSelWord I])
              (g := g) (rate := rate)
              (prev := dripVatIlksPrevWord out)
              (by simp) hrateMax hprevMax (by simpa using rd2397)
            let foldBaseMem :=
              twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                  (dripVatIlksPostCallMem I out))
            have hpostSize :
                (dripVatIlksPostCallMem I out).size = 192 :=
              dripVatIlksPostCallMem_size_long I out hlo hout
            have hpostRead64 :
                (dripVatIlksPostCallMem I out).readWithPadding 64 32 =
                  UInt256.toByteArray ⟨128⟩ :=
              dripVatIlksPostCallMem_read64_long I out hlo hout
            have hinnerSize :
                (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                  (dripVatIlksPostCallMem I out)).size = 192 := by
              rw [twoWordHashMem_size_of_ge64
                (fileDutyIlkWord I) (⟨1⟩ : UInt256)
                (by rw [hpostSize]; omega), hpostSize]
            have hinnerRead64 :
                (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                  (dripVatIlksPostCallMem I out)).readWithPadding
                    64 32 = UInt256.toByteArray ⟨128⟩ :=
              twoWordHashMem_read64_of_ge_96
                (fileDutyIlkWord I) (⟨1⟩ : UInt256)
                (by rw [hpostSize]; omega) hpostRead64
            have hfoldBaseSize : foldBaseMem.size = 192 := by
              dsimp [foldBaseMem]
              rw [twoWordHashMem_size_of_ge64
                (fileDutyIlkWord I) (⟨1⟩ : UInt256)
                (by rw [hinnerSize]; omega), hinnerSize]
            have hfoldBaseRead64 :
                foldBaseMem.readWithPadding 64 32 =
                  UInt256.toByteArray ⟨128⟩ := by
              dsimp [foldBaseMem]
              exact twoWordHashMem_read64_of_ge_96
                (fileDutyIlkWord I) (⟨1⟩ : UInt256)
                (by rw [hinnerSize]; omega) hinnerRead64
            obtain ⟨gasWordFold, _, _, rd1650⟩ :=
              RD.jugDripVatFoldCallReady hfoldBaseSize hfoldBaseRead64
                hfoldNoCode rd1570
            obtain
              ⟨σ'', z, foldOut, AinFold, callGasFold, _, _,
                hΘFold, rd1651, hfoldOutSize⟩ :=
              RD.jugDripVatFoldPostCall rd1650 hdepth
            let evmVatE :=
              { evm with
                accountMap := σ',
                substate := A'_solm }
            have hfoldDepthNe :
                evmVatE.executionEnv.depth ≠ 1024 := by
              simpa [evmVatE, evm, initState] using
                initStateDepth_ne_1024_of_lt
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) hdepth
            have hvowWord :
                dripVowTargetWord σ'_solm I = dripVowTargetWord σ' I :=
              by rfl
            have hfoldEncode :
                config.externalABI.encode? "fold"
                    [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                      .address (AccountAddress.ofUInt256
                        (dripVowTargetWord σ'_solm I)),
                      .int ((rate.toNat : Int) -
                        ((dripVatIlksPrevWord out).toNat : Int))] =
                  some ((dripVatFoldCalldataMem σ' I
                    (UInt256.sub rate (dripVatIlksPrevWord out))
                    foldBaseMem).readWithPadding
                      dripVatFoldOutPtr.toNat
                      dripVatFoldInSize.toNat) := by
              rw [hvowWord]
              exact dripVatFoldEncode_signed_eq σ' I rate
                (dripVatIlksPrevWord out)
                (UInt256.sub rate (dripVatIlksPrevWord out))
                hfoldBaseSize hsz36 hrateMax hprevMax rfl
            have hfoldCodeSolmNe :
                Reasoning.Theory.extCodeSizeWord σ'_solm
                    (dripVatTargetWord σ'_solm I) ≠ ⟨0⟩ :=
              by simpa [σ'_solm] using hfoldNoCode
            have hfoldCodeSolm :
                0 <
                  (UInt256.ofNat
                    ((evmVatS.lookupAccount
                      (dripVatAddress evmVatS.accountMap
                        evmVatS.executionEnv)).option 0
                          (fun acc => acc.code.size))).toNat := by
              simpa [evmVatS, evm, initState] using
                (dripVatCode_pos_of_codeSize_ne_zero
                  (σ := σ'_solm) (σ₀ := σ₀)
                  (A := A'_solm) (I := I) (g := g) hfoldCodeSolmNe)
            cases z
            · rcases hΘFold with ⟨gFold'', AFold', hΘFold'⟩
              have hΘFoldE :
                  (σ'', gFold'', AFold', false, foldOut) =
                    Ethereum.EVM.Θ evmVatE.accountMap evmVatE.σ₀ AinFold
                      (AccountAddress.ofUInt256
                        (UInt256.ofNat evmVatE.executionEnv.codeOwner))
                      evmVatE.executionEnv.sender
                      (AccountAddress.ofUInt256
                        (dripVatTargetWord σ' I))
                      (toExecute evmVatE.accountMap
                        (AccountAddress.ofUInt256
                          (dripVatTargetWord σ' I)))
                      callGasFold
                      (UInt256.ofNat evmVatE.executionEnv.gasPrice)
                      ⟨0⟩ ⟨0⟩
                      ((dripVatFoldCalldataMem σ' I
                        (UInt256.sub rate (dripVatIlksPrevWord out))
                        foldBaseMem).readWithPadding
                          dripVatFoldOutPtr.toNat
                          dripVatFoldInSize.toNat)
                      (evmVatE.executionEnv.depth + 1)
                      (evmVatE.executionEnv.header) (evmVatE.executionEnv.blobVersionedHashes) (evmVatE.executionEnv.blocks) true := by
                simpa [evmVatE, evm, initState, hperm, foldBaseMem] using
                  hΘFold'
              let σ''_solm := σ''
              let A''_solm := AFold'
              have hfoldTargetAddr :
                  dripVatAddress σ'_solm I =
                    AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
                simpa [σ'_solm] using dripVatAddress_eq_target σ' I
              have hfoldTarget :
                  EVM.address (dripVatAddress σ'_solm I) =
                    AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
                rw [hfoldTargetAddr]
                exact address_of_val _
              have hfoldCallSolm :
                  typedCallViaEVM config evmVatS
                    (EVM.address (dripVatAddress σ'_solm I)) "fold" 0
                    [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                      .address (AccountAddress.ofUInt256 (dripVowTargetWord σ'_solm I)),
                      .int ((rate.toNat : Int) -
                        ((dripVatIlksPrevWord out).toNat : Int))]
                    (false, { evmVatS with accountMap := σ'', substate := AFold' }, foldOut) true := by
                simpa [evmVatE, evmVatS, σ'_solm, evm] using
                  callCoincides hfoldDepthNe
                    hfoldTarget
                    hfoldEncode hΘFoldE
              have hbody :
                  ExecTransitionBody config contract evm locals
                    dripTransition.body .reverted := by
                simpa [evm, evmVatS, locals, initState, solcSlotWordAt,
                  rate] using
                  (jugDripSourceBodyVatFoldCallFailedRevertsGeneric
                    (σ := σ)
                    (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (evmVat := evmVatS)
                    (evmFold :=
                      { evmVatS with
                        accountMap := σ''_solm,
                        substate := A''_solm })
                    (out := out) (foldOut := foldOut)
                    (age := age) (pow := pow) (rpowLocals := rpowLocals)
                    hwv hsz36 hleSolm hvatCodeSolm
                    (by simpa [evm, evmVatS] using hcallSolm)
                    _hdecOut
                    (by
                      simpa [evmVatS, evm, initState, solcSlotWordAt]
                        using haddNoSolm)
                    (by
                      simpa [evmVatS, evm, initState, solcSlotWordAt]
                        using hageSolm)
                    (by
                      simpa [evmVatS, evm, initState, solcSlotWordAt,
                        hfeeEqSolm] using hrpowBody)
                    hfitRmul
                    (by simpa [rate] using hrateMax)
                    hprevMax hfoldCodeSolm
                    (by
                      simpa [evmVatS, evm, initState, solcSlotWordAt,
                        rate] using hfoldCallSolm))
              have hrev := RD.jugDripVatFoldCallFailed
                (targetWord := dripVatTargetWord σ' I) rd1651
                hfoldOutSize
              exact hrev.reEquivExecutionRevert hcode hdispatch
                (jugDecode_drip_ok hsz36) hbody
            · rcases hΘFold with ⟨gFold'', AFold', hΘFold'⟩
              have hΘFoldE :
                  (σ'', gFold'', AFold', true, foldOut) =
                    Ethereum.EVM.Θ evmVatE.accountMap evmVatE.σ₀ AinFold
                      (AccountAddress.ofUInt256
                        (UInt256.ofNat evmVatE.executionEnv.codeOwner))
                      evmVatE.executionEnv.sender
                      (AccountAddress.ofUInt256
                        (dripVatTargetWord σ' I))
                      (toExecute evmVatE.accountMap
                        (AccountAddress.ofUInt256
                          (dripVatTargetWord σ' I)))
                      callGasFold
                      (UInt256.ofNat evmVatE.executionEnv.gasPrice)
                      ⟨0⟩ ⟨0⟩
                      ((dripVatFoldCalldataMem σ' I
                        (UInt256.sub rate (dripVatIlksPrevWord out))
                        foldBaseMem).readWithPadding
                          dripVatFoldOutPtr.toNat
                          dripVatFoldInSize.toNat)
                      (evmVatE.executionEnv.depth + 1)
                      (evmVatE.executionEnv.header) (evmVatE.executionEnv.blobVersionedHashes) (evmVatE.executionEnv.blocks) true := by
                simpa [evmVatE, evm, initState, hperm, foldBaseMem] using
                  hΘFold'
              let σ''_solm := σ''
              let A''_solm := AFold'
              have hfoldTargetAddr :
                  dripVatAddress σ'_solm I =
                    AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
                simpa [σ'_solm] using dripVatAddress_eq_target σ' I
              have hfoldTarget :
                  EVM.address (dripVatAddress σ'_solm I) =
                    AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
                rw [hfoldTargetAddr]
                exact address_of_val _
              have hfoldCallSolm :
                  typedCallViaEVM config evmVatS
                    (EVM.address (dripVatAddress σ'_solm I)) "fold" 0
                    [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                      .address (AccountAddress.ofUInt256 (dripVowTargetWord σ'_solm I)),
                      .int ((rate.toNat : Int) -
                        ((dripVatIlksPrevWord out).toNat : Int))]
                    (true, { evmVatS with accountMap := σ'', substate := AFold' }, foldOut) true := by
                simpa [evmVatE, evmVatS, σ'_solm, evm] using
                  callCoincides hfoldDepthNe
                    hfoldTarget
                    hfoldEncode hΘFoldE
              let evmFoldS :=
                { evmVatS with
                  accountMap := σ''_solm,
                  substate := A''_solm }
              let finalLocals :=
                (dripDeltaLocalsInt I out
                  (solcSlotWordAt ⟨4⟩ evmVatS.accountMap evmVatS.executionEnv +
                    solcSlotWordAt (fileDutyDutySlotFor I)
                      evmVatS.accountMap evmVatS.executionEnv)
                  pow rate
                  ((rate.toNat : Int) -
                    ((dripVatIlksPrevWord out).toNat : Int))).insert
                      "_foldRet" .unit
              let evmRhoS :=
                Solm.EVM.storageStore evmFoldS
                  evmFoldS.executionEnv.codeOwner
                  (fileDutyRhoSlotFor I)
                  (UInt256.ofNat evmFoldS.executionEnv.header.timestamp)
              have hbody :
                  ExecTransitionBody config contract evm locals
                    dripTransition.body
                    (.returned
                      { contract := contract, locals := finalLocals }
                      evmRhoS
                      (some [.int (Int.ofNat rate.toNat)])) := by
                simpa [evm, evmVatS, evmFoldS, finalLocals, evmRhoS,
                  locals, initState, solcSlotWordAt, rate] using
                  (jugDripSourceBodyVatFoldCallSucceededReturnsGeneric
                    (σ := σ)
                    (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (evmVat := evmVatS) (evmFold := evmFoldS)
                    (out := out) (foldOut := foldOut)
                    (age := age) (pow := pow) (rpowLocals := rpowLocals)
                    hwv hsz36 hleSolm hvatCodeSolm
                    (by simpa [evm, evmVatS] using hcallSolm)
                    _hdecOut
                    (by
                      simpa [evmVatS, evm, initState, solcSlotWordAt]
                        using haddNoSolm)
                    (by
                      simpa [evmVatS, evm, initState, solcSlotWordAt]
                        using hageSolm)
                    (by
                      simpa [evmVatS, evm, initState, solcSlotWordAt,
                        hfeeEqSolm] using hrpowBody)
                    hfitRmul
                    (by simpa [rate] using hrateMax)
                    hprevMax hfoldCodeSolm
                    (by
                      simpa [evmVatS, evm, initState, solcSlotWordAt,
                        rate] using hfoldCallSolm))
              have hfoldCallMemSize :
                  (dripVatFoldCalldataMem σ' I
                    (UInt256.sub rate (dripVatIlksPrevWord out))
                    foldBaseMem).size = 228 :=
                dripVatFoldCalldataMem_size σ' I
                  (UInt256.sub rate (dripVatIlksPrevWord out))
                  hfoldBaseSize
              have hfoldCallMemRead64 :
                  (dripVatFoldCalldataMem σ' I
                    (UInt256.sub rate (dripVatIlksPrevWord out))
                    foldBaseMem).readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                dripVatFoldCalldataMem_read64 σ' I
                  (UInt256.sub rate (dripVatIlksPrevWord out))
                  hfoldBaseSize hfoldBaseRead64
              obtain ⟨_, _, rd1669⟩ :=
                RD.jugDripVatFoldCallSucceeded
                  (targetWord := dripVatTargetWord σ' I) rd1651
              have hret := RD.jugDripVatFoldStoreRhoReturns
                (targetWord := dripVatTargetWord σ' I)
                hsz36 hperm hfoldCallMemSize hfoldCallMemRead64 rd1669
              exact hret.reEquivExecutionGen hcode hdispatch
                (jugDecode_drip_ok hsz36) hbody
                (by
                  simp [evmRhoS, evmFoldS, evmVatS, evmVatE, σ''_solm,
                    A''_solm, σ'_solm, evm, initState,
                    storageStore_accountMap])
                (by
                  rw [show dripTransition.returnType = [uint256] by rfl]
                  exact returnEquiv_of_encode
                    (by simpa [uint256] using
                      uint256ReturnEncoding rate))
        · have hbody :
              ExecTransitionBody config contract evm locals
                dripTransition.body .reverted := by
            simpa [evm, locals, initState, solcSlotWordAt] using
              (jugDripSourceBodyVatIlksDiffYBoundRevertsGeneric
                (σ := σ)
                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                (evmVat := evmVatS) (out := out) (age := age)
                (pow := pow) (rpowLocals := rpowLocals)
                hwv hsz36 hleSolm hvatCodeSolm
                (by simpa [evm, evmVatS] using hcallSolm) _hdecOut
                (by
                  simpa [evmVatS, evm, initState, solcSlotWordAt] using
                    haddNoSolm)
                (by
                  simpa [evmVatS, evm, initState, solcSlotWordAt] using
                    hageSolm)
                (by
                  simpa [evmVatS, evm, initState, solcSlotWordAt, hfeeEqSolm] using
                    hrpowBody)
                hfitRmul
                (by simpa [rate] using hrateMax)
                hprevMax)
          obtain ⟨_, _, rd1530Raw⟩ :=
            RD.jugDripRmulReturns
              (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
              (by simp) hfitRmul rd1524
          have rd1530 := by
            simpa [rate] using rd1530Raw
          obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530
          have hrev := RD.jugDiffRevertYBound
            (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
              dripVatFoldSelectorWord, dripVatTargetWord σ' I,
              dripVatIlksPrevWord out, rate, fileDutyIlkWord I,
              ⟨357⟩, jugSelWord I])
            (g := g) (rate := rate) (prev := dripVatIlksPrevWord out)
            (by simp) hrateMax hprevMax (by simpa using rd2397)
          exact hrev.reEquivExecutionRevert hcode hdispatch
            (jugDecode_drip_ok hsz36) hbody
      · have hbody :
            ExecTransitionBody config contract evm locals
              dripTransition.body .reverted := by
          simpa [evm, locals, initState, solcSlotWordAt] using
            (jugDripSourceBodyVatIlksDiffXBoundRevertsGeneric
              (σ := σ)
              (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (evmVat := evmVatS) (out := out) (age := age)
              (pow := pow) (rpowLocals := rpowLocals)
              hwv hsz36 hleSolm hvatCodeSolm
              (by simpa [evm, evmVatS] using hcallSolm) _hdecOut
              (by
                simpa [evmVatS, evm, initState, solcSlotWordAt] using
                  haddNoSolm)
              (by
                simpa [evmVatS, evm, initState, solcSlotWordAt] using
                  hageSolm)
              (by
                simpa [evmVatS, evm, initState, solcSlotWordAt, hfeeEqSolm] using
                  hrpowBody)
              hfitRmul
              (by simpa [rate] using hrateMax))
        obtain ⟨_, _, rd1530Raw⟩ :=
          RD.jugDripRmulReturns
            (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
            (by simp) hfitRmul rd1524
        have rd1530 := by
          simpa [rate] using rd1530Raw
        obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530
        have hrev := RD.jugDiffRevertXBound
          (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
            dripVatFoldSelectorWord, dripVatTargetWord σ' I,
            dripVatIlksPrevWord out, rate, fileDutyIlkWord I,
            ⟨357⟩, jugSelWord I])
          (g := g) (rate := rate) (prev := dripVatIlksPrevWord out)
          (by simp) hrateMax (by simpa using rd2397)
        exact hrev.reEquivExecutionRevert hcode hdispatch
          (jugDecode_drip_ok hsz36) hbody
| inr hrev =>
    rcases hrev with ⟨hrpowBody, hrdRev⟩
    have hbody :
        ExecTransitionBody config contract evm locals
          dripTransition.body .reverted := by
      simpa [evm, locals, initState, solcSlotWordAt] using
        (jugDripSourceBodyVatIlksRpowReverts
          (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (evmVat := evmVatS) (out := out) (age := age)
          hwv hsz36 hleSolm hvatCodeSolm
          (by simpa [evm, evmVatS] using hcallSolm) _hdecOut
          (by
            simpa [evmVatS, evm, initState, solcSlotWordAt] using
              haddNoSolm)
          (by
            simpa [evmVatS, evm, initState, solcSlotWordAt] using
              hageSolm)
          (by
            simpa [evmVatS, evm, initState, solcSlotWordAt, hfeeEqSolm] using
              hrpowBody))
    exact hrdRev.reEquivExecutionRevert hcode hdispatch
      (jugDecode_drip_ok hsz36) hbody
"#

elab "jug_drip_generic_age_tac" : tactic => do
  let tacSeq ← match Mathlib.GuardExceptions.parseAsTacticSeq (← getEnv) jugDripGenericAgeScript with
    | .ok tacSeq => pure tacSeq
    | .error err => throwError "failed to parse jug_drip_generic_age_tac:
{err}"
  evalTactic (← `(tactic| ($tacSeq:tacticSeq)))

end Benchmarks.Dss.Jug
