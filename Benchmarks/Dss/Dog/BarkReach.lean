import Benchmarks.Dss.Dog.BarkDecode

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog


theorem dogNonpayableLivePrefixRevert {v : DogImmutables}
    {σ σ₀ A I} {g : Sat256}
    {locals : Store} {rest : List Stmt}
    (hbase : locals.get? "live" = none)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I ≠ ⟨1⟩) :
    ExecTransitionBody config contract
      (initState σ σ₀ g A I) locals
      (nonpayable ++ [.require (.binary .eq (.storage liveRef) (.intLit 1))] ++ rest)
      .reverted (immStore v) := by
  let evm0 := initState σ σ₀ g A I
  have hcallvalue :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  have hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    simpa [evm0] using
      dogLiveGuardEval_false (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (locals := locals) hbase hlive
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (nonpayable ++ [.require (.binary .eq (.storage liveRef) (.intLit 1))] ++ rest)
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue hcallvalue) ?_
    change ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
      ([.require (.binary .eq (.storage liveRef) (.intLit 1))] ++ rest) .reverted
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock


theorem dogDecode_bark_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (barkTransition.params.map Param.name)
      (transitionSignature barkTransition).paramTypes I.calldata =
        some (barkLocals I) := by
  simpa [config, barkTransition, barkLocals, barkIlkBytes, barkUrn, barkKpr, barkUrnWord,
    barkKprWord, bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width, abiAddress] using
    decodeCalldataWithMode_legacyBytes32_address_address_ok (cd := I.calldata)
      (x := "ilk") (y := "urn") (z := "kpr") hsz100

theorem dogDecode_bark_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    config.externalABI.decodeCalldata? (barkTransition.params.map Param.name)
      (transitionSignature barkTransition).paramTypes I.calldata = none := by
  simpa [config, barkTransition, bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width,
    abiAddress] using
    decodeCalldataWithMode_legacyBytes32_address_address_none_short
      (cd := I.calldata) (x := "ilk") (y := "urn") (z := "kpr") hsz4 hshort

theorem dogReachBarkBody {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 2)) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) ⟨785⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨0xed998908⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xed 0x99 0x89 0x08 ⟨0xed998908⟩
      (by native_decide) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootWidth : armTgtWidth code (⟨32⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hhighWidth : armTgtWidth code (⟨43⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h43 : RD code I g (initState σ σ₀ g A I) ⟨43⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ (k32 + 5) (C32 + 22) := by
    simpa [selArmNextPc, hrootWidth] using
      RD.selectorSplitNotTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot (by simp)
  have hhigh :
      UInt256.gt (armSelNat code (⟨43⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h54 : RD code I g (initState σ σ₀ g A I) ⟨54⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [selArmNextPc, hhighWidth] using
      RD.selectorSplitNotTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh (by simp)
  have hchop : UInt256.eq (dogSelectorWord 4) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hilks : UInt256.eq (dogSelectorWord 11) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hfileIlkClip : UInt256.eq (dogSelectorWord 10) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hbark : UInt256.eq (dogSelectorWord 2) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h65 := by
    simpa [selArmNextPc] using
      h54.selectorArmNotTaken (selNat := dogSelectorWord 4) (tgt := (⟨629⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hchop
        (by simp)
  have h76 := by
    simpa [selArmNextPc] using
      h65.selectorArmNotTaken (selNat := dogSelectorWord 11) (tgt := (⟨658⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hilks
        (by simp)
  have h87 := by
    simpa [selArmNextPc] using
      h76.selectorArmNotTaken (selNat := dogSelectorWord 10) (tgt := (⟨735⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hfileIlkClip
        (by simp)
  have h785 := by
    simpa using
      h87.selectorArmTaken (selNat := dogSelectorWord 2) (tgt := (⟨785⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hbark
        (dogPatchedDJumpPrefix1405 ⟨785⟩ hpatch (by native_decide))
        (by simp)
  exact ⟨_, _, h785⟩


end Benchmarks.Dss.Dog
