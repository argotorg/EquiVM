import Benchmarks.UniswapV3.Pool.SetFeeProtocolTrace

/-!
# UniswapV3Pool `setFeeProtocol(uint8,uint8)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1486; reach lemma `uniswapV3PoolReachSetFeeProtocolBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

theorem setFeeProtocolDecode (I : ExecutionEnv) (hlen : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (setFeeProtocolTransition.params.map Param.name)
      (transitionSignature setFeeProtocolTransition).paramTypes I.calldata =
      some (setFeeProtocolLocals
        (UInt256.land (calldataWord I.calldata 4) (UInt256.ofNat 255))
        (UInt256.land (calldataWord I.calldata 36) (UInt256.ofNat 255))) := by
  have h := decodeCalldata_legacyIntPair_ok (.uint ⟨8, by decide⟩) (.uint ⟨8, by decide⟩)
    (x := "feeProtocol0") (y := "feeProtocol1") hlen
  rw [normalizeUIntWord_mask ⟨8, by decide⟩ _ (UInt256.ofNat 255) (by decide),
    normalizeUIntWord_mask ⟨8, by decide⟩ _ (UInt256.ofNat 255) (by decide)] at h
  exact h

/-- `setFeeProtocol(uint8,uint8)`: the theorem `Correct.lean` routes selector 14 to. -/
theorem uniswapV3PoolSetFeeProtocolBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 14)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 14) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setFeeProtocolTransition := by
    apply uniswapV3PoolDispatch_setFeeProtocol <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 68 ≤ I.calldata.size
  · let fp0 := UInt256.land (calldataWord I.calldata 4) (UInt256.ofNat 255)
    let fp1 := UInt256.land (calldataWord I.calldata 36) (UInt256.ofNat 255)
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hdec := setFeeProtocolDecode I hlen
    obtain ⟨k, C, rdDecoded⟩ := uniswapV3PoolSetFeeProtocolDecodedX
      (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen
    rcases setFeeProtocolReadLockX (v := v) rdDecoded (by simp) with
      ⟨rdRevert, hlocked⟩ | ⟨hunlocked, k', C', rdLock⟩
    · exact rdRevert.reEquivExecutionRevert hcode hd hdec
        (setFeeProtocolRevertsLocked v evm fp0 fp1 hwv hlocked)
    · cases hperm : I.perm with
      | false =>
          have rdStatic := setFeeProtocolLockStaticX (v := v) rdLock hperm (by simp)
          exact rdStatic.reEquivStaticHalt hcode hd hdec
            (setFeeProtocolStatic v evm fp0 fp1 hwv hunlocked hperm)
      | true =>
          rcases setFeeProtocolOwnerX (v := v) (evm := evm) rdLock rfl hperm (by simp) with
            ⟨rdRevert, hfactory⟩ | ⟨out, σ', A', aw', k'', C'', hout, houtsize, hfactory, rdOwner⟩
          · exact rdRevert.reEquivExecutionRevert hcode hd hdec
              (setFeeProtocolFactoryReverts v evm fp0 fp1 hwv hunlocked hfactory)
          · let evm' : EVM.State := { (storeSlot0Unlocked evm false) with accountMap := σ', substate := A' }
            have henv' : evm'.executionEnv = I := storeSlot0Unlocked_executionEnv evm false
            rcases setFeeProtocolOwnerGuardX (v := v) rdOwner hout houtsize (by simp) with
              ⟨rdRevert, howner⟩ | ⟨howner, aw'', kAuth, CAuth, rdAuthorized⟩
            · exact rdRevert.reEquivExecutionRevert hcode hd hdec
                (setFeeProtocolRevertsOwner v evm evm' fp0 fp1 _ _ hwv hunlocked hfactory
                  (by simpa only [henv'] using howner))
            · rcases setFeeProtocolValidX (v := v) rdAuthorized
                (maskTwice _ _) (maskTwice _ _) (by simp) with
                ⟨rdRevert, hinvalid⟩ | ⟨hvalid, kValid, CValid, rdValid⟩
              · exact rdRevert.reEquivExecutionRevert hcode hd hdec
                  (setFeeProtocolRevertsInvalid v evm evm' fp0 fp1 _ _ hwv hunlocked hfactory
                    (by simpa only [henv'] using howner) hinvalid)
              · have hvalids := Bool.and_eq_true_iff.mp hvalid
                have rdFinal := setFeeProtocolStoreX (v := v) (evm := evm')
                  (by simpa only [henv'] using rdValid) (by simpa only [henv'] using hperm)
                  (feeProtocolValid_le fp0 hvalids.1) (feeProtocolValid_le fp1 hvalids.2) (by simp)
                exact rdFinal.reEquivExecutionGen hcode hd hdec
                  (setFeeProtocolReturns v evm evm' fp0 fp1 _ _ hwv hunlocked hfactory
                    (by simpa only [henv'] using howner) hvalid) rfl
                  (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide))
  · have hshort : I.calldata.size < 68 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (setFeeProtocolTransition.params.map Param.name)
        (transitionSignature setFeeProtocolTransition).paramTypes I.calldata = none :=
      decodeCalldata_legacyIntPair_none_short (.uint ⟨8, by decide⟩) (.uint ⟨8, by decide⟩) hsz hshort
    exact (uniswapV3PoolSetFeeProtocolShortX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.UniswapV3.Pool
