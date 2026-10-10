import Benchmarks.UniswapV3.Pool.CollectProtocolBodyTrace
import Benchmarks.UniswapV3.Pool.CollectProtocolCalldata

/-!
# UniswapV3Pool `collectProtocol(address,uint128,uint128)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1526; reach lemma `uniswapV3PoolReachCollectProtocolBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `collectProtocol(address,uint128,uint128)`: the theorem `Correct.lean` routes selector 15 to. -/
theorem uniswapV3PoolCollectProtocolBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 15)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 15) rfl hsel
  have hd : dispatchMsg contract I.calldata = some collectProtocolTransition := by
    apply uniswapV3PoolDispatch_collectProtocol <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 100 ≤ I.calldata.size
  · let recipient := collectProtocolRecipient I.calldata
    let req0 := collectProtocolRequestedWord I.calldata false
    let req1 := collectProtocolRequestedWord I.calldata true
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hdec := collectProtocolDecode hlen
    have hreq0 : req0.toNat < 2 ^ 128 := collectProtocolRequestedWord_lt I.calldata false
    have hreq1 : req1.toNat < 2 ^ 128 := collectProtocolRequestedWord_lt I.calldata true
    obtain ⟨_, _, rdDecoded⟩ := uniswapV3PoolCollectProtocolDecodedX
      (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen
    rcases collectProtocolReadLockX (v := v) rdDecoded (by simp) with
      ⟨rdRevert, hlocked⟩ | ⟨hunlocked, _, _, rdLock⟩
    · exact rdRevert.reEquivExecutionRevert hcode hd hdec
        (collectProtocolRevertsLocked v evm recipient req0 req1 hwv hlocked)
    · cases hperm : I.perm with
      | false =>
          have rdStatic := collectProtocolLockStaticX (v := v) rdLock hperm (by simp)
          exact rdStatic.reEquivStaticHalt hcode hd hdec
            (collectProtocolStatic v evm recipient req0 req1 hwv hunlocked hperm)
      | true =>
          rcases collectProtocolOwnerX (v := v) (evm := evm) rdLock rfl hperm
              (by unfold ActiveWords; constructor <;> decide) (by simp) with
            ⟨rdRevert, hfactory⟩ | ⟨out, σ', A', aw', _, _, hout, houtsize, ha', hfactory, rdOwner⟩
          · exact rdRevert.reEquivExecutionRevert hcode hd hdec
              (collectProtocolFactoryReverts v evm recipient req0 req1 hwv hunlocked hfactory)
          · let evm' : EVM.State := { (storeSlot0Unlocked evm false) with accountMap := σ', substate := A' }
            let owner := AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32))
            have henv' : evm'.executionEnv = I := storeSlot0Unlocked_executionEnv evm false
            have hs' : SourceState evm I σ' evm' :=
              ⟨storeSlot0Unlocked_originalAccounts evm false, henv', rfl⟩
            rcases collectProtocolOwnerGuardX (v := v) rdOwner hout houtsize ha' (by simp) with
              ⟨rdRevert, howner⟩ | ⟨howner, awAuth, _, _, haAuth, rdAuthorized⟩
            · exact rdRevert.reEquivExecutionRevert hcode hd hdec
                (collectProtocolRevertsOwner v evm evm' recipient req0 req1 owner _ hwv hunlocked hfactory
                  (by simpa only [henv'] using howner))
            · have howner' : evm'.executionEnv.source = owner := by simpa only [henv'] using howner
              let amount0 := minWord req0 (protocolFeesWord false evm'.accountMap evm'.executionEnv)
              let amount1 := minWord req1 (protocolFeesWord true evm'.accountMap evm'.executionEnv)
              let locals := (collectProtocolAmountsFrame v recipient req0 req1 owner amount0 amount1).locals
              have hprefix := collectProtocolOwnerAmountsPrefix v evm evm' recipient req0 req1 owner _
                hwv hunlocked hfactory howner'
              have hvalues := collectProtocolAmounts_values v recipient req0 req1 owner amount0 amount1
              have hfit0 : amount0.toNat < 2 ^ 128 := minWord_lt _ _
                (protocolFeesWord_lt false evm'.accountMap evm'.executionEnv)
              have hfit1 : amount1.toNat < 2 ^ 128 := minWord_lt _ _
                (protocolFeesWord_lt true evm'.accountMap evm'.executionEnv)
              obtain ⟨_, _, rdAmounts⟩ := collectProtocolAmountsX (v := v) rdAuthorized hreq0 hreq1 (by simp)
              have hfee0 : protocolFeesWord false σ' I = protocolFeesWord false evm'.accountMap evm'.executionEnv := by
                simp only [hs'.accounts, hs'.env]
              have hfee1 : protocolFeesWord true σ' I = protocolFeesWord true evm'.accountMap evm'.executionEnv := by
                simp only [hs'.accounts, hs'.env]
              rw [show evm.executionEnv = I from rfl, hfee0, hfee1] at rdAmounts
              rcases collectProtocolPaymentsBodyX (v := v) (evm0 := evm) recipient locals rdAmounts hs' hperm
                  hprefix hvalues hfit0 hfit1 (factoryOwnerOutputMem_heap out awAuth houtsize haAuth)
                  (by rw [factoryOwnerOutputMem_size out houtsize]; decide)
                  (factoryOwnerOutputMem_zero out houtsize) (by decide) (by simp) with
                ⟨rdRevert, hbody⟩ | ⟨evmFinal, localsFinal, final0, final1, hbody, hf0, hf1, rdFinal⟩
              · exact rdRevert.reEquivExecutionRevert hcode hd hdec hbody
              · exact rdFinal.reEquivExecutionGen hcode hd hdec hbody rfl
                  (returnEquiv.returned rfl (uintPairReturnEncoding ⟨128, by decide⟩ ⟨128, by decide⟩
                    final0 final1 hf0 hf1))
  · have hshort : I.calldata.size < 100 := by omega
    exact (uniswapV3PoolCollectProtocolShortX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort)
      |>.reEquivDecodingFailed hcode hd (collectProtocolDecodeShort hsz hshort)

end Benchmarks.UniswapV3.Pool
