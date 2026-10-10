import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Bytes4
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_031
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_032

/-!
# PoolManager `supportsInterface(bytes4)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 11286; reach lemma `poolManagerReachSupportsInterfaceBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

abbrev interfaceResult (cd : ByteArray) : Bool :=
  (calldataBytes4Arg cd == [0x01, 0xff, 0xc9, 0xa7]) ||
  (calldataBytes4Arg cd == [0x0f, 0x63, 0x2f, 0xb3])

theorem supportsInterfaceBodyReturns (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hget : locals.get? "interfaceId" =
      some (.fixedBytes abiBytes4Width (calldataBytes4Arg evm.executionEnv.calldata))) :
    ExecTransitionBody config contract evm locals supportsInterfaceTransition.body
      (.returned (calldataFrame contract locals imms evm) evm
        (some [.bool (interfaceResult evm.executionEnv.calldata)])) imms := by
  have hid := evalLocalValue (cfg := config) (evm := evm) (f := calldataFrame contract locals imms evm)
    ((store_get_ne locals _ (by decide : ("__calldata" == "interfaceId") = false)).trans hget)
  have h165 : evalExpr? config (calldataFrame contract locals imms evm) evm
      (.fixedBytesLit abiBytes4Width [0x01, 0xff, 0xc9, 0xa7]) =
      .ok (.fixedBytes abiBytes4Width [0x01, 0xff, 0xc9, 0xa7]) := by
    simp only [evalExpr?, pure]
  have h6909 : evalExpr? config (calldataFrame contract locals imms evm) evm
      (.fixedBytesLit abiBytes4Width [0x0f, 0x63, 0x2f, 0xb3]) =
      .ok (.fixedBytes abiBytes4Width [0x0f, 0x63, 0x2f, 0xb3]) := by
    simp only [evalExpr?, pure]
  apply guardedReturnBody hwv hhi
  have hleft := evalEqFixedBytes hid h165
  have hright := evalEqFixedBytes hid h6909
  exact evalOrBool hleft hright

theorem supportsInterfaceTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {selector : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hlen : 36 ≤ I.calldata.size) (hstack : R.length + 6 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨11379⟩
      (UInt256.land (calldataWord I.calldata 4) bytes4Mask :: selector :: R)
      entryMemory aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (interfaceResult I.calldata).toUInt256.toByteArray := by
  have heq165 := maskedBytes4_eq (cd := I.calldata) (bytes := [0x01,0xff,0xc9,0xa7])
    (word := UInt256.ofNat 904250603428552709895185118199468575982109441609966099573332780532423983104)
    hlen rfl (by decide +kernel)
  have heq6909 := maskedBytes4_eq (cd := I.calldata) (bytes := [0x0f,0x63,0x2f,0xb3])
    (word := UInt256.ofNat 6959939796070808450691141534347583630554614852963606718971573583076382474240)
    hlen rfl (by decide +kernel)
  by_cases h165 : (calldataBytes4Arg I.calldata == [0x01,0xff,0xc9,0xa7]) = true
  · have rdReturn := poolManagerBlocks.poolManager_block_11379_fallthrough (by simpa using hstack)
      (by rw [heq165, h165]; decide) h
    have hret := poolManagerBlocks.poolManager_block_11424 (by simp; omega) rdReturn
    simpa only [poolManagerBlocks.poolManager_block_11379_fallthrough_stack, heq165,
      h165, interfaceResult, Bool.true_or, show UInt256.ofNat 64 = (⟨64⟩ : UInt256) from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, entryMemory_returnWord, boolWord_normalize] using hret
  · have hf : (calldataBytes4Arg I.calldata == [0x01,0xff,0xc9,0xa7]) = false :=
      Bool.eq_false_iff.mpr h165
    have hjump35 : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
        (UInt256.ofNat 11435) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
    have hjump24 : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
        (UInt256.ofNat 11424) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
    have rdSecond := poolManagerBlocks.poolManager_block_11379_taken (by simpa using hstack)
      (by rw [heq165, hf]; decide) hjump35 h
    have rdReturn := poolManagerBlocks.poolManager_block_11435 (by omega) hjump24 rdSecond
    have hret := poolManagerBlocks.poolManager_block_11424 (by simp; omega) rdReturn
    simpa only [poolManagerBlocks.poolManager_block_11435_stack, heq6909, interfaceResult,
      hf, Bool.false_or, show UInt256.ofNat 64 = (⟨64⟩ : UInt256) from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, entryMemory_returnWord, boolWord_normalize] using hret

theorem poolManagerSupportsInterfaceBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 1) rfl hsel
  have hd : dispatchMsg contract I.calldata = some supportsInterfaceTransition := by
    apply poolManagerDispatch_supportsInterface <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachSupportsInterfaceBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨11286⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 816) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_11286_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_11292_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 1) hlen hhi hsize) rdSize
        cases hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 with
        | none =>
          have hcond : UInt256.sub (calldataWord I.calldata 4)
              (UInt256.land (calldataWord I.calldata 4) bytes4Mask) ≠ ⟨0⟩ := by
            intro hz
            have hp := (bytes4Padding_mask_iff hlen).mpr (u256_sub_eq_zero_iff_eq.mp hz).symm
            rw [hpad] at hp
            contradiction
          have rdRevert := poolManagerBlocks.poolManager_block_11334_taken (by simp) hcond hjump rdDecode
          exact (emptyRevert v (by simp [poolManagerBlocks.poolManager_block_11334_taken_stack]) rdRevert).reEquivDecodingFailed
            hcode hd (decodeCalldata_bytes4_none_pad hlen hhi hpad)
        | some u =>
          cases u
          have hclean := (bytes4Padding_mask_iff hlen).mp hpad
          have hcond : UInt256.sub (calldataWord I.calldata 4)
              (UInt256.land (calldataWord I.calldata 4) bytes4Mask) = ⟨0⟩ :=
            u256_sub_eq_zero_iff_eq.mpr hclean.symm
          have rdCompare := poolManagerBlocks.poolManager_block_11334_fallthrough (by simp) hcond rdDecode
          have hret := supportsInterfaceTrace v hlen (by simp) rdCompare
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (supportsInterfaceTransition.params.map Param.name)
              (transitionSignature supportsInterfaceTransition).paramTypes I.calldata =
              some ((∅ : Store).insert "interfaceId" (.fixedBytes abiBytes4Width (calldataBytes4Arg I.calldata))) :=
            decodeCalldata_bytes4_ok hlen hhi hpad
          have hbody := supportsInterfaceBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            ((∅ : Store).insert "interfaceId" (.fixedBytes abiBytes4Width (calldataBytes4Arg I.calldata)))
            (immStore v) hwv hhi (store_get_self _ _ _)
          exact hret.reEquivExecution hcode hd hdec hbody (returnEquiv_of_encode (boolReturnEncoding _))
      · have hguard := viaIRStaticLenCheckHuge (words := 1) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_11292_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_bytes4_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 1) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_11292_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_bytes4_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_11286_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `supportsInterface(bytes4)`: the theorem `Correct.lean` routes selector 1 to. -/
theorem poolManagerSupportsInterfaceBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerSupportsInterfaceBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
