import Benchmarks.UniswapV3.Pool.SwapMemoryModel
import Benchmarks.UniswapV3.Pool.FlashProtocolTrace
import Benchmarks.UniswapV3.Pool.FeeGrowthStorage
import Benchmarks.UniswapV3.Pool.SourceFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapPoolProtocolStmt (second : Bool) : Stmt :=
  .ite (.binary .gt (.field (.var "state") "protocolFee") (.intLit 0))
    [.assign .storage ⟨"protocolFees", [.field (protocolFeesField second)]⟩
      (.cast (.binary .add (protocolFeesExpr second) (.field (.var "state") "protocolFee"))
        (.elem (.int (.uint ⟨128, by decide⟩))))] []

def swapPoolFeesBody (second : Bool) : List Stmt :=
  [.assign .storage ⟨feeGrowthName second, []⟩ (.field (.var "state") "feeGrowthGlobalX128"),
    swapPoolProtocolStmt second]

def swapPoolFeesState (evm : EVM.State) (second : Bool) (s : SwapStateData) : EVM.State :=
  flashProtocolState (storeFeeGrowth evm second s.feeGrowth) second s.protocolFee

def swapPoolFeesMap (σ : AccountMap) (ee : ExecutionEnv) (second : Bool)
    (s : SwapStateData) : AccountMap :=
  flashProtocolMap (sstoreAccountMap ee.codeOwner σ (feeGrowthSlot second) s.feeGrowth)
    ee second s.protocolFee

theorem SourceState.swapPoolFees {s0 ee σ evm} (hsource : SourceState s0 ee σ evm)
    (second : Bool) (s : SwapStateData) :
    SourceState s0 ee (swapPoolFeesMap σ ee second s) (swapPoolFeesState evm second s) := by
  have hstore : SourceState s0 ee
      (sstoreAccountMap ee.codeOwner σ (feeGrowthSlot second) s.feeGrowth)
      (storeFeeGrowth evm second s.feeGrowth) := by
    simpa only [storeFeeGrowth, hsource.env] using
      hsource.storageWrite (feeGrowthSlot second) s.feeGrowth
  exact SourceState.flashProtocolState hstore second s.protocolFee

theorem swapPoolProtocolSource {frame : Frame} (evm : EVM.State) (second : Bool)
    (s : SwapStateData) (hf : frame.contract = contract)
    (hs : frame.locals.get? "state" = some s.value)
    (hbase : frame.locals.get? "protocolFees" = none) (hfit : s.Fits) :
    ExecStmt config frame evm (swapPoolProtocolStmt second)
      (.ok frame (flashProtocolState evm second s.protocolFee)) := by
  have hp : evalExpr? config frame evm (.field (.var "state") "protocolFee") =
      .ok (.int (Int.ofNat s.protocolFee.toNat)) :=
    evalExpr_structField (name := "protocolFee") (evalExpr_var_get hs) rfl
  have he := evalExpr_word_gt hp
    (show evalExpr? config frame evm (.intLit 0) =
      .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by simp only [evalExpr?, pure]; rfl)
  have hc := uint128Word_clean hfit.2.2.2.2.1
  by_cases hz : s.protocolFee = ⟨0⟩
  · rw [flashProtocolState, hc, if_pos hz]
    exact ExecStmt.iteFalse
      (by simpa only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl,
        decide_false] using he) .nil
  · rw [flashProtocolState, hc, if_neg hz]
    have hpos : 0 < s.protocolFee.toNat :=
      Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    refine ExecStmt.iteTrue ?_ (ExecBlock.consNormal ?_ .nil)
    · simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hpos, decide_true] using he
    have hold := evalProtocolFeesWord frame.locals frame.immutables evm second hbase
    rw [← frame_eq_of_parts hf rfl] at hold
    have hsum : evalExpr? config frame evm
        (.binary .add (protocolFeesExpr second) (.field (.var "state") "protocolFee")) =
        .ok (.int (Int.ofNat (protocolFeesWord second evm.accountMap evm.executionEnv).toNat +
          Int.ofNat s.protocolFee.toNat)) := by
      simp only [evalExpr?, hold, hp, bind, EvalResult.bind, evalBinaryOp?]
    have hcast := evalExpr_intCast (.uint ⟨128, by decide⟩) hsum
    rw [uint128_add_cast] at hcast
    have hass := assignProtocolFee evm frame.locals frame.immutables second
      (uint128Word (protocolFeesWord second evm.accountMap evm.executionEnv + s.protocolFee)) hbase
    rw [← frame_eq_of_parts hf rfl, storeProtocolFee_uint128Word] at hass
    exact ExecStmt.assign hcast hass

theorem swapPoolFeesBranchSource {frame : Frame} (evm : EVM.State) (second : Bool)
    (s : SwapStateData) (hf : frame.contract = contract)
    (hs : frame.locals.get? "state" = some s.value)
    (hg : frame.locals.get? (feeGrowthName second) = none)
    (hp : frame.locals.get? "protocolFees" = none) (hfit : s.Fits) :
    ExecBlock config frame evm (swapPoolFeesBody second)
      (.ok frame (swapPoolFeesState evm second s)) := by
  have hass := assignFeeGrowth frame.locals frame.immutables evm second s.feeGrowth hg
  rw [← frame_eq_of_parts hf rfl] at hass
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_structField (name := "feeGrowthGlobalX128") (evalExpr_var_get hs) rfl) hass)
    (ExecBlock.consNormal
      (swapPoolProtocolSource (storeFeeGrowth evm second s.feeGrowth) second s hf hs hp hfit) .nil)

theorem swapPoolFeesSource {frame : Frame} (evm : EVM.State) (zeroForOne : Bool)
    (s : SwapStateData) (hf : frame.contract = contract)
    (hz : frame.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hs : frame.locals.get? "state" = some s.value)
    (hg : ∀ second, frame.locals.get? (feeGrowthName second) = none)
    (hp : frame.locals.get? "protocolFees" = none) (hfit : s.Fits) :
    ExecStmt config frame evm swapTransition.body[16]!
      (.ok frame (swapPoolFeesState evm (!zeroForOne) s)) := by
  cases zeroForOne
  · exact ExecStmt.iteFalse (evalExpr_var_get hz)
      (swapPoolFeesBranchSource evm true s hf hs (hg true) hp hfit)
  · exact ExecStmt.iteTrue (evalExpr_var_get hz)
      (swapPoolFeesBranchSource evm false s hf hs (hg false) hp hfit)

end Benchmarks.UniswapV3.Pool
