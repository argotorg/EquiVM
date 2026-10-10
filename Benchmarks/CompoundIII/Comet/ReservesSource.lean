import Benchmarks.CompoundIII.Comet.ReservesMath
import Benchmarks.CompoundIII.Comet.TokenBalanceCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def ReservesReplyValid (v : CometWithExtendedAssetListImmutables) (w0 w1 time : UInt256)
    (z : Bool) (out : ByteArray) : Prop :=
  z = true ∧ 32 ≤ out.size ∧ ReservesMathValid v w0 w1 time (calldataWord out 0)

instance (v : CometWithExtendedAssetListImmutables) (w0 w1 time : UInt256) (z : Bool)
    (out : ByteArray) : Decidable (ReservesReplyValid v w0 w1 time z out) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def reservesTailBlock : List Stmt :=
  .externalCall (.var "token") "balanceOf" (.intLit 0) [.env .this] "balance" (perm := false) ::
    reservesPresentBlock ++ reservesSignedBlock

def reservesCallable : CallableDecl :=
  { params := [], returnType := [.elem (.int (.sint ⟨256, by decide⟩))]
    body := reservesStartBlock ++ reservesTailBlock }

theorem reservesCallable_lookup :
    lookupCallable? contract "getReserves_body" = some reservesCallable := rfl

theorem reservesTail_result (v : CometWithExtendedAssetListImmutables)
    (w0 w1 time : UInt256) (evm evm' : EVM.State) (z : Bool) (out : ByteArray)
    (hv : CurrentIndicesValid v w0 w1 time)
    (hc : callViaEVM evm v.baseToken 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (z, evm', out) false) (hhi : out.size < 2^255) :
    ExecBlock config (reservesReadyFrame v w0 w1 time) evm reservesTailBlock
      (if ReservesReplyValid v w0 w1 time z out then
        .returned (reservesFinalFrame v w0 w1 time (calldataWord out 0)) evm'
          (some [.int (reservesValue v w0 w1 time (calldataWord out 0))]) else .reverted) := by
  have he : evalExpr? config (reservesReadyFrame v w0 w1 time) evm (.var "token") =
      .ok (.address v.baseToken) := by
    simp only [evalExpr?, reservesReadyFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  by_cases hcall : z = true ∧ 32 ≤ out.size
  · rcases hcall with ⟨rfl, hlen⟩
    simp only [ReservesReplyValid, hlen, and_self, true_and]
    apply ExecBlock.consNormal (tokenBalance_source_ok he hc hlen hhi)
    exact execBlockAppendOk (reservesPresent_result v w0 w1 time (calldataWord out 0) evm' hv)
      (reservesSigned_result v w0 w1 time (calldataWord out 0) evm' hv)
  · rw [if_neg (show ¬ ReservesReplyValid v w0 w1 time z out from fun h ↦ hcall ⟨h.1, h.2.1⟩)]
    exact ExecBlock.consRevert (tokenBalance_source_revert he hc hcall)

theorem reserves_body_early_revert (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (hv : ¬ CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v }
      evm reservesCallable.body .reverted := by
  have hs := reservesStart_result v evm
  dsimp only at hs
  rw [if_neg hv] at hs
  exact ExecFuncBody.execBlockRevert (execBlockAppendReverted hs)

theorem reserves_body_result (v : CometWithExtendedAssetListImmutables)
    (evm evm' : EVM.State) (z : Bool) (out : ByteArray)
    (hv : CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv))
    (hc : callViaEVM evm v.baseToken 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (z, evm', out) false) (hhi : out.size < 2^255) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    let time := timestampWord evm.executionEnv
    ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v }
      evm reservesCallable.body
      (if ReservesReplyValid v w0 w1 time z out then
        .returned (reservesFinalFrame v w0 w1 time (calldataWord out 0)) evm'
          (some [.int (reservesValue v w0 w1 time (calldataWord out 0))]) else .reverted) := by
  dsimp only
  have hs := reservesStart_result v evm
  dsimp only at hs
  rw [if_pos hv] at hs
  have hb := execBlockAppendOk hs (reservesTail_result v _ _ _ evm evm' z out hv hc hhi)
  split_ifs with hm
  · rw [if_pos hm] at hb
    exact ExecFuncBody.execBlockRet hb
  · rw [if_neg hm] at hb
    exact ExecFuncBody.execBlockRevert hb

theorem reserves_call_early_revert (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (ret : Ident)
    (hf : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hv : ¬ CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)) :
    ExecStmt config frame evm (.internalCall "getReserves_body" [] ret) .reverted := by
  exact ExecStmt.internalCallRevert (callee := reservesCallable) (locals := ∅)
    (cfg := config) (solm := frame) (evm := evm) (args := []) (argVals := []) rfl
    (by rw [hf]; exact reservesCallable_lookup) rfl
    (by simpa only [hf, hi] using reserves_body_early_revert v evm hv)

theorem reserves_call_result (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm evm' : EVM.State) (ret : Ident) (z : Bool) (out : ByteArray)
    (hf : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hv : CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv))
    (hc : callViaEVM evm v.baseToken 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (z, evm', out) false) (hhi : out.size < 2^255) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    let time := timestampWord evm.executionEnv
    ExecStmt config frame evm (.internalCall "getReserves_body" [] ret)
      (if ReservesReplyValid v w0 w1 time z out then
        .ok { frame with locals :=
          frame.locals.insert ret (.int (reservesValue v w0 w1 time (calldataWord out 0))) }
          evm' else .reverted) := by
  dsimp only
  have hb := reserves_body_result v evm evm' z out hv hc hhi
  dsimp only at hb
  split_ifs with hm
  · rw [if_pos hm] at hb
    exact ExecStmt.internalCallReturn (callee := reservesCallable) (locals := ∅)
      (cfg := config) (solm := frame) (evm := evm) (args := []) (argVals := []) rfl
      (by rw [hf]; exact reservesCallable_lookup) rfl (by simpa only [hf, hi] using hb)
  · rw [if_neg hm] at hb
    exact ExecStmt.internalCallRevert (callee := reservesCallable) (locals := ∅)
      (cfg := config) (solm := frame) (evm := evm) (args := []) (argVals := []) rfl
      (by rw [hf]; exact reservesCallable_lookup) rfl (by simpa only [hf, hi] using hb)

end Benchmarks.CompoundIII.Comet
