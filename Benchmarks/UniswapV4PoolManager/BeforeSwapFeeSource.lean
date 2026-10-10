import Benchmarks.UniswapV4PoolManager.BytesUintSlice
import Benchmarks.UniswapV4PoolManager.Slot0FeeSource
import Benchmarks.UniswapV4PoolManager.InitializeHookABI
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def beforeSwapDynamic (key : PoolKeyWords) : Prop := key.fee = ⟨8388608⟩
instance (key : PoolKeyWords) : Decidable (beforeSwapDynamic key) := inferInstanceAs (Decidable (_ = _))
def beforeSwapFeeWord (out : ByteArray) : UInt256 := UInt256.land (calldataWord out 64) ⟨16777215⟩
def beforeSwapFee (key : PoolKeyWords) (out : ByteArray) : UInt256 :=
  if beforeSwapDynamic key then beforeSwapFeeWord out else ⟨0⟩
def beforeSwapFeeFrame (f : Frame) (key : PoolKeyWords) (out : ByteArray) : Frame :=
  if beforeSwapDynamic key then valueLocal f "lpFeeOverride" (.int (Int.ofNat (beforeSwapFeeWord out).toNat)) else f
def beforeSwapFeeStmt : Stmt :=
  .ite (.binary .eq (.field (.var "key") "fee") (.intLit 8388608))
    [.assign .localVar {base := "lpFeeOverride"}
      (.cast (.abiDecode abiUInt256 (.bytesSlice (.var "result") (.intLit 64) (.intLit 96)))
        (.elem (.int (.uint ⟨24, by decide⟩))))] []

theorem beforeSwapFee_bound (key : PoolKeyWords) (out : ByteArray) : (beforeSwapFee key out).toNat < 2^24 := by
  rw [beforeSwapFee]
  split_ifs
  · rw [beforeSwapFeeWord, uland_toNat]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by decide)
  · decide

theorem beforeSwapFeeSource {f : Frame} {evm : State} {key : PoolKeyWords} {out : ByteArray} {old : Value}
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hr : f.locals.get? "result" = some (.bytes out))
    (hf : f.locals.get? "lpFeeOverride" = some old) (hsize : 96 ≤ out.size) :
    ExecStmt config f evm beforeSwapFeeStmt (.ok (beforeSwapFeeFrame f key out) evm) := by
  have hfee := evalStructField (evalLocalValue (cfg := config) (evm := evm) hk) (field := "fee") rfl
  have hcondition := evalEqWords hfee
    (show evalExpr? config f evm (.intLit 8388608) = .ok (.int (Int.ofNat (⟨8388608⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  change evalExpr? config f evm _ = .ok (.bool (decide (beforeSwapDynamic key))) at hcondition
  by_cases hd : beforeSwapDynamic key
  · rw [beforeSwapFeeFrame, if_pos hd]
    have hdecode := evalDecodeUint256Slice (start := 64) rfl (evalLocalValue (cfg := config) (evm := evm) hr) hsize
    have hcast := evalExpr_cast_int (intType := .uint ⟨24, by decide⟩) hdecode
    rw [normalizeUintWord ⟨24, by decide⟩ _ ⟨16777215⟩ rfl] at hcast
    exact ExecStmt.iteTrue (hcondition.trans (by rw [decide_eq_true hd]))
      (execBlock_singleton (ExecStmt.assign hcast (assignLocalValue hf)))
  · rw [beforeSwapFeeFrame, if_neg hd]
    exact ExecStmt.iteFalse (hcondition.trans (by rw [decide_eq_false hd])) ExecBlock.nil

theorem beforeSwapFeeFrame_get (f : Frame) (key : PoolKeyWords) (out : ByteArray) (name : Ident)
    (hn : ("lpFeeOverride" == name) = false) :
    (beforeSwapFeeFrame f key out).locals.get? name = f.locals.get? name := by
  rw [beforeSwapFeeFrame]
  split_ifs <;> simp only [valueLocal_get, hn, Bool.false_eq_true, if_false]

theorem beforeSwapFeeFrame_fee {f : Frame} (key : PoolKeyWords) (out : ByteArray)
    (hf : f.locals.get? "lpFeeOverride" = some (.int 0)) :
    (beforeSwapFeeFrame f key out).locals.get? "lpFeeOverride" = some (.int (Int.ofNat (beforeSwapFee key out).toNat)) := by
  simp only [beforeSwapFeeFrame, beforeSwapFee]
  split_ifs
  · exact store_get_self _ _ _
  · exact hf

end Benchmarks.UniswapV4PoolManager
