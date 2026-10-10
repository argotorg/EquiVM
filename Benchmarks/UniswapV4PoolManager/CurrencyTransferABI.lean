import Benchmarks.UniswapV4PoolManager.TwoWordCallMemory
import Benchmarks.UniswapV4PoolManager.CurrencyBalanceABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def transferSelector : ByteArray := ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
def transferSelectorWord : UInt256 := ⟨76450787359836037641860180984291677749980919077056822294353438043884394381312⟩
def transferPayload (recipient : AccountAddress) (amount : UInt256) : ByteArray :=
  (transferSelector ++ (accountWord recipient).toByteArray) ++ amount.toByteArray

theorem transferPayload_size (recipient : AccountAddress) (amount : UInt256) :
    (transferPayload recipient amount).size = 68 := by
  simp only [transferPayload, ByteArray.size_append, toByteArray_size]
  rfl

theorem transferCallMemory_read (base : ByteArray) (off : Nat) (recipient : AccountAddress) (amount : UInt256)
    (hgap : off-base.size < USize.size) :
    (twoWordCallMemory base off transferSelectorWord (accountWord recipient) amount).readWithPadding off 68 =
      transferPayload recipient amount := by
  rw [twoWordCallMemory_read _ _ _ _ _ hgap]
  rw [show transferSelectorWord.toByteArray.extract 0 4 = transferSelector from by native_decide]
  rfl

def transferPayloadExpr : Expr := .abiEncodePacked
  [(.elem (.bytes 3), .fixedBytesLit 3 [169, 5, 156, 187]),
   (.elem (.int (.uint ⟨256, by decide⟩)), .cast (.var "to") (.elem (.int (.uint ⟨160, by decide⟩)))),
   (.elem (.int (.uint ⟨256, by decide⟩)), .var "amount")]

theorem evalTransferPayload {f : Frame} {evm : EVM.State} {recipient : AccountAddress} {amount : UInt256}
    (ht : f.locals.get? "to" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    evalExpr? config f evm transferPayloadExpr = .ok (.bytes (transferPayload recipient amount)) := by
  have hto : evalExpr? config f evm (.cast (.var "to") (.elem (.int (.uint ⟨160, by decide⟩)))) =
      .ok (.int (Int.ofNat (accountWord recipient).toNat)) := by
    rw [accountWord_toNat]
    exact evalCastValue (evalLocalValue ht) (by simp only [castValue?, show recipient.toNat < EVM.twoPow 160 from recipient.isLt, if_pos]; rfl)
  have hpacked := evalPackedArgs_cons
    (by simp only [evalExpr?, pure] : evalExpr? config f evm (.fixedBytesLit 3 [169, 5, 156, 187]) = .ok (.fixedBytes 3 [169, 5, 156, 187]))
    (by decide : encodePackedValue? (.elem (.bytes 3)) (.fixedBytes 3 [169, 5, 156, 187]) = some [169, 5, 156, 187])
    (evalPackedArgs_cons hto (encodePacked_uint256 (accountWord recipient))
      (evalPackedArgs_single (evalLocalValue ha) (encodePacked_uint256 amount)))
  simp only [transferPayloadExpr, evalExpr?, hpacked, bind, EvalResult.bind, pure]
  rw [transferPayload, ← word_toBytesBE_toByteArray_eq_toByteArray,
    ← word_toBytesBE_toByteArray_eq_toByteArray]
  congr 2
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_append, Array.toList_append, List.data_toByteArray,
    transferSelector, List.append_assoc]

end Benchmarks.UniswapV4PoolManager
