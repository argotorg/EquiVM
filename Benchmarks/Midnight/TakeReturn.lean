import Benchmarks.Midnight.TakeSourceFrame
import Benchmarks.Midnight.MemoryWords
import Benchmarks.Midnight.WordTuple
import Benchmarks.Midnight.RuntimeBlocks_049

variable {fork : Ethereum.Fork}

/-! Take's two-word ABI return and source return statement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem takeReturnEncoding (bought sold : UInt256) :
    encodeReturnValues? [Model.u256, Model.u256] [.int bought.toNat, .int sold.toNat] =
      some (wordArrayBytes [bought, sold]) := by
  apply uintWordTupleReturnEncoding [(⟨256, by decide⟩, bought), (⟨256, by decide⟩, sold)]
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact bought.val.isLt
  · exact sold.val.isLt

theorem takeReturnSource {frame : Frame} {evm : State} {bought sold : UInt256}
    (hb : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hs : frame.locals.get? "sellerAssets" = some (.int sold.toNat)) :
    ExecStmt fork config frame evm (takeTransition.body[74]!)
      (.returned frame evm (some [.int bought.toNat, .int sold.toNat])) := by
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, hb, hs, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem midnightTakeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root bought sold : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hroot : root.toNat < 2^64) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hpaid : memLoad (UInt256.ofNat 416) mem = sold)
    (rd : RD fork midnightBytecode I g s0 ⟨13372⟩ R mem aw rdata σ k C) :
    RDret fork midnightBytecode g s0 σ (wordArrayBytes [bought, sold]) := by
  have hr := midnightBlocks.midnight_block_13372 hstack rd
  have h32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hp : memLoad (UInt256.ofNat 416) (writeWord mem root.toNat bought) = sold := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by change 448 ≤ mem.size; omega)
      (Or.inl (by change 448 ≤ root.toNat; omega)), hpaid]
  simp only [hfree, hbought, h32] at hr
  change RDret fork midnightBytecode g s0 σ
    ((writeWord (writeWord mem root.toNat bought) (root.toNat + 32)
      (memLoad (UInt256.ofNat 416) (writeWord mem root.toNat bought))).readWithPadding
      root.toNat 64) at hr
  rw [hp] at hr
  have hm : writeWord (writeWord mem root.toNat bought) (root.toNat + 32) sold =
      writeWordArray mem root.toNat [bought, sold] := rfl
  rw [hm] at hr
  have hread := (MemoryWords.of_writeWordArray mem root.toNat [bought, sold]
    (by change root.toNat + 64 < 2^256; omega) (by simp)).read
  exact hread ▸ hr

end Benchmarks.Midnight
