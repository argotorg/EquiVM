import Benchmarks.Midnight.LiquidateSourceFrame
import Benchmarks.Midnight.MemoryWords
import Benchmarks.Midnight.WordTuple
import Benchmarks.Midnight.RuntimeBlocks_024

/-! Liquidation's two-word ABI return and its source return statement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem liquidateReturnEncoding (seized repaid : UInt256) :
    encodeReturnValues? [Model.u256, Model.u256] [.int seized.toNat, .int repaid.toNat] =
      some (wordArrayBytes [seized, repaid]) := by
  apply uintWordTupleReturnEncoding [(⟨256, by decide⟩, seized), (⟨256, by decide⟩, repaid)]
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact seized.val.isLt
  · exact repaid.val.isLt

theorem liquidateReturnSource {frame : Frame} {evm : State} {m : MarketData}
    {id index seized repaid borrower mode : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    ExecStmt config frame evm (liquidateTransition.body[24]!)
      (.returned frame evm (some [.int seized.toNat, .int repaid.toNat])) := by
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, hf.seized, hf.repaid, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

theorem midnightLiquidateReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root seized repaid : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hroot : root.toNat < 2^64) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (rd : RD midnightBytecode I g s0 ⟨5803⟩ R mem aw rdata σ k C) :
    RDret midnightBytecode g s0 σ (wordArrayBytes [seized, repaid]) := by
  have hr := midnightBlocks.midnight_block_5803 hstack rd
  have h32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hp : memLoad (UInt256.ofNat 608) (writeWord mem root.toNat seized) = repaid := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by change 640 ≤ mem.size; omega)
      (Or.inl (by change 640 ≤ root.toNat; omega)), hpaid]
  simp only [hfree, hseized, h32] at hr
  change RDret midnightBytecode g s0 σ
    ((writeWord (writeWord mem root.toNat seized) (root.toNat + 32)
      (memLoad (UInt256.ofNat 608) (writeWord mem root.toNat seized))).readWithPadding
      root.toNat 64) at hr
  rw [hp] at hr
  have hm : writeWord (writeWord mem root.toNat seized) (root.toNat + 32) repaid =
      writeWordArray mem root.toNat [seized, repaid] := rfl
  rw [hm] at hr
  have hread := (MemoryWords.of_writeWordArray mem root.toNat [seized, repaid]
    (by change root.toNat + 64 < 2^256; omega) (by simp)).read
  exact hread ▸ hr

end Benchmarks.Midnight
