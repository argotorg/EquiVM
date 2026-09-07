import Examples.UniswapV2Pair.Bytecode
import Examples.UniswapV2Pair.ErrorDynamicRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

def uniswapSafeMathMulOverflowStringWord : UInt256 :=
  UInt256.shiftLeft
    (⟨573467620053399432674451404801797420674347462519⟩ : UInt256) ⟨96⟩

theorem uint256_mul_div_eq_zero_of_overflow {a b : UInt256}
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    UInt256.eq (UInt256.div (UInt256.mul a b) b) a = ⟨0⟩ := by
  have hbNat : b.toNat ≠ 0 := by
    intro hb
    have hprod : a.toNat * b.toNat = 0 := by simp [hb]
    have hpos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  apply u256_eq_of_ne
  intro heq
  have hnat := congrArg UInt256.toNat heq
  have hdivNat : (UInt256.div (UInt256.mul a b) b).toNat =
      ((a.toNat * b.toNat) % UInt256.size) / b.toNat := by
    unfold UInt256.div UInt256.toNat
    simp only
    change (UInt256.mul a b).toNat / b.toNat =
      (a.toNat * b.toNat) % UInt256.size / b.toNat
    rw [u256_mul_toNat]
  have hdivEq : ((a.toNat * b.toNat) % UInt256.size) / b.toNat = a.toNat := by
    simpa [hdivNat] using hnat
  have hle : a.toNat * b.toNat ≤ (a.toNat * b.toNat) % UInt256.size := by
    calc
      a.toNat * b.toNat =
          (((a.toNat * b.toNat) % UInt256.size) / b.toNat) * b.toNat := by
        rw [hdivEq]
      _ ≤ (a.toNat * b.toNat) % UInt256.size := Nat.div_mul_le_self _ _
  have hmodLt : (a.toNat * b.toNat) % UInt256.size < a.toNat * b.toNat := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num [UInt256.size])) hover
  omega

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathMulOverflow_dynamic
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret aw ptr : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD uniswapV2PairBytecode ee g s0 ⟨6780⟩ (b :: a :: ret :: R)
      mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hawLo : 96 ≤ aw.toNat * 32) (hread64 : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 9 ≤ 1024) :
    RDrev uniswapV2PairBytecode g s0 := by
  have hb : b ≠ ⟨0⟩ := by
    intro hb
    subst b
    have hle0 : UInt256.size ≤ 0 := by simpa using hover
    norm_num [UInt256.size] at hle0
  have heq : UInt256.eq (UInt256.div (UInt256.mul a b) b) a = ⟨0⟩ :=
    uint256_mul_div_eq_zero_of_overflow hover
  have rd6804pre := evm_run h with [jumpdest, push1 ⟨0⟩, dup2, iszero, dup1,
    push2 ⟨6807⟩]
  rw [isZero_eq_zero_of_ne hb] at rd6804pre
  have rd6804 := evm_run rd6804pre with [
    jumpiNT (by native_decide), pop, pop, dup1, dup3, mul, dup3, dup3, dup3,
    dup2, push2 ⟨6804⟩, jumpiT hb (by jump_dest)]
  have rd6807 := evm_run rd6804 with [jumpdest, div, eq]
  rw [heq] at rd6807
  have rdTail := evm_run rd6807 with [jumpdest, push2 ⟨2911⟩,
    jumpiNT (by native_decide)]
  exact RD.solcErrorStringRevertTail_dynamic
    (code := uniswapV2PairBytecode) (pc := ⟨6812⟩) (len := ⟨20⟩)
    (rawWord := (⟨573467620053399432674451404801797420674347462519⟩ : UInt256))
    (shift := ⟨96⟩) (word := uniswapSafeMathMulOverflowStringWord)
    (op := .PUSH20) (width := 20) rdTail
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl) hin hlo hgap hfit haw hawLo hread64 (by simp only [List.length_cons]; omega)

end UniswapV2Pair
