import Examples.Ripemd160Old.HashScratch
import Examples.Precompiles.Ripemd160.ParserCursor

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Reasoning.Reach

private theorem oldSwap9_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok (stSwap s (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t),
        .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP9, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap9 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t).length - 10 + 10 >
        1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.swap9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => oldSwap9_xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace Ripemd160Old

open Ripemd160

def oldBlockCountWord (I : ExecutionEnv) : UInt256 :=
  UInt256.div (hashPaddedLengthWord I) ⟨64⟩

theorem oldBlockCountWord_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (oldBlockCountWord I).toNat = Model.paddedLength I.calldata.size / 64 := by
  unfold oldBlockCountWord
  rw [udiv_toNat, hashPaddedLengthWord_toNat I hsmall,
    show (⟨64⟩ : UInt256).toNat = 64 from by decide]

private theorem oldOfNatMulShift (n scale shift : Nat)
    (hn : n * scale < UInt256.size) (hscale : scale = 2 ^ shift)
    (hshift : shift < 256) :
    UInt256.ofNat n * UInt256.ofNat scale =
      UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat shift) := by
  have hscalePos : 0 < scale := by rw [hscale]; positivity
  have hnSize : n < UInt256.size :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right n hscalePos) hn
  have hscaleSize : scale < UInt256.size := by
    rw [hscale, UInt256.size]
    exact Nat.pow_lt_pow_right (by decide) hshift
  apply u256_inj
  rw [umul_toNat]
  · rw [ulit_toNat' n hnSize, ulit_toNat' scale hscaleSize,
      ushl_ofNat_toNat _ shift hshift]
    rw [ulit_toNat' n hnSize, Nat.shiftLeft_eq, ← hscale,
      Nat.mod_eq_of_lt hn]
  · rw [ulit_toNat' n hnSize, ulit_toNat' scale hscaleSize]
    exact hn

theorem oldBlockMul64_eq (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {block : Nat}
    (hblock : block < Model.paddedLength I.calldata.size / 64) :
    UInt256.mul (UInt256.ofNat block) ⟨64⟩ =
      UInt256.shiftLeft (UInt256.ofNat block) ⟨6⟩ := by
  change UInt256.ofNat block * ⟨64⟩ = _
  have hp := (hashPaddedLength_bounds I.calldata.size).2
  have hfit : block * 64 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    unfold maxFallbackCalldataSize at hsmall
    omega
  simpa using oldOfNatMulShift block 64 6 hfit (by decide) (by decide)

theorem oldIndexMul4_eq {i : Nat} (hi : i < 16) :
    UInt256.mul (UInt256.ofNat i) ⟨4⟩ =
      UInt256.shiftLeft (UInt256.ofNat i) ⟨2⟩ := by
  change UInt256.ofNat i * ⟨4⟩ = _
  simpa using oldOfNatMulShift i 4 2 (by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega) (by decide) (by decide)

def oldParseLoopStack (I : ExecutionEnv) (block i : Nat)
    (h : RuntimeChain) : List UInt256 :=
  [UInt256.ofNat i,
    hashPadPtr I + UInt256.shiftLeft (UInt256.ofNat block) ⟨6⟩,
    h.h1, hashPadPtr I, hashPaddedLengthWord I, hashScratchPtr I,
    UInt256.ofNat block, h.h2, h.h0, h.h4, h.h3, ⟨254⟩]

/-- Take the old outer block guard and enter its 16-word parser. -/
theorem runtime_enterParseLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (rd8533 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8533⟩ (oldBlockLoopStack I (UInt256.ofNat block) h)
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8635⟩ (oldParseLoopStack I block 0 h)
      c.mem c.aw ByteArray.empty (cA, σ) k' C' := by
  simp only [oldBlockLoopStack] at rd8533
  have hblk : UInt256.lt (UInt256.ofNat block) (oldBlockCountWord I) = ⟨1⟩ := by
    apply ult_one
    rw [oldBlockCountWord_toNat I hsmall,
      ulit_toNat' block (by
        have hp := (hashPaddedLength_bounds I.calldata.size).2
        rw [show UInt256.size = 2 ^ 256 from by decide]
        unfold maxFallbackCalldataSize at hsmall
        omega)]
    exact hblock
  have rd8618 := evm_run_rfl rd8533 with [
    jumpdest, push1 ⟨64⟩, dup3, div, dup5, lt, push2 ⟨8618⟩,
    jumpiT (by rw [show UInt256.lt (UInt256.ofNat block)
      (UInt256.div (hashPaddedLengthWord I) ⟨64⟩) = ⟨1⟩ from hblk]; decide)
      jump_8618 ]
  have rd8635 := evm_run_rfl rd8618 with [
    jumpdest, swap1, swap2, swap3, swap4, swap6, swap8,
    push1 ⟨64⟩, dup6, swap9, swap7, swap9, mul, dup3, add,
    push0 ]
  rw [oldBlockMul64_eq I hsmall hblock] at rd8635
  exact ⟨_, _, by
    simpa [oldBlockLoopStack, oldParseLoopStack] using rd8635⟩

/-- One iteration of the old parser, expressed by the shared parser cursor step. -/
theorem runtime_parseLoopBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {block i : Nat} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (hi : i < 16)
    (rd8635 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8635⟩ (oldParseLoopStack I block i h)
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8635⟩ (oldParseLoopStack I block (i + 1) h)
      (hashParseStep I (UInt256.ofNat block) (UInt256.ofNat i) c).mem
      (hashParseStep I (UInt256.ofNat block) (UInt256.ofNat i) c).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldParseLoopStack] at rd8635
  have hguard : UInt256.lt (UInt256.ofNat i) ⟨16⟩ = ⟨1⟩ := by
    apply ult_one
    rw [ulit_toNat' i (lt_trans hi (by decide)),
      show (⟨16⟩ : UInt256).toNat = 16 from by decide]
    exact hi
  have rd8997 := evm_run_rfl rd8635 with [
    jumpdest, push1 ⟨16⟩, dup2, lt, push2 ⟨8997⟩,
    jumpiT (by rw [hguard]; decide) jump_8997 ]
  have rd9011pre := evm_run_rfl rd8997 with [
    jumpdest, dup1, push1 ⟨4⟩, push1 ⟨1⟩, swap3, mul,
    dup4, add, push1 ⟨3⟩, dup2, add ]
  rw [oldIndexMul4_eq hi] at rd9011pre
  have rd9012 := RD.runtimeMload rd9011pre (by old_decode) (by simp)
  have rd9021pre := evm_run_rfl rd9012 with [
    push0, byte, push1 ⟨24⟩, shl, push1 ⟨2⟩, dup3, add ]
  have rd9022 := RD.runtimeMload rd9021pre (by old_decode) (by simp)
  have rd9032pre := evm_run_rfl rd9022 with [
    push0, byte, push1 ⟨16⟩, shl, or, swap1, dup4, dup2, add ]
  have rd9033 := RD.runtimeMload rd9032pre (by old_decode) (by simp)
  have rd9039pre := evm_run_rfl rd9033 with [
    push0, byte, push1 ⟨8⟩, shl, swap1 ]
  have rd9040 := RD.runtimeMload rd9039pre (by old_decode) (by simp)
  have rd9050pre := evm_run_rfl rd9040 with [
    push0, byte, or, or, push1 ⟨32⟩, dup3, mul, dup9, add ]
  have rd9051 := RD.runtimeMstore rd9050pre (by old_decode) (by simp)
  have rd8635next := evm_run_rfl rd9051 with [
    add, push2 ⟨8635⟩, jump jump_8635 ]
  have hdst : UInt256.mul (UInt256.ofNat i) ⟨32⟩ =
      UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩ := by
    change UInt256.ofNat i * ⟨32⟩ = _
    exact oldOfNatMulShift i 32 5 (by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega) (by decide) (by decide)
  rw [hdst] at rd8635next
  exact ⟨_, _, by
    simpa [oldParseLoopStack, hashParseStep, hashParseAddress,
      hashParseScratchAddress, hashParseWord, hashParseV3, hashParseV2,
      hashParseV1, hashParseV0, hashParseAw3, hashParseAw2,
      hashParseAw1, hashParseAw0, u256_add_comm, u256_one_add_ofNat,
      u256_lor_comm] using rd8635next⟩

theorem runtime_parseLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {block n : Nat} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (hn : n ≤ 16)
    (rd : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8635⟩ (oldParseLoopStack I block 0 h)
      initial.mem initial.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8635⟩ (oldParseLoopStack I block n h)
      (hashParseCursor I (UInt256.ofNat block) initial n).mem
      (hashParseCursor I (UInt256.ofNat block) initial n).aw
      ByteArray.empty (cA, σ) k' C' := by
  induction n with
  | zero => exact ⟨_, _, by simpa [hashParseCursor] using rd⟩
  | succ n ih =>
      obtain ⟨_, _, rdn⟩ := ih (by omega)
      obtain ⟨_, _, rdnext⟩ := runtime_parseLoopBody hblock (by omega) rdn
      exact ⟨_, _, by simpa [hashParseCursor] using rdnext⟩

end Ripemd160Old
