import Examples.Ripemd160.HashWideInitInvariant

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem RuntimeRightWideInvariant.activeCover {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n : Nat} {X : Fin 16 → UInt256}
    {left right : RuntimeLineState}
    (hinv : RuntimeRightWideInvariant I cursor n X left right)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashScratchPtr I).toNat + 832 ≤ 32 * cursor.aw.toNat := by
  have hw : RuntimeWordAt cursor (hashScratchPtr I + ⟨800⟩) right.e := by
    simpa [u256_add_assoc,
      show (⟨672⟩ : UInt256) + ⟨128⟩ = ⟨800⟩ by native_decide] using
      hinv.rightLine.2.2.2.2
  have haddr : (hashScratchPtr I + ⟨800⟩).toNat =
      (hashScratchPtr I).toNat + 800 :=
    hashScratchAdd_toNat I hsmall (by omega : 800 ≤ 895)
  have hlt : (hashScratchPtr I).toNat + 800 < 32 * cursor.aw.toNat := by
    have hn := hw.2.2
    change ¬ (cursor.aw * ⟨32⟩).toNat ≤
      (hashScratchPtr I + ⟨800⟩).toNat at hn
    rw [mul32_toNat_of_lt_pow64 hinv.padded.awSmall, haddr] at hn
    omega
  let q := 30 + (I.calldata.size + 31) / 32 +
    2 * ((I.calldata.size + 72) / 64)
  have halign : (hashScratchPtr I).toNat + 800 = 32 * q := by
    change (hashNewFreePtr I).toNat + 800 = 32 * q
    rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall]
    simp only [Model.paddedLength, q]
    omega
  omega

theorem ripemd160X_recombine_wide {cA σ I} {g : Sat256} {s0 : State}
    {c : RuntimeMemCursor} {rdata : ByteArray} {k C n : Nat}
    {h : RuntimeChain} {left right : RuntimeLineState} {blk : UInt256}
    {X : Fin 16 → UInt256}
    (hinv : RuntimeRightWideInvariant I c n X left right)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (rd1406 : RD ripemd160RuntimeBytecode I g s0 ⟨1406⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD ripemd160RuntimeBytecode I g s0 ⟨1028⟩
      (hashBlockLoopStack I (blk + ⟨1⟩) (runtimeRecombineChain h left right))
      c.mem c.aw rdata (cA, σ) k' C' := by
  have hcover := hinv.activeCover hsmall
  have addrNat (m : UInt256) (hm : m.toNat ≤ 832) :
      (hashScratchPtr I + m).toNat = (hashScratchPtr I).toNat + m.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt]
    have hu := hashScratchPtr_add_uint I hsmall
    omega
  have awEq (m : UInt256) (hm : m.toNat ≤ 800) :
      runtimeMloadAw c.aw (hashScratchPtr I + m) = c.aw := by
    apply runtimeMloadAw_eq_of_covers_wide hinv.padded.awSmall
    · have hw := hashScratchPtr_add_wide I hsmall
      rw [show UInt256.size = 2 ^ 256 from by decide]
      rw [addrNat m (by omega)]
      norm_num at hw ⊢
      omega
    · rw [addrNat m (by omega)]
      omega
  have lv512 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨512⟩) = left.a :=
    hinv.leftLine.1.load
  have lv544 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨544⟩) = left.b := by
    rw [← show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.leftLine.2.1.load
  have lv576 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨576⟩) = left.c := by
    rw [← show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.leftLine.2.2.1.load
  have lv608 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨608⟩) = left.d := by
    rw [← show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.leftLine.2.2.2.1.load
  have lv640 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨640⟩) = left.e := by
    rw [← show (⟨512⟩ : UInt256) + ⟨128⟩ = ⟨640⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.leftLine.2.2.2.2.load
  have rv672 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨672⟩) = right.a :=
    hinv.rightLine.1.load
  have rv704 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨704⟩) = right.b := by
    rw [← show (⟨672⟩ : UInt256) + ⟨32⟩ = ⟨704⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.rightLine.2.1.load
  have rv736 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨736⟩) = right.c := by
    rw [← show (⟨672⟩ : UInt256) + ⟨64⟩ = ⟨736⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.rightLine.2.2.1.load
  have rv768 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨768⟩) = right.d := by
    rw [← show (⟨672⟩ : UInt256) + ⟨96⟩ = ⟨768⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.rightLine.2.2.2.1.load
  have rv800 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨800⟩) = right.e := by
    rw [← show (⟨672⟩ : UInt256) + ⟨128⟩ = ⟨800⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.rightLine.2.2.2.2.load
  have rd1p := evm_run rd1406 with [push2 ⟨512⟩, dup5, add]
  have rd1 := RD.runtimeMload rd1p (by native_decide) (by simp)
  rw [awEq ⟨512⟩ (by decide), lv512] at rd1
  have rd2p := evm_run rd1 with [swap1, push2 ⟨544⟩, dup6, add]
  have rd2 := RD.runtimeMload rd2p (by native_decide) (by simp)
  rw [awEq ⟨544⟩ (by decide), lv544] at rd2
  have rd3p := evm_run rd2 with [swap1, push2 ⟨576⟩, dup7, add]
  have rd3 := RD.runtimeMload rd3p (by native_decide) (by simp)
  rw [awEq ⟨576⟩ (by decide), lv576] at rd3
  have rd4p := evm_run rd3 with [swap3, push2 ⟨608⟩, dup8, add]
  have rd4 := RD.runtimeMload rd4p (by native_decide) (by simp)
  rw [awEq ⟨608⟩ (by decide), lv608] at rd4
  have rd5p := evm_run rd4 with [swap2, push2 ⟨640⟩, dup9, add]
  have rd5 := RD.runtimeMload rd5p (by native_decide) (by simp)
  rw [awEq ⟨640⟩ (by decide), lv640] at rd5
  have rd6p := evm_run rd5 with [push2 ⟨672⟩, dup10, add]
  have rd6 := RD.runtimeMload rd6p (by native_decide) (by simp)
  rw [awEq ⟨672⟩ (by decide), rv672] at rd6
  have rd7p := evm_run rd6 with [swap2, push2 ⟨704⟩, dup11, add]
  have rd7 := RD.runtimeMload rd7p (by native_decide) (by simp)
  rw [awEq ⟨704⟩ (by decide), rv704] at rd7
  have rd8p := evm_run rd7 with [swap5, push2 ⟨736⟩, dup12, add]
  have rd8 := RD.runtimeMload rd8p (by native_decide) (by simp)
  rw [awEq ⟨736⟩ (by decide), rv736] at rd8
  have rd9p := evm_run rd8 with [swap8, push2 ⟨768⟩, dup13, add]
  have rd9 := RD.runtimeMload rd9p (by native_decide) (by simp)
  rw [awEq ⟨768⟩ (by decide), rv768] at rd9
  have rd10p := evm_run rd9 with [swap1, push2 ⟨800⟩, dup14, add]
  have rd10 := RD.runtimeMload rd10p (by native_decide) (by simp)
  rw [awEq ⟨800⟩ (by decide), rv800] at rd10
  have rd1028 := evm_run rd10 with [
    swap4, add, add, push4 ⟨4294967295⟩, and, swap13,
    add, add, push4 ⟨4294967295⟩, and, swap14,
    add, add, push4 ⟨4294967295⟩, and, swap11,
    add, add, push4 ⟨4294967295⟩, and, swap8,
    add, add, push4 ⟨4294967295⟩, and, swap5,
    swap4, push1 ⟨1⟩, add, swap3, swap2, swap1,
    push2 ⟨1028⟩, jump (by jump_dest) ]
  exact ⟨_, _, by
    simpa [hashBlockLoopStack, runtimeRecombineChain, mask32Word,
      u256_add_comm, u256_add_assoc] using rd1028⟩

end Ripemd160
