import Examples.UniswapV2Pair.SkimDynamicSecondRuntimeNoCode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathSubUnderflow_dynamic {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩ (b :: a :: ret :: R)
      mem aw rdata σ k C)
    (hlt : a.toNat < b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6886 := evm_run h with [jumpdest, dup1, dup3, sub, dup3, dup2]
  have rd6887₀ := evm_run rd6886 with [gt]
  have rd6887 := rd6887₀
  rw [hgt] at rd6887
  have rd6888₀ := evm_run rd6887 with [iszero]
  have rd6888 := rd6888₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6888
  have rd6891 := evm_run rd6888 with [
    push2 ⟨2911⟩, jumpiNT (by decide)]
  let fp0 : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size then
      ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))
  let aw1 : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6895a := evm_run rd6891 with [push1 ⟨64⟩, dup1]
  have rd6895 := RD.mload
    (Cₘ aw1 - Cₘ aw) fp0 aw1 rd6895a (by decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, aw1])
    (by rfl)
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6899 := rd6895.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd6918a := evm_run rd6899 with [push1 ⟨229⟩, shl, dup2]
  let mem0 : ByteArray := (UInt256.toByteArray uniswapErrorStringSelector).write 0 mem fp0.toNat 32
  let aw2 : UInt256 := UInt256.ofNat (MachineState.M aw1.toNat fp0.toNat 32)
  have rd6918a' := RD.mstore
    (Cₘ aw2 - Cₘ aw1) mem0 aw2 rd6918a (by decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, aw1, aw2])
    (by simp [mem0, uniswapErrorStringSelector, solcErrorStringSelector])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6918b0 := evm_run rd6918a' with [push1 ⟨32⟩, push1 ⟨4⟩, dup3, add]
  let off1 : UInt256 := fp0 + ⟨4⟩
  let mem1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem0 off1.toNat 32
  let aw3 : UInt256 := UInt256.ofNat (MachineState.M aw2.toNat off1.toNat 32)
  have rd6918b := RD.mstore
    (Cₘ aw3 - Cₘ aw2) mem1 aw3 rd6918b0 (by decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, aw2, aw3, off1])
    (by simp [mem1, off1])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6918c0 := evm_run rd6918b with [push1 ⟨21⟩, push1 ⟨36⟩, dup3, add]
  let off2 : UInt256 := fp0 + ⟨36⟩
  let mem2 : ByteArray := (UInt256.toByteArray (⟨21⟩ : UInt256)).write 0 mem1 off2.toNat 32
  let aw4 : UInt256 := UInt256.ofNat (MachineState.M aw3.toNat off2.toNat 32)
  have rd6918 := RD.mstore
    (Cₘ aw4 - Cₘ aw3) mem2 aw4 rd6918c0 (by decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, aw3, aw4, off2])
    (by simp [mem2, off2])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6940 := rd6918.pushConst
    (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256)
    (width := 21) (op := .PUSH21) (by decide) (by decide) (by evm_ov)
  have rd6944 := evm_run rd6940 with [push1 ⟨88⟩, shl, push1 ⟨68⟩, dup3, add]
  let off3 : UInt256 := fp0 + ⟨68⟩
  let mem3 : ByteArray :=
    (UInt256.toByteArray uniswapSafeMathSubUnderflowStringWord).write 0 mem2 off3.toNat 32
  let aw5 : UInt256 := UInt256.ofNat (MachineState.M aw4.toNat off3.toNat 32)
  have rd6944' := RD.mstore
    (Cₘ aw5 - Cₘ aw4) mem3 aw5 rd6944 (by decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, aw4, aw5, off3])
    (by simp [mem3, off3, uniswapSafeMathSubUnderflowStringWord])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6945 := evm_run rd6944' with [swap1]
  let fp1 : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ mem3.size then
      ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem3.readWithPadding 64 32))
  let aw6 : UInt256 := UInt256.ofNat (MachineState.M aw5.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6946 := RD.mload
    (Cₘ aw6 - Cₘ aw5) fp1 aw6 rd6945 (by decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, aw5, aw6])
    (by rfl)
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6954 := evm_run rd6946 with [
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat
      (MachineState.M aw6.toNat fp1.toNat ((⟨100⟩ : UInt256) + fp0.sub fp1).toNat)) -
      Cₘ aw6)
    rd6954 (by decide)
    (by
      simp [M])
    (by simp only [List.length_cons, List.length_nil]; omega)


end UniswapV2Pair
