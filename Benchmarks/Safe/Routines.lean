import Benchmarks.Safe.Dispatch

/-!
# Safe shared routine lemmas

Contract-wide `RD` and refinement combinators for per-function non-payable guards and direct
selector dispatch. These mirror generic library patterns while accounting for Safe's payable
runtime prefix and Shanghai `PUSH0; PUSH0; REVERT` guard stubs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: `Reasoning.Reach` has LOG1/LOG3/LOG4 but not LOG2.
def stLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem log2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG2 +
          (GasConstants.Glog + GasConstants.Glogdata * b.toNat +
            2 * GasConstants.Glogtopic) then
        .error .OutOfGass
      else .ok (stLog2 s a b c d t, .none) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog2]

theorem RD.log2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat +
        2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
      hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := log2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost +
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog2]; exact hcode
      · simp only [stLog2]; rw [hpc]
      · simp only [stLog2]
      · simp only [stLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog2]; exact hmem
      · simp only [stLog2]; rw [haw, hawout]
      · simp only [stLog2]; exact hrdata
      · simp only [stLog2]; exact hacc
      · simp only [stLog2]; exact hee
      · simp only [stLog2]; exact hworld

theorem safeStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot (.int uint256Int)) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc, uint256Int] using storageLocLoad_uint256 evm slot

theorem safeStorageLocStore_fullAddr (evm : EVM.State) (slot addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    storageLocStore evm (fullAddrLoc slot)
        (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot addr) := by
  unfold storageLocStore storageLocWriteWord fullAddrLoc loc
  simp only [valueToWord_address_ofNat_canonical addr hcanon, bind, Option.bind]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof addr).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = addr.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem safeAddressEq_one {I : ExecutionEnv} (hauth : I.source = I.codeOwner) :
    UInt256.eq (UInt256.ofNat I.codeOwner.val) (UInt256.ofNat I.source.val) = ⟨1⟩ := by
  rw [← hauth]
  exact uInt256_eq_self _

theorem safeAddressEq_zero {I : ExecutionEnv} (hauth : I.source ≠ I.codeOwner) :
    UInt256.eq (UInt256.ofNat I.codeOwner.val) (UInt256.ofNat I.source.val) = ⟨0⟩ := by
  apply uInt256_eq_zero_of_ne
  intro hone
  have hword := uInt256_eq_one_eq hone
  apply hauth
  apply Fin.ext
  have hnat := congrArg UInt256.toNat hword
  have hsrc :
      (UInt256.ofNat I.source.val).toNat = I.source.val := by
    exact ulit_toNat' I.source.val (lt_trans I.source.isLt (by native_decide))
  have howner :
      (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
    exact ulit_toNat' I.codeOwner.val (lt_trans I.codeOwner.isLt (by native_decide))
  rw [howner, hsrc] at hnat
  exact hnat.symm

theorem safeAuthorized_true {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hauth : I.source = I.codeOwner) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (eqE sender this) = .ok (.bool true) := by
  have hbeq :
      (Value.address I.source == Value.address I.codeOwner) = true := by
    simp [BEq.beq, hauth]
  unfold eqE
  simp [evalExpr?, sender, this, envValue, evalBinaryOp?, initState, EvalResult.bind,
    bind, pure, hbeq]

theorem safeAuthorized_false {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hauth : I.source ≠ I.codeOwner) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (eqE sender this) = .ok (.bool false) := by
  have hbeq :
      (Value.address I.source == Value.address I.codeOwner) = false := by
    simp [BEq.beq, hauth]
  unfold eqE
  simp [evalExpr?, sender, this, envValue, evalBinaryOp?, initState, EvalResult.bind,
    bind, pure, hbeq]

-- LIBRARY CANDIDATE: per-function analogue of `solcGuardCallvalueZero`.
theorem safeGuardPeelOk {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {entry gt sel : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 entry [sel] mem aw rdata acc k C)
    (hcv : ee.weiValue = ⟨0⟩)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.CALLVALUE, .none))
    (hd2 : decode code (entry + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hd3 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hd4 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (gt, 2)))
    (hd7 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3) =
      some (.JUMPI, .none))
    (hgtjd : (D_J code 0).contains gt = true)
    (hdgt : decode code gt = some (.JUMPDEST, .none))
    (hdpop : decode code (gt + ⟨1⟩) = some (.POP, .none)) :
    ∃ k' C', RD code ee g s0 (gt + ⟨1⟩ + ⟨1⟩) [sel] mem aw rdata acc k' C' := by
  have hcond : UInt256.isZero ee.weiValue ≠ ⟨0⟩ := by rw [hcv]; decide
  exact ⟨_, _, h.jumpdest hd0 (by simp)
    |>.callvalue hd1 (by simp)
    |>.dup1 hd2 (by simp)
    |>.iszero hd3 (by simp)
    |>.pushConst gt (op := .PUSH2) (width := 2) (by simp) hd4 (by simp)
    |>.jumpiT hd7 hcond hgtjd (by simp)
    |>.jumpdest hdgt (by simp)
    |>.pop hdpop (by simp)⟩

-- LIBRARY CANDIDATE: per-function callvalue guard to Shanghai `revert(0,0)`.
theorem safeGuardPeelRev {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {entry gt sel : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 entry [sel] mem aw rdata acc k C)
    (hcv : ee.weiValue ≠ ⟨0⟩)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.CALLVALUE, .none))
    (hd2 : decode code (entry + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hd3 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hd4 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (gt, 2)))
    (hd7 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3) =
      some (.JUMPI, .none))
    (hd8 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩) =
      some (.PUSH0, .none))
    (hd9 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ +
      ⟨1⟩) = some (.PUSH0, .none))
    (hd10 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none)) :
    RDrev code g s0 := by
  have hcond : UInt256.isZero ee.weiValue = ⟨0⟩ := isZero_eq_zero_of_ne hcv
  have hfall := h.jumpdest hd0 (by simp)
    |>.callvalue hd1 (by simp)
    |>.dup1 hd2 (by simp)
    |>.iszero hd3 (by simp)
    |>.pushConst gt (op := .PUSH2) (width := 2) (by simp) hd4 (by simp)
    |>.jumpiNT hd7 hcond (by simp)
  exact RD.revertStub hfall hd8 hd9 hd10 (by simp)

set_option maxHeartbeats 1000000 in
theorem safeErrorStringRevert6898 {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {word : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD safeBytecode ee g s0 ⟨6898⟩ (word :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 5 ≤ 1024) :
    RDrev safeBytecode g s0 := by
  have rd6910pre := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)
    |>.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨229⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd6911 := rd6910pre.mstore 6 (solcErrorStringMem0 mem)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6917pre := rd6911
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  have rd6918 := rd6917pre.mstore 3 (solcErrorStringMem1 mem)
    (UInt256.ofNat 6) (by native_decide) mem_cost
    (by rw [show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 by decide]; rfl)
    (by native_decide) (by evm_ov)
  have rd6924pre := rd6918
    |>.push1 ⟨5⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨36⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  have rd6925 := rd6924pre.mstore 3 (solcErrorStringMem2 ⟨5⟩ mem)
    (UInt256.ofNat 7) (by native_decide) mem_cost
    (by rw [show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 by decide]; rfl)
    (by native_decide) (by evm_ov)
  have rd6930pre := rd6925
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push1 ⟨68⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  have rd6931 := rd6930pre.mstore 3 (solcErrorStringMem3 ⟨5⟩ word mem)
    (UInt256.ofNat 8) (by native_decide) mem_cost
    (by rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 by decide]; rfl)
    (by native_decide) (by evm_ov)
  have rd6934 := rd6931
    |>.push1 ⟨100⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  exact rd6934.rev 0 (by native_decide) mem_cost (by evm_ov)

-- Safe's optimized runtime stores one return word at the free pointer, then jumps to a common
-- `RETURN` block at pc 771.
theorem RD.safeReturnWordFromMem974 {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {val : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD safeBytecode ee g s0 ⟨974⟩ (val :: R) solcFreePtrMem
      (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    RDret safeBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push2 ⟨771⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (solcReturnMem_mload64 val) (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray val) (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨32⟩ from by decide]
        exact solcReturnMem_read128 val)
      (by evm_ov)]

theorem RD.safeReturnWordFromScratchMem974 {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {val : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD safeBytecode ee g s0 ⟨974⟩ (val :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 3 ≤ 1024) :
    RDret safeBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcScratchReturnMem mem val) (UInt256.ofNat 5) (by native_decide)
      mem_cost (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push2 ⟨771⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (solcScratchReturnMem_mload64 val hmem hread64) (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray val) (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨32⟩ from by decide]
        exact solcScratchReturnMem_read128 val hmem)
      (by evm_ov)]

-- Safe's optimized bool return block at pc 759 normalizes a word with `iszero(iszero(_))`.
theorem RD.safeReturnBoolFromScratchMem759 {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {val : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD safeBytecode ee g s0 ⟨759⟩ (val :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 3 ≤ 1024) :
    RDret safeBytecode g s0 acc
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) := by
  exact evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcScratchReturnMem mem (UInt256.isZero (UInt256.isZero val)))
      (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (solcScratchReturnMem_mload64 (UInt256.isZero (UInt256.isZero val))
        hmem hread64) (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val)))
      (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨32⟩ from by decide]
        exact solcScratchReturnMem_read128 (UInt256.isZero (UInt256.isZero val)) hmem)
      (by evm_ov)]

/-- Combined nested-mapping getter for Safe public mapping getters. -/
theorem safeNestedMappingGetter {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {pc baseSlot owner spender ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot baseSlot owner) spender) :: ret :: R)
      (solcNestedMappingHashMem baseSlot owner spender) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hinner⟩ := RD.solcNestedMappingInnerHash h hwf hov
  obtain ⟨_, _, houter⟩ := RD.solcNestedMappingOuterHash hinner hwf hov
  exact RD.solcNestedMappingLoadAndJump houter hwf hret (by omega)

theorem safeReEquivExecGen {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {o : ByteArray} {callargs cs retVal}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {evm'' : EVM.State}
    (hcode : I.code = safeBytecode)
    (h : RDret safeBytecode g (initState cA gh bl σ_evm σ₀ g A I) acc o)
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
              (.returned cs evm'' retVal))
    (hCreated : acc.1 = evm''.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evm''.accountMap)
    (henc : returnEquiv o retVal t.returnType) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨s, hX, hsacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    have hbody' :
        ExecTransitionBody cfg contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
          callargs t.body (.returned cs evm'' retVal) := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    refine runtimeEquivalenceFor.execution rfl
      (solmExec.intro hsel rfl hdec rfl hbody') ?_
    rw [hxi]
    have hcreated : s.createdAccounts = evm''.createdAccounts :=
      (congrArg Prod.fst hsacc).trans hCreated
    have haccounts : accountMapEquiv s.accountMap evm''.accountMap := by
      change accountMapEquiv (s.createdAccounts, s.accountMap).2 evm''.accountMap
      rw [congrArg Prod.snd hsacc]; exact hAccounts
    exact execResultsEquiv.success rfl rfl hcreated haccounts (.abi henc)

theorem safeReEquivExecTransport {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {o : ByteArray} {callargs cs rvSolm rvEvm}
    (hcode : I.code = safeBytecode)
    (h : RDret safeBytecode g (initState cA gh bl σ_evm σ₀ g A I) (cA, σ_evm) o)
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
              (.returned cs (initState cA gh bl σ_solm σ₀ g A I) rvSolm))
    (hval : rvSolm = rvEvm)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (henc : returnEquiv o rvEvm t.returnType) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  subst hval
  exact safeReEquivExecGen hcode h hsel hdec hbody (by simp [initState])
    (by simpa [initState] using hAccounts) henc

theorem safeReEquivExecRev {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256} {callargs}
    (hcode : I.code = safeBytecode)
    (h : RDrev safeBytecode g (initState cA gh bl σ_evm σ₀ g A I))
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body .reverted) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨g', o, hrev⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_revert_of_X (g := g.toUInt256) (by
      rw [← hcode] at hrev
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hrev)
    have hbody' :
        ExecTransitionBody cfg contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
          callargs t.body .reverted := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    refine runtimeEquivalenceFor.execution rfl
      (solmExec.intro hsel rfl hdec rfl hbody') ?_
    rw [hxi]; exact execResultsEquiv.revert rfl rfl

theorem safeReEquivDecodeFailed {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode)
    (h : RDrev safeBytecode g (initState cA gh bl σ_evm σ₀ g A I))
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = none) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨g', o, hrev⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_revert_of_X (g := g.toUInt256) (by
      rw [← hcode] at hrev
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hrev)
    exact runtimeEquivalenceFor.decodingFailed hsel rfl hdec hxi

theorem safeNonpayableRevert {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode)
    (h : RDrev safeBytecode g (initState cA gh bl σ_evm σ₀ g A I))
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hbodyRev : ∀ callargs,
      decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
        (transitionSignature t).paramTypes I.calldata = some callargs →
      ExecTransitionBody cfg contract (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
        .reverted) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  by_cases hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = none
  · exact safeReEquivDecodeFailed hcode h hsel hdec
  · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
    exact safeReEquivExecRev hcode h hsel hca (hbodyRev callargs hca)

end Benchmarks.Safe
