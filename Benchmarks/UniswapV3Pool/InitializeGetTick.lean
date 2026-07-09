import Benchmarks.UniswapV3Pool.InitializeBase

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev getTickRatioMask : UInt256 :=
  ⟨6277101735386680763835789423207666416102355444459739545600⟩

abbrev getTickRatioWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.shiftLeft (initializeArgWord ee) ⟨32⟩) getTickRatioMask

abbrev getTickMsbThreshold7 : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩

abbrev getTickMsbF7Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft (UInt256.gt (getTickRatioWord ee) getTickMsbThreshold7) ⟨7⟩

abbrev getTickRAfterMsb7Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickRatioWord ee) (getTickMsbF7Word ee)

abbrev getTickMsbThreshold6 : UInt256 := ⟨18446744073709551615⟩

abbrev getTickMsbF6Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft (UInt256.gt (getTickRAfterMsb7Word ee) getTickMsbThreshold6) ⟨6⟩

abbrev getTickRAfterMsb6Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickRAfterMsb7Word ee) (getTickMsbF6Word ee)

abbrev getTickMsbThreshold5 : UInt256 := ⟨4294967295⟩

abbrev getTickMsbF5Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft (UInt256.gt (getTickRAfterMsb6Word ee) getTickMsbThreshold5) ⟨5⟩

abbrev getTickRAfterMsb5Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickRAfterMsb6Word ee) (getTickMsbF5Word ee)

abbrev getTickMsbThreshold4 : UInt256 := ⟨65535⟩

abbrev getTickMsbF4Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft (UInt256.gt (getTickRAfterMsb5Word ee) getTickMsbThreshold4) ⟨4⟩

abbrev getTickRAfterMsb4Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickRAfterMsb5Word ee) (getTickMsbF4Word ee)

abbrev getTickMsbThreshold3 : UInt256 := ⟨255⟩

abbrev getTickMsbF3Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft (UInt256.gt (getTickRAfterMsb4Word ee) getTickMsbThreshold3) ⟨3⟩

abbrev getTickRAfterMsb3Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickRAfterMsb4Word ee) (getTickMsbF3Word ee)

abbrev getTickMsbThreshold2 : UInt256 := ⟨15⟩

abbrev getTickMsbF2Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft (UInt256.gt (getTickRAfterMsb3Word ee) getTickMsbThreshold2) ⟨2⟩

abbrev getTickRAfterMsb2Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickRAfterMsb3Word ee) (getTickMsbF2Word ee)

abbrev getTickMsbThreshold1 : UInt256 := ⟨3⟩

abbrev getTickMsbF1Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft (UInt256.gt (getTickRAfterMsb2Word ee) getTickMsbThreshold1) ⟨1⟩

abbrev getTickRAfterMsb1Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickRAfterMsb2Word ee) (getTickMsbF1Word ee)

abbrev getTickMsbF0Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.gt (getTickRAfterMsb1Word ee) ⟨1⟩

abbrev getTickMsbF67Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickMsbF6Word ee) (getTickMsbF7Word ee)

abbrev getTickMsbF567Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickMsbF5Word ee) (getTickMsbF67Word ee)

abbrev getTickMsbF4567Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickMsbF4Word ee) (getTickMsbF567Word ee)

abbrev getTickMsbF34567Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickMsbF4567Word ee) (getTickMsbF3Word ee)

abbrev getTickMsbF234567Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickMsbF2Word ee) (getTickMsbF34567Word ee)

abbrev getTickMsbF1234567Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickMsbF234567Word ee) (getTickMsbF1Word ee)

abbrev getTickMsbWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickMsbF1234567Word ee) (getTickMsbF0Word ee)

abbrev getTickRNormalizedHighWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickRatioWord ee) (UInt256.sub (getTickMsbWord ee) ⟨127⟩)

abbrev getTickRNormalizedLowWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft (getTickRatioWord ee) (UInt256.sub ⟨127⟩ (getTickMsbWord ee))

abbrev getTickRNormalizedWord (ee : ExecutionEnv) : UInt256 :=
  if UInt256.lt (getTickMsbWord ee) ⟨128⟩ = ⟨0⟩ then
    getTickRNormalizedHighWord ee
  else
    getTickRNormalizedLowWord ee

abbrev getTickLogRSquared63Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickRNormalizedWord ee) (getTickRNormalizedWord ee)

abbrev getTickLogRShifted63Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared63Word ee) ⟨127⟩

abbrev getTickLogF63Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared63Word ee) ⟨255⟩

abbrev getTickLogRAfter63Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted63Word ee) (getTickLogF63Word ee)

abbrev getTickLogRSquared62Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter63Word ee) (getTickLogRAfter63Word ee)

abbrev getTickLogRShifted62Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared62Word ee) ⟨127⟩

abbrev getTickLogF62Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared62Word ee) ⟨255⟩

abbrev getTickLogRAfter62Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted62Word ee) (getTickLogF62Word ee)

private theorem uniswapV3PoolInitializePatchPreservesJumpDest14263 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨14263⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest14273 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨14273⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched14263 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨14263⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest14263

theorem uniswapV3PoolJumpDestPatched14273 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨14273⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest14273

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioMsbStep7 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14102⟩
      (⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14150⟩
      (getTickRAfterMsb7Word ee :: getTickMsbF7Word ee :: getTickRatioWord ee ::
        ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14102 : decode code ⟨14102⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14103 : decode code ⟨14103⟩ =
      some (.Push .PUSH24, some (getTickRatioMask, 24)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14128 : decode code ⟨14128⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14130 : decode code ⟨14130⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14131 : decode code ⟨14131⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14132 : decode code ⟨14132⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14133 : decode code ⟨14133⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14134 : decode code ⟨14134⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14136 : decode code ⟨14136⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14138 : decode code ⟨14138⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14140 : decode code ⟨14140⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14141 : decode code ⟨14141⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14142 : decode code ⟨14142⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14143 : decode code ⟨14143⟩ = some (.GT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14144 : decode code ⟨14144⟩ = some (.Push .PUSH1, some (⟨7⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14146 : decode code ⟨14146⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14147 : decode code ⟨14147⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14148 : decode code ⟨14148⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14149 : decode code ⟨14149⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14103 := by
    simpa using h.jumpdest hd14102 (by
      simp only [List.length_cons]
      omega)
  have rd14128 := by
    simpa using rd14103.pushConst getTickRatioMask
      (by native_decide : Operation.POp.PUSH24 ≠ .PUSH0) hd14103 (by
        simp only [List.length_cons]
        omega)
  have rd14130 := by
    simpa using rd14128.push1 ⟨32⟩ hd14128 (by
      simp only [List.length_cons]
      omega)
  have rd14131 := by
    simpa using rd14130.dup4 hd14130 (by
      simp only [List.length_cons]
      omega)
  have rd14132 := by
    simpa using rd14131.swap1 hd14131 (by
      simp only [List.length_cons]
      omega)
  have rd14133 := by
    simpa using rd14132.shl hd14132 (by
      simp only [List.length_cons]
      omega)
  have rd14134 := by
    simpa [getTickRatioWord] using rd14133.and hd14133 (by
      simp only [List.length_cons]
      omega)
  have rd14136 := by
    simpa using rd14134.push1 ⟨1⟩ hd14134 (by
      simp only [List.length_cons]
      omega)
  have rd14138 := by
    simpa using rd14136.push1 ⟨1⟩ hd14136 (by
      simp only [List.length_cons]
      omega)
  have rd14140 := by
    simpa using rd14138.push1 ⟨128⟩ hd14138 (by
      simp only [List.length_cons]
      omega)
  have rd14141 := by
    simpa using rd14140.shl hd14140 (by
      simp only [List.length_cons]
      omega)
  have rd14142 := by
    simpa [getTickMsbThreshold7] using rd14141.sub hd14141 (by
      simp only [List.length_cons]
      omega)
  have rd14143 := by
    simpa using rd14142.dup2 hd14142 (by
      simp only [List.length_cons]
      omega)
  have rd14144 := by
    simpa using rd14143.gt hd14143 (by
      simp only [List.length_cons]
      omega)
  have rd14146 := by
    simpa using rd14144.push1 ⟨7⟩ hd14144 (by
      simp only [List.length_cons]
      omega)
  have rd14147 := by
    simpa [getTickMsbF7Word] using rd14146.shl hd14146 (by
      simp only [List.length_cons]
      omega)
  have rd14148 := by
    simpa using rd14147.dup2 hd14147 (by
      simp only [List.length_cons]
      omega)
  have rd14149 := by
    simpa using rd14148.dup2 hd14148 (by
      simp only [List.length_cons]
      omega)
  have rd14150 := by
    simpa [getTickRAfterMsb7Word] using rd14149.shr hd14149 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14150⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioMsbStep6 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14150⟩
      (getTickRAfterMsb7Word ee :: getTickMsbF7Word ee :: getTickRatioWord ee ::
        ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14167⟩
      (getTickRAfterMsb6Word ee :: getTickMsbF6Word ee :: getTickMsbF7Word ee ::
        getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
          initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14150 : decode code ⟨14150⟩ =
      some (.Push .PUSH8, some (getTickMsbThreshold6, 8)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14159 : decode code ⟨14159⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14160 : decode code ⟨14160⟩ = some (.GT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14161 : decode code ⟨14161⟩ = some (.Push .PUSH1, some (⟨6⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14163 : decode code ⟨14163⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14164 : decode code ⟨14164⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14165 : decode code ⟨14165⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14166 : decode code ⟨14166⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14159 := by
    simpa using h.pushConst getTickMsbThreshold6
      (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0) hd14150 (by
        simp only [List.length_cons]
        omega)
  have rd14160 := by
    simpa using rd14159.dup2 hd14159 (by
      simp only [List.length_cons]
      omega)
  have rd14161 := by
    simpa using rd14160.gt hd14160 (by
      simp only [List.length_cons]
      omega)
  have rd14163 := by
    simpa using rd14161.push1 ⟨6⟩ hd14161 (by
      simp only [List.length_cons]
      omega)
  have rd14164 := by
    simpa [getTickMsbF6Word] using rd14163.shl hd14163 (by
      simp only [List.length_cons]
      omega)
  have rd14165 := by
    simpa using rd14164.swap1 hd14164 (by
      simp only [List.length_cons]
      omega)
  have rd14166 := by
    simpa using rd14165.dup2 hd14165 (by
      simp only [List.length_cons]
      omega)
  have rd14167 := by
    simpa [getTickRAfterMsb6Word] using rd14166.shr hd14166 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14167⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioMsbStep5 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14167⟩
      (getTickRAfterMsb6Word ee :: getTickMsbF6Word ee :: getTickMsbF7Word ee ::
        getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
          initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14180⟩
      (getTickRAfterMsb5Word ee :: getTickMsbF5Word ee :: getTickMsbF6Word ee ::
        getTickMsbF7Word ee :: getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee ::
          ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14167 : decode code ⟨14167⟩ =
      some (.Push .PUSH4, some (getTickMsbThreshold5, 4)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14172 : decode code ⟨14172⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14173 : decode code ⟨14173⟩ = some (.GT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14174 : decode code ⟨14174⟩ = some (.Push .PUSH1, some (⟨5⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14176 : decode code ⟨14176⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14177 : decode code ⟨14177⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14178 : decode code ⟨14178⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14179 : decode code ⟨14179⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14172 := by
    simpa using h.pushConst getTickMsbThreshold5
      (by native_decide : Operation.POp.PUSH4 ≠ .PUSH0) hd14167 (by
        simp only [List.length_cons]
        omega)
  have rd14173 := by
    simpa using rd14172.dup2 hd14172 (by
      simp only [List.length_cons]
      omega)
  have rd14174 := by
    simpa using rd14173.gt hd14173 (by
      simp only [List.length_cons]
      omega)
  have rd14176 := by
    simpa using rd14174.push1 ⟨5⟩ hd14174 (by
      simp only [List.length_cons]
      omega)
  have rd14177 := by
    simpa [getTickMsbF5Word] using rd14176.shl hd14176 (by
      simp only [List.length_cons]
      omega)
  have rd14178 := by
    simpa using rd14177.swap1 hd14177 (by
      simp only [List.length_cons]
      omega)
  have rd14179 := by
    simpa using rd14178.dup2 hd14178 (by
      simp only [List.length_cons]
      omega)
  have rd14180 := by
    simpa [getTickRAfterMsb5Word] using rd14179.shr hd14179 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14180⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioMsbStep4 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14180⟩
      (getTickRAfterMsb5Word ee :: getTickMsbF5Word ee :: getTickMsbF6Word ee ::
        getTickMsbF7Word ee :: getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee ::
          ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14191⟩
      (getTickRAfterMsb4Word ee :: getTickMsbF4Word ee :: getTickMsbF5Word ee ::
        getTickMsbF6Word ee :: getTickMsbF7Word ee :: getTickRatioWord ee ::
          ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee ::
            ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14180 : decode code ⟨14180⟩ =
      some (.Push .PUSH2, some (getTickMsbThreshold4, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14183 : decode code ⟨14183⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14184 : decode code ⟨14184⟩ = some (.GT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14185 : decode code ⟨14185⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14187 : decode code ⟨14187⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14188 : decode code ⟨14188⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14189 : decode code ⟨14189⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14190 : decode code ⟨14190⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14183 := by
    simpa using h.push2 getTickMsbThreshold4 hd14180 (by
      simp only [List.length_cons]
      omega)
  have rd14184 := by
    simpa using rd14183.dup2 hd14183 (by
      simp only [List.length_cons]
      omega)
  have rd14185 := by
    simpa using rd14184.gt hd14184 (by
      simp only [List.length_cons]
      omega)
  have rd14187 := by
    simpa using rd14185.push1 ⟨4⟩ hd14185 (by
      simp only [List.length_cons]
      omega)
  have rd14188 := by
    simpa [getTickMsbF4Word] using rd14187.shl hd14187 (by
      simp only [List.length_cons]
      omega)
  have rd14189 := by
    simpa using rd14188.swap1 hd14188 (by
      simp only [List.length_cons]
      omega)
  have rd14190 := by
    simpa using rd14189.dup2 hd14189 (by
      simp only [List.length_cons]
      omega)
  have rd14191 := by
    simpa [getTickRAfterMsb4Word] using rd14190.shr hd14190 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14191⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioMsbStep3 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14191⟩
      (getTickRAfterMsb4Word ee :: getTickMsbF4Word ee :: getTickMsbF5Word ee ::
        getTickMsbF6Word ee :: getTickMsbF7Word ee :: getTickRatioWord ee ::
          ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee ::
            ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14203⟩
      (getTickRAfterMsb3Word ee :: ⟨3⟩ :: getTickMsbF3Word ee :: getTickMsbF4Word ee ::
        getTickMsbF5Word ee :: getTickMsbF6Word ee :: getTickMsbF7Word ee ::
          getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
            initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14191 : decode code ⟨14191⟩ =
      some (.Push .PUSH1, some (getTickMsbThreshold3, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14193 : decode code ⟨14193⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14194 : decode code ⟨14194⟩ = some (.GT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14195 : decode code ⟨14195⟩ = some (.Push .PUSH1, some (⟨3⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14197 : decode code ⟨14197⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14198 : decode code ⟨14198⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14199 : decode code ⟨14199⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14200 : decode code ⟨14200⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14201 : decode code ⟨14201⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14202 : decode code ⟨14202⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14193 := by
    simpa using h.push1 getTickMsbThreshold3 hd14191 (by
      simp only [List.length_cons]
      omega)
  have rd14194 := by
    simpa using rd14193.dup2 hd14193 (by
      simp only [List.length_cons]
      omega)
  have rd14195 := by
    simpa using rd14194.gt hd14194 (by
      simp only [List.length_cons]
      omega)
  have rd14197 := by
    simpa using rd14195.push1 ⟨3⟩ hd14195 (by
      simp only [List.length_cons]
      omega)
  have rd14198 := by
    simpa using rd14197.swap1 hd14197 (by
      simp only [List.length_cons]
      omega)
  have rd14199 := by
    simpa using rd14198.dup2 hd14198 (by
      simp only [List.length_cons]
      omega)
  have rd14200 := by
    simpa [getTickMsbF3Word] using rd14199.shl hd14199 (by
      simp only [List.length_cons]
      omega)
  have rd14201 := by
    simpa using rd14200.swap2 hd14200 (by
      simp only [List.length_cons]
      omega)
  have rd14202 := by
    simpa using rd14201.dup3 hd14201 (by
      simp only [List.length_cons]
      omega)
  have rd14203 := by
    simpa [getTickRAfterMsb3Word] using rd14202.shr hd14202 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14203⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioMsbStep2 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14203⟩
      (getTickRAfterMsb3Word ee :: ⟨3⟩ :: getTickMsbF3Word ee :: getTickMsbF4Word ee ::
        getTickMsbF5Word ee :: getTickMsbF6Word ee :: getTickMsbF7Word ee ::
          getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
            initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14213⟩
      (getTickRAfterMsb2Word ee :: getTickMsbF2Word ee :: ⟨3⟩ ::
        getTickMsbF3Word ee :: getTickMsbF4Word ee :: getTickMsbF5Word ee ::
          getTickMsbF6Word ee :: getTickMsbF7Word ee :: getTickRatioWord ee ::
            ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee ::
              ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14203 : decode code ⟨14203⟩ =
      some (.Push .PUSH1, some (getTickMsbThreshold2, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14205 : decode code ⟨14205⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14206 : decode code ⟨14206⟩ = some (.GT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14207 : decode code ⟨14207⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14209 : decode code ⟨14209⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14210 : decode code ⟨14210⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14211 : decode code ⟨14211⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14212 : decode code ⟨14212⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14205 := by
    simpa using h.push1 getTickMsbThreshold2 hd14203 (by
      simp only [List.length_cons]
      omega)
  have rd14206 := by
    simpa using rd14205.dup2 hd14205 (by
      simp only [List.length_cons]
      omega)
  have rd14207 := by
    simpa using rd14206.gt hd14206 (by
      simp only [List.length_cons]
      omega)
  have rd14209 := by
    simpa using rd14207.push1 ⟨2⟩ hd14207 (by
      simp only [List.length_cons]
      omega)
  have rd14210 := by
    simpa [getTickMsbF2Word] using rd14209.shl hd14209 (by
      simp only [List.length_cons]
      omega)
  have rd14211 := by
    simpa using rd14210.swap1 hd14210 (by
      simp only [List.length_cons]
      omega)
  have rd14212 := by
    simpa using rd14211.dup2 hd14211 (by
      simp only [List.length_cons]
      omega)
  have rd14213 := by
    simpa [getTickRAfterMsb2Word] using rd14212.shr hd14212 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14213⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioMsbStep1 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14213⟩
      (getTickRAfterMsb2Word ee :: getTickMsbF2Word ee :: ⟨3⟩ ::
        getTickMsbF3Word ee :: getTickMsbF4Word ee :: getTickMsbF5Word ee ::
          getTickMsbF6Word ee :: getTickMsbF7Word ee :: getTickRatioWord ee ::
            ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee ::
              ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14224⟩
      (getTickRAfterMsb1Word ee :: ⟨1⟩ :: getTickMsbF2Word ee ::
        getTickMsbF1Word ee :: getTickMsbF3Word ee :: getTickMsbF4Word ee ::
          getTickMsbF5Word ee :: getTickMsbF6Word ee :: getTickMsbF7Word ee ::
            getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
              initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14213 : decode code ⟨14213⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14214 : decode code ⟨14214⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14215 : decode code ⟨14215⟩ = some (.GT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14216 : decode code ⟨14216⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14218 : decode code ⟨14218⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14219 : decode code ⟨14219⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14220 : decode code ⟨14220⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14221 : decode code ⟨14221⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14222 : decode code ⟨14222⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14223 : decode code ⟨14223⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14214 := by
    simpa using h.swap2 hd14213 (by
      simp only [List.length_cons]
      omega)
  have rd14215 := by
    simpa using rd14214.dup3 hd14214 (by
      simp only [List.length_cons]
      omega)
  have rd14216 := by
    simpa using rd14215.gt hd14215 (by
      simp only [List.length_cons]
      omega)
  have rd14218 := by
    simpa using rd14216.push1 ⟨1⟩ hd14216 (by
      simp only [List.length_cons]
      omega)
  have rd14219 := by
    simpa using rd14218.swap1 hd14218 (by
      simp only [List.length_cons]
      omega)
  have rd14220 := by
    simpa using rd14219.dup2 hd14219 (by
      simp only [List.length_cons]
      omega)
  have rd14221 := by
    simpa [getTickMsbF1Word] using rd14220.shl hd14220 (by
      simp only [List.length_cons]
      omega)
  have rd14222 := by
    simpa using rd14221.swap3 hd14221 (by
      simp only [List.length_cons]
      omega)
  have rd14223 := by
    simpa using rd14222.dup4 hd14222 (by
      simp only [List.length_cons]
      omega)
  have rd14224 := by
    simpa [getTickRAfterMsb1Word] using rd14223.shr hd14223 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14224⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioMsbCombine {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14224⟩
      (getTickRAfterMsb1Word ee :: ⟨1⟩ :: getTickMsbF2Word ee ::
        getTickMsbF1Word ee :: getTickMsbF3Word ee :: getTickMsbF4Word ee ::
          getTickMsbF5Word ee :: getTickMsbF6Word ee :: getTickMsbF7Word ee ::
            getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
              initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14242⟩
      (getTickMsbWord ee :: getTickRAfterMsb1Word ee :: getTickRatioWord ee :: ⟨0⟩ ::
        initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14224 : decode code ⟨14224⟩ = some (.SWAP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14225 : decode code ⟨14225⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14226 : decode code ⟨14226⟩ = some (.DUP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14227 : decode code ⟨14227⟩ = some (.GT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14228 : decode code ⟨14228⟩ = some (.SWAP7, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14229 : decode code ⟨14229⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14230 : decode code ⟨14230⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14231 : decode code ⟨14231⟩ = some (.SWAP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14232 : decode code ⟨14232⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14233 : decode code ⟨14233⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14234 : decode code ⟨14234⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14235 : decode code ⟨14235⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14236 : decode code ⟨14236⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14237 : decode code ⟨14237⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14238 : decode code ⟨14238⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14239 : decode code ⟨14239⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14240 : decode code ⟨14240⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14241 : decode code ⟨14241⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14225 := by
    simpa using h.swap8 hd14224 (by
      simp only [List.length_cons]
      omega)
  have rd14226 := by
    simpa using rd14225.swap1 hd14225 (by
      simp only [List.length_cons]
      omega)
  have rd14227 := by
    simpa using rd14226.dup9 hd14226 (by
      simp only [List.length_cons]
      omega)
  have rd14228 := by
    simpa [getTickMsbF0Word] using rd14227.gt hd14227 (by
      simp only [List.length_cons]
      omega)
  have rd14229 := by
    simpa using rd14228.swap7 hd14228 (by
      simp only [List.length_cons]
      omega)
  have rd14230 := by
    simpa [getTickMsbF67Word] using rd14229.lor hd14229 (by
      simp only [List.length_cons]
      omega)
  have rd14231 := by
    simpa using rd14230.swap1 hd14230 (by
      simp only [List.length_cons]
      omega)
  have rd14232 := by
    simpa using rd14231.swap5 hd14231 (by
      simp only [List.length_cons]
      omega)
  have rd14233 := by
    simpa [getTickMsbF567Word] using rd14232.lor hd14232 (by
      simp only [List.length_cons]
      omega)
  have rd14234 := by
    simpa using rd14233.swap1 hd14233 (by
      simp only [List.length_cons]
      omega)
  have rd14235 := by
    simpa using rd14234.swap3 hd14234 (by
      simp only [List.length_cons]
      omega)
  have rd14236 := by
    simpa [getTickMsbF4567Word] using rd14235.lor hd14235 (by
      simp only [List.length_cons]
      omega)
  have rd14237 := by
    simpa [getTickMsbF34567Word] using rd14236.lor hd14236 (by
      simp only [List.length_cons]
      omega)
  have rd14238 := by
    simpa using rd14237.swap1 hd14237 (by
      simp only [List.length_cons]
      omega)
  have rd14239 := by
    simpa using rd14238.swap2 hd14238 (by
      simp only [List.length_cons]
      omega)
  have rd14240 := by
    simpa [getTickMsbF234567Word] using rd14239.lor hd14239 (by
      simp only [List.length_cons]
      omega)
  have rd14241 := by
    simpa [getTickMsbF1234567Word] using rd14240.lor hd14240 (by
      simp only [List.length_cons]
      omega)
  have rd14242 := by
    simpa [getTickMsbWord] using rd14241.lor hd14241 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14242⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioNormalizeR {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14242⟩
      (getTickMsbWord ee :: getTickRAfterMsb1Word ee :: getTickRatioWord ee :: ⟨0⟩ ::
        initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14273⟩
      (getTickMsbWord ee :: getTickRNormalizedWord ee :: getTickRatioWord ee :: ⟨0⟩ ::
        initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14242 : decode code ⟨14242⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14244 : decode code ⟨14244⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14245 : decode code ⟨14245⟩ = some (.LT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14246 : decode code ⟨14246⟩ = some (.Push .PUSH2, some (⟨14263⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14249 : decode code ⟨14249⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14250 : decode code ⟨14250⟩ = some (.Push .PUSH1, some (⟨127⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14252 : decode code ⟨14252⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14253 : decode code ⟨14253⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14254 : decode code ⟨14254⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14255 : decode code ⟨14255⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14256 : decode code ⟨14256⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14257 : decode code ⟨14257⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14258 : decode code ⟨14258⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14259 : decode code ⟨14259⟩ = some (.Push .PUSH2, some (⟨14273⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14262 : decode code ⟨14262⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14263 : decode code ⟨14263⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14264 : decode code ⟨14264⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14265 : decode code ⟨14265⟩ = some (.Push .PUSH1, some (⟨127⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14267 : decode code ⟨14267⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14268 : decode code ⟨14268⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14269 : decode code ⟨14269⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14270 : decode code ⟨14270⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14271 : decode code ⟨14271⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14272 : decode code ⟨14272⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14244 := by
    simpa using h.push1 ⟨128⟩ hd14242 (by
      simp only [List.length_cons]
      omega)
  have rd14245 := by
    simpa using rd14244.dup2 hd14244 (by
      simp only [List.length_cons]
      omega)
  have rd14246 := by
    simpa using rd14245.lt hd14245 (by
      simp only [List.length_cons]
      omega)
  have rd14249 := by
    simpa using rd14246.push2 ⟨14263⟩ hd14246 (by
      simp only [List.length_cons]
      omega)
  by_cases hltZero : UInt256.lt (getTickMsbWord ee) ⟨128⟩ = ⟨0⟩
  · have rd14250 := by
      simpa [show (⟨14246⟩ + UInt256.ofNat 3 + ⟨1⟩ : UInt256) = ⟨14250⟩
          by native_decide] using
        rd14249.jumpiNT hd14249 hltZero (by
          simp only [List.length_cons]
          omega)
    have rd14252 := by
      simpa using rd14250.push1 ⟨127⟩ hd14250 (by
        simp only [List.length_cons]
        omega)
    have rd14253 := by
      simpa using rd14252.dup2 hd14252 (by
        simp only [List.length_cons]
        omega)
    have rd14254 := by
      simpa using rd14253.sub hd14253 (by
        simp only [List.length_cons]
        omega)
    have rd14255 := by
      simpa using rd14254.dup4 hd14254 (by
        simp only [List.length_cons]
        omega)
    have rd14256 := by
      simpa using rd14255.swap1 hd14255 (by
        simp only [List.length_cons]
        omega)
    have rd14257 := by
      simpa [getTickRNormalizedHighWord] using rd14256.shr hd14256 (by
        simp only [List.length_cons]
        omega)
    have rd14258 := by
      simpa using rd14257.swap2 hd14257 (by
        simp only [List.length_cons]
        omega)
    have rd14259 := by
      simpa using rd14258.pop hd14258 (by
        simp only [List.length_cons]
        omega)
    have rd14262 := by
      simpa using rd14259.push2 ⟨14273⟩ hd14259 (by
        simp only [List.length_cons]
        omega)
    exact ⟨_, _, by
      simpa [getTickRNormalizedWord, hltZero] using
        rd14262.jump hd14262 (uniswapV3PoolJumpDestPatched14273 hpatch) (by
          simp only [List.length_cons]
          omega)⟩
  · have rd14263 := rd14249.jumpiT hd14249 hltZero
      (uniswapV3PoolJumpDestPatched14263 hpatch) (by
        simp only [List.length_cons]
        omega)
    have rd14264 := by
      simpa using rd14263.jumpdest hd14263 (by
        simp only [List.length_cons]
        omega)
    have rd14265 := by
      simpa using rd14264.dup1 hd14264 (by
        simp only [List.length_cons]
        omega)
    have rd14267 := by
      simpa using rd14265.push1 ⟨127⟩ hd14265 (by
        simp only [List.length_cons]
        omega)
    have rd14268 := by
      simpa using rd14267.sub hd14267 (by
        simp only [List.length_cons]
        omega)
    have rd14269 := by
      simpa using rd14268.dup4 hd14268 (by
        simp only [List.length_cons]
        omega)
    have rd14270 := by
      simpa using rd14269.swap1 hd14269 (by
        simp only [List.length_cons]
        omega)
    have rd14271 := by
      simpa [getTickRNormalizedLowWord] using rd14270.shl hd14270 (by
        simp only [List.length_cons]
        omega)
    have rd14272 := by
      simpa using rd14271.swap2 hd14271 (by
        simp only [List.length_cons]
        omega)
    have rd14273 := by
      simpa using rd14272.pop hd14272 (by
        simp only [List.length_cons]
        omega)
    exact ⟨_, _, by
      simpa [getTickRNormalizedWord, hltZero] using rd14273⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep63 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14273⟩
      (getTickMsbWord ee :: getTickRNormalizedWord ee :: getTickRatioWord ee :: ⟨0⟩ ::
        initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14291⟩
      (getTickLogRAfter63Word ee :: ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee ::
        getTickMsbWord ee :: getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee ::
          ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14273 : decode code ⟨14273⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14274 : decode code ⟨14274⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14275 : decode code ⟨14275⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14276 : decode code ⟨14276⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14277 : decode code ⟨14277⟩ = some (.Push .PUSH1, some (⟨127⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14279 : decode code ⟨14279⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14280 : decode code ⟨14280⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14281 : decode code ⟨14281⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14282 : decode code ⟨14282⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14284 : decode code ⟨14284⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14285 : decode code ⟨14285⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14286 : decode code ⟨14286⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14287 : decode code ⟨14287⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14288 : decode code ⟨14288⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14289 : decode code ⟨14289⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14290 : decode code ⟨14290⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14274 := by
    simpa using h.jumpdest hd14273 (by
      simp only [List.length_cons]
      omega)
  have rd14275 := by
    simpa using rd14274.swap1 hd14274 (by
      simp only [List.length_cons]
      omega)
  have rd14276 := by
    simpa using rd14275.dup1 hd14275 (by
      simp only [List.length_cons]
      omega)
  have rd14277 := by
    simpa [getTickLogRSquared63Word] using rd14276.mul hd14276 (by
      simp only [List.length_cons]
      omega)
  have rd14279 := by
    simpa using rd14277.push1 ⟨127⟩ hd14277 (by
      simp only [List.length_cons]
      omega)
  have rd14280 := by
    simpa using rd14279.dup2 hd14279 (by
      simp only [List.length_cons]
      omega)
  have rd14281 := by
    simpa using rd14280.dup2 hd14280 (by
      simp only [List.length_cons]
      omega)
  have rd14282 := by
    simpa [getTickLogRShifted63Word] using rd14281.shr hd14281 (by
      simp only [List.length_cons]
      omega)
  have rd14284 := by
    simpa using rd14282.push1 ⟨255⟩ hd14282 (by
      simp only [List.length_cons]
      omega)
  have rd14285 := by
    simpa using rd14284.dup4 hd14284 (by
      simp only [List.length_cons]
      omega)
  have rd14286 := by
    simpa using rd14285.dup2 hd14285 (by
      simp only [List.length_cons]
      omega)
  have rd14287 := by
    simpa [getTickLogF63Word] using rd14286.shr hd14286 (by
      simp only [List.length_cons]
      omega)
  have rd14288 := by
    simpa using rd14287.swap2 hd14287 (by
      simp only [List.length_cons]
      omega)
  have rd14289 := by
    simpa using rd14288.swap1 hd14288 (by
      simp only [List.length_cons]
      omega)
  have rd14290 := by
    simpa using rd14289.swap2 hd14289 (by
      simp only [List.length_cons]
      omega)
  have rd14291 := by
    simpa [getTickLogRAfter63Word] using rd14290.shr hd14290 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14291⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep62 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14291⟩
      (getTickLogRAfter63Word ee :: ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee ::
        getTickMsbWord ee :: getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee ::
          ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14300⟩
      (getTickLogRAfter62Word ee :: getTickLogRSquared62Word ee :: ⟨255⟩ ::
        ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
          getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
            initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14291 : decode code ⟨14291⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14292 : decode code ⟨14292⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14293 : decode code ⟨14293⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14294 : decode code ⟨14294⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14295 : decode code ⟨14295⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14296 : decode code ⟨14296⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14297 : decode code ⟨14297⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14298 : decode code ⟨14298⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14299 : decode code ⟨14299⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14292 := by
    simpa using h.dup1 hd14291 (by
      simp only [List.length_cons]
      omega)
  have rd14293 := by
    simpa [getTickLogRSquared62Word] using rd14292.mul hd14292 (by
      simp only [List.length_cons]
      omega)
  have rd14294 := by
    simpa using rd14293.dup1 hd14293 (by
      simp only [List.length_cons]
      omega)
  have rd14295 := by
    simpa using rd14294.dup4 hd14294 (by
      simp only [List.length_cons]
      omega)
  have rd14296 := by
    simpa [getTickLogRShifted62Word] using rd14295.shr hd14295 (by
      simp only [List.length_cons]
      omega)
  have rd14297 := by
    simpa using rd14296.dup2 hd14296 (by
      simp only [List.length_cons]
      omega)
  have rd14298 := by
    simpa using rd14297.dup4 hd14297 (by
      simp only [List.length_cons]
      omega)
  have rd14299 := by
    simpa [getTickLogF62Word] using rd14298.shr hd14298 (by
      simp only [List.length_cons]
      omega)
  have rd14300 := by
    simpa [getTickLogRAfter62Word] using rd14299.shr hd14299 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14300⟩

end Benchmarks.UniswapV3Pool
