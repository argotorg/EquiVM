import Examples.UniswapV2Pair.Dispatch
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Reasoning.Theory

/-! ### Uniswap-local EXP stepping support for dynamic string ABI cleanup -/

-- LIBRARY CANDIDATE: Reasoning.Stepping — reusable EVM `EXP` gas-cost helper.
def uniswapExpGasCost (b : UInt256) : ℕ :=
  if b = ⟨0⟩ then
    GasConstants.Gexp
  else
    GasConstants.Gexp + GasConstants.Gexpbyte * (1 + Nat.log 256 b.toNat)

-- LIBRARY CANDIDATE: Reasoning.Stepping — reusable positivity fact for `EXP` gas.
theorem uniswapExpGasCost_pos (b : UInt256) : 0 < uniswapExpGasCost b := by
  unfold uniswapExpGasCost
  split <;> simp [GasConstants.Gexp]

def uniswapStExp (s : State) (a b : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.exp a b :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat (uniswapExpGasCost b) } }

-- LIBRARY CANDIDATE: Reasoning.Stepping — reusable EVM `EXP` one-step wrapper.
theorem uniswapExp_xstep {s : State} {code : ByteArray} {pcv a b : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.EXP, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < uniswapExpGasCost b
         then .error .OutOfGass else .ok (uniswapStExp s a b t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.EXP, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_exp s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', uniswapExpGasCost, uniswapStExp]

end Reasoning.Theory

namespace Reasoning.Reach

open Reasoning.Theory

-- LIBRARY CANDIDATE: Reasoning.Reach — reusable `RD` combinator for the EVM `EXP` opcode.
theorem RD.exp {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.EXP, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.exp a b :: t) mem aw rdata acc
      (k + 1) (C + uniswapExpGasCost b) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := uniswapExp_xstep hcode hpc hdec hstk hov
    have hcostpos : 0 < uniswapExpGasCost b := uniswapExpGasCost_pos b
    by_cases gg : g.toNat < C + uniswapExpGasCost b
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨uniswapStExp s a b t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
        by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [uniswapStExp]; exact hcode
      · simp only [uniswapStExp]; rw [hpc]
      · rfl
      · simp only [uniswapStExp]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [uniswapStExp]; exact hmem
      · simp only [uniswapStExp]; exact haw
      · simp only [uniswapStExp]; exact hrdata
      · simp only [uniswapStExp]; exact hacc
      · exact hee
      · exact hworld

end Reasoning.Reach

namespace UniswapV2Pair

/-! ## Shared dynamic string getter facts -/

-- LIBRARY CANDIDATE: Reasoning.SolmBody — generic nonpayable dynamic-bytes/string literal
-- return body, parameterized by config, contract, and literal bytes.
theorem uniswapBytesLiteralBodyReturns (evm : EVM.State) (locals : Store) (bytes : ByteArray)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return (.bytesLit bytes) ])
      (.returned { contract := contract, locals := locals } evm (some (.bytes bytes))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by simp [evalExpr?, pure])

theorem uniswapDecode_name {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (nameTransition.params.map Param.name)
      (transitionSignature nameTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem uniswapDecode_symbol {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (symbolTransition.params.map Param.name)
      (transitionSignature symbolTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- Reach the `name()` body entry through the optimized dispatcher. -/
theorem uniswapReachNameBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x06, 0xfd, 0xde, 0x03]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨572⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x06fdde03⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x06 0xfd 0xde 0x03 ⟨0x06fdde03⟩ (by decide) hsel
  exact uniswapReachLowestBody 1 (by decide) ⟨572⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `symbol()` body entry through the optimized dispatcher. -/
theorem uniswapReachSymbolBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x95d89b41⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x95 0xd8 0x9b 0x41 ⟨0x95d89b41⟩ (by decide) hsel
  exact uniswapReachHighLowerBody 2 (by decide) ⟨1226⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

end UniswapV2Pair
