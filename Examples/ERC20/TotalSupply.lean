import Examples.ERC20.Common
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace ERC20

def totalSupplyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

theorem totalSupplyWord_eq_storageLoad_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    totalSupplyWord σ I =
      Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
        (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner ⟨2⟩ :=
  rfl

/-- The Solm `totalSupply()` body returns the word stored in slot 2. -/
theorem erc20TotalSupplyBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "totalSupply" = none) :
    ExecTransitionBody erc20Config erc20Contract evm locals totalSupplyTransition.body
      (.returned { contract := erc20Contract, locals := locals } evm
        (some (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef erc20Config { contract := erc20Contract, locals := locals } evm
          totalSupplyRef = .ok { base := "totalSupply", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? erc20Contract.storage ({ base := "totalSupply", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint256Int)) := by decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := erc20Config_storage_totalSupply), erc20StorageLocLoad_uint256])

/-- The EVM `totalSupply()` wrapper loads slot 2 and returns it as a single ABI word. -/
theorem erc20X_totalSupply {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨148⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc20Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (totalSupplyWord σ I)) := by
  obtain ⟨k, C, rd148⟩ := hreach
  have rd610 := evm_run rd148 with [
    jumpdest, push2 ⟨156⟩, push2 ⟨607⟩, jump (by jump_dest),
    jumpdest, push1 ⟨2⟩ ]
  obtain ⟨k1, C1, rd611⟩ := rd610.sload (by decide) (by evm_ov)
  have rd156 := evm_run rd611 with [
    dup2, jump (by jump_dest) ]
  have rd2073 := evm_run rd156 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨169⟩, swap2, swap1, push2 ⟨2073⟩, jump (by jump_dest) ]
  obtain ⟨k2, C2, rd169⟩ := rd2073.erc20RoutineEncodeUint256 (by jump_dest) (by
    simp only [List.length_cons, List.length_nil]
    omega)
  exact evm_run rd169 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 (totalSupplyWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (totalSupplyWord σ I)) (by decide)
      mem_cost
      (by
        unfold totalSupplyWord
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          erc20SubRet32_toNat, solcReturnMem_read128])
      (by evm_ov) ]

theorem erc20TotalSupplySelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc20Dispatch_totalSupply {cd : ByteArray}
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some totalSupplyTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) :=
    (erc20ByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (pre := [approveTransition])
    (post := [transferFromTransition, balanceOfTransition, transferTransition, allowanceTransition])
    rfl ?_ (by rw [selectorOf, erc20TotalSupplySelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_singleton] at ht; subst ht
  rw [selectorOf, erc20ApproveSelectorBytes, hcd]; decide

theorem erc20Decode_totalSupply {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (totalSupplyTransition.params.map Param.name)
      (transitionSignature totalSupplyTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem erc20TotalSupplyBodyCore {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨148⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  have hsz := erc20TotalSupplySelector_size hsel
  have hd := erc20Dispatch_totalSupply (cd := I.calldata) hsel
  have hdec := erc20Decode_totalSupply (I := I) hsz
  have hbody₀ := erc20TotalSupplyBodyReturns
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅ (by simp only [initState]; exact hwv)
    (by simp)
  have hbody :
      ExecTransitionBody erc20Config erc20Contract
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅ totalSupplyTransition.body
        (.returned { contract := erc20Contract, locals := ∅ }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat (totalSupplyWord σ I).toNat)))) := by
    simpa [totalSupplyWord] using hbody₀
  exact (erc20X_totalSupply (g := Sat256.ofUInt256 g) hreach).reEquivExecution hcode hd hdec
    hbody (returnEquiv_of_encode (erc20Uint256ReturnEncoding (totalSupplyWord σ I)))

end ERC20
