import Examples.VyperERC20.Bytecode
import Examples.VyperERC20.Storage
import Examples.ERC20.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace VyperERC20

def totalSupplyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def totalSupplySelectorWord : UInt256 :=
  ⟨0x18160ddd⟩

def runtimeDispatchMem : ByteArray :=
  vyperERC20Bytecode.write 815 ByteArray.empty 30 2

def totalSupplyReturnMem (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 runtimeDispatchMem 64 32

theorem runtimeDispatchMem_size : runtimeDispatchMem.size = 32 := by
  decide +native

theorem runtimeDispatchMem_mload0 :
    (if (⟨0⟩ : UInt256).toNat ≥ runtimeDispatchMem.size ∨
        (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (runtimeDispatchMem.readWithPadding (⟨0⟩ : UInt256).toNat 32)))
      = (⟨769⟩ : UInt256) := by
  decide +native

theorem totalSupplyReturnMem_read64 (val : UInt256) :
    (totalSupplyReturnMem val).readWithPadding 64 32 = UInt256.toByteArray val := by
  unfold totalSupplyReturnMem
  exact toByteArray_write_read_back_of_gap val runtimeDispatchMem 64
    (by rw [runtimeDispatchMem_size]; exact lt_usize 32 (by norm_num))

theorem erc20TotalSupplyBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "totalSupply" = none) :
    ExecTransitionBody vyperERC20Config erc20Contract evm locals ERC20.totalSupplyTransition.body
      (.returned { contract := erc20Contract, locals := locals } evm
        (some [(.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef vyperERC20Config { contract := erc20Contract, locals := locals } evm
          totalSupplyRef = .ok { base := "totalSupply", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, ERC20.totalSupplyRef,
          EvalResult.bind, pure, bind]
      have hty : storageTypeAt? erc20Contract.storage ({ base := "totalSupply", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint256Int)) := by
        decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := vyperERC20Config_storage_totalSupply),
        vyperERC20StorageLocLoad_uint256])

macro "vyper_erc20_runtime_decode" : tactic =>
  `(tactic| decide +native)

macro "vyper_erc20_runtime_jd" : term =>
  `(by decide +native)

theorem vyperRuntimeRevert801 {cA gh bl σ σ₀ A I} {g : Sat256}
    {pc stk mem aw rdata acc k C}
    (hreach : RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) pc
      stk mem aw rdata acc k C)
    (hpc : pc = ⟨801⟩)
    (hov : stk.length + 2 ≤ 1024) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  subst pc
  have rd804 := evm_run hreach with [
    jumpdest,
    push0,
    dup1]
  exact rd804.rev 0 (by vyper_erc20_runtime_decode)
    (fun s _ hstks => memExpRevert0 s hstks) (by omega)

theorem vyperRuntimeRevert797 {cA gh bl σ σ₀ A I} {g : Sat256}
    {pc stk mem aw rdata acc k C}
    (hreach : RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) pc
      stk mem aw rdata acc k C)
    (hpc : pc = ⟨797⟩)
    (hov : stk.length + 2 ≤ 1024) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  subst pc
  have rd800 := evm_run hreach with [
    jumpdest,
    push0,
    push0]
  exact rd800.rev 0 (by vyper_erc20_runtime_decode)
    (fun s _ hstks => memExpRevert0 s hstks) (by omega)

theorem calldataSizeGuardOk {n m : Nat}
    (hm : m ≤ n) (hsize : n < UInt256.size) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat m) = ⟨0⟩ := by
  exact ult_zero (by
    have hn : (UInt256.ofNat n).toNat = n := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt hsize
    have hm' : (UInt256.ofNat m).toNat = m := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt hm hsize)
    rw [hn, hm']
    exact hm)

theorem calldataSizeGuardShort {n m : Nat}
    (hsize : n < UInt256.size) (hmlt : m < UInt256.size) (hshort : n < m) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat m) = ⟨1⟩ := by
  exact ult_one (by
    have hn : (UInt256.ofNat n).toNat = n := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt hsize
    have hm : (UInt256.ofNat m).toNat = m := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt hmlt
    rw [hn, hm]
    exact hshort)

theorem u256_lt_addressModulus_of_shiftRight160_zero (w : UInt256)
    (h : UInt256.shiftRight w ⟨160⟩ = ⟨0⟩) :
    w.toNat < EVM.addressModulus := by
  cases w with
  | mk val =>
    unfold UInt256.shiftRight at h
    simp at h
    have hdiv : val.val / 2 ^ 160 = 0 := by
      have hval := congrArg Fin.val h
      simpa [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow] using hval
    unfold UInt256.toNat
    change val.val < 2 ^ 160
    by_contra hnot
    have hge : 2 ^ 160 ≤ val.val := by omega
    have hpos : 0 < val.val / 2 ^ 160 := Nat.div_pos hge (by positivity)
    omega

theorem totalSupplySelectorWord_of_calldata {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ =
      totalSupplySelectorWord := by
  have h := evmSelectorDecode hsz 0x18 0x16 0x0d 0xdd totalSupplySelectorWord (by decide +native)
  rw [hsel] at h
  unfold UInt256.eq at h
  by_cases heq :
      totalSupplySelectorWord =
        UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩
  · exact heq.symm
  · simp [heq] at h
    have hne : UInt256.ofNat 0 ≠ (⟨1⟩ : UInt256) := by decide
    exact False.elim (hne h)

theorem erc20X_totalSupplyReach {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨769⟩
      [totalSupplySelectorWord] runtimeDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have hsz : 4 ≤ I.calldata.size := by
    have hs := byteArray_size_eq_of_beq hsel
    have hleft : (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray).size = 4 := rfl
    rw [hleft, ByteArray.size_extract] at hs
    omega
  have hword := totalSupplySelectorWord_of_calldata (I := I) hsz hsel
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0,
    calldataload,
    push1 ⟨224⟩,
    shr,
    push1 ⟨2⟩,
    push1 ⟨7⟩,
    dup3,
    mod,
    push1 ⟨1⟩,
    shl,
    push2 ⟨805⟩,
    add,
    push1 ⟨30⟩]
  have rdBeforeCopy := by
    simpa [hword, totalSupplySelectorWord] using rdBeforeCopy0
  have rdAfterCopy := rdBeforeCopy.codecopy 3 runtimeDispatchMem (UInt256.ofNat 1)
    (by vyper_erc20_runtime_decode)
    mem_cost
    (by decide +native)
    (by decide)
    (by evm_ov)
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨769⟩ (UInt256.ofNat 1)
      (by vyper_erc20_runtime_decode)
      mem_cost
      runtimeDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_runtime_decode) (by decide +native) (by evm_ov)⟩

theorem erc20X_totalSupplyFromEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨769⟩
      [totalSupplySelectorWord] runtimeDispatchMem (UInt256.ofNat 1) ByteArray.empty (cA, σ) k C) :
    RDret vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (totalSupplyWord σ I)) := by
  obtain ⟨k, C, rd769⟩ := hreach
  have rdBeforeLoad := evm_run rd769 with [
    jumpdest,
    raw push4 totalSupplySelectorWord (by vyper_erc20_runtime_decode) (by evm_ov),
    dup2,
    xor,
    push2 ⟨797⟩,
    jumpiNT (by decide +native),
    callvalue,
    push2 ⟨801⟩,
    jumpiNT (by simp [hwv]),
    push1 ⟨2⟩]
  obtain ⟨k1, C1, rdAfterLoad⟩ :=
    rdBeforeLoad.sload (by vyper_erc20_runtime_decode) (by evm_ov)
  have rdBeforeReturn := evm_run rdAfterLoad with [
    push1 ⟨64⟩,
    raw mstore 6 (totalSupplyReturnMem (totalSupplyWord σ I)) (UInt256.ofNat 3)
      (by vyper_erc20_runtime_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨64⟩]
  exact rdBeforeReturn.ret 0 (UInt256.toByteArray (totalSupplyWord σ I))
    (by vyper_erc20_runtime_decode)
    mem_cost
    (totalSupplyReturnMem_read64 (totalSupplyWord σ I))
    (by evm_ov)

theorem erc20TotalSupplySelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc20Dispatch_totalSupply {cd : ByteArray}
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some ERC20.totalSupplyTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (contract := erc20Contract)
    (pre := [ERC20.approveTransition])
    (post := [ERC20.transferFromTransition, ERC20.balanceOfTransition,
      ERC20.transferTransition, ERC20.allowanceTransition])
    (hfallback := rfl) (htr := rfl) ?_
    (by rw [selectorOf, vyperERC20TotalSupplySelectorBytes]; exact hsel)
  · intro t ht
    simp only [List.mem_singleton] at ht; subst ht
    rw [selectorOf, vyperERC20ApproveSelectorBytes, hcd]; decide

theorem erc20Decode_totalSupply {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (ERC20.totalSupplyTransition.params.map Param.name)
      (transitionSignature ERC20.totalSupplyTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem erc20TotalSupplyBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨769⟩
      [totalSupplySelectorWord] runtimeDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := erc20TotalSupplySelector_size hsel
  have hd := erc20Dispatch_totalSupply (cd := I.calldata) hsel
  have hdec :
      decodeCalldataWithMode vyperERC20Config.abiDecodeMode
        (ERC20.totalSupplyTransition.params.map Param.name)
        (transitionSignature ERC20.totalSupplyTransition).paramTypes I.calldata =
          some ∅ := by
    simpa [vyperERC20Config, erc20Contract, ERC20.erc20Contract, ERC20.totalSupplyTransition]
      using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  have hword : totalSupplyWord σ_evm I = totalSupplyWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hbody :
      ExecTransitionBody vyperERC20Config erc20Contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ ERC20.totalSupplyTransition.body
        (.returned { contract := erc20Contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (totalSupplyWord σ_solm I).toNat))])) := by
    simpa [totalSupplyWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      erc20TotalSupplyBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (erc20X_totalSupplyFromEntry (g := Sat256.ofUInt256 g) hwv hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
      (returnEquiv_of_encode (ERC20.erc20Uint256ReturnEncoding (totalSupplyWord σ_evm I)))

theorem erc20TotalSupplyRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20TotalSupplyBodyCore hcode hwv hsel
    (erc20X_totalSupplyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsel)
    hAccounts

end VyperERC20
