import Benchmarks.Safe.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def domainTypehashWord : UInt256 :=
  ⟨32523383700587834770323112271211932718128200013265661849047136999858837557784⟩

def domainPreimage (I : ExecutionEnv) : ByteArray :=
  domainTypehashWord.toByteArray ++ (UInt256.ofNat Ethereum.chainId).toByteArray ++
    (UInt256.ofNat I.codeOwner.val).toByteArray

def domainWord (I : ExecutionEnv) : UInt256 := uInt256OfByteArray (KEC (domainPreimage I))

def domainMemory (I : ExecutionEnv) : ByteArray :=
  (solcFreePtrMem ++ ByteArray.zeroes 32) ++ domainPreimage I

theorem domainPreimage_size (I : ExecutionEnv) : (domainPreimage I).size = 96 := by
  simp [domainPreimage]

theorem domainMemory_size (I : ExecutionEnv) : (domainMemory I).size = 224 := by
  simp [domainMemory, domainPreimage_size, solcFreePtrMem_size, ByteArray_zeroes_size]

theorem domainMemory_read (I : ExecutionEnv) :
    (domainMemory I).readWithPadding 128 96 = domainPreimage I := by
  rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide)
    (by rw [domainMemory_size])]
  exact extract_append_right' _ _ _ _ solcFreePtrMem_pad_size.symm
    (by rw [solcFreePtrMem_pad_size, domainPreimage_size])

theorem domainMemory_read64 (I : ExecutionEnv) :
    (domainMemory I).readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray := by
  rw [readWithPadding_eq_extract _ _ (by rw [domainMemory_size]; decide)]
  rw [domainMemory, extract_append_left _ _ _ _ (by rw [solcFreePtrMem_pad_size]; decide),
    extract_append_left _ _ _ _ (by rw [solcFreePtrMem_size])]
  exact (readWithPadding_eq_extract _ _ (by rw [solcFreePtrMem_size])).symm.trans
    solcFreePtrMem_read64

-- LIBRARY CANDIDATE: turn an evaluated byte string into its word-valued Keccak digest.
theorem evalKeccakWord {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {bytes : ByteArray}
    (he : evalExpr? cfg frame evm e = .ok (.bytes bytes)) :
    evalExpr? cfg frame evm (.keccak256 e) =
      .ok (wordBytes32Value (uInt256OfByteArray (KEC bytes))) := by
  simp only [evalExpr?, he, bind, EvalResult.bind, pure]
  rw [wordBytes32Value, toBytesBE_keccak_uInt256OfByteArray]
  rfl

set_option maxRecDepth 1000000 in
theorem evalDomainSeparator {cfg : Config} (frame : Frame) (evm : EVM.State) :
    evalExpr? cfg frame evm domainSeparatorExpr = .ok (wordBytes32Value
      (domainWord evm.executionEnv)) := by
  unfold domainSeparatorExpr domainWord
  apply evalKeccakWord
  have haddr : evm.executionEnv.codeOwner.val < UInt256.size := by
    have := evm.executionEnv.codeOwner.isLt
    exact lt_trans this (by decide)
  have hcast : evm.executionEnv.codeOwner.val < EVM.twoPow 256 := haddr
  have htype : encodePackedValue? bytes32
      (.fixedBytes bytes32Width
        [0x47, 0xe7, 0x95, 0x34, 0xa2, 0x45, 0x95, 0x2e,
         0x8b, 0x16, 0x89, 0x3a, 0x33, 0x6b, 0x85, 0xa3,
         0xd9, 0xea, 0x9f, 0xa8, 0xc5, 0x73, 0xf3, 0xd8,
         0x03, 0xaf, 0xb9, 0x2a, 0x79, 0x46, 0x92, 0x18]) =
      some (EVM.Word.toBytesBE domainTypehashWord) := by native_decide
  have hchain : encodePackedValue? uint256 (.int (Int.ofNat Ethereum.chainId)) =
      some (EVM.Word.toBytesBE (UInt256.ofNat Ethereum.chainId)) := by
    exact encodePacked_uint256 (UInt256.ofNat Ethereum.chainId)
  have hself : encodePackedValue? uint256 (.int (Int.ofNat evm.executionEnv.codeOwner.toNat)) =
      some (EVM.Word.toBytesBE (UInt256.ofNat evm.executionEnv.codeOwner.val)) := by
    have h := encodePacked_uint256 (UInt256.ofNat evm.executionEnv.codeOwner.val)
    rw [ulit_toNat' _ haddr] at h
    exact h
  have hpacked : evalPackedArgs? cfg frame evm
      [(bytes32, domainSeparatorTypehash), (uint256, .env .chainid),
        (uint256, addressAsUint256 this)] = .ok
      (EVM.Word.toBytesBE domainTypehashWord ++
        (EVM.Word.toBytesBE (UInt256.ofNat Ethereum.chainId) ++
          EVM.Word.toBytesBE (UInt256.ofNat evm.executionEnv.codeOwner.val))) := by
    apply evalPackedArgs_cons (by simp [evalExpr?, domainSeparatorTypehash, pure]) htype
    apply evalPackedArgs_cons (by simp [evalExpr?, envValue, pure]) hchain
    apply evalPackedArgs_single ?_ hself
    simp [evalExpr?, addressAsUint256, this, uint256St, uint256Int,
      castValue?, envValue, hcast, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [evalExpr?, hpacked]
  simp only [bind, EvalResult.bind, pure]
  apply congrArg EvalResult.ok
  apply congrArg Value.bytes
  simp [domainPreimage, mk_toArray_eq,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

end Benchmarks.Safe
