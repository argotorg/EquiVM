import Examples.OpenZeppelinBench.ERC6909.Storage
import Examples.OpenZeppelinBench.AccessControl.SupportsInterface
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## `supportsInterface(bytes4)` -/

def supportsInterfaceArgBytes (I : ExecutionEnv) : List UInt8 :=
  ((I.calldata.toList.drop 4).take 32).take 4

def supportsInterfaceArgWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes 4 32)

abbrev supportsInterfaceWord (I : ExecutionEnv) : UInt256 :=
  OpenZeppelinBench.AccessControl.supportsInterfaceWord I

abbrev supportsInterfaceBytes (I : ExecutionEnv) : List UInt8 :=
  supportsInterfaceArgBytes I

abbrev supportsInterfaceMask : UInt256 :=
  OpenZeppelinBench.AccessControl.supportsInterfaceMask

abbrev ierc6909IdWord : UInt256 :=
  UInt256.shiftLeft (⟨0x0f632fb3⟩ : UInt256) ⟨224⟩

abbrev ierc165IdWord : UInt256 :=
  OpenZeppelinBench.AccessControl.ierc165IdWord

def supportsInterfaceStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "interfaceId" (.fixedBytes bytes4Width (supportsInterfaceArgBytes I))

def supportsInterfaceResult (I : ExecutionEnv) : Bool :=
  (supportsInterfaceArgBytes I == [0x0f, 0x63, 0x2f, 0xb3]) ||
    (supportsInterfaceArgBytes I == [0x01, 0xff, 0xc9, 0xa7])

def supportsInterfaceResultWord (I : ExecutionEnv) : UInt256 :=
  if supportsInterfaceResult I then ⟨1⟩ else ⟨0⟩

theorem erc6909SupportsInterfaceSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_supportsInterface {cd : ByteArray}
    (hsel : ((⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some supportsInterfaceTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition, isOperatorTransition,
      setOperatorTransition])
    (post := [transferTransition, transferFromTransition]) rfl rfl ?_
    (by rw [selectorOf, erc6909SupportsInterfaceSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, erc6909AllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909BalanceOfSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909IsOperatorSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909SetOperatorSelectorBytes, hcd]; decide

theorem erc6909Decode_supportsInterface_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata =
        some (supportsInterfaceStore I) := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = some (supportsInterfaceStore I)
  simpa [supportsInterfaceStore, supportsInterfaceArgBytes, calldataBytes4Arg, bytes4, bytes4Width,
    abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_ok (cd := I.calldata) (x := "interfaceId") hsz36 hbig hpad

theorem erc6909Decode_supportsInterface_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  simpa [bytes4, bytes4Width, abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_none_short (cd := I.calldata) (x := "interfaceId") hsz4 hshort

theorem erc6909Decode_supportsInterface_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  simpa [bytes4, bytes4Width, abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_none_huge (cd := I.calldata) (x := "interfaceId") hbig

theorem erc6909Decode_supportsInterface_none_pad {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  simpa [bytes4, bytes4Width, abiBytes4, abiBytes4Width] using
    decodeCalldata_bytes4_none_pad (cd := I.calldata) (x := "interfaceId") hsz36 hbig hpad

theorem erc6909Decide_eq_list_beq_uint8 (xs ys : List UInt8) :
    decide (xs = ys) = (xs == ys) := by
  by_cases h : xs = ys
  · subst ys
    simp
  · have hb : (xs == ys) = false := by
      exact beq_eq_false_iff_ne.mpr h
    simp [h, hb]

theorem supportsInterfaceEqOne_of_padding {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    UInt256.eq (supportsInterfaceWord I)
      (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨1⟩ := by
  have hclean :
      UInt256.land (supportsInterfaceWord I) supportsInterfaceMask = supportsInterfaceWord I :=
    OpenZeppelinBench.AccessControl.supportsInterfaceClean_of_mod_zero _
      (OpenZeppelinBench.AccessControl.supportsInterfaceModZero_of_padding hsz36 hpad)
  rw [hclean]
  exact uInt256_eq_self _

theorem supportsInterfaceEqZero_of_padding_none {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none) :
    UInt256.eq (supportsInterfaceWord I)
      (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨0⟩ := by
  apply uInt256_eq_zero_of_ne
  intro heq
  have hword :
      supportsInterfaceWord I =
        UInt256.land (supportsInterfaceWord I) supportsInterfaceMask :=
    OpenZeppelinBench.AccessControl.accessControlUInt256_eq_one_eq heq
  exact (OpenZeppelinBench.AccessControl.supportsInterfaceModNeZero_of_padding_none hsz36 hpad)
    (OpenZeppelinBench.AccessControl.supportsInterfaceModZero_of_land_eq _ hword.symm)

theorem supportsInterfaceMaskedWord_toNat {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask).toNat =
      fromBytesBigEndian (supportsInterfaceBytes I) * 2 ^ 224 := by
  change (UInt256.land (OpenZeppelinBench.AccessControl.supportsInterfaceWord I)
      OpenZeppelinBench.AccessControl.supportsInterfaceMask).toNat =
    fromBytesBigEndian (OpenZeppelinBench.AccessControl.supportsInterfaceBytes I) * 2 ^ 224
  exact OpenZeppelinBench.AccessControl.supportsInterfaceMaskedWord_toNat (I := I) hsz36

theorem supportsInterfaceBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (supportsInterfaceBytes I).length = 4 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp [supportsInterfaceBytes, supportsInterfaceArgBytes, List.length_take, List.length_drop,
    htlen]
  omega

theorem ierc6909IdWord_toNat :
    ierc6909IdWord.toNat = fromBytesBigEndian [0x0f, 0x63, 0x2f, 0xb3] * 2 ^ 224 := by
  decide

theorem ierc165IdWord_toNat :
    ierc165IdWord.toNat = fromBytesBigEndian [0x01, 0xff, 0xc9, 0xa7] * 2 ^ 224 := by
  decide

theorem supportsInterfaceEq_erc6909 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    UInt256.eq ierc6909IdWord
        (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) =
      if (supportsInterfaceBytes I == [0x0f, 0x63, 0x2f, 0xb3]) then ⟨1⟩ else ⟨0⟩ := by
  by_cases h : supportsInterfaceBytes I = [0x0f, 0x63, 0x2f, 0xb3]
  · have hbeq : (supportsInterfaceBytes I == [0x0f, 0x63, 0x2f, 0xb3]) = true := by
      rw [h]
      decide
    rw [hbeq]
    have heq :
        ierc6909IdWord =
          UInt256.land (supportsInterfaceWord I) supportsInterfaceMask := by
      apply u256_inj
      rw [ierc6909IdWord_toNat, supportsInterfaceMaskedWord_toNat hsz36, h]
    rw [heq]
    exact uInt256_eq_self _
  · have hbeq : (supportsInterfaceBytes I == [0x0f, 0x63, 0x2f, 0xb3]) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      exact h (eq_of_beq hb)
    rw [hbeq]
    apply uInt256_eq_zero_of_ne
    intro heq1
    have heq :
        ierc6909IdWord =
          UInt256.land (supportsInterfaceWord I) supportsInterfaceMask := by
      by_contra hne
      simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
        Bool.false_eq_true, ↓reduceIte] at heq1
      exact absurd heq1 (by decide)
    have hn :
        fromBytesBigEndian (supportsInterfaceBytes I) =
          fromBytesBigEndian [0x0f, 0x63, 0x2f, 0xb3] := by
      have ht := congrArg UInt256.toNat heq
      rw [ierc6909IdWord_toNat, supportsInterfaceMaskedWord_toNat hsz36] at ht
      omega
    exact h (fromBytesBigEndian_inj4 (supportsInterfaceBytes_length hsz36) rfl hn)

theorem supportsInterfaceEq_erc165 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    UInt256.eq ierc165IdWord
        (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) =
      if (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) then ⟨1⟩ else ⟨0⟩ := by
  by_cases h : supportsInterfaceBytes I = [0x01, 0xff, 0xc9, 0xa7]
  · have hbeq : (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) = true := by
      rw [h]
      decide
    rw [hbeq]
    have heq :
        ierc165IdWord =
          UInt256.land (supportsInterfaceWord I) supportsInterfaceMask := by
      apply u256_inj
      rw [ierc165IdWord_toNat, supportsInterfaceMaskedWord_toNat hsz36, h]
    rw [heq]
    exact uInt256_eq_self _
  · have hbeq : (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      exact h (eq_of_beq hb)
    rw [hbeq]
    apply uInt256_eq_zero_of_ne
    intro heq1
    have heq :
        ierc165IdWord =
          UInt256.land (supportsInterfaceWord I) supportsInterfaceMask := by
      by_contra hne
      simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
        Bool.false_eq_true, ↓reduceIte] at heq1
      exact absurd heq1 (by decide)
    have hn :
        fromBytesBigEndian (supportsInterfaceBytes I) =
          fromBytesBigEndian [0x01, 0xff, 0xc9, 0xa7] := by
      have ht := congrArg UInt256.toNat heq
      rw [ierc165IdWord_toNat, supportsInterfaceMaskedWord_toNat hsz36] at ht
      omega
    exact h (fromBytesBigEndian_inj4 (supportsInterfaceBytes_length hsz36) rfl hn)

theorem supportsInterfaceResultWord_norm (I : ExecutionEnv) :
    UInt256.isZero (UInt256.isZero (supportsInterfaceResultWord I)) =
      supportsInterfaceResultWord I := by
  by_cases h : supportsInterfaceResult I <;> simp [supportsInterfaceResultWord, h] <;> decide

theorem erc6909SupportsInterfaceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (supportsInterfaceStore I) supportsInterfaceTransition.body
      (.returned { contract := contract, locals := supportsInterfaceStore I } evm
        (some [(.bool (supportsInterfaceResult I))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      by_cases h6909 : (supportsInterfaceArgBytes I).beq [0x0f, 0x63, 0x2f, 0xb3] = true
      · simp [supportsInterfaceStore, supportsInterfaceResult, ierc6909Id, ierc165Id,
          evalExpr?, evalBinaryOp?, EvalResult.bind, EvalResult.ofOption, bind, pure, BEq.beq,
          erc6909Decide_eq_list_beq_uint8, h6909]
      · simp [supportsInterfaceStore, supportsInterfaceResult, ierc6909Id, ierc165Id,
          evalExpr?, evalBinaryOp?, EvalResult.bind, EvalResult.ofOption, bind, pure, BEq.beq,
          erc6909Decide_eq_list_beq_uint8, h6909])

theorem erc6909SupportsInterfaceX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨174⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1696⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨188⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨193⟩, push2 ⟨188⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1696⟩, jump (by jump_dest) ]⟩

theorem erc6909SupportsInterfaceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ())
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨174⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩
      [supportsInterfaceWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  have hclean : UInt256.eq (supportsInterfaceWord I)
      (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨1⟩ :=
    supportsInterfaceEqOne_of_padding hsz36 hpad
  obtain ⟨_, _, rd1696⟩ := erc6909SupportsInterfaceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact ⟨_, _, evm_run rd1696 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1712⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub,
    not, dup2, and, dup2, eq, push2 ⟨1735⟩,
    jumpiT (by
      change UInt256.eq (supportsInterfaceWord I)
        (UInt256.land (supportsInterfaceWord I)
          (UInt256.lnot
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩))) ≠ ⟨0⟩
      rw [show UInt256.lnot
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩) =
        supportsInterfaceMask from rfl, hclean]
      decide) (by jump_dest),
    jumpdest, swap4, swap3, pop, pop, pop, jump (by jump_dest),
    jumpdest, push2 ⟨447⟩, jump (by jump_dest) ]⟩

theorem erc6909ReturnBool193 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {val : UInt256}
    (h : RD erc6909BenchBytecode ee g s0 ⟨193⟩ (val :: R) solcFreePtrMem
        (UInt256.ofNat 3) rdata acc k C)
    (hnorm : UInt256.isZero (UInt256.isZero val) = val)
    (hov : R.length + 8 ≤ 1024) :
    RDret erc6909BenchBytecode g s0 acc (UInt256.toByteArray val) := by
  have rd165 := evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by decide)
      mem_cost (by rw [hnorm]; rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨165⟩, jump (by jump_dest) ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 val) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide)
      mem_cost
      (by
        rw [show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
          from by decide]
        exact solcReturnMem_read128 val)
      (by evm_ov) ]

theorem erc6909SupportsInterfaceX_body {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨447⟩
      [supportsInterfaceWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨193⟩
      [supportsInterfaceResultWord I, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd447⟩ := hreach
  have hmask :
      UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩) =
        supportsInterfaceMask := rfl
  have h6909 := supportsInterfaceEq_erc6909 (I := I) hsz36
  have h165 := supportsInterfaceEq_erc165 (I := I) hsz36
  by_cases hERC : (supportsInterfaceBytes I == [0x0f, 0x63, 0x2f, 0xb3]) = true
  · have hERCeq : UInt256.eq ierc6909IdWord
        (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨1⟩ := by
      simpa [hERC] using h6909
    have hresult : supportsInterfaceResultWord I = ⟨1⟩ := by
      simp [supportsInterfaceResultWord, supportsInterfaceResult, hERC]
    have rd441 := evm_run rd447 with [
      jumpdest, push0, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, not,
      dup3, and, push4 ⟨0x0f632fb3⟩, push1 ⟨224⟩, shl, eq, dup1, push2 ⟨441⟩,
      jumpiT (by
        change UInt256.eq ierc6909IdWord
          (UInt256.land (supportsInterfaceWord I)
            (UInt256.lnot
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩))) ≠ ⟨0⟩
        rw [hmask, hERCeq]
        decide) (by jump_dest) ]
    exact ⟨_, _, by
      simpa [hresult, hmask, hERCeq, ierc6909IdWord] using evm_run rd441 with [
        jumpdest, swap3, swap2, pop, pop, jump (by jump_dest) ]⟩
  · have hERCfalse : (supportsInterfaceBytes I == [0x0f, 0x63, 0x2f, 0xb3]) = false :=
      Bool.eq_false_iff.mpr hERC
    have hERCeq : UInt256.eq ierc6909IdWord
        (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨0⟩ := by
      simpa [hERCfalse] using h6909
    have rd474 := evm_run rd447 with [
      jumpdest, push0, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, not,
      dup3, and, push4 ⟨0x0f632fb3⟩, push1 ⟨224⟩, shl, eq, dup1, push2 ⟨441⟩,
      jumpiNT (by
        change UInt256.eq ierc6909IdWord
          (UInt256.land (supportsInterfaceWord I)
            (UInt256.lnot
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩))) = ⟨0⟩
        rw [hmask, hERCeq]) ]
    have rd441 := evm_run rd474 with [
      pop, push4 ⟨0x01ffc9a7⟩, push1 ⟨224⟩, shl, push1 ⟨1⟩, push1 ⟨1⟩,
      push1 ⟨224⟩, shl, sub, not, dup4, and, eq, push2 ⟨441⟩,
      jump (by jump_dest) ]
    have hresult :
        UInt256.eq ierc165IdWord
            (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) =
          supportsInterfaceResultWord I := by
      by_cases h165beq : (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) = true
      · simp [supportsInterfaceResultWord, supportsInterfaceResult, hERCfalse, h165beq] at *
        simpa [h165beq] using h165
      · have h165false :
            (supportsInterfaceBytes I == [0x01, 0xff, 0xc9, 0xa7]) = false :=
          Bool.eq_false_iff.mpr h165beq
        simp [supportsInterfaceResultWord, supportsInterfaceResult, hERCfalse, h165false] at *
        simpa [h165false] using h165
    have hresultRev :
        UInt256.eq (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) ierc165IdWord =
          supportsInterfaceResultWord I := by
      rw [uInt256_eq_comm, hresult]
    exact ⟨_, _, by
      simpa [hmask, hresultRev, ierc165IdWord] using evm_run rd441 with [
        jumpdest, swap3, swap2, pop, pop, jump (by jump_dest) ]⟩

theorem erc6909X_supportsInterface {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ())
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨174⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (supportsInterfaceResultWord I)) := by
  obtain ⟨_, _, rd447⟩ := erc6909SupportsInterfaceX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hpad hreach
  obtain ⟨_, _, rd193⟩ := erc6909SupportsInterfaceX_body (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 ⟨_, _, rd447⟩
  exact erc6909ReturnBool193 rd193 (supportsInterfaceResultWord_norm I) (by evm_ov)

theorem erc6909SupportsInterfaceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨174⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd1696⟩ := erc6909SupportsInterfaceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd1696 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1712⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909SupportsInterfaceX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (_hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨174⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd1696⟩ := erc6909SupportsInterfaceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd1696 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1712⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909SupportsInterfaceX_badpad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = none)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨174⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  have hclean : UInt256.eq (supportsInterfaceWord I)
      (UInt256.land (supportsInterfaceWord I) supportsInterfaceMask) = ⟨0⟩ :=
    supportsInterfaceEqZero_of_padding_none hsz36 hpad
  obtain ⟨_, _, rd1696⟩ := erc6909SupportsInterfaceX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd1696 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1712⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub,
    not, dup2, and, dup2, eq, push2 ⟨1735⟩,
    jumpiNT (by
      change UInt256.eq (supportsInterfaceWord I)
        (UInt256.land (supportsInterfaceWord I)
          (UInt256.lnot
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩))) = ⟨0⟩
      simp [hclean]),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909SupportsInterfaceBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (erc6909SelBytes 1))
    (hreach : ∃ k C, RD erc6909BenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨174⟩
      [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hselSupports : selIs I ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ := by
    simpa [erc6909SelBytes] using hsel
  have hsz4 := erc6909SupportsInterfaceSelector_size (by simpa [selIs] using hselSupports)
  have hd := erc6909Dispatch_supportsInterface (cd := I.calldata) (by
    simpa [selIs] using hselSupports)
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · cases hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 with
      | none =>
          have hdec := erc6909Decode_supportsInterface_none_pad
            (I := I) hsz36 hbig hpad
          exact (erc6909SupportsInterfaceX_badpad (g := Sat256.ofUInt256 g)
              hsz36 hsize hbig hpad hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      | some _ =>
          have hpadSome :
              zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some () := by
            simpa using hpad
          have hdec := erc6909Decode_supportsInterface_ok
            (I := I) hsz36 hbig hpadSome
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (supportsInterfaceStore I)
                supportsInterfaceTransition.body
                (.returned { contract := contract, locals := supportsInterfaceStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (some [(.bool (supportsInterfaceResult I))])) := by
            exact erc6909SupportsInterfaceBodyReturns
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
          exact (erc6909X_supportsInterface (g := Sat256.ofUInt256 g)
              hsz36 hsize hbig hpadSome hreach)
            |>.reEquivExecutionTransport hcode hd hdec hbody rfl hAccounts
              (returnEquiv_of_encode (by
                by_cases hr : supportsInterfaceResult I
                · simpa [supportsInterfaceResultWord, hr] using
                    OpenZeppelinBench.AccessControl.boolTrueReturnEncodingAC
                · simpa [boolTy, supportsInterfaceResultWord, hr] using
                    Reasoning.Theory.boolFalseReturnEncoding))
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc6909Decode_supportsInterface_none_huge (I := I) hbigge
      exact (erc6909SupportsInterfaceX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := erc6909Decode_supportsInterface_none_short (I := I) hsz4 hshort
    exact (erc6909SupportsInterfaceX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.ERC6909
