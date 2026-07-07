import Benchmarks.Safe.Routines

/-! # Safe `VERSION()` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Safe

abbrev safeVersionStore : Store :=
  ∅

def safeVersionBytes : ByteArray :=
  String.toByteArray "1.5.0"

abbrev safeVersionLen : UInt256 :=
  ⟨5⟩

def safeVersionReturnBytes : ByteArray :=
  (encodeReturnValue? stringTy (.bytes safeVersionBytes)).getD ByteArray.empty

theorem safeVersionReturnEncoding :
    encodeReturnValue? stringTy (.bytes safeVersionBytes) = some safeVersionReturnBytes := by
  native_decide

def safeStringObjectMem0 : ByteArray :=
  (UInt256.toByteArray (⟨192⟩ : UInt256)).write 0 solcFreePtrMem
    (⟨64⟩ : UInt256).toNat 32

def safeStringObjectMem1 (len : UInt256) : ByteArray :=
  (UInt256.toByteArray len).write 0 safeStringObjectMem0 (⟨128⟩ : UInt256).toNat 32

def safeStringObjectMem (len payloadWord : UInt256) : ByteArray :=
  (UInt256.toByteArray payloadWord).write 0 (safeStringObjectMem1 len)
    (⟨160⟩ : UInt256).toNat 32

def safeStringAbiMem0 (len payloadWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (safeStringObjectMem len payloadWord) (⟨192⟩ : UInt256).toNat 32

def safeStringAbiMem1 (len payloadWord : UInt256) : ByteArray :=
  (UInt256.toByteArray len).write 0 (safeStringAbiMem0 len payloadWord)
    (⟨224⟩ : UInt256).toNat 32

def safeStringAbiMem2 (len payloadWord : UInt256) : ByteArray :=
  (UInt256.toByteArray payloadWord).write 0 (safeStringAbiMem1 len payloadWord)
    (⟨256⟩ : UInt256).toNat 32

def safeStringAbiMem3 (len payloadWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0 (safeStringAbiMem2 len payloadWord) 261 32

abbrev safeVersionRawWord : UInt256 :=
  ⟨0x0312e352e3⟩

abbrev safeVersionLiteralWord : UInt256 :=
  UInt256.shiftLeft safeVersionRawWord ⟨220⟩

theorem safeVersionReturnRead :
    (safeStringAbiMem3 safeVersionLen safeVersionLiteralWord).readWithPadding 192 96 =
      safeVersionReturnBytes := by
  native_decide

theorem safeDecode_version_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (versionTransition.params.map Param.name)
      (transitionSignature versionTransition).paramTypes I.calldata = some safeVersionStore := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

theorem safeVersionBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) safeVersionStore
      versionTransition.body
      (.returned { contract := contract, locals := safeVersionStore }
        (initState cA gh bl σ σ₀ g A I) (some [.bytes safeVersionBytes])) := by
  simpa [versionTransition, safeVersionStore, safeVersionBytes] using
    nonpayableBytesLiteralBodyReturns (cfg := config) (contract := contract)
      (initState cA gh bl σ σ₀ g A I) safeVersionStore safeVersionBytes
      (by simp only [initState]; exact hwv)

theorem safeVersionX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (safeSelBytes 0)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      safeVersionReturnBytes := by
  obtain ⟨_, _, h1688⟩ := safeReachVersionBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1701⟩ := safeGuardPeelOk (gt := ⟨1699⟩) h1688 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have h1714 := evm_run h1701 with [
    push2 ⟨918⟩, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    dup1, push1 ⟨64⟩, add, push1 ⟨64⟩]
  have h1719 := evm_run h1714 with [
    raw mstore 0 safeStringObjectMem0 (UInt256.ofNat 3) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup1, push1 safeVersionLen, dup2]
  have h1722 := evm_run h1719 with [
    raw mstore 6 (safeStringObjectMem1 safeVersionLen) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, add]
  have h1731 := h1722.pushConst safeVersionRawWord (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨220⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have h918 := evm_run h1731 with [
    raw mstore 3 (safeStringObjectMem safeVersionLen safeVersionLiteralWord)
      (UInt256.ofNat 6) (by native_decide) mem_cost
      (by native_decide) (by decide) (by evm_ov),
    pop, dup2, jump (by jump_dest)]
  have h9876 := evm_run h918 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    push2 ⟨771⟩, swap2, swap1, push2 ⟨9876⟩, jump (by jump_dest)]
  have h9767 := evm_run h9876 with [
    jumpdest, push1 ⟨32⟩, dup2,
    raw mstore 3 (safeStringAbiMem0 safeVersionLen safeVersionLiteralWord)
      (UInt256.ofNat 7) (by native_decide) mem_cost
      (by native_decide) (by decide) (by evm_ov),
    push0, push2 ⟨6891⟩, push1 ⟨32⟩, dup4, add, dup5, push2 ⟨9767⟩,
    jump (by jump_dest)]
  have h9733 := evm_run h9767 with [
    jumpdest, push0, dup2,
    raw mload 0 safeVersionLen (UInt256.ofNat 7) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup1, dup5,
    raw mstore 3 (safeStringAbiMem1 safeVersionLen safeVersionLiteralWord)
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by native_decide) (by decide) (by evm_ov),
    push2 ⟨9790⟩, dup2, push1 ⟨32⟩, dup7, add, push1 ⟨32⟩, dup7, add,
    push2 ⟨9733⟩, jump (by jump_dest)]
  have h9735 := evm_run h9733 with [
    jumpdest, push0, jumpdest, dup4, dup2, lt, iszero, push2 ⟨9759⟩,
    jumpiNT (by decide),
    dup2, dup2, add,
    raw mload 0 safeVersionLiteralWord (UInt256.ofNat 8) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup4, dup3, add,
    raw mstore 3 (safeStringAbiMem2 safeVersionLen safeVersionLiteralWord)
      (UInt256.ofNat 9) (by native_decide) mem_cost
      (by native_decide) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨9735⟩, jump (by jump_dest)]
  have h9790 := evm_run h9735 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨9759⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, pop, push0, swap2, add,
    raw mstore 3 (safeStringAbiMem3 safeVersionLen safeVersionLiteralWord)
      (UInt256.ofNat 10) (by native_decide) mem_cost
      (by native_decide) (by decide) (by evm_ov),
    jump (by jump_dest)]
  have h6891 := evm_run h9790 with [
    jumpdest, push1 ⟨31⟩, add, push1 ⟨31⟩, not, and, swap3, swap1, swap3,
    add, push1 ⟨32⟩, add, swap3, swap2, pop, pop, jump (by jump_dest)]
  have h771 := evm_run h6891 with [jumpdest, swap4, swap3, pop, pop, pop, jump (by jump_dest)]
  exact evm_run h771 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (by native_decide) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 safeVersionReturnBytes (by native_decide) mem_cost
      safeVersionReturnRead (by evm_ov)]

theorem safeVersionBodyCoreOk {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (safeSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (safeSelBytes 0) (by native_decide) hsel
  exact safeReEquivExecTransport hcode
    (safeVersionX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    (safeSelectorDispatchVersion hsel) (safeDecode_version_ok hsz4)
    (safeVersionBodyReturns hwv) rfl hAccounts
    (returnEquiv_of_encode (by simpa [versionTransition] using safeVersionReturnEncoding))

theorem safeVersionBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact safeVersionBodyCoreOk hcode hsize hwv hsel hAccounts
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 0) (by native_decide) hsel
    obtain ⟨_, _, h1688⟩ := safeReachVersionBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode
      hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨1699⟩) h1688 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchVersion hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
