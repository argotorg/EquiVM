import Reasoning.SolcRoutines
import Benchmarks.Dss.ExponentialDecrease.Bytecode
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS ExponentialDecrease shared proof foundation

Contract-wide selector notation and constants for the optimized runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.ExponentialDecrease

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev stairstepSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def stairstepSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xe6, 0xfd, 0x60, 0x4c]⟩ -- cut()
  | 1 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 2 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 3 => ⟨#[0x48, 0x7a, 0x23, 0x95]⟩ -- price(uint256,uint256)
  | 4 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)


theorem stairstepUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_uint256 evm slot))

theorem stairstepUint256GetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = exponentialDecreaseBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD exponentialDecreaseBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf exponentialDecreaseBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf exponentialDecreaseBytecode routine slot)
    (hroutine : (D_J exponentialDecreaseBytecode 0).contains routine = true)
    (hreturnJd : (D_J exponentialDecreaseBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf exponentialDecreaseBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))]))) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  have hret := RD.solcWordGetterExternal
    (code := exponentialDecreaseBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret exponentialDecreaseBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    simpa [solcSlotWordAt] using hret
  exact hret'.reEquivExecution hcode hdispatch hdecode hbody henc


/-! ### LOG2

The reasoning library has LOG1/LOG3/LOG4 combinators; this contract emits two-topic auth logs.
-/


/-! ### CODECOPY-backed `Error(string)` revert tail

This optimized artifact keeps the long auth error string in the deployed code and copies it
into the ABI error payload with `CODECOPY`.
-/


def stairstepAuthErrorMem (mem : ByteArray) : ByteArray :=
  exponentialDecreaseBytecode.write 1275
    (solcErrorStringMem2 (⟨34⟩ : UInt256) mem) 196 34

theorem stairstepAuthErrorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (stairstepAuthErrorMem mem).size = 230 := by
  unfold stairstepAuthErrorMem
  rw [show 196 = (solcErrorStringMem2 (⟨34⟩ : UInt256) mem).size by
    rw [solcErrorStringMem2_size (⟨34⟩ : UInt256) hmem]]
  rw [write_end_size_from exponentialDecreaseBytecode
    (solcErrorStringMem2 (⟨34⟩ : UInt256) mem) 1275 34 (by decide) (by native_decide)]
  rw [solcErrorStringMem2_size (⟨34⟩ : UInt256) hmem]

theorem stairstepAuthErrorMem_read64 {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (stairstepAuthErrorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold stairstepAuthErrorMem
  rw [show 196 = (solcErrorStringMem2 (⟨34⟩ : UInt256) mem).size by
    rw [solcErrorStringMem2_size (⟨34⟩ : UInt256) hmem]]
  rw [write_read_below_end_from exponentialDecreaseBytecode
    (solcErrorStringMem2 (⟨34⟩ : UInt256) mem) 1275 34 64 (by decide)
    (by native_decide)
    (by rw [solcErrorStringMem2_size (⟨34⟩ : UInt256) hmem]; omega)]
  exact solcErrorStringMem2_read64 (⟨34⟩ : UInt256) hmem hread64

theorem stairstepAuthErrorMem_mload64 {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (stairstepAuthErrorMem mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((stairstepAuthErrorMem mem).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [stairstepAuthErrorMem_size hmem]; decide) (stairstepAuthErrorMem_read64 hmem hread64)

@[reducible] def stairstepAuthCodecopyRevertTailWf (pc : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p7 := p3 + UInt256.ofNat 4
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p27 := p25 + UInt256.ofNat 2
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p36 := p33 + UInt256.ofNat 3
  let p38 := p36 + UInt256.ofNat 2
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p42 := p40 + UInt256.ofNat 2
  let p43 := p42 + ⟨1⟩
  let p44 := p43 + ⟨1⟩
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p48 := p46 + UInt256.ofNat 2
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p51 := p50 + ⟨1⟩
  let p52 := p51 + ⟨1⟩
  let p53 := p52 + ⟨1⟩
  decode exponentialDecreaseBytecode pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode exponentialDecreaseBytecode p2 = some (.MLOAD, .none)
  ∧ decode exponentialDecreaseBytecode p3 =
      some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode exponentialDecreaseBytecode p7 =
      some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode exponentialDecreaseBytecode p9 = some (.SHL, .none)
  ∧ decode exponentialDecreaseBytecode p10 = some (.DUP2, .none)
  ∧ decode exponentialDecreaseBytecode p11 = some (.MSTORE, .none)
  ∧ decode exponentialDecreaseBytecode p12 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode exponentialDecreaseBytecode p14 = some (.ADD, .none)
  ∧ decode exponentialDecreaseBytecode p15 = some (.DUP1, .none)
  ∧ decode exponentialDecreaseBytecode p16 = some (.DUP1, .none)
  ∧ decode exponentialDecreaseBytecode p17 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode exponentialDecreaseBytecode p19 = some (.ADD, .none)
  ∧ decode exponentialDecreaseBytecode p20 = some (.DUP3, .none)
  ∧ decode exponentialDecreaseBytecode p21 = some (.DUP2, .none)
  ∧ decode exponentialDecreaseBytecode p22 = some (.SUB, .none)
  ∧ decode exponentialDecreaseBytecode p23 = some (.DUP3, .none)
  ∧ decode exponentialDecreaseBytecode p24 = some (.MSTORE, .none)
  ∧ decode exponentialDecreaseBytecode p25 =
      some (.Push .PUSH1, some (⟨34⟩, 1))
  ∧ decode exponentialDecreaseBytecode p27 = some (.DUP2, .none)
  ∧ decode exponentialDecreaseBytecode p28 = some (.MSTORE, .none)
  ∧ decode exponentialDecreaseBytecode p29 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode exponentialDecreaseBytecode p31 = some (.ADD, .none)
  ∧ decode exponentialDecreaseBytecode p32 = some (.DUP1, .none)
  ∧ decode exponentialDecreaseBytecode p33 =
      some (.Push .PUSH2, some (⟨1275⟩, 2))
  ∧ decode exponentialDecreaseBytecode p36 =
      some (.Push .PUSH1, some (⟨34⟩, 1))
  ∧ decode exponentialDecreaseBytecode p38 = some (.SWAP2, .none)
  ∧ decode exponentialDecreaseBytecode p39 = some (.CODECOPY, .none)
  ∧ decode exponentialDecreaseBytecode p40 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode exponentialDecreaseBytecode p42 = some (.ADD, .none)
  ∧ decode exponentialDecreaseBytecode p43 = some (.SWAP2, .none)
  ∧ decode exponentialDecreaseBytecode p44 = some (.POP, .none)
  ∧ decode exponentialDecreaseBytecode p45 = some (.POP, .none)
  ∧ decode exponentialDecreaseBytecode p46 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode exponentialDecreaseBytecode p48 = some (.MLOAD, .none)
  ∧ decode exponentialDecreaseBytecode p49 = some (.DUP1, .none)
  ∧ decode exponentialDecreaseBytecode p50 = some (.SWAP2, .none)
  ∧ decode exponentialDecreaseBytecode p51 = some (.SUB, .none)
  ∧ decode exponentialDecreaseBytecode p52 = some (.SWAP1, .none)
  ∧ decode exponentialDecreaseBytecode p53 = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.stairstepAuthCodecopyRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc : UInt256}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD exponentialDecreaseBytecode ee g s0 pc stk mem
        (UInt256.ofNat 3) rdata acc k C)
    (hwf : stairstepAuthCodecopyRevertTailWf pc)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 6 ≤ 1024) :
    RDrev exponentialDecreaseBytecode g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd7, hd9, hd10, hd11, hd12, hd14, hd15, hd16, hd17, hd19,
      hd20, hd21, hd22, hd23, hd24, hd25, hd27, hd28, hd29, hd31, hd32, hd33,
      hd36, hd38, hd39, hd40, hd42, hd43, hd44, hd45, hd46, hd48, hd49, hd50,
      hd51, hd52, hd53⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd2
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd3
    (by simp only [List.length_cons]; omega)
  have rdPrefix0 := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd7 (by evm_ov),
    raw shl hd9 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd11 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ hd12 (by evm_ov),
    raw add hd14 (by evm_ov),
    raw dup1 hd15 (by evm_ov),
    raw dup1 hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd17 (by evm_ov),
    raw add hd19 (by evm_ov),
    raw dup3 hd20 (by evm_ov),
    raw dup2 hd21 (by evm_ov),
    raw sub hd22 (by evm_ov),
    raw dup3 hd23 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd24 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨34⟩ hd25 (by evm_ov),
    raw dup2 hd27 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨34⟩ : UInt256) mem)
      (UInt256.ofNat 7) hd28 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd29 (by evm_ov),
    raw add hd31 (by evm_ov),
    raw dup1 hd32 (by evm_ov)]
  have hcopy :
      exponentialDecreaseBytecode.write 1275
          (solcErrorStringMem2 (⟨34⟩ : UInt256) mem) 196 34 =
        stairstepAuthErrorMem mem := by
    rfl
  have rdCopy := evm_run rdPrefix0 with [
    raw push2 ⟨1275⟩ hd33 (by simp only [List.length_cons]; omega),
    raw push1 ⟨34⟩ hd36 (by simp only [List.length_cons]; omega),
    raw swap2 hd38 (by simp only [List.length_cons]; omega),
    raw codecopy 3 (stairstepAuthErrorMem mem) (UInt256.ofNat 8)
      hd39 mem_cost hcopy (by native_decide) (by evm_ov)]
  exact evm_run rdCopy with [
    raw push1 ⟨64⟩ hd40 (by evm_ov),
    raw add hd42 (by evm_ov),
    raw swap2 hd43 (by evm_ov),
    raw pop hd44 (by evm_ov),
    raw pop hd45 (by evm_ov),
    raw push1 ⟨64⟩ hd46 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hd48
      mem_cost
      (stairstepAuthErrorMem_mload64 hmem hread64)
      (by decide) (by evm_ov),
    raw dup1 hd49 (by evm_ov),
    raw swap2 hd50 (by evm_ov),
    raw sub hd51 (by evm_ov),
    raw swap1 hd52 (by evm_ov),
    raw rev 3 hd53 mem_cost (by evm_ov)]

/-! The same tail, parameterized by the string window in the deployed code. -/

def stairstepCodecopyErrorMem (offset len : UInt256)
    (mem : ByteArray) : ByteArray :=
  exponentialDecreaseBytecode.write offset.toNat
    (solcErrorStringMem2 len mem) 196 len.toNat

theorem stairstepCodecopyErrorMem_size {mem : ByteArray} (offset len : UInt256)
    (hmem : mem.size = 96) (hlen : len.toNat ≠ 0)
    (hsrc : offset.toNat + len.toNat ≤ exponentialDecreaseBytecode.size) :
    (stairstepCodecopyErrorMem offset len mem).size = 196 + len.toNat := by
  unfold stairstepCodecopyErrorMem
  rw [show 196 = (solcErrorStringMem2 len mem).size by
    rw [solcErrorStringMem2_size len hmem]]
  rw [write_end_size_from exponentialDecreaseBytecode
    (solcErrorStringMem2 len mem) offset.toNat len.toNat hlen hsrc]

theorem stairstepCodecopyErrorMem_read64 {mem : ByteArray} (offset len : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlen : len.toNat ≠ 0)
    (hsrc : offset.toNat + len.toNat ≤ exponentialDecreaseBytecode.size) :
    (stairstepCodecopyErrorMem offset len mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold stairstepCodecopyErrorMem
  rw [show 196 = (solcErrorStringMem2 len mem).size by
    rw [solcErrorStringMem2_size len hmem]]
  rw [write_read_below_end_from exponentialDecreaseBytecode
    (solcErrorStringMem2 len mem) offset.toNat len.toNat 64 hlen hsrc
    (by rw [solcErrorStringMem2_size len hmem]; omega)]
  exact solcErrorStringMem2_read64 len hmem hread64

theorem stairstepCodecopyErrorMem_mload64 {mem : ByteArray} (offset len : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlen : len.toNat ≠ 0)
    (hsrc : offset.toNat + len.toNat ≤ exponentialDecreaseBytecode.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (stairstepCodecopyErrorMem offset len mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((stairstepCodecopyErrorMem offset len mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [stairstepCodecopyErrorMem_size offset len hmem hlen hsrc]
      omega)
    (stairstepCodecopyErrorMem_read64 offset len hmem hread64 hlen hsrc)

@[reducible] def stairstepCodecopyRevertTailWf
    (pc offset len : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p7 := p3 + UInt256.ofNat 4
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p27 := p25 + UInt256.ofNat 2
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p36 := p33 + UInt256.ofNat 3
  let p38 := p36 + UInt256.ofNat 2
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p42 := p40 + UInt256.ofNat 2
  let p43 := p42 + ⟨1⟩
  let p44 := p43 + ⟨1⟩
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p48 := p46 + UInt256.ofNat 2
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p51 := p50 + ⟨1⟩
  let p52 := p51 + ⟨1⟩
  let p53 := p52 + ⟨1⟩
  decode exponentialDecreaseBytecode pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode exponentialDecreaseBytecode p2 = some (.MLOAD, .none)
  ∧ decode exponentialDecreaseBytecode p3 =
      some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode exponentialDecreaseBytecode p7 =
      some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode exponentialDecreaseBytecode p9 = some (.SHL, .none)
  ∧ decode exponentialDecreaseBytecode p10 = some (.DUP2, .none)
  ∧ decode exponentialDecreaseBytecode p11 = some (.MSTORE, .none)
  ∧ decode exponentialDecreaseBytecode p12 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode exponentialDecreaseBytecode p14 = some (.ADD, .none)
  ∧ decode exponentialDecreaseBytecode p15 = some (.DUP1, .none)
  ∧ decode exponentialDecreaseBytecode p16 = some (.DUP1, .none)
  ∧ decode exponentialDecreaseBytecode p17 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode exponentialDecreaseBytecode p19 = some (.ADD, .none)
  ∧ decode exponentialDecreaseBytecode p20 = some (.DUP3, .none)
  ∧ decode exponentialDecreaseBytecode p21 = some (.DUP2, .none)
  ∧ decode exponentialDecreaseBytecode p22 = some (.SUB, .none)
  ∧ decode exponentialDecreaseBytecode p23 = some (.DUP3, .none)
  ∧ decode exponentialDecreaseBytecode p24 = some (.MSTORE, .none)
  ∧ decode exponentialDecreaseBytecode p25 =
      some (.Push .PUSH1, some (len, 1))
  ∧ decode exponentialDecreaseBytecode p27 = some (.DUP2, .none)
  ∧ decode exponentialDecreaseBytecode p28 = some (.MSTORE, .none)
  ∧ decode exponentialDecreaseBytecode p29 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode exponentialDecreaseBytecode p31 = some (.ADD, .none)
  ∧ decode exponentialDecreaseBytecode p32 = some (.DUP1, .none)
  ∧ decode exponentialDecreaseBytecode p33 =
      some (.Push .PUSH2, some (offset, 2))
  ∧ decode exponentialDecreaseBytecode p36 =
      some (.Push .PUSH1, some (len, 1))
  ∧ decode exponentialDecreaseBytecode p38 = some (.SWAP2, .none)
  ∧ decode exponentialDecreaseBytecode p39 = some (.CODECOPY, .none)
  ∧ decode exponentialDecreaseBytecode p40 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode exponentialDecreaseBytecode p42 = some (.ADD, .none)
  ∧ decode exponentialDecreaseBytecode p43 = some (.SWAP2, .none)
  ∧ decode exponentialDecreaseBytecode p44 = some (.POP, .none)
  ∧ decode exponentialDecreaseBytecode p45 = some (.POP, .none)
  ∧ decode exponentialDecreaseBytecode p46 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode exponentialDecreaseBytecode p48 = some (.MLOAD, .none)
  ∧ decode exponentialDecreaseBytecode p49 = some (.DUP1, .none)
  ∧ decode exponentialDecreaseBytecode p50 = some (.SWAP2, .none)
  ∧ decode exponentialDecreaseBytecode p51 = some (.SUB, .none)
  ∧ decode exponentialDecreaseBytecode p52 = some (.SWAP1, .none)
  ∧ decode exponentialDecreaseBytecode p53 = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.stairstepCodecopyRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc : UInt256}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (offset len : UInt256)
    (h : RD exponentialDecreaseBytecode ee g s0 pc stk mem
        (UInt256.ofNat 3) rdata acc k C)
    (hwf : stairstepCodecopyRevertTailWf pc offset len)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlen : len.toNat ≠ 0)
    (hsrc : offset.toNat + len.toNat ≤ exponentialDecreaseBytecode.size)
    (hmcost :
      Cₘ (UInt256.ofNat
          (MachineState.M (UInt256.ofNat 7).toNat 196 len.toNat)) -
        Cₘ (UInt256.ofNat 7) = 3)
    (hawout :
      UInt256.ofNat (MachineState.M (UInt256.ofNat 7).toNat 196 len.toNat) =
        UInt256.ofNat 8)
    (hov : stk.length + 6 ≤ 1024) :
    RDrev exponentialDecreaseBytecode g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd7, hd9, hd10, hd11, hd12, hd14, hd15, hd16, hd17, hd19,
      hd20, hd21, hd22, hd23, hd24, hd25, hd27, hd28, hd29, hd31, hd32, hd33,
      hd36, hd38, hd39, hd40, hd42, hd43, hd44, hd45, hd46, hd48, hd49, hd50,
      hd51, hd52, hd53⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd2
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd3
    (by simp only [List.length_cons]; omega)
  have rdPrefix0 := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd7 (by evm_ov),
    raw shl hd9 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd11 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ hd12 (by evm_ov),
    raw add hd14 (by evm_ov),
    raw dup1 hd15 (by evm_ov),
    raw dup1 hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd17 (by evm_ov),
    raw add hd19 (by evm_ov),
    raw dup3 hd20 (by evm_ov),
    raw dup2 hd21 (by evm_ov),
    raw sub hd22 (by evm_ov),
    raw dup3 hd23 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd24 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd25 (by evm_ov),
    raw dup2 hd27 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd28 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd29 (by evm_ov),
    raw add hd31 (by evm_ov),
    raw dup1 hd32 (by evm_ov)]
  have hcopy :
      exponentialDecreaseBytecode.write offset.toNat
          (solcErrorStringMem2 len mem) 196 len.toNat =
        stairstepCodecopyErrorMem offset len mem := by
    rfl
  have rdCopy := evm_run rdPrefix0 with [
    raw push2 offset hd33 (by simp only [List.length_cons]; omega),
    raw push1 len hd36 (by simp only [List.length_cons]; omega),
    raw swap2 hd38 (by simp only [List.length_cons]; omega),
    raw codecopy 3 (stairstepCodecopyErrorMem offset len mem) (UInt256.ofNat 8)
      hd39
      (by
        simpa [M, show
          ({ val := 32 } + ({ val := 32 } + ({ val := 4 } + { val := 128 })) : UInt256).toNat =
            196 by native_decide] using hmcost)
      hcopy
      (by
        simpa [show
          ({ val := 32 } + ({ val := 32 } + ({ val := 4 } + { val := 128 })) : UInt256).toNat =
            196 by native_decide] using hawout)
      (by evm_ov)]
  exact evm_run rdCopy with [
    raw push1 ⟨64⟩ hd40 (by evm_ov),
    raw add hd42 (by evm_ov),
    raw swap2 hd43 (by evm_ov),
    raw pop hd44 (by evm_ov),
    raw pop hd45 (by evm_ov),
    raw push1 ⟨64⟩ hd46 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hd48
      mem_cost
      (stairstepCodecopyErrorMem_mload64 offset len hmem hread64 hlen hsrc)
      (by decide) (by evm_ov),
    raw dup1 hd49 (by evm_ov),
    raw swap2 hd50 (by evm_ov),
    raw sub hd51 (by evm_ov),
    raw swap1 hd52 (by evm_ov),
    raw rev 3 hd53 mem_cost (by evm_ov)]

end Benchmarks.Dss.ExponentialDecrease
