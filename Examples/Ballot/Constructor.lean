import Examples.Ballot.Bytecode
import Examples.Ballot.Spec
import Examples.Ballot.Common
import Reasoning.Initcode
import Reasoning.ABI
import Reasoning.Reach
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Dispatch
import Reasoning.JumpDest

/-!
# Ballot — constructor / creation-code equivalence

This file proves the creation-code half of `Ballot`'s contract equivalence: the real solc
`--optimize --evm-version shanghai` **creation bytecode** refines the Solm `constructorDecl`.

The creation code is `ballotCtorPrefix ++ ballotBytecode`: the first 442 bytes are the genuine
solc constructor (callvalue guard, `bytes32[]` ABI decoder, `chairperson = msg.sender`,
`voters[chairperson].weight = 1`, the `for` loop pushing `Proposal`s, then `CODECOPY`/`RETURN` of
the runtime).  The embedded runtime window is pinned to the repo's trusted `ballotBytecode` (only the
non-executable trailing metadata hash differs between solc invocations), so the deployed code returned
by the constructor is *exactly* the runtime the existing `ballotCorrect` proof is about.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

namespace Ballot

/-- The genuine solc constructor code (creation code minus the embedded runtime + metadata). -/
def ballotCtorPrefix : ByteArray :=
  ⟨#[
    96, 128, 96, 64, 82, 52, 128, 21, 97, 0, 15, 87, 95, 95, 253, 91, 80, 96, 64, 81,
    97, 9, 64, 56, 3, 128, 97, 9, 64, 131, 57, 129, 1, 96, 64, 129, 144, 82, 97, 0,
    46, 145, 97, 0, 210, 86, 91, 95, 128, 84, 96, 1, 96, 1, 96, 160, 27, 3, 25, 22,
    51, 144, 129, 23, 130, 85, 129, 82, 96, 1, 96, 32, 129, 144, 82, 96, 64, 130, 32, 85,
    91, 129, 81, 129, 16, 21, 97, 0, 183, 87, 96, 2, 96, 64, 81, 128, 96, 64, 1, 96,
    64, 82, 128, 132, 132, 129, 81, 129, 16, 97, 0, 120, 87, 97, 0, 120, 97, 1, 153, 86,
    91, 96, 32, 144, 129, 2, 145, 144, 145, 1, 129, 1, 81, 130, 82, 95, 145, 129, 1, 130,
    144, 82, 131, 84, 96, 1, 129, 129, 1, 134, 85, 148, 131, 82, 145, 129, 144, 32, 131, 81,
    96, 2, 144, 147, 2, 1, 145, 130, 85, 145, 144, 145, 1, 81, 144, 130, 1, 85, 1, 97,
    0, 80, 86, 91, 80, 80, 97, 1, 173, 86, 91, 99, 78, 72, 123, 113, 96, 224, 27, 95,
    82, 96, 65, 96, 4, 82, 96, 36, 95, 253, 91, 95, 96, 32, 130, 132, 3, 18, 21, 97,
    0, 226, 87, 95, 95, 253, 91, 129, 81, 96, 1, 96, 1, 96, 64, 27, 3, 129, 17, 21,
    97, 0, 247, 87, 95, 95, 253, 91, 130, 1, 96, 31, 129, 1, 132, 19, 97, 1, 7, 87,
    95, 95, 253, 91, 128, 81, 96, 1, 96, 1, 96, 64, 27, 3, 129, 17, 21, 97, 1, 32,
    87, 97, 1, 32, 97, 0, 190, 86, 91, 96, 64, 81, 96, 5, 130, 144, 27, 144, 96, 63,
    130, 1, 96, 31, 25, 22, 129, 1, 96, 1, 96, 1, 96, 64, 27, 3, 129, 17, 130, 130,
    16, 23, 21, 97, 1, 78, 87, 97, 1, 78, 97, 0, 190, 86, 91, 96, 64, 82, 145, 130,
    82, 96, 32, 129, 132, 1, 129, 1, 146, 144, 129, 1, 135, 132, 17, 21, 97, 1, 107, 87,
    95, 95, 253, 91, 96, 32, 133, 1, 148, 80, 91, 131, 133, 16, 21, 97, 1, 142, 87, 132,
    81, 128, 130, 82, 96, 32, 149, 134, 1, 149, 144, 147, 80, 1, 97, 1, 114, 86, 91, 80,
    150, 149, 80, 80, 80, 80, 80, 80, 86, 91, 99, 78, 72, 123, 113, 96, 224, 27, 95, 82,
    96, 50, 96, 4, 82, 96, 36, 95, 253, 91, 97, 7, 134, 128, 97, 1, 186, 95, 57, 95,
    243, 254
  ]⟩

/-- Full creation/initcode: real constructor prefix followed by the deployed runtime. -/
def ballotInitcode : ByteArray := ballotCtorPrefix ++ ballotBytecode

theorem ballotCtorPrefix_size : ballotCtorPrefix.size = 442 := by decide +native

theorem ballotBytecode_size : ballotBytecode.size = 1926 := by decide +native

theorem ballotInitcode_size : ballotInitcode.size = 2368 := by decide +native

/-- The constructor copies the embedded runtime window — which is *exactly* `ballotBytecode`. -/
theorem ballotInitcode_runtime_window :
    ballotInitcode.extract 442 (442 + 1926) = ballotBytecode := by decide +native

/-! ## Decode automation for the symbolic argument tail

`I.code` is `ballotInitcode ++ argBytes` where `argBytes` is the (symbolic) ABI-encoded constructor
argument.  Every instruction lives in the concrete `ballotInitcode` prefix (`pc < 442`), so each
`decode (ballotInitcode ++ argBytes) pc` is tail-independent and reduces to a concrete
`decode ballotInitcode pc`.  The `ctor_decode` tactic discharges these decode obligations inside
`evm_run … with [raw … (by ctor_decode) …]` steps. -/

theorem ballotInitcode_decode_append (tail : ByteArray) (pc : UInt256) (hpc : pc.toNat < 442) :
    decode (ballotInitcode ++ tail) pc = decode ballotInitcode pc :=
  Reasoning.Theory.decode_append_left_window ballotInitcode tail pc
    (by rw [ballotInitcode_size]; omega) (by rw [ballotInitcode_size]; norm_num)

/-- Discharge `decode (ballotInitcode ++ argBytes) ⟨pc⟩ = op` for a concrete `pc < 442`. -/
macro "ctor_decode" : tactic =>
  `(tactic| (rw [ballotInitcode_decode_append _ _ (by decide)]; decide +native))

/-- Discharge `(D_J (ballotInitcode ++ argBytes) 0).contains ⟨pc⟩ = true` for an in-prefix
    `JUMPDEST`: the destination is valid in the concrete `ballotInitcode` and survives the symbolic
    argument tail via `D_J_contains_append_left`. -/
macro "ctor_jd" : tactic =>
  `(tactic| (apply Reasoning.Theory.D_J_contains_append_left; decide +native))

/-- Smoke test: the callvalue-guard target (`pc 15`) and the decoder entry (`pc 0xd2`) are valid
    jump destinations regardless of the appended argument bytes. -/
example (tail : ByteArray) : (D_J (ballotInitcode ++ tail) 0).contains ⟨15⟩ = true := by ctor_jd

example (tail : ByteArray) : (D_J (ballotInitcode ++ tail) 0).contains ⟨210⟩ = true := by ctor_jd

open Lean in
/-- `ctor_run` mirrors `evm_run` but discharges the decode obligation with `ctor_decode` (which
    handles the symbolic argument tail) instead of `decide +native`.  Identical threading otherwise. -/
macro "ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by ctor_decode) $(args[0]!) $(args[1]!) (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

/-- Smoke test: the decode of the very first instruction (`PUSH1 0x80`) and the first `CODECOPY`
    resolve regardless of the appended argument bytes. -/
example (tail : ByteArray) :
    decode (ballotInitcode ++ tail) ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by ctor_decode

example (tail : ByteArray) :
    decode (ballotInitcode ++ tail) ⟨30⟩ = some (.CODECOPY, .none) := by ctor_decode

/-! ## Deployment shape

`ballotConfig.selfDeployment` ABI-encodes the constructor's sole `bytes32[]` argument and appends it
to the initcode.  Any successful deployment therefore has `args = [.array vs]` and the appended bytes
are `offset(0x20) ‖ length ‖ elements`. -/

theorem ballotDeployment_shape {args : List Value} {deployedInitcode : ByteArray} :
    ballotConfig.selfDeployment ballotInitcode args = some deployedInitcode →
    ∃ (vs : List Value) (elemBytes : List UInt8),
      args = [.array vs]
        ∧ ABI.encodeABIStaticArrayElems? Ballot.bytes32 vs = some elemBytes
        ∧ deployedInitcode
            = ballotInitcode
                ++ (ABI.natBytes 32 ++ (ABI.natBytes vs.length ++ elemBytes)).toByteArray := by
  intro h
  simp only [ballotConfig, genSolidityConstructorDeployment, ballotContract, Ballot.constructorDecl,
    List.map_cons, List.map_nil, Option.bind_eq_bind] at h
  match args with
  | [] =>
      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.abiTupleHeadSize?,
        ABI.isDynamicABIType] at h
  | [.array vs] =>
      rw [Reasoning.Theory.encodeABIValues_single_dynArray_static
        (by decide : ABI.isDynamicABIType Ballot.bytes32 = false)] at h
      cases he : ABI.encodeABIStaticArrayElems? Ballot.bytes32 vs with
      | none => rw [he] at h; simp at h
      | some elemBytes =>
          rw [he] at h
          simp only [Option.bind_some, Option.some.injEq] at h
          exact ⟨vs, elemBytes, rfl, he, h.symm⟩
  | [.int _] | [.bool _] | [.address _] | [.fixedBytes _ _] | [.bytes _] | [.tuple _]
  | [.struct _ _] | [.unit] | [.storageRef _ _] =>
      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.abiTupleHeadSize?,
        ABI.isDynamicABIType, ABI.encodeABIValue?] at h
  | _ :: _ :: _ =>
      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.abiTupleHeadSize?,
        ABI.isDynamicABIType] at h

/-! ## Prologue trace (pc 0 → ABI decoder entry at pc 0xd2)

The constructor prologue stores the free-memory pointer, reverts on non-zero call value (the
non-payable guard), `CODECOPY`s the appended ABI arguments into memory at `0x80`, sets the free
pointer past them, and `JUMP`s into solc's `bytes32[]` ABI decoder at pc 210 with
`[dataStart=0x80, dataEnd, retAddr=0x2e]` on the stack.  The argument length `0x0940 - CODESIZE`
(= `argBytes.size`) and the copied memory are carried symbolically. -/

/-- The decoded argument length the constructor computes: `CODESIZE − 0x0940 = argBytes.size`. -/
noncomputable def ballotArgLen (argBytes : ByteArray) : UInt256 :=
  (UInt256.ofNat (ballotInitcode ++ argBytes).size).sub ⟨2368⟩

/-- Active-words count when the prologue jumps into the ABI decoder. -/
noncomputable def ballotDecoderAW (argBytes : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 128 (ballotArgLen argBytes).toNat)).toNat 64 32)

/-- Memory image when the prologue jumps into the ABI decoder: the free pointer (`0x80 + argLen`) at
    `0x40`, and the appended ABI argument bytes copied to `[0x80, …)`. -/
noncomputable def ballotDecoderMem (argBytes : ByteArray) : ByteArray :=
  (⟨128⟩ + ballotArgLen argBytes).toByteArray.write 0
    ((ballotInitcode ++ argBytes).write 2368 solcFreePtrMem 128 (ballotArgLen argBytes).toNat) 64 32

set_option maxHeartbeats 2000000 in
/-- The genuine solc prologue drives from `initState` (pc 0) to the ABI-decoder entry (pc 210),
    provided the creation message carries no value (`weiValue = 0`; the non-payable guard reverts
    otherwise). -/
theorem ballotReachDecoder
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256} (argBytes : ByteArray)
    (hcode : I.code = ballotInitcode ++ argBytes) (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨210⟩
      [⟨128⟩, ⟨128⟩ + ballotArgLen argBytes, ⟨46⟩]
      (ballotDecoderMem argBytes) (ballotDecoderAW argBytes) ByteArray.empty (cA, σ) k C := by
  simp only [ballotDecoderMem, ballotDecoderAW, ballotArgLen]
  have rd0 : RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨0⟩ []
      ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 :=
    RD.initState hcode
  set code := ballotInitcode ++ argBytes with hcodeDef
  have h128 : ((⟨128⟩ : UInt256)).toNat = 128 := by decide
  have h64 : ((⟨64⟩ : UInt256)).toNat = 64 := by decide
  set aL := ((UInt256.ofNat code.size).sub ⟨2368⟩).toNat with haL
  have rd30 := ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by ctor_decode) mem_cost
      (by rw [h64]; rfl) (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨15⟩,
    jumpiT (by rw [hwv]; decide) (by ctor_jd),
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by ctor_decode) mem_cost solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨2368⟩, codesize, sub, dup1, push2 ⟨2368⟩, dup4,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 128 aL)) - Cₘ (UInt256.ofNat 3))
      (code.write 2368 solcFreePtrMem 128 aL)
      (UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 128 aL))
      (by ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ, h128, haL])
      rfl (by rw [h128]) (by evm_ov) ]
  set AW1 := UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 128 aL) with hAW1
  have rd45 := ctor_run rd30 with [
    dup2, add, push1 ⟨64⟩, dup2, swap1,
    raw mstore
      (Cₘ (UInt256.ofNat (MachineState.M AW1.toNat 64 32)) - Cₘ AW1)
      ((⟨128⟩ + ((UInt256.ofNat code.size).sub ⟨2368⟩)).toByteArray.write 0
        (code.write 2368 solcFreePtrMem 128 aL) 64 32)
      (UInt256.ofNat (MachineState.M AW1.toNat 64 32))
      (by ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, h64])
      (by rw [h64]) (by rw [h64]) (by evm_ov),
    push2 ⟨46⟩, swap2, push2 ⟨210⟩, jump (by ctor_jd) ]
  exact ⟨_, _, rd45⟩

/-! ## Decoder memory — clean characterization

The decoder reads the ABI argument bytes back out of `ballotDecoderMem`.  Those reads compose two
writes (the free-pointer store at `0x40`, the argument `CODECOPY` at `0x80`), so we first reduce the
inner copy to a clean append `(solcFreePtrMem ++ zeroes 32) ++ argBytes` and pin the computed length
`argLen = CODESIZE − 0x0940` to `argBytes.size`. -/

/-- The constructor's computed argument length is exactly the appended ABI bytes' length (no `UInt256`
    wrap, given the deployed code fits a word — true of any real creation transaction). -/
theorem ballotArgLen_toNat (argBytes : ByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) :
    (ballotArgLen argBytes).toNat = argBytes.size := by
  have hsize : (ballotInitcode ++ argBytes).size = 2368 + argBytes.size := by
    rw [ByteArray.size_append, ballotInitcode_size]
  have hofnat : (UInt256.ofNat (ballotInitcode ++ argBytes).size).toNat
      = (ballotInitcode ++ argBytes).size := UInt256.toNat_ofNat_of_lt hsz
  unfold ballotArgLen
  rw [usub_toNat (by rw [hofnat, hsize, show (⟨2368⟩ : UInt256).toNat = 2368 from by decide]; omega),
    hofnat, hsize, show (⟨2368⟩ : UInt256).toNat = 2368 from by decide]
  omega

/-- The inner argument-`CODECOPY` lands entirely past `solcFreePtrMem`'s end (`96 < 128`): the write
    pads `[96,128)` with zeros and appends the argument bytes. -/
theorem ballotInnerMem_eq (argBytes : ByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (hpos : 0 < argBytes.size) :
    (ballotInitcode ++ argBytes).write 2368 solcFreePtrMem 128 (ballotArgLen argBytes).toNat
      = (solcFreePtrMem ++ ffi.ByteArray.zeroes 32) ++ argBytes := by
  rw [ballotArgLen_toNat argBytes hsz]
  have hcodeS : (ballotInitcode ++ argBytes).size = 2368 + argBytes.size := by
    rw [ByteArray.size_append, ballotInitcode_size]
  have hbiD : ballotInitcode.data.size = 2368 := ballotInitcode_size
  have hsfpD : solcFreePtrMem.data.size = 96 := solcFreePtrMem_size
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by omega : ¬ argBytes.size = 0),
      if_neg (show ¬ 2368 ≥ (ballotInitcode ++ argBytes).size from by omega)]
  have e1 : min argBytes.size ((ballotInitcode ++ argBytes).size - 2368) = argBytes.size := by omega
  have e2 : min solcFreePtrMem.size (128 + argBytes.size) = 96 := by rw [solcFreePtrMem_size]; omega
  simp only [ByteArray.data_copySlice, ByteArray.data_append, e1, solcFreePtrMem_size,
    show (128 : ℕ) - 96 = 32 from by norm_num,
    show min 96 (128 + argBytes.size) - (128 + argBytes.size) = 0 from by omega]
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
        rw [zeroes_zero (n := 0) (by rfl)]; rfl]
  have hz32 : (ffi.ByteArray.zeroes 32).data.size = 32 := by
    show (ffi.ByteArray.zeroes 32).size = 32
    exact zeroes_ofNat_size 32 (by norm_num)
  simp only [Array.append_empty, Nat.add_zero]
  have ext1 : (solcFreePtrMem.data ++ (ffi.ByteArray.zeroes 32).data).extract 0 128
      = solcFreePtrMem.data ++ (ffi.ByteArray.zeroes 32).data :=
    Array.extract_eq_self_of_le (by rw [Array.size_append, hsfpD, hz32])
  have ext2 : (ballotInitcode.data ++ argBytes.data).extract 2368 (2368 + argBytes.size)
      = argBytes.data := by
    rw [show (2368 : ℕ) = ballotInitcode.data.size from hbiD.symm, Array.extract_append_right]
    exact Array.extract_eq_self_of_le (Nat.le_refl _)
  rw [ext1, ext2,
    Array.extract_empty_of_size_le_start (by rw [Array.size_append, hsfpD, hz32]; omega),
    Array.append_empty]

/-- A 32-byte read from the decoder's working memory at `0x80 + k` returns the `k`-th window of the
    ABI argument bytes — the decoder reads the offset (`k=0`), the length (`k=0x20`), and each element
    (`k = 0x40 + 0x20·i`) straight out of the copied arguments. -/
theorem ballotDecoderMem_read (argBytes : ByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (hpos : 0 < argBytes.size)
    (k : ℕ) (hk : k + 32 ≤ argBytes.size) :
    (ballotDecoderMem argBytes).readWithPadding (128 + k) 32 = argBytes.readWithPadding k 32 := by
  have hbase : (solcFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
  unfold ballotDecoderMem
  rw [ballotInnerMem_eq argBytes hsz hpos,
      write32_read_above _ _ 64 (128 + k) (by simp)
        (by rw [ByteArray.size_append, hbase]; omega) (by omega)
        (by rw [ByteArray.size_append, hbase]; omega),
      readWithPadding_eq_extract _ _ (by rw [ByteArray.size_append, hbase]; omega),
      extract_append_right_window _ _ _ _ (by rw [hbase]; omega), hbase,
      show (128 + k - 128 : ℕ) = k from by omega,
      show (128 + k + 32 - 128 : ℕ) = k + 32 from by omega,
      ← readWithPadding_eq_extract _ _ (by omega)]

/-- The big-endian value of a 32-byte ABI `natBytes` word is the number itself. -/
theorem fromByteArrayBigEndian_natBytes (n : ℕ) (hn : n < UInt256.size) :
    fromByteArrayBigEndian ((ABI.natBytes n).toByteArray) = n := by
  unfold ABI.natBytes
  rw [word_toBytesBE_toByteArray_eq_toByteArray, fromByteArrayBigEndian_toByteArray]
  exact UInt256.toNat_ofNat_of_lt hn

theorem natBytes_toByteArray_size (n : ℕ) : (ABI.natBytes n).toByteArray.size = 32 := by
  unfold ABI.natBytes; exact word_toBytesBE_toByteArray_size _

/-- Every successful ABI encoding of a `bytes32` value is exactly one 32-byte word. -/
theorem encodeABIValue_bytes32_length {v : Value} {bs : List UInt8}
    (h : ABI.encodeABIValue? Ballot.bytes32 v = some bs) : bs.length = 32 := by
  cases v <;> simp [Ballot.bytes32, ABI.encodeABIValue?, ABI.encodeABIWord?] at h
  case fixedBytes n bytes =>
    rcases h with ⟨⟨rfl, hlen⟩, hbs⟩
    subst bs
    simp [ABI.zeroBytes, hlen]

/-- A successful ABI encoding of a `bytes32[]` element tail has one 32-byte word per element. -/
theorem encodeABIStaticArrayElems_bytes32_length {vs : List Value} {elemBytes : List UInt8}
    (h : ABI.encodeABIStaticArrayElems? Ballot.bytes32 vs = some elemBytes) :
    elemBytes.length = 32 * vs.length := by
  induction vs generalizing elemBytes with
  | nil =>
      simp [ABI.encodeABIStaticArrayElems?] at h
      subst elemBytes
      simp
  | cons v rest ih =>
      simp [ABI.encodeABIStaticArrayElems?] at h
      rcases hv : ABI.encodeABIValue? Ballot.bytes32 v with _ | enc <;> simp [hv] at h
      rcases hr : ABI.encodeABIStaticArrayElems? Ballot.bytes32 rest with _ | encRest <;>
        simp [hr] at h
      subst elemBytes
      have henc := encodeABIValue_bytes32_length (v := v) (bs := enc) hv
      have hrest := ih hr
      simp [henc, hrest]
      omega

/-- Reading the first 32-byte word of `natBytes m ‖ rest` returns `natBytes m`. -/
theorem natBytes_read0 (m : ℕ) (rest : List UInt8) :
    ((ABI.natBytes m ++ rest).toByteArray).readWithPadding 0 32 = (ABI.natBytes m).toByteArray := by
  have hm := natBytes_toByteArray_size m
  rw [List.toByteArray_append,
      readWithPadding_eq_extract _ _ (by rw [ByteArray.size_append, hm]; omega),
      extract_append_left _ _ _ _ (by rw [hm])]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (le_of_eq hm)

/-- Reading the second 32-byte word of `natBytes a ‖ natBytes b ‖ rest` returns `natBytes b`. -/
theorem natBytes_read1 (a b : ℕ) (rest : List UInt8) :
    ((ABI.natBytes a ++ (ABI.natBytes b ++ rest)).toByteArray).readWithPadding 32 32
      = (ABI.natBytes b).toByteArray := by
  have ha := natBytes_toByteArray_size a
  have hb := natBytes_toByteArray_size b
  rw [List.toByteArray_append, List.toByteArray_append,
      readWithPadding_eq_extract _ _
        (by rw [ByteArray.size_append, ByteArray.size_append, ha, hb]; omega),
      extract_append_right_window _ _ _ _ (le_of_eq ha), ha,
      show (32 - 32 : ℕ) = 0 from rfl, show (32 + 32 - 32 : ℕ) = 32 from rfl,
      extract_append_left _ _ _ _ (by rw [hb])]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (le_of_eq hb)

/-- The decoder's offset `MLOAD` at `mem[0x80]` reads the ABI offset word `m` (`= 0x20`). -/
theorem ballotDecoderMem_offsetVal (m : ℕ) (rest : List UInt8)
    (hsz : (ballotInitcode ++ (ABI.natBytes m ++ rest).toByteArray).size < UInt256.size)
    (hpos : 0 < (ABI.natBytes m ++ rest).toByteArray.size) (hm : m < UInt256.size) :
    fromByteArrayBigEndian
        ((ballotDecoderMem ((ABI.natBytes m ++ rest).toByteArray)).readWithPadding 128 32) = m := by
  have hrd := ballotDecoderMem_read ((ABI.natBytes m ++ rest).toByteArray) hsz hpos 0
    (by have := natBytes_toByteArray_size m; rw [List.toByteArray_append, ByteArray.size_append]; omega)
  simp only [Nat.add_zero] at hrd
  rw [hrd, natBytes_read0, fromByteArrayBigEndian_natBytes m hm]

/-- The decoder's length `MLOAD` at `mem[0xa0]` reads the array length word `b` (`= n`). -/
theorem ballotDecoderMem_lengthVal (a b : ℕ) (rest : List UInt8)
    (hsz : (ballotInitcode ++ (ABI.natBytes a ++ (ABI.natBytes b ++ rest)).toByteArray).size
            < UInt256.size)
    (hpos : 0 < (ABI.natBytes a ++ (ABI.natBytes b ++ rest)).toByteArray.size) (hb : b < UInt256.size) :
    fromByteArrayBigEndian
        ((ballotDecoderMem ((ABI.natBytes a ++ (ABI.natBytes b ++ rest)).toByteArray)).readWithPadding
          (128 + 32) 32) = b := by
  have hrd := ballotDecoderMem_read ((ABI.natBytes a ++ (ABI.natBytes b ++ rest)).toByteArray)
    hsz hpos 32
    (by have ha := natBytes_toByteArray_size a; have hbb := natBytes_toByteArray_size b
        rw [List.toByteArray_append, List.toByteArray_append, ByteArray.size_append,
          ByteArray.size_append]; omega)
  rw [hrd, natBytes_read1, fromByteArrayBigEndian_natBytes b hb]

/-- The decoder's working memory spans the free-pointer scratch plus the copied arguments. -/
theorem ballotDecoderMem_size (argBytes : ByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (hpos : 0 < argBytes.size) :
    (ballotDecoderMem argBytes).size = 128 + argBytes.size := by
  have hbase : ((solcFreePtrMem ++ ffi.ByteArray.zeroes 32) ++ argBytes).size
      = 128 + argBytes.size := by
    rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
      zeroes_ofNat_size 32 (by norm_num)]
  unfold ballotDecoderMem
  rw [ballotInnerMem_eq argBytes hsz hpos,
    write_eq_gen _ _ 64 32 (by decide) (by rw [toByteArray_size]) (by rw [hbase]; omega)]
  simp only [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hbase]
  omega

/-- The decoder's active-words count, in closed form (the args span past `0x80`). -/
theorem ballotDecoderAW_toNat (argBytes : ByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size) :
    (ballotDecoderAW argBytes).toNat = max 3 ((159 + argBytes.size) / 32) := by
  have hargsz : argBytes.size < UInt256.size :=
    lt_of_le_of_lt (by rw [ByteArray.size_append]; omega) hsz
  unfold ballotDecoderAW
  rw [ballotArgLen_toNat argBytes hsz]
  obtain ⟨m, hm⟩ : ∃ m, argBytes.size = m + 1 := ⟨argBytes.size - 1, by omega⟩
  rw [hm] at hargsz ⊢
  simp only [MachineState.M, show (UInt256.ofNat 3).toNat = 3 from by decide]
  rw [UInt256.toNat_ofNat_of_lt (show max 3 ((128 + (m + 1) + 31) / 32) < UInt256.size from by omega),
    UInt256.toNat_ofNat_of_lt
      (show max (max 3 ((128 + (m + 1) + 31) / 32)) ((64 + 32 + 31) / 32) < UInt256.size from by omega)]
  omega

/-- A read offset `≤ 0xa0` lies within the decoder's active memory window (no `MLOAD` zero-pad). -/
theorem ballotDecoderAW_mloadBound (argBytes : ByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size)
    (a : UInt256) (ha : a.toNat ≤ 160) :
    ¬ a ≥ ballotDecoderAW argBytes * ⟨32⟩ := by
  have hszsz : 2368 + argBytes.size < UInt256.size := by
    rw [← ballotInitcode_size, ← ByteArray.size_append]; exact hsz
  have hawval := ballotDecoderAW_toNat argBytes hsz h64
  have hd := Nat.div_mul_le_self (159 + argBytes.size) 32
  have hawge : 6 ≤ (ballotDecoderAW argBytes).toNat := by rw [hawval]; omega
  have haw32 : (ballotDecoderAW argBytes).toNat * 32 < UInt256.size := by
    rw [hawval]
    have hmul := Nat.mul_le_mul_right (k := 32)
      (show max 3 ((159 + argBytes.size) / 32) ≤ (159 + argBytes.size) / 32 + 3 from by omega)
    omega
  intro hge
  have hge' : (ballotDecoderAW argBytes * ⟨32⟩).toNat ≤ a.toNat := hge
  rw [show ballotDecoderAW argBytes * ⟨32⟩ = UInt256.mul (ballotDecoderAW argBytes) ⟨32⟩ from rfl,
    u256_mul_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt haw32] at hge'
  omega

/-- The decoder's offset `MLOAD` reads exactly `UInt256.toByteArray ⟨0x20⟩` (the `mloadWordValue`
    `hread` premise). -/
theorem ballotDecoderOffsetRead (argBytes : ByteArray) (rest : List UInt8)
    (hstruct : argBytes = (ABI.natBytes 32 ++ rest).toByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (hpos : 0 < argBytes.size) :
    (ballotDecoderMem argBytes).readWithPadding 128 32 = UInt256.toByteArray (UInt256.ofNat 32) := by
  have hk : (0 : ℕ) + 32 ≤ argBytes.size := by
    rw [hstruct, List.toByteArray_append, ByteArray.size_append, natBytes_toByteArray_size]; omega
  have hrd := ballotDecoderMem_read argBytes hsz hpos 0 hk
  simp only [Nat.add_zero] at hrd
  rw [hrd, hstruct, natBytes_read0]
  unfold ABI.natBytes
  rw [word_toBytesBE_toByteArray_eq_toByteArray]
  rfl

/-- The decoder's length `MLOAD` reads `UInt256.toByteArray ⟨n⟩` (the array length word). -/
theorem ballotDecoderLengthRead (argBytes : ByteArray) (n : ℕ) (rest : List UInt8)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ rest)).toByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (hpos : 0 < argBytes.size) :
    (ballotDecoderMem argBytes).readWithPadding (128 + 32) 32 = UInt256.toByteArray (UInt256.ofNat n) := by
  have hk : 32 + 32 ≤ argBytes.size := by
    rw [hstruct, List.toByteArray_append, List.toByteArray_append, ByteArray.size_append,
      ByteArray.size_append, natBytes_toByteArray_size, natBytes_toByteArray_size]; omega
  have hrd := ballotDecoderMem_read argBytes hsz hpos 32 hk
  rw [hrd, hstruct, natBytes_read1]
  unfold ABI.natBytes
  rw [word_toBytesBE_toByteArray_eq_toByteArray]
  rfl

/-- The free-pointer `MLOAD` at `mem[0x40]` reads back the stored free pointer `0x80 + argLen` (the
    `OUTER` write of `ballotDecoderMem`, read-self via `write32_read_back`). -/
theorem ballotDecoderFreeptrRead (argBytes : ByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (hpos : 0 < argBytes.size) :
    (ballotDecoderMem argBytes).readWithPadding 64 32
      = UInt256.toByteArray (⟨128⟩ + ballotArgLen argBytes) := by
  have hinner : ((ballotInitcode ++ argBytes).write 2368 solcFreePtrMem 128
      (ballotArgLen argBytes).toNat).size = 128 + argBytes.size := by
    rw [ballotInnerMem_eq argBytes hsz hpos, ByteArray.size_append, ByteArray.size_append,
      solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
  unfold ballotDecoderMem
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size]) (by rw [hinner]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  simp [Array.extract_eq_self_of_le]

/-- A 32-byte read at offset `≤ 0x80` lies entirely inside the decoder's already-active memory, so it
    does not grow the active-words count.  Keeps the `MLOAD`/`MSTORE` gas trivial across the decoder. -/
theorem ballotDecoderAW_mloadStable (argBytes : ByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size)
    (off : ℕ) (hoff : off ≤ 160) :
    MachineState.M (ballotDecoderAW argBytes).toNat off 32 = (ballotDecoderAW argBytes).toNat := by
  have hge : 6 ≤ (ballotDecoderAW argBytes).toNat := by
    rw [ballotDecoderAW_toNat argBytes hsz h64]; omega
  unfold MachineState.M
  simp only []
  omega

/-- The decoder's first length-availability check `slt(dataEnd − headStart, 0x20)` is false (the
    appended arguments contain at least the offset + length words), so the guard `JUMPI` is taken. -/
theorem ballotDecoderValid1 (argBytes : ByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size)
    (h255 : argBytes.size < 2 ^ 255) :
    (((⟨128⟩ + ballotArgLen argBytes).sub ⟨128⟩).slt ⟨32⟩).isZero ≠ ⟨0⟩ := by
  have h128 : (⟨128⟩ : UInt256).toNat = 128 := by decide
  have hszsz : 2368 + argBytes.size < UInt256.size := by
    rw [← ballotInitcode_size, ← ByteArray.size_append]; exact hsz
  have hadd : (⟨128⟩ + ballotArgLen argBytes).toNat = 128 + argBytes.size := by
    rw [uadd_toNat, ballotArgLen_toNat argBytes hsz, h128, Nat.mod_eq_of_lt (by omega)]
  have hsub : (⟨128⟩ + ballotArgLen argBytes).sub ⟨128⟩ = ballotArgLen argBytes := by
    apply u256_inj
    rw [usub_toNat (by rw [hadd, h128]; omega), hadd, h128, ballotArgLen_toNat argBytes hsz]; omega
  rw [hsub,
    show (⟨32⟩ : UInt256) = UInt256.ofNat 32 from by decide,
    slt_lit_zero (by norm_num) (by rw [ballotArgLen_toNat argBytes hsz]; omega)
      (by rw [ballotArgLen_toNat argBytes hsz]; exact h255)]
  decide

/-! ### Remaining decoder bounds checks (offset/length ≤ 2^64-1, data-room SGT) -/

/-- The `2^64 - 1` literal built by `PUSH1 1; PUSH1 1; PUSH1 0x40; SHL; SUB`. -/
theorem u64mask_toNat :
    (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨0x40⟩) ⟨1⟩).toNat = 2 ^ 64 - 1 := by decide

/-- `GT a b` is `0` (false) when `a ≤ b`. -/
theorem ugt_eq_zero {a b : UInt256} (h : a.toNat ≤ b.toNat) : UInt256.gt a b = ⟨0⟩ := by
  show UInt256.fromBool (decide (a > b)) = ⟨0⟩
  rw [decide_eq_false (show ¬ a > b by show ¬ b.toNat < a.toNat; omega)]
  rfl

/-- The offset bound check `iszero(gt(0x20, 2^64-1))` is taken (offset `0x20 ≤ 2^64-1`). -/
theorem ballotDecoderValidOff :
    (UInt256.isZero (UInt256.gt (UInt256.ofNat 32)
      (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨0x40⟩) ⟨1⟩))) ≠ ⟨0⟩ := by
  rw [ugt_eq_zero (by rw [u64mask_toNat, ulit_toNat' _ (by decide : (32:ℕ) < UInt256.size)]; omega)]
  decide

/-- The length bound check `iszero(gt(n, 2^64-1))` is taken when the array length `n < 2^64`. -/
theorem ballotDecoderValidLen (n : ℕ) (hn : n < 2 ^ 64) :
    (UInt256.isZero (UInt256.gt (UInt256.ofNat n)
      (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨0x40⟩) ⟨1⟩))) ≠ ⟨0⟩ := by
  rw [ugt_eq_zero (by rw [u64mask_toNat, ulit_toNat' _ (lt_of_lt_of_le hn (by decide))]; omega)]
  decide

/-- The decoded array head `0x80 + 0x20 = 0xa0`. -/
theorem arrayHead_eq : (⟨128⟩ + UInt256.ofNat 32 : UInt256) = UInt256.ofNat 160 := by
  apply u256_inj
  rw [uadd_toNat, show ((⟨128⟩ : UInt256)).toNat = 128 from by decide,
    ulit_toNat' _ (by decide : (32:ℕ) < UInt256.size),
    ulit_toNat' _ (by decide : (160:ℕ) < UInt256.size)]
  decide

theorem arrayHead_toNat : (⟨128⟩ + UInt256.ofNat 32 : UInt256).toNat = 160 := by
  rw [arrayHead_eq]; exact ulit_toNat' _ (by decide)

/-- The data-room check `sgt(dataEnd, arrayHead + 0x1f)` is taken: with `argBytes.size ≥ 64` the
    appended data extends past the array head + length word. -/
theorem ballotDecoderValid2 (argBytes : ByteArray)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size)
    (h255 : argBytes.size < 2 ^ 255 - 128) :
    UInt256.sgt (⟨128⟩ + ballotArgLen argBytes) ((⟨128⟩ + UInt256.ofNat 32) + ⟨31⟩) ≠ ⟨0⟩ := by
  have hde : (⟨128⟩ + ballotArgLen argBytes : UInt256).toNat = 128 + argBytes.size := by
    rw [uadd_toNat, show ((⟨128⟩ : UInt256)).toNat = 128 from by decide,
      ballotArgLen_toNat argBytes hsz, Nat.mod_eq_of_lt (by
        have : (2:ℕ) ^ 255 < UInt256.size := by decide
        omega)]
  have hlit : ((⟨128⟩ + UInt256.ofNat 32) + ⟨31⟩ : UInt256) = UInt256.ofNat 191 := by
    apply u256_inj
    rw [uadd_toNat, arrayHead_eq, ulit_toNat' _ (by decide : (160:ℕ) < UInt256.size),
      show ((⟨31⟩ : UInt256)).toNat = 31 from by decide,
      ulit_toNat' _ (by decide : (191:ℕ) < UInt256.size)]
    decide
  rw [hlit, sgt_lit_one (by decide) (by rw [hde]; omega) (by rw [hde]; omega)]
  decide

set_option maxHeartbeats 8000000 in
/-- **Decoder validations** (pc `0xd2 → 0x120`): drives the four `bytes32[]` ABI bounds checks
    (length-available `SLT`, offset `≤ 2^64-1`, data-room `SGT`, length `≤ 2^64-1`), reading the
    offset (`0x20`) and length (`n`) words out of the copied calldata.  All four guard `JUMPI`s are
    taken (no revert), leaving the array head, length, and book-keeping words on the stack with memory
    and active-words unchanged.  Requires the deployment shape and `n < 2^64`, `size < 2^255-128`. -/
theorem ballotDecoderValidations {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {k C : ℕ} (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (hszH : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size)
    (h255 : argBytes.size < 2 ^ 255 - 128) (hn : n < 2 ^ 64)
    (rd210 : RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨210⟩
      [⟨128⟩, ⟨128⟩ + ballotArgLen argBytes, ⟨46⟩]
      (ballotDecoderMem argBytes) (ballotDecoderAW argBytes) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨288⟩
      [UInt256.ofNat n, ⟨128⟩ + UInt256.ofNat 32, ⟨0⟩, ⟨128⟩,
        ⟨128⟩ + ballotArgLen argBytes, ⟨46⟩]
      (ballotDecoderMem argBytes) (ballotDecoderAW argBytes) ByteArray.empty (cA, σ) k' C' := by
  have hpos : 0 < argBytes.size := by omega
  have h255' : argBytes.size < 2 ^ 255 := by
    have : (2:ℕ) ^ 255 - 128 < 2 ^ 255 := by norm_num
    omega
  have rd := ctor_run rd210 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨0xe2⟩,
    jumpiT (ballotDecoderValid1 argBytes hszH h64 h255') (by ctor_jd),
    jumpdest, dup2,
    raw mload 0 (UInt256.ofNat 32) (ballotDecoderAW argBytes) (by ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, show (⟨128⟩:UInt256).toNat = 128 from by decide,
          ballotDecoderAW_mloadStable argBytes hszH h64 128 (by omega), u256_ofNat_toNat,
          Nat.sub_self])
      (mloadWordValue_of_readWithPadding
        (by rw [ballotDecoderMem_size argBytes hszH hpos]; show 128 < 128 + argBytes.size; omega)
        (ballotDecoderAW_mloadBound argBytes hszH h64 ⟨128⟩ (by decide))
        (ballotDecoderOffsetRead argBytes (ABI.natBytes n ++ elemBytes) hstruct hszH hpos))
      (by rw [show (⟨128⟩:UInt256).toNat = 128 from by decide,
          ballotDecoderAW_mloadStable argBytes hszH h64 128 (by omega), u256_ofNat_toNat])
      (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0x40⟩, shl, sub, dup2, gt, iszero, push2 ⟨0xf7⟩,
    jumpiT ballotDecoderValidOff (by ctor_jd),
    jumpdest, dup3, add, push1 ⟨0x1f⟩, dup2, add, dup5, sgt, push2 ⟨0x107⟩,
    jumpiT (ballotDecoderValid2 argBytes hszH h64 h255) (by ctor_jd),
    jumpdest, dup1,
    raw mload 0 (UInt256.ofNat n) (ballotDecoderAW argBytes) (by ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, arrayHead_toNat,
          ballotDecoderAW_mloadStable argBytes hszH h64 160 (by omega), u256_ofNat_toNat,
          Nat.sub_self])
      (mloadWordValue_of_readWithPadding
        (by rw [ballotDecoderMem_size argBytes hszH hpos, arrayHead_toNat]; omega)
        (ballotDecoderAW_mloadBound argBytes hszH h64 (⟨128⟩ + UInt256.ofNat 32) (by rw [arrayHead_toNat]))
        (by rw [arrayHead_toNat]; exact ballotDecoderLengthRead argBytes n elemBytes hstruct hszH hpos))
      (by rw [arrayHead_toNat, ballotDecoderAW_mloadStable argBytes hszH h64 160 (by omega), u256_ofNat_toNat])
      (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0x40⟩, shl, sub, dup2, gt, iszero, push2 ⟨0x120⟩,
    jumpiT (ballotDecoderValidLen n hn) (by ctor_jd) ]
  exact ⟨_, _, rd⟩

/-! ### Allocation segment support (pc `0x120 → 0x172`)

The new `bytes32[]` array is allocated at the free pointer: `mem[0x40] ← newFP = fp + 0x20·(n+1)`,
`mem[fp] ← n`, then a copy loop fills the elements.  These lemmas characterize the symbolic words the
allocation arithmetic produces (`fp`, `newFP`, the rounded size, the two bounds checks, the post-write
active-words), all over the deployment shape `argBytes = natBytes 0x20 ‖ natBytes n ‖ elemBytes` with
`elemBytes.length = 0x20·n` and the (realistic) master bound `0x40·n + 0xe0 < 2^64` (so the allocation
fits a 64-bit pointer; this also subsumes `n < 2^64` and `argBytes.size < 2^255-128`). -/

/-- `argBytes.size = 0x40 + 0x20·n` for the `bytes32[]` deployment shape. -/
theorem ballotArg_size (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n) :
    argBytes.size = 64 + 32 * n := by
  rw [hstruct, List.toByteArray_append, ByteArray.size_append, List.toByteArray_append,
    ByteArray.size_append, natBytes_toByteArray_size, natBytes_toByteArray_size,
    List.size_toByteArray, helems]
  omega

/-- The free pointer `fp = 0x80 + argLen = 0xc0 + 0x20·n`. -/
theorem ballotFp_toNat (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) :
    (⟨128⟩ + ballotArgLen argBytes).toNat = 192 + 32 * n := by
  have hszval : argBytes.size = 64 + 32 * n := ballotArg_size n elemBytes argBytes hstruct helems
  have hbnd : 2368 + argBytes.size < UInt256.size := by
    rw [← ballotInitcode_size, ← ByteArray.size_append]; exact hsz
  rw [uadd_toNat, show ((⟨128⟩ : UInt256)).toNat = 128 from by decide,
    ballotArgLen_toNat argBytes hsz, Nat.mod_eq_of_lt (by omega)]; omega

/-- Active words after the `mem[fp] ← n` array-length write: it grows the count by exactly one word,
    from `6 + n` to `7 + n`. -/
theorem ballotAllocAW (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size) :
    MachineState.M (ballotDecoderAW argBytes).toNat (⟨128⟩ + ballotArgLen argBytes).toNat 32 = 7 + n := by
  have hszval : argBytes.size = 64 + 32 * n := ballotArg_size n elemBytes argBytes hstruct helems
  have haw : (ballotDecoderAW argBytes).toNat = 6 + n := by
    rw [ballotDecoderAW_toNat argBytes hsz h64, hszval]; omega
  unfold MachineState.M
  simp only [haw, ballotFp_toNat n elemBytes argBytes hstruct helems hsz]
  omega

/-- `LT a b = 0` when `b ≤ a` (unsigned). -/
theorem ult_eq_zero {a b : UInt256} (h : b.toNat ≤ a.toNat) : UInt256.lt a b = ⟨0⟩ := by
  show UInt256.fromBool (decide (a < b)) = ⟨0⟩
  rw [decide_eq_false (show ¬ a < b by show ¬ a.toNat < b.toNat; omega)]
  rfl

/-- The new free pointer `newFP = fp + (0x20·n + 0x20) = 0xe0 + 0x40·n`. -/
theorem ballotNewFP_toNat (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (_h64 : 64 ≤ argBytes.size)
    (hn64 : 64 * n + 224 < 2 ^ 64) :
    ((⟨128⟩ + ballotArgLen argBytes) +
      (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ + ⟨32⟩)).toNat = 224 + 64 * n := by
  have hfp : (⟨128⟩ + ballotArgLen argBytes).toNat = 192 + 32 * n :=
    ballotFp_toNat n elemBytes argBytes hstruct helems hsz
  have hszbig : (2:ℕ) ^ 64 < UInt256.size := by decide
  have hD : (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩).toNat = 32 * n :=
    ushl5_ofNat_toNat n (by have hb : (2:ℕ) ^ 64 ≤ 2 ^ 251 := by norm_num
                            omega)
  have hDplus : (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ + ⟨32⟩).toNat = 32 * n + 32 := by
    rw [uadd_toNat, hD, show ((⟨32⟩ : UInt256)).toNat = 32 from by decide, Nat.mod_eq_of_lt (by omega)]
  rw [uadd_toNat, hfp, hDplus, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The allocation overflow guard `iszero(newFP > 2^64-1 ∨ newFP < fp)` is taken (no revert): the new
    pointer neither overflows 64 bits nor wraps below `fp`.  `newFP` carries the raw `&~0x1f` rounding
    (cleaned via `alloc_round` inside the proof). -/
theorem ballotAllocOverflow (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size)
    (hn64 : 64 * n + 224 < 2 ^ 64) :
    UInt256.isZero (UInt256.lor
      (UInt256.lt ((⟨128⟩ + ballotArgLen argBytes) +
          UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ + ⟨63⟩))
        (⟨128⟩ + ballotArgLen argBytes))
      (UInt256.gt ((⟨128⟩ + ballotArgLen argBytes) +
          UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ + ⟨63⟩))
        (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨0x40⟩) ⟨1⟩))) ≠ ⟨0⟩ := by
  have hD32 : (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩).toNat = 32 * n :=
    ushl5_ofNat_toNat n (by have hb : (2:ℕ) ^ 64 ≤ 2 ^ 251 := by norm_num
                            omega)
  rw [alloc_round (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩) n hD32
      (by rw [hD32]; have hb : (2:ℕ) ^ 64 < 2 ^ 256 := by norm_num
          omega)]
  have hnewfp := ballotNewFP_toNat n elemBytes argBytes hstruct helems hsz h64 hn64
  have hfp := ballotFp_toNat n elemBytes argBytes hstruct helems hsz
  rw [ult_eq_zero (by rw [hfp, hnewfp]; omega),
      ugt_eq_zero (by rw [hnewfp, u64mask_toNat]; omega)]
  decide

/-- The data-fits guard `iszero(srcEnd > dataEnd)` is taken: the source elements end exactly at the
    appended data end (`srcEnd.toNat = dataEnd.toNat = 0xc0 + 0x20·n`). -/
theorem ballotAllocDataFits (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (_h64 : 64 ≤ argBytes.size)
    (hn64 : 64 * n + 224 < 2 ^ 64) :
    UInt256.isZero (UInt256.gt
      (⟨32⟩ + ((⟨128⟩ + UInt256.ofNat 32) + UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩))
      (⟨128⟩ + ballotArgLen argBytes)) ≠ ⟨0⟩ := by
  have hfp := ballotFp_toNat n elemBytes argBytes hstruct helems hsz
  have hszb : (2:ℕ) ^ 64 < UInt256.size := by decide
  have hD : (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩).toNat = 32 * n :=
    ushl5_ofNat_toNat n (by have hb : (2:ℕ) ^ 64 ≤ 2 ^ 251 := by norm_num
                            omega)
  have e1 : ((⟨128⟩ + UInt256.ofNat 32) + UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩).toNat
      = 160 + 32 * n := by
    rw [uadd_toNat, arrayHead_eq, ulit_toNat' _ (by decide : (160:ℕ) < UInt256.size), hD,
      Nat.mod_eq_of_lt (by omega)]
  have hsrcEnd : (⟨32⟩ + ((⟨128⟩ + UInt256.ofNat 32) + UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩)).toNat
      = 192 + 32 * n := by
    rw [uadd_toNat, e1, show ((⟨32⟩ : UInt256)).toNat = 32 from by decide, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [ugt_eq_zero (by rw [hsrcEnd, hfp])]
  decide

/-! ### Allocation trace (pc `0x120 → 0x172`)

`ballotDecoderAlloc` drives the full allocation: read the free pointer, compute the rounded size,
clear the two overflow guards, write `mem[0x40] ← newFP` and `mem[fp] ← n`, and arrive at the copy-loop
header with the array set up.  The free pointer is carried as an **abstract variable** `fp` (with
`hfp : fp = 0x80 + argLen`): materializing its concrete value forces `(ballotInitcode ++ argBytes).size`
to whnf the ~2.3 KB initcode array, which blows the elaborator — keeping `fp` opaque sidesteps that and
also threads cleanly into the loop/body (which use `fp` symbolically). -/

/-- Copy-loop-header memory: the allocation base — `newFP` stored at `mem[0x40]` and the array length
    `n` stored at `mem[fp]` (the copy loop then fills the elements above `fp`). -/
noncomputable def ballotAllocMem (argBytes : ByteArray) (n : ℕ) (fp : UInt256) : ByteArray :=
  (UInt256.ofNat n).toByteArray.write 0
    ((fp + UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ + ⟨63⟩)).toByteArray.write
      0 (ballotDecoderMem argBytes) 64 32)
    fp.toNat 32

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
/-- **Allocation** (pc `0x120 → 0x172`): from the decoder-validations exit, drives the array allocation
    to the copy-loop header.  All four arithmetic guards (the two overflow `OR` checks and the data-fits
    `GT`) are taken; memory becomes `ballotAllocMem` and active-words grow to `7 + n`.  The free pointer
    is the abstract `fp = 0x80 + argLen`. -/
theorem ballotDecoderAlloc {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {k C : ℕ} (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n)
    (hszH : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size)
    (hn64 : 64 * n + 224 < 2 ^ 64)
    (fp : UInt256) (hfp : fp = ⟨128⟩ + ballotArgLen argBytes)
    (rd288 : RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨288⟩
      [UInt256.ofNat n, ⟨128⟩ + UInt256.ofNat 32, ⟨0⟩, ⟨128⟩,
        ⟨128⟩ + ballotArgLen argBytes, ⟨46⟩]
      (ballotDecoderMem argBytes) (ballotDecoderAW argBytes) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨370⟩
      [fp + ⟨32⟩, fp, UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩,
        ⟨32⟩ + (⟨128⟩ + UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩),
        ⟨128⟩ + UInt256.ofNat 32 + ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨128⟩ + ballotArgLen argBytes, ⟨46⟩]
      (ballotAllocMem argBytes n fp) (UInt256.ofNat (7 + n)) ByteArray.empty (cA, σ) k' C' := by
  have hpos : 0 < argBytes.size := by omega
  -- part 1: freeptr MLOAD (abstract fp) + rounded-size computation through the AND
  have rd1 := ctor_run rd288 with [
    jumpdest, push1 ⟨0x40⟩,
    raw mload 0 fp (ballotDecoderAW argBytes) (by ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, show (⟨64⟩:UInt256).toNat = 64 from by decide,
          ballotDecoderAW_mloadStable argBytes hszH h64 64 (by omega), u256_ofNat_toNat,
          Nat.sub_self])
      (mloadWordValue_of_readWithPadding
        (by rw [ballotDecoderMem_size argBytes hszH hpos]; show 64 < 128 + argBytes.size; omega)
        (ballotDecoderAW_mloadBound argBytes hszH h64 ⟨64⟩ (by decide))
        (show (ballotDecoderMem argBytes).readWithPadding (⟨64⟩ : UInt256).toNat 32
            = UInt256.toByteArray fp by
          rw [hfp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
          exact ballotDecoderFreeptrRead argBytes hszH hpos))
      (by rw [show (⟨64⟩:UInt256).toNat = 64 from by decide,
          ballotDecoderAW_mloadStable argBytes hszH h64 64 (by omega), u256_ofNat_toNat])
      (by evm_ov),
    push1 ⟨5⟩, dup3, swap1, shl, swap1, push1 ⟨63⟩, dup3, add, push1 ⟨31⟩, not, and ]
  -- part 2: newFP + overflow check
  have rd2 := ctor_run rd1 with [
    dup2, add,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0x40⟩, shl, sub, dup2, gt, dup3, dup3, lt, or, iszero, push2 ⟨0x14e⟩,
    jumpiT (by rw [hfp]; exact ballotAllocOverflow n elemBytes argBytes hstruct helems hszH h64 hn64)
      (by ctor_jd) ]
  -- part 3: MSTORE M[0x40] := newFP  (aw stable)
  have rd3 := ctor_run rd2 with [
    jumpdest, push1 ⟨0x40⟩,
    raw mstore 0
      ((fp + UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ + ⟨63⟩)).toByteArray.write
        0 (ballotDecoderMem argBytes) 64 32)
      (ballotDecoderAW argBytes) (by ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, show (⟨64⟩:UInt256).toNat = 64 from by decide,
          ballotDecoderAW_mloadStable argBytes hszH h64 64 (by omega), u256_ofNat_toNat, Nat.sub_self])
      (by rfl)
      (by rw [show (⟨64⟩:UInt256).toNat = 64 from by decide,
          ballotDecoderAW_mloadStable argBytes hszH h64 64 (by omega), u256_ofNat_toNat])
      (by evm_ov) ]
  -- part 4: MSTORE M[fp] := n  (aw grows 6+n → 7+n)
  have rd4 := ctor_run rd3 with [
    swap2, dup3,
    raw mstore
      (Cₘ (UInt256.ofNat (MachineState.M (ballotDecoderAW argBytes).toNat fp.toNat 32))
        - Cₘ (ballotDecoderAW argBytes))
      ((UInt256.ofNat n).toByteArray.write 0
        ((fp + UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ + ⟨63⟩)).toByteArray.write
          0 (ballotDecoderMem argBytes) 64 32)
        fp.toNat 32)
      (UInt256.ofNat (7 + n)) (by ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero])
      (by rfl)
      (by rw [hfp, ballotAllocAW n elemBytes argBytes hstruct helems hszH h64])
      (by evm_ov) ]
  -- part 5: array-head/srcEnd computation + data-fits check → loop header 0x172
  have rd5 := ctor_run rd4 with [
    push1 ⟨0x20⟩, dup2, dup5, add, dup2, add, swap3, swap1, dup2, add, dup8, dup5, gt, iszero,
    push2 ⟨0x16b⟩,
    jumpiT (ballotAllocDataFits n elemBytes argBytes hstruct helems hszH h64 hn64) (by ctor_jd),
    jumpdest, push1 ⟨0x20⟩, dup6, add, swap5, pop ]
  exact ⟨_, _, rd5⟩

/-! ### Copy loop (pc `0x172 → 0x18e`) — memory foundation

The copy loop reads each `bytes32[]` element out of the (intact) calldata-args region `[0xc0, 0xc0+0x20·n)`
and writes it into the freshly allocated array above `fp`.  The first step is that the allocation left
the source region untouched. -/

/-- The copy loop's source region survives allocation: reading element `j < n` from `ballotAllocMem`
    agrees with `ballotDecoderMem` (the `mem[0x40]` and `mem[fp]` writes lie strictly below/above it). -/
theorem ballotAllocMem_src_read (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size)
    (fp : UInt256) (hfp : fp = ⟨128⟩ + ballotArgLen argBytes)
    (j : ℕ) (hj : j < n) :
    (ballotAllocMem argBytes n fp).readWithPadding (192 + 32 * j) 32
      = (ballotDecoderMem argBytes).readWithPadding (192 + 32 * j) 32 := by
  have hpos : 0 < argBytes.size := by omega
  have hszval : argBytes.size = 64 + 32 * n := ballotArg_size n elemBytes argBytes hstruct helems
  have hdmsz : (ballotDecoderMem argBytes).size = 128 + argBytes.size :=
    ballotDecoderMem_size argBytes hsz hpos
  have hfpval : fp.toNat = 192 + 32 * n := by
    rw [hfp]; exact ballotFp_toNat n elemBytes argBytes hstruct helems hsz
  have hW1 : ((UInt256.toByteArray
      (fp + UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ + ⟨63⟩))).write 0
      (ballotDecoderMem argBytes) 64 32).size = 128 + argBytes.size := by
    rw [write32_eq _ _ 64 (by rw [toByteArray_size]) (by rw [hdmsz]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hdmsz, toByteArray_size]
    omega
  unfold ballotAllocMem
  rw [write32_read_below _ _ fp.toNat (192 + 32 * j) (by rw [toByteArray_size])
        (by rw [hW1, hfpval, hszval]; omega) (by rw [hfpval]; omega),
      write32_read_above _ _ 64 (192 + 32 * j) (by rw [toByteArray_size])
        (by rw [hdmsz]; omega) (by omega) (by rw [hdmsz, hszval]; omega)]

/-- Active-words is **stable** for the copy loop's source `MLOAD`: reading element `i` at `0xc0+0x20·i`
    stays within the `7+n+i` active words. -/
theorem M_copy_stable (n i : ℕ) :
    MachineState.M (7 + n + i) (192 + 32 * i) 32 = 7 + n + i := by
  unfold MachineState.M; simp only []; omega

/-- Active-words **grows by one word** for the copy loop's destination `MSTORE`: writing at
    `fp+0x20+0x20·i = (7+n+i)·0x20` (the current end) bumps the count to `8+n+i`. -/
theorem M_copy_grow (n i : ℕ) :
    MachineState.M (7 + n + i) (224 + 32 * n + 32 * i) 32 = 8 + n + i := by
  unfold MachineState.M; simp only []; omega

/-- A 32-byte in-bounds memory read round-trips through `uInt256OfByteArray`: the bytes the copy loop
    re-stores (`MLOAD`'s `ofNat ∘ fromBE`, then `MSTORE`'s `toByteArray`) are exactly the source bytes. -/
theorem read32_roundtrip (mem : ByteArray) (addr : ℕ) (h : addr + 32 ≤ mem.size) :
    mem.readWithPadding addr 32
      = UInt256.toByteArray (uInt256OfByteArray (mem.readWithPadding addr 32)) := by
  have hsz : (mem.readWithPadding addr 32).size = 32 := by
    rw [readWithPadding_eq_extract mem addr h, ByteArray.size_extract]; omega
  rw [← word_toBytesBE_toByteArray_eq_toByteArray,
    toBytesBE_uInt256OfByteArray_of_size hsz]
  apply ByteArray.ext
  apply Array.ext'
  rw [byteArray_toList_eq] at *
  rw [List.toList_data_toByteArray]

/-! ### Copy loop (pc `0x172 → 0x18e`) — the full element-copy via `RD.whileLoopCarry`

Carries `(dst, src, garbage, mem, i)`; the invariant tracks the source region (intact) and the
destination words written so far.  One body iteration (`MLOAD` source word, `MSTORE` to the array,
advance both pointers, `aw` grows one word) is proved once; `RD.whileLoopCarry` lifts it over the
symbolic length `n`.  Result at `0x18e`: the array `[fp+0x20 + 0x20·j ↦ source[j] | j < n]`. -/

private structure CopyState where
  dst : UInt256
  src : UInt256
  g : UInt256
  mem : ByteArray
  i : ℕ

theorem ballotAllocMem_size (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n)
    (hsz : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size)
    (fp : UInt256) (hfp : fp = ⟨128⟩ + ballotArgLen argBytes) :
    (ballotAllocMem argBytes n fp).size = 224 + 32 * n := by
  have hpos : 0 < argBytes.size := by omega
  have hszval : argBytes.size = 64 + 32 * n := ballotArg_size n elemBytes argBytes hstruct helems
  have hdmsz : (ballotDecoderMem argBytes).size = 128 + argBytes.size :=
    ballotDecoderMem_size argBytes hsz hpos
  have hfpval : fp.toNat = 192 + 32 * n := by
    rw [hfp]; exact ballotFp_toNat n elemBytes argBytes hstruct helems hsz
  have hW1 : ((UInt256.toByteArray
      (fp + UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ + ⟨63⟩))).write 0
      (ballotDecoderMem argBytes) 64 32).size = 128 + argBytes.size := by
    rw [write32_eq _ _ 64 (by rw [toByteArray_size]) (by rw [hdmsz]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hdmsz, toByteArray_size]
    omega
  unfold ballotAllocMem
  rw [write32_eq _ _ fp.toNat (by rw [toByteArray_size]) (by rw [hW1, hfpval, hszval]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hW1, toByteArray_size, hfpval, hszval]
  omega

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000 in
theorem ballotDecoderCopyLoop {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {k C : ℕ} (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n)
    (hszH : (ballotInitcode ++ argBytes).size < UInt256.size) (h64 : 64 ≤ argBytes.size)
    (hn64 : 64 * n + 224 < 2 ^ 64)
    (fp : UInt256) (hfp : fp = ⟨128⟩ + ballotArgLen argBytes)
    (h : RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨370⟩
      [fp + ⟨32⟩, fp, UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩,
        ⟨32⟩ + (⟨128⟩ + UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩),
        ⟨128⟩ + UInt256.ofNat 32 + ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨128⟩ + ballotArgLen argBytes, ⟨46⟩]
      (ballotAllocMem argBytes n fp) (UInt256.ofNat (7 + n)) ByteArray.empty (cA, σ) k C) :
    ∃ (mem' : ByteArray) (dst' src' gg : UInt256) (k' C' : ℕ),
      mem'.size = 224 + 32 * n + 32 * n ∧
      (∀ j, j < n → mem'.readWithPadding (224 + 32 * n + 32 * j) 32
        = UInt256.toByteArray (uInt256OfByteArray
            ((ballotAllocMem argBytes n fp).readWithPadding (192 + 32 * j) 32))) ∧
      RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨398⟩
        [dst', fp, gg,
          ⟨32⟩ + (⟨128⟩ + UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩),
          src', ⟨0⟩, ⟨128⟩, ⟨128⟩ + ballotArgLen argBytes, ⟨46⟩]
        mem' (UInt256.ofNat (7 + n + n)) ByteArray.empty (cA, σ) k' C' := by
  set srcEnd : UInt256 :=
    ⟨32⟩ + (⟨128⟩ + UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩) with hsrcEnd
  set de : UInt256 := ⟨128⟩ + ballotArgLen argBytes with hde
  let srcWords : ℕ → UInt256 := fun j =>
    uInt256OfByteArray ((ballotAllocMem argBytes n fp).readWithPadding (192 + 32 * j) 32)
  let Inv : ℕ → CopyState → Prop := fun v a =>
    a.i + v = n ∧ a.src.toNat = 192 + 32 * a.i ∧ a.dst.toNat = 224 + 32 * n + 32 * a.i ∧
      a.mem.size = 224 + 32 * n + 32 * a.i ∧
      (∀ j, j < n → a.mem.readWithPadding (192 + 32 * j) 32 = UInt256.toByteArray (srcWords j)) ∧
      (∀ j, j < a.i → a.mem.readWithPadding (224 + 32 * n + 32 * j) 32 = UInt256.toByteArray (srcWords j))
  let stk : CopyState → List UInt256 := fun a =>
    [a.dst, fp, a.g, srcEnd, a.src, ⟨0⟩, ⟨128⟩, de, ⟨46⟩]
  let stateMem : CopyState → ByteArray := fun a => a.mem
  let stateAw : CopyState → UInt256 := fun a => UInt256.ofNat (7 + n + a.i)
  let exitStk : CopyState → List UInt256 := fun a =>
    [a.dst, fp, a.g, srcEnd, a.src, ⟨0⟩, ⟨128⟩, de, ⟨46⟩]
  have hsrcEndNat : srcEnd.toNat = 192 + 32 * n := by
    have hszb : (2:ℕ) ^ 64 < UInt256.size := by decide
    have hD : (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩).toNat = 32 * n :=
      ushl5_ofNat_toNat n (by have hb : (2:ℕ) ^ 64 ≤ 2 ^ 251 := by norm_num
                              omega)
    have e1 : ((⟨128⟩ + UInt256.ofNat 32) + UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩).toNat
        = 160 + 32 * n := by
      rw [uadd_toNat, arrayHead_eq, ulit_toNat' _ (by decide : (160:ℕ) < UInt256.size), hD,
        Nat.mod_eq_of_lt (by omega)]
    rw [hsrcEnd, uadd_toNat, e1, show ((⟨32⟩ : UInt256)).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have hexit : ∀ a, Inv 0 a → ∀ kk CC,
      RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨370⟩
        (stk a) (stateMem a) (stateAw a) ByteArray.empty (cA, σ) kk CC →
      ∃ k' C', RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨398⟩
        (exitStk a) (stateMem a) (stateAw a) ByteArray.empty (cA, σ) k' C' := by
    intro a hInv kk CC hh
    obtain ⟨hvar, hsrc, _, _, _, _⟩ := hInv
    dsimp only [stk, stateMem, stateAw] at hh
    have hltz : UInt256.lt a.src srcEnd = ⟨0⟩ := by
      apply ult_zero; rw [hsrcEndNat, hsrc]; omega
    have res := ctor_run hh with [
      jumpdest, dup4, dup6, lt, iszero, push2 ⟨0x18e⟩,
      jumpiT (by rw [hltz]; decide) (by ctor_jd) ]
    exact ⟨_, _, res⟩
  have hbody : ∀ v a, Inv (v + 1) a → ∀ kk CC,
      RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨370⟩
        (stk a) (stateMem a) (stateAw a) ByteArray.empty (cA, σ) kk CC →
      ∃ a' k' C', Inv v a' ∧
        RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨370⟩
          (stk a') (stateMem a') (stateAw a') ByteArray.empty (cA, σ) k' C' := by
    intro v a hInv kk CC hh
    obtain ⟨hvar, hsrc, hdst, hsize, hsrcRead, hdstRead⟩ := hInv
    dsimp only [stk, stateMem, stateAw] at hh
    have hszb : (2:ℕ) ^ 64 < UInt256.size := by decide
    have hin : a.i < n := by omega
    have hawN : (UInt256.ofNat (7 + n + a.i)).toNat = 7 + n + a.i := ulit_toNat' _ (by omega)
    have hread : a.mem.readWithPadding a.src.toNat 32 = UInt256.toByteArray (srcWords a.i) := by
      rw [hsrc]; exact hsrcRead a.i hin
    have hlt1 : UInt256.lt a.src srcEnd = ⟨1⟩ := by
      apply ult_one; rw [hsrcEndNat, hsrc]; omega
    have hsrcLt : a.src.toNat < a.mem.size := by rw [hsrc, hsize]; omega
    have hsrcAw : ¬ a.src ≥ UInt256.ofNat (7 + n + a.i) * ⟨32⟩ := by
      intro hge
      have hge' : (UInt256.ofNat (7 + n + a.i) * ⟨32⟩).toNat ≤ a.src.toNat := hge
      rw [show UInt256.ofNat (7 + n + a.i) * ⟨32⟩
            = UInt256.mul (UInt256.ofNat (7 + n + a.i)) ⟨32⟩ from rfl,
        u256_mul_toNat, hawN, show ((⟨32⟩ : UInt256)).toNat = 32 from by decide, hsrc,
        Nat.mod_eq_of_lt (by omega)] at hge'
      omega
    have hdmend : a.dst.toNat = a.mem.size := by rw [hdst, hsize]
    have res := ctor_run hh with [
      jumpdest, dup4, dup6, lt, iszero, push2 ⟨0x18e⟩,
      jumpiNT (by rw [hlt1]; decide),
      dup5,
      raw mload 0 (srcWords a.i) (UInt256.ofNat (7 + n + a.i)) (by ctor_decode)
        (fun s haws hstks => by
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, hsrc, hawN, M_copy_stable, Nat.sub_self])
        (mloadWordValue_of_readWithPadding hsrcLt hsrcAw hread)
        (by rw [hawN, hsrc, M_copy_stable])
        (by evm_ov),
      dup1, dup3,
      raw mstore
        (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat (7 + n + a.i)).toNat a.dst.toNat 32))
          - Cₘ (UInt256.ofNat (7 + n + a.i)))
        ((UInt256.toByteArray (srcWords a.i)).write 0 a.mem a.dst.toNat 32)
        (UInt256.ofNat (7 + n + a.i + 1)) (by ctor_decode)
        (fun s haws hstks => by
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero])
        (by rfl)
        (by rw [hawN, hdst, M_copy_grow]; congr 1; omega)
        (by evm_ov),
      push1 ⟨0x20⟩, swap6, dup7, add, swap6, swap1, swap4, pop, add, push2 ⟨0x172⟩,
      jump (by ctor_jd) ]
    set a' : CopyState := ⟨⟨32⟩ + a.dst, ⟨32⟩ + a.src, srcWords a.i,
      (UInt256.toByteArray (srcWords a.i)).write 0 a.mem a.dst.toNat 32, a.i + 1⟩ with ha'
    have hInvA' : Inv v a' := by
      refine ⟨by show a.i + 1 + v = n; omega, ?_, ?_, ?_, ?_, ?_⟩
      · show (⟨32⟩ + a.src).toNat = 192 + 32 * (a.i + 1)
        rw [uadd_toNat, show ((⟨32⟩ : UInt256)).toNat = 32 from by decide, hsrc,
          Nat.mod_eq_of_lt (by omega)]; omega
      · show (⟨32⟩ + a.dst).toNat = 224 + 32 * n + 32 * (a.i + 1)
        rw [uadd_toNat, show ((⟨32⟩ : UInt256)).toNat = 32 from by decide, hdst,
          Nat.mod_eq_of_lt (by omega)]; omega
      · show ((UInt256.toByteArray (srcWords a.i)).write 0 a.mem a.dst.toNat 32).size
          = 224 + 32 * n + 32 * (a.i + 1)
        rw [hdmend, write_at_end_eq _ _ 32 (by norm_num) (by rw [toByteArray_size]),
          ByteArray.size_append, ByteArray.size_extract, hsize, toByteArray_size]; omega
      · show ∀ j, j < n → ((UInt256.toByteArray (srcWords a.i)).write 0 a.mem a.dst.toNat 32).readWithPadding
            (192 + 32 * j) 32 = UInt256.toByteArray (srcWords j)
        intro j hj
        rw [write32_read_below _ _ a.dst.toNat (192 + 32 * j) (by rw [toByteArray_size])
            (by rw [hdmend]) (by rw [hdst]; omega)]
        exact hsrcRead j hj
      · show ∀ j, j < a.i + 1 → ((UInt256.toByteArray (srcWords a.i)).write 0 a.mem a.dst.toNat 32).readWithPadding
            (224 + 32 * n + 32 * j) 32 = UInt256.toByteArray (srcWords j)
        intro j hj
        rcases Nat.lt_or_ge j a.i with hlt | hge
        · rw [write32_read_below _ _ a.dst.toNat (224 + 32 * n + 32 * j) (by rw [toByteArray_size])
              (by rw [hdmend]) (by rw [hdst]; omega)]
          exact hdstRead j hlt
        · have hje : j = a.i := by omega
          subst hje
          rw [show 224 + 32 * n + 32 * a.i = a.dst.toNat from hdst.symm,
            write32_read_back _ _ a.dst.toNat (by rw [toByteArray_size]) (by rw [hdmend])]
          apply ByteArray.ext
          rw [ByteArray.data_extract]
          have hs : (srcWords a.i).toByteArray.data.size = 32 := toByteArray_size (srcWords a.i)
          rw [Array.extract_eq_self_of_le (by rw [hs])]
    obtain ⟨k', C', res'⟩ :
        ∃ k' C', RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨370⟩
          (stk a') (stateMem a') (stateAw a') ByteArray.empty (cA, σ) k' C' :=
      ⟨_, _, by dsimp only [stk, stateMem, stateAw, a']; exact res⟩
    exact ⟨a', k', C', hInvA', res'⟩
  obtain ⟨a', k', C', hInvF, hrdF⟩ :=
    RD.whileLoopCarry (code := ballotInitcode ++ argBytes) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty) (acc := (cA, σ))
      (α := CopyState) ⟨370⟩ ⟨398⟩ Inv stk stateMem stateAw exitStk hexit hbody
      n ⟨fp + ⟨32⟩, ⟨128⟩ + UInt256.ofNat 32 + ⟨32⟩, UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩,
        ballotAllocMem argBytes n fp, 0⟩
      (by
        have hszb : (2:ℕ) ^ 64 < UInt256.size := by decide
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · show (0:ℕ) + n = n; omega
        · show (⟨128⟩ + UInt256.ofNat 32 + ⟨32⟩).toNat = 192 + 32 * 0
          rw [uadd_toNat, arrayHead_eq, ulit_toNat' _ (by decide : (160:ℕ) < UInt256.size),
            show ((⟨32⟩ : UInt256)).toNat = 32 from by decide, Nat.mod_eq_of_lt (by decide)]
        · show (fp + ⟨32⟩).toNat = 224 + 32 * n + 32 * 0
          rw [uadd_toNat, hfp, ballotFp_toNat n elemBytes argBytes hstruct helems hszH,
            show ((⟨32⟩ : UInt256)).toNat = 32 from by decide, Nat.mod_eq_of_lt (by omega)]; omega
        · show (ballotAllocMem argBytes n fp).size = 224 + 32 * n + 32 * 0
          rw [ballotAllocMem_size n elemBytes argBytes hstruct helems hszH h64 fp hfp]; omega
        · intro j hj
          exact read32_roundtrip (ballotAllocMem argBytes n fp) (192 + 32 * j)
            (by rw [ballotAllocMem_size n elemBytes argBytes hstruct helems hszH h64 fp hfp]; omega)
        · intro j hj; exact absurd hj (by show ¬ j < (0:ℕ); omega))
      k C
      (by dsimp only [stk, stateMem, stateAw]; simpa using h)
  obtain ⟨hi, _, _, hsize', _, hdstR'⟩ := hInvF
  have hin : a'.i = n := by omega
  refine ⟨a'.mem, a'.dst, a'.src, a'.g, k', C', by rw [hsize', hin], ?_, ?_⟩
  · intro j hj; exact hdstR' j (by rw [hin]; exact hj)
  · dsimp only [exitStk, stateMem, stateAw] at hrdF; rw [hin] at hrdF; exact hrdF

/-- Cleanup (pc `0x18e → 0x2e`): pop/swap the loop scratch off the stack and JUMP to the body entry. -/
theorem ballotDecoderCleanup {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {k C : ℕ} (argBytes : ByteArray) (fp dst' src' gg srcEnd de : UInt256)
    (memv : ByteArray) (awv : UInt256)
    (h : RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨398⟩
      [dst', fp, gg, srcEnd, src', ⟨0⟩, ⟨128⟩, de, ⟨46⟩]
      memv awv ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨46⟩
      [fp] memv awv ByteArray.empty (cA, σ) k' C' := by
  have res := ctor_run h with [
    jumpdest, pop, swap7, swap6, pop, pop, pop, pop, pop, pop, jump (by ctor_jd) ]
  exact ⟨_, _, res⟩

/-- Compose the constructor prologue and ABI decoder: after validating and materializing the
    `bytes32[]` constructor argument, execution returns to the constructor body entry at pc `0x2e`
    with the decoded memory array pointer on the stack.  The remaining proof obligations after this
    point are the constructor's storage writes and final runtime `RETURN`. -/
theorem ballotReachConstructorBody
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n)
    (hszH : (ballotInitcode ++ argBytes).size < UInt256.size)
    (h64 : 64 ≤ argBytes.size) (h255 : argBytes.size < 2 ^ 255 - 128)
    (hn : n < 2 ^ 64) (hn64 : 64 * n + 224 < 2 ^ 64)
    (hcode : I.code = ballotInitcode ++ argBytes) (hwv : I.weiValue = ⟨0⟩) :
    ∃ (fp : UInt256) (mem : ByteArray) (aw : UInt256) (k C : ℕ),
      fp = ⟨128⟩ + ballotArgLen argBytes ∧
      mem.size = 224 + 32 * n + 32 * n ∧
      RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨46⟩
        [fp] mem aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨k210, C210, rd210⟩ := ballotReachDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) argBytes hcode hwv
  obtain ⟨k288, C288, rd288⟩ := ballotDecoderValidations
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) n elemBytes argBytes hstruct hszH h64 h255 hn rd210
  let fp : UInt256 := ⟨128⟩ + ballotArgLen argBytes
  obtain ⟨k370, C370, rd370⟩ := ballotDecoderAlloc
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) n elemBytes argBytes hstruct helems hszH h64 hn64 fp rfl rd288
  obtain ⟨mem', dst', src', gg, k398, C398, hmemSize, _hcopy, rd398⟩ :=
    ballotDecoderCopyLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) n elemBytes argBytes hstruct helems hszH h64 hn64 fp rfl rd370
  obtain ⟨k46, C46, rd46⟩ := ballotDecoderCleanup
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) argBytes fp dst' src' gg
    (⟨32⟩ + (⟨128⟩ + UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩))
    (⟨128⟩ + ballotArgLen argBytes) mem' (UInt256.ofNat (7 + n + n)) rd398
  exact ⟨fp, mem', UInt256.ofNat (7 + n + n), k46, C46, rfl, hmemSize, rd46⟩

/-! ## Constructor body — initial storage setup (pc `0x2e → 0x50`)

Before the proposal loop, solc writes `chairperson = msg.sender`, materializes the
`voters[msg.sender]` mapping slot in scratch memory, and writes the chairperson's voter weight to
one.  The proposal loop starts at pc `0x50` with stack `[i = 0, proposalNamesPtr]`.
-/

abbrev ballotSourceWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.source.val

def ballotStorageWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)

noncomputable def ballotCtorChairWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.land (ballotStorageWord σ I ⟨0⟩) (UInt256.lnot solcAddrMask))
    (ballotSourceWord I)

noncomputable def ballotCtorScratchMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray ⟨1⟩).write 0
    ((UInt256.toByteArray (ballotSourceWord I)).write 0 mem 0 32) 32 32

noncomputable def ballotCtorVoterSlot (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((ballotCtorScratchMem I mem).readWithPadding 0 64)))

noncomputable def ballotCtorPreludeMap (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨0⟩ (ballotCtorChairWord σ I))
    (ballotCtorVoterSlot I mem) ⟨1⟩

set_option maxHeartbeats 2000000 in
/-- The constructor body prefix writes `chairperson` and `voters[chairperson].weight`, then reaches
    the proposal loop header at pc `0x50`. -/
theorem ballotConstructorPrelude {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {k C : ℕ} (n : ℕ) (argBytes : ByteArray) (fp : UInt256) (mem : ByteArray)
    (_hmemSize : mem.size = 224 + 32 * n + 32 * n)
    (hn64 : 64 * n + 224 < 2 ^ 64)
    (hperm : I.perm = true)
    (h : RD (ballotInitcode ++ argBytes) I g (initState cA gh bl σ σ₀ g A I) ⟨46⟩
      [fp] mem (UInt256.ofNat (7 + n + n)) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (ballotInitcode ++ argBytes) I g
      (initState cA gh bl σ σ₀ g A I) ⟨80⟩ [⟨0⟩, fp]
      (ballotCtorScratchMem I mem) (UInt256.ofNat (7 + n + n)) ByteArray.empty
      (cA, ballotCtorPreludeMap σ I mem) k' C' := by
  have hnSmall : n < 2 ^ 64 := by omega
  have hawLt : 7 + n + n < UInt256.size := by
    unfold UInt256.size
    omega
  have hawN : (UInt256.ofNat (7 + n + n)).toNat = 7 + n + n := by
    rw [UInt256.toNat_ofNat_of_lt hawLt]
  have hM0 : MachineState.M (7 + n + n) 0 32 = 7 + n + n := by
    unfold MachineState.M; simp only []; omega
  have hM32 : MachineState.M (7 + n + n) 32 32 = 7 + n + n := by
    unfold MachineState.M; simp only []; omega
  have hM64 : MachineState.M (7 + n + n) 0 64 = 7 + n + n := by
    unfold MachineState.M; simp only []; omega
  have hM0w :
      MachineState.M (7 + n + n) ({ val := 0 } : UInt256).toNat 32 = 7 + n + n := by
    simpa using hM0
  have hM32w :
      MachineState.M (7 + n + n) ({ val := 32 } : UInt256).toNat 32 = 7 + n + n := by
    simpa using hM32
  have hM64w :
      MachineState.M (7 + n + n) ({ val := 0 } : UInt256).toNat ({ val := 64 } : UInt256).toNat =
        7 + n + n := by
    simpa using hM64
  obtain ⟨k52, C52, rd52⟩ :=
    (ctor_run h with [
      jumpdest, push0, dup1 ]).sload (by ctor_decode) (by evm_ov)
  have rd65 := ctor_run rd52 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0xa0⟩, shl, sub, not, and, caller, swap1, dup2 ]
  have rd66 := RD.or rd65 (by ctor_decode) (by evm_ov)
  have rd67 := ctor_run rd66 with [dup3]
  have hchair :
      UInt256.lor (ballotSourceWord I)
          (UInt256.land
            (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
            (ballotStorageWord σ I ⟨0⟩)) =
        ballotCtorChairWord σ I := by
    have hmask :
        UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
          UInt256.lnot solcAddrMask := by
      decide
    unfold ballotCtorChairWord
    rw [hmask, u256_land_comm, u256_lor_comm]
  obtain ⟨k66, C66, rd66⟩ :=
    rd67.sstore hperm (by ctor_decode) (by evm_ov)
  have rd68 := ctor_run rd66 with [
    dup2,
    raw mstore 0 ((UInt256.toByteArray (ballotSourceWord I)).write 0 mem 0 32)
      (UInt256.ofNat (7 + n + n)) (by ctor_decode)
        (fun s haws hstks => by
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, hawN, hM0w, Nat.sub_self])
        (by rfl)
        (by rw [hawN, hM0w])
        (by evm_ov),
      push1 ⟨1⟩, push1 ⟨0x20⟩, dup2, swap1 ]
  have rd75 := ctor_run rd68 with [
    raw mstore 0 (ballotCtorScratchMem I mem) (UInt256.ofNat (7 + n + n)) (by ctor_decode)
      (fun s haws hstks => by
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
            hawN, hM32, Nat.sub_self])
        (by rfl)
        (by rw [hawN, hM32w])
        (by evm_ov),
      push1 ⟨0x40⟩, dup3 ]
  have rd79 := ctor_run rd75 with [
    raw keccak256 0 (ballotCtorVoterSlot I mem) (UInt256.ofNat (7 + n + n)) (by ctor_decode)
        (fun s haws hstks => by
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ, hawN, hM64w, Nat.sub_self])
        (by rfl)
        (by rw [hawN, hM64w])
        (by evm_ov) ]
  obtain ⟨k80, C80, rd80⟩ := rd79.sstore hperm (by ctor_decode) (by evm_ov)
  have hchairRaw := hchair
  simp [ballotStorageWord, ballotSourceWord] at hchairRaw
  rw [hchairRaw] at rd80
  simpa [ballotCtorPreludeMap, ballotCtorVoterSlot, ballotCtorScratchMem,
    ballotSourceWord] using ⟨k80, C80, rd80⟩

end Ballot
