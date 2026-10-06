import Reasoning.StateFacts
import Reasoning.BytecodePatching
import Reasoning.SolcRoutines
import Reasoning.ABILegacy
import Benchmarks.Dss.Dog.Bytecode
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.Initcode
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases


/-!
# MakerDAO/Sky DSS Dog shared proof foundation

Contract-wide selector notation and constants for the optimized Dog runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

@[reducible] def solcIlksChopGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p8 := p6 + UInt256.ofNat 2
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.SWAP1, .none)
  ∧ decode code p4 = some (.DUP2, .none)
  ∧ decode code p5 = some (.MSTORE, .none)
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p10 = some (.DUP2, .none)
  ∧ decode code p11 = some (.SWAP1, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p15 = some (.SWAP1, .none)
  ∧ decode code p16 = some (.SWAP2, .none)
  ∧ decode code p17 = some (.KECCAK256, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.SLOAD, .none)
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.JUMP, .none)

end Benchmarks.Dss.Dog

namespace Benchmarks.Dss.Dog.RD

theorem solcIlksChopGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcIlksChopGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨1⟩) :: R)
      (twoWordHashMem key ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3) rdata
      σ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd8, hd10, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd21⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd4 := rd3.swap1 hd3 (by evm_ov)
  have rd5 := rd4.dup2 hd4 (by evm_ov)
  have rd6 := rd5.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) hd5 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd8 := rd6.push1 ⟨1⟩ hd6 (by evm_ov)
  have rd10 := rd8.push1 ⟨32⟩ hd8 (by evm_ov)
  have rd11 := rd10.dup2 hd10 (by evm_ov)
  have rd12 := rd11.swap1 hd11 (by evm_ov)
  have rd13 := rd12.mstore 0 (twoWordHashMem key ⟨1⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd12 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd15 := rd13.push1 ⟨64⟩ hd13 (by evm_ov)
  have rd16 := rd15.swap1 hd15 (by evm_ov)
  have rd17 := rd16.swap2 hd16 (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨1⟩ key solcFreePtrMem_size
  have rd18 := rd17.keccak256 0 (solcMappingSlot ⟨1⟩ key)
    (UInt256.ofNat 3) hd17 mem_cost hslot (by decide) (by evm_ov)
  have rd19 := rd18.add hd18 (by evm_ov)
  obtain ⟨_, _, rd20⟩ := rd19.sload hd19 (by evm_ov)
  have rd21 := rd20.swap1 hd20 (by evm_ov)
  exact ⟨_, _, by simpa [solcSlotWord] using rd21.jump hd21 hret (by evm_ov)⟩

end Benchmarks.Dss.Dog.RD

end

namespace Benchmarks.Dss.Dog


/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev dogSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `(contract v).transitions` order. -/
def dogSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xed, 0xa6, 0xe1, 0x21]⟩ -- Dirt()
  | 1 => ⟨#[0xaf, 0x7c, 0xfe, 0xb1]⟩ -- Hole()
  | 2 => ⟨#[0xed, 0x99, 0x89, 0x08]⟩ -- bark(bytes32,address,address)
  | 3 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | 4 => ⟨#[0xd7, 0x92, 0x65, 0x38]⟩ -- chop(bytes32)
  | 5 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 6 => ⟨#[0xc8, 0x71, 0x93, 0xf4]⟩ -- digs(bytes32,uint256)
  | 7 => ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩ -- file(bytes32,bytes32,uint256)
  | 8 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 9 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)
  | 10 => ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩ -- file(bytes32,bytes32,address)
  | 11 => ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩ -- ilks(bytes32)
  | 12 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 13 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 14 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 15 => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ -- vow()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)

def dogSelectorWord : ℕ → UInt256
  | 0 => ⟨0xeda6e121⟩ -- Dirt()
  | 1 => ⟨0xaf7cfeb1⟩ -- Hole()
  | 2 => ⟨0xed998908⟩ -- bark(bytes32,address,address)
  | 3 => ⟨0x69245009⟩ -- cage()
  | 4 => ⟨0xd7926538⟩ -- chop(bytes32)
  | 5 => ⟨0x9c52a7f1⟩ -- deny(address)
  | 6 => ⟨0xc87193f4⟩ -- digs(bytes32,uint256)
  | 7 => ⟨0x1a0b287e⟩ -- file(bytes32,bytes32,uint256)
  | 8 => ⟨0x29ae8114⟩ -- file(bytes32,uint256)
  | 9 => ⟨0xd4e8be83⟩ -- file(bytes32,address)
  | 10 => ⟨0xebecb39d⟩ -- file(bytes32,bytes32,address)
  | 11 => ⟨0xd9638d36⟩ -- ilks(bytes32)
  | 12 => ⟨0x957aa58c⟩ -- live()
  | 13 => ⟨0x65fae35e⟩ -- rely(address)
  | 14 => ⟨0x36569e77⟩ -- vat()
  | 15 => ⟨0x626cb3c5⟩ -- vow()
  | _ => ⟨0xbf353dbb⟩ -- wards(address)

theorem dogEvmSelectorEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (i : ℕ) (hi : i < 17) :
    UInt256.eq (dogSelectorWord i) (solcSelectorWord I) =
      if (dogSelBytes i == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases i <;>
    simpa [dogSelectorWord, dogSelBytes, solcSelectorWord] using
      (evmSelectorDecode (cd := I.calldata) hsz _ _ _ _ _ (by native_decide))

theorem dogSelectorEqZero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 17 → (dogSelBytes i == I.calldata.extract 0 4) = false)
    (i : ℕ) (hi : i < 17) :
    UInt256.eq (dogSelectorWord i) (solcSelectorWord I) = ⟨0⟩ := by
  rw [dogEvmSelectorEq I hsz i hi, hnm i hi]
  rfl


theorem dogAddressGetterBodyReturns (v : DogImmutables) (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef (config v) { contract := contract v, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? (contract v).storage er = some (.elem .address))
    (hloc : (config v).storage.layout er = fun _ => some (addrLoc slot)) :
    ExecTransitionBody (config v) (contract v) evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract v, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_address_offset0 evm slot))

theorem dogUint256GetterBodyReturns (v : DogImmutables) (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef (config v) { contract := contract v, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? (contract v).storage er = some (.elem (.int uint256Int)))
    (hloc : (config v).storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody (config v) (contract v) evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract v, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_uint256 evm slot))

theorem dogAddressGetterBodyCore
    {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hreturnJd : (D_J code 0).contains returnPc = true)
    (hretmem : solcReturnAddressFromMemWf code returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (solcAddressSlotWord slot σ I).toNat))]))) :
    runtimeEquivalenceFor (config v) (contract v) σ σ₀ g A I := by
  have hval :
      some [Value.address (AccountAddress.ofNat (solcAddressSlotWord slot σ I).toNat)] =
        some [Value.address (AccountAddress.ofNat (solcAddressSlotWord slot σ I).toNat)] := by
    rfl
  have henc :
      returnEquiv (UInt256.toByteArray (solcAddressSlotWord slot σ I))
        (some [(.address (AccountAddress.ofNat (solcAddressSlotWord slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [solcAddressSlotWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (solcSlotWordAt slot σ I)))
  have hret := RD.solcAddressGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret code (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcAddressSlotWord slot σ I)) := by
    simpa [solcAddressSlotWord, solcSlotWordAt] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval henc

theorem dogUint256GetterBodyCore
    {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcWordSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hreturnJd : (D_J code 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf code returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))]))) :
    runtimeEquivalenceFor (config v) (contract v) σ σ₀ g A I := by
  have hval :
      some [Value.int (Int.ofNat (solcSlotWordAt slot σ I).toNat)] =
        some [Value.int (Int.ofNat (solcSlotWordAt slot σ I).toNat)] := by
    rfl
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  have hret := RD.solcWordGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret code (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    simpa [solcSlotWordAt] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval henc


theorem dogAddrLitEval {v : DogImmutables}
    {σ σ₀ A I} {g : Sat256} (a : EVM.Address) :
    evalExpr? (config v) { contract := contract v, locals := ∅ }
      (initState σ σ₀ g A I) (Reasoning.Theory.addressLiteral a) =
      .ok (Value.address (AccountAddress.ofNat a.toNat)) := by
  dsimp [Reasoning.Theory.addressLiteral]
  have hint :
      evalExpr? (config v) { contract := contract v, locals := ∅ }
        (initState σ σ₀ g A I) (.intLit (↑↑a)) =
        .ok (.int (↑↑a)) := by
    simp [evalExpr?, pure]
  unfold evalExpr?
  rw [hint]
  change (if (↑↑a : Int) < 0 then EvalResult.error EvalError.typeError
      else EvalResult.ok
        (Value.address (AccountAddress.ofNat (Int.toNat (↑↑a : Int))))) =
    EvalResult.ok (Value.address (AccountAddress.ofNat ↑a))
  rw [if_neg (by omega)]
  simp

/-! ### LOG2

The base reasoning library has LOG1/LOG3/LOG4 combinators; Dog emits two-topic auth logs.
-/


abbrev dogCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

abbrev dogCallerWardsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address I.source)] }

theorem dogCallerWardsEvaledRef_ok {v : DogImmutables}
    {σ σ₀ A I} {g : Sat256} {locals : Store}
    (_hbase : locals.get? "wards" = none) :
    evalStorageRef (config v) { contract := contract v, locals := locals }
      (initState σ σ₀ g A I) (wardsRef sender) =
        .ok (dogCallerWardsEvaledRef I) := by
  simp [dogCallerWardsEvaledRef, wardsRef, sender, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind, initState]

theorem dogAuthGuardEval_true {v : DogImmutables}
    {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : solcSlotWordAt (dogCallerWardsSlot I) σ I = ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := locals }
      (initState σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have her := dogCallerWardsEvaledRef_ok (v := v)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  have hload : Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
      (dogCallerWardsSlot I) = ⟨1⟩ := by
    simpa [solcSlotWordAt] using hauth
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (dogCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        dogCallerWardsEvaledRef, dogCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals native_decide

theorem dogAuthGuardEval_false {v : DogImmutables}
    {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : solcSlotWordAt (dogCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := locals }
      (initState σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have her := dogCallerWardsEvaledRef_ok (v := v)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  let w := Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
      (dogCallerWardsSlot I)
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hauth (by simpa [w, solcSlotWordAt] using hw)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (dogCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        dogCallerWardsEvaledRef, dogCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals native_decide


abbrev dogNotAuthorizedRawWord : UInt256 :=
  ⟨0x111bd9cbdb9bdd0b585d5d1a1bdc9a5e9959⟩

abbrev dogFileUnrecognizedRawWord : UInt256 :=
  ⟨30954105885628950283353179477659576776954465509597691851899989870914947776512⟩


theorem RD.dogAuthCheckRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcAuthCheckWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcAuthTailPc pc) ⟨18⟩
      dogNotAuthorizedRawWord ⟨114⟩ .PUSH18 18)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ≠ ⟨1⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 :=
  Reasoning.Reach.RD.solcAuthCheckRevert18 h hwf htail hauth hov


/-! ## Patched-runtime prefix facts -/


private theorem dog_patches_ge_1405 (v : DogImmutables) :
    ∀ p ∈ patches v, 1405 ≤ p.1 := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, Reasoning.Theory.wordBytes?, valueToWord,
    List.lookup] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

theorem dogPatchedPrefix1405 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    ∃ rest, code = dogBytecode.extract 0 1405 ++ rest := by
  exact patchRuntime_eq_pref_append (by native_decide) (dog_patches_ge_1405 v) hpatch

theorem dogDecodePatchedEqTemplate1405 {v : DogImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) (hwin : pc.toNat + 33 ≤ 1405) :
    decode code pc = decode dogBytecode pc := by
  let pref := dogBytecode.extract 0 1405
  let tail0 := dogBytecode.extract 1405 dogBytecode.size
  obtain ⟨tail, htail⟩ := dogPatchedPrefix1405 hpatch
  have htemplate : dogBytecode = pref ++ tail0 := by
    dsimp [pref, tail0]
    exact (byteArray_prefix_suffix dogBytecode 1405 (by native_decide)).symm
  have hprefSize : pref.size = 1405 := by
    dsimp [pref]
    rw [ByteArray.size_extract]
    have hs : 1405 ≤ dogBytecode.size := by native_decide
    omega
  rw [htail]
  change decode (pref ++ tail) pc = decode dogBytecode pc
  rw [Reasoning.Theory.decode_append_left_window pref tail pc
    (by rw [hprefSize]; exact hwin) (by rw [hprefSize]; norm_num)]
  rw [htemplate]
  rw [Reasoning.Theory.decode_append_left_window pref tail0 pc
    (by rw [hprefSize]; exact hwin) (by rw [hprefSize]; norm_num)]

theorem dogDecodePatchedEqPrefix1405 {v : DogImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hpc : pc.toNat < 1405)
    (hwin : ∀ b instr,
      (dogBytecode.extract 0 1405).get? pc.toNat = some b → parseInstr b = some instr →
        pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 1405)
    (hwin64 : ∀ b instr,
      (dogBytecode.extract 0 1405).get? pc.toNat = some b → parseInstr b = some instr →
        pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64) :
    decode code pc = decode dogBytecode pc := by
  let pref := dogBytecode.extract 0 1405
  let tail0 := dogBytecode.extract 1405 dogBytecode.size
  obtain ⟨tail, htail⟩ := dogPatchedPrefix1405 hpatch
  have htemplate : dogBytecode = pref ++ tail0 := by
    dsimp [pref, tail0]
    exact (byteArray_prefix_suffix dogBytecode 1405 (by native_decide)).symm
  have hprefSize : pref.size = 1405 := by
    dsimp [pref]
    rw [ByteArray.size_extract]
    have hs : 1405 ≤ dogBytecode.size := by native_decide
    omega
  have hleft : decode (pref ++ tail) pc = decode pref pc := by
    exact Reasoning.Theory.decode_append_left pref tail pc
      (by rw [hprefSize]; exact hpc)
      (by
        intro b instr hb hparse
        rw [hprefSize]
        exact hwin b instr (by simpa [pref] using hb) hparse)
      (by
        intro b instr hb hparse
        exact hwin64 b instr (by simpa [pref] using hb) hparse)
  have hright : decode dogBytecode pc = decode pref pc := by
    rw [htemplate]
    exact Reasoning.Theory.decode_append_left pref tail0 pc
      (by rw [hprefSize]; exact hpc)
      (by
        intro b instr hb hparse
        rw [hprefSize]
        exact hwin b instr (by simpa [pref] using hb) hparse)
      (by
        intro b instr hb hparse
        exact hwin64 b instr (by simpa [pref] using hb) hparse)
  rw [htail]
  change decode (pref ++ tail) pc = decode dogBytecode pc
  rw [hleft, hright]

def prefixWindowLe (bytes : ByteArray) (pc : UInt256) : Bool :=
  match bytes.get? pc.toNat with
  | some b =>
      match parseInstr b with
      | some instr => decide (pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 1405)
      | none => true
  | none => true

theorem prefixWindowLe_of_true {bytes : ByteArray} {pc : UInt256}
    (hok : prefixWindowLe bytes pc = true) :
    ∀ b instr, bytes.get? pc.toNat = some b → parseInstr b = some instr →
      pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 1405 := by
  intro b instr hb hparse
  unfold prefixWindowLe at hok
  simp only [hb, hparse] at hok
  exact of_decide_eq_true hok

def dogPrefixWindowLe1405 (pc : UInt256) : Bool :=
  prefixWindowLe (dogBytecode.extract 0 1405) pc

theorem dogPrefixWindowLe1405_of_true {pc : UInt256}
    (hok : dogPrefixWindowLe1405 pc = true) :
    ∀ b instr,
    (dogBytecode.extract 0 1405).get? pc.toNat = some b → parseInstr b = some instr →
        pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 1405 := by
  intro b instr hb hparse
  change prefixWindowLe (dogBytecode.extract 0 1405) pc = true at hok
  exact prefixWindowLe_of_true hok b instr hb hparse


def dogPrefixWindowLt64 (pc : UInt256) : Bool :=
  prefixWindowLt64 (dogBytecode.extract 0 1405) pc

theorem dogPrefixWindowLt64_of_true {pc : UInt256}
    (hok : dogPrefixWindowLt64 pc = true) :
    ∀ b instr,
    (dogBytecode.extract 0 1405).get? pc.toNat = some b → parseInstr b = some instr →
        pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64 := by
  intro b instr hb hparse
  change prefixWindowLt64 (dogBytecode.extract 0 1405) pc = true at hok
  exact prefixWindowLt64_of_true hok b instr hb hparse

theorem dogPushAtPatchedEqTemplate1405 {v : DogImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) (hwin : pc.toNat + 33 ≤ 1405) :
    pushAt code pc = pushAt dogBytecode pc := by
  unfold pushAt
  rw [dogDecodePatchedEqTemplate1405 hpatch hwin]

theorem dogPatchedDJumpPrefix1405 {v : DogImmutables} {code : ByteArray} (target : UInt256)
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcontains : (D_J (dogBytecode.extract 0 1405) 0).contains target = true) :
    (D_J code 0).contains target = true := by
  let pref := dogBytecode.extract 0 1405
  obtain ⟨tail, htail⟩ := dogPatchedPrefix1405 hpatch
  rw [htail]
  change (D_J (pref ++ tail) 0).contains target = true
  exact Reasoning.Theory.D_J_contains_append_left pref tail target hcontains


theorem dogPatchedSize {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    code.size = dogBytecode.size :=
  patchRuntime_size_eq hpatch


theorem dogDecodePatchedEqTemplateDisjoint {v : DogImmutables} {code : ByteArray}
    {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hwin : pc.toNat + 33 ≤ dogBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat) :
    decode code pc = decode dogBytecode pc := by
  unfold decode
  have hsize := patchRuntime_size_eq hpatch
  have hsize64 : dogBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = dogBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (by omega) (by omega)
        (by
          intro p hp
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  rw [hget]
  cases hgetTemplate : dogBytecode.get? pc.toNat with
  | none => simp
  | some b =>
      cases hinstr : parseInstr b with
      | none => simp [hinstr]
      | some instr =>
          simp [hinstr]
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [harg]
          · simp [harg]
            have hargpos : 0 < argOnNBytesOfInstr instr := Nat.pos_of_ne_zero harg
            have hargle := argOnNBytesOfInstr_le_32 instr
            rw [patchRuntime_extract'_eq (template := dogBytecode) (out := code)
              (ps := patches v) (start := pc.toNat.succ)
              (stop := pc.toNat.succ + argOnNBytesOfInstr instr)]
            · omega
            · omega
            · omega
            · omega
            · intro p hp
              rcases hdisj p hp with hbefore | hafter
              · exact Or.inl (by
                  omega)
              · exact Or.inr (by omega)
            · exact hpatch

def dogPatchOffsets : List Nat :=
  [1405, 2890, 3170, 3965]

theorem dogPatchOffsetMem (v : DogImmutables) :
    ∀ p ∈ patches v, p.1 ∈ dogPatchOffsets := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, Reasoning.Theory.wordBytes?, valueToWord,
    List.lookup] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp [dogPatchOffsets]

theorem dogDecodePatchedEqTemplateAway {v : DogImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hwin : pc.toNat + 33 ≤ dogBytecode.size)
    (hoffsets : ∀ off ∈ dogPatchOffsets, pc.toNat + 33 ≤ off ∨ off + 32 ≤ pc.toNat) :
    decode code pc = decode dogBytecode pc :=
  dogDecodePatchedEqTemplateDisjoint hpatch hwin (by
    intro p hp
    exact hoffsets p.1 (dogPatchOffsetMem v p hp))

theorem dogDecodePatchedNoArg {v : DogImmutables} {code : ByteArray}
    {pc : UInt256} {byte : UInt8} {op : Operation}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hwin : pc.toNat + 1 ≤ dogBytecode.size)
    (hoffsets : ∀ off ∈ dogPatchOffsets, pc.toNat + 1 ≤ off ∨ off + 32 ≤ pc.toNat)
    (hgetTemplate : dogBytecode.get? pc.toNat = some byte)
    (hparse : (some byte >>= parseInstr) = some op)
    (harg : argOnNBytesOfInstr op = 0) :
    decode code pc = some (op, .none) := by
  have hsize := dogPatchedSize hpatch
  have hget : code.get? pc.toNat = dogBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := dogBytecode) (out := code) (ps := patches v)
        (by omega) hwin
        (by
          intro p hp
          exact hoffsets p.1 (dogPatchOffsetMem v p hp))
        hpatch
  unfold decode
  rw [hget, hgetTemplate, hparse]
  simp [harg]


theorem dogPatchedJumpDest {v : DogImmutables} {code : ByteArray} {target : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hscan : D_J_auxPreservesTargetBool dogBytecode dogPatchOffsets target 0 = true) :
    (D_J code 0).contains target = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (dogPatchOffsetMem v) hscan

end Benchmarks.Dss.Dog
