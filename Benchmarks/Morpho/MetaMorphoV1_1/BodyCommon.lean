import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Shared source-body guards and ABI-return facts for the runtime proofs. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: the via-IR no-argument calldata guard, in its NOT/ADD form.
theorem calldataLengthCheckOk {size : Nat} (hsz : 4 ≤ size)
    (hhi : size < 2 ^ 255 + 4) (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat size) ⟨0⟩ = ⟨0⟩ := by
  rw [lnot3_add_returnSize hsz hsize]
  apply slt_lit_zero (by decide)
  · exact Nat.zero_le _
  · rw [ulit_toNat' _ (by omega)]
    omega

theorem calldataLengthCheckHuge {size : Nat} (hhi : 2 ^ 255 + 4 ≤ size)
    (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat size) ⟨0⟩ = ⟨1⟩ := by
  rw [lnot3_add_returnSize (by omega) hsize]
  apply slt_lit_one_high (by decide)
  rw [ulit_toNat' _ (by omega)]
  omega

-- LIBRARY CANDIDATE: evaluate a length guard on a byte array held in a local variable.
theorem evalLocalBytesLengthLt {cfg : Config} {solm : Frame} {evm : EVM.State}
    {name : Ident} {bytes : ByteArray} (limit : Nat)
    (hget : solm.locals.get? name = some (.bytes bytes)) :
    evalExpr? cfg solm evm
      (.binary .lt (.arrayLength .localVar ⟨name, []⟩) (.intLit (Int.ofNat limit))) =
      .ok (.bool (decide (bytes.size < limit))) := by
  simp only [evalExpr?, hget, readLocalPath?, evalBinaryOp?, pure, bind, EvalResult.bind]
  congr 3
  exact propext Int.ofNat_lt

-- LIBRARY CANDIDATE: exclude a different selector after a successful selector comparison.
theorem selectorMismatch {hit other cd : ByteArray} (h : (hit == cd) = true)
    (hne : other ≠ hit) : ¬ (other == cd) = true := by
  intro ho
  exact hne ((byteArray_eq_of_beq ho).trans (byteArray_eq_of_beq h).symm)

-- LIBRARY CANDIDATE: advance through the common nonpayable/calldata-bound prefix.
theorem nonpayableCalldataPrefix {cfg : Config} {evm : EVM.State} {solm : Frame}
    {rest : List Stmt} (name : Ident) (limit : Nat)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < limit) :
    ABlock cfg evm solm
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .letDecl name (some .bytes) (.env .msgData) ::
        .require (.binary .lt (.arrayLength .localVar ⟨name, []⟩) (.intLit (Int.ofNat limit))) ::
        rest)
      { solm with locals := solm.locals.insert name (.bytes evm.executionEnv.calldata) } rest := by
  refine ((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep ?_).requireStep ?_
  · simp only [evalExpr?, envValue, pure]
  · simpa only [hhi, decide_true] using
      (evalLocalBytesLengthLt (cfg := cfg) (evm := evm)
        (solm := { solm with locals := solm.locals.insert name (.bytes evm.executionEnv.calldata) })
        limit (store_get_self _ _ _))

-- LIBRARY CANDIDATE: the common nonpayable/calldata-bound prefix rejects an oversized input.
theorem bodyReverts_calldataBound {cfg : Config} {imms : Store} {C : ContractDecl}
    {evm : EVM.State} {locals : Store} {rest : List Stmt} (name : Ident) (limit : Nat)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : limit ≤ evm.executionEnv.calldata.size) :
    ExecTransitionBody cfg C evm locals
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .letDecl name (some .bytes) (.env .msgData) ::
        .require (.binary .lt (.arrayLength .localVar ⟨name, []⟩) (.intLit (Int.ofNat limit))) ::
        rest) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  refine ((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep
    (value := .bytes evm.executionEnv.calldata) ?_).requireRevert ?_
  · simp only [evalExpr?, envValue, pure]
  · have hh : ¬ evm.executionEnv.calldata.size < limit := by omega
    simpa only [hh, decide_false] using
      (evalLocalBytesLengthLt (cfg := cfg) (evm := evm)
        (solm :=
          { contract := C
            locals := locals.insert name (.bytes evm.executionEnv.calldata)
            immutables := imms }) limit (store_get_self _ _ _))

-- LIBRARY CANDIDATE: a single ABI word returned through the solc free-memory pointer.
theorem returnWordMemory (w : UInt256) :
    ((w.toByteArray.write 0 solcFreePtrMem (memLoad ⟨64⟩ solcFreePtrMem).toNat 32).readWithPadding
      (memLoad ⟨64⟩ solcFreePtrMem).toNat 32) = w.toByteArray := by
  have hload : memLoad ⟨64⟩ solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  rw [hload]
  exact solcReturnMem_read128 w

-- LIBRARY CANDIDATE: ABI encoding of a canonical address value.
theorem addressReturnEncoding (addr : EVM.Address) :
    encodeReturnValue? (.elem .address) (.address addr) =
      some (EVM.word addr.val).toByteArray := by
  exact scalarReturnEncoding rfl
    (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
        decide)
    (by simp [encodeABIValue?, encodeABIWord?])

-- LIBRARY CANDIDATE: call an argument-free internal helper that returns one expression.
theorem internalCallReturnExpr {cfg : Config} {solm : Frame} {evm : EVM.State}
    {name retVar : Ident} {retTy : List ABIType} {expr : Expr} {value : Value}
    (hlookup : lookupCallable? solm.contract name =
      some { params := [], returnType := retTy, body := [.return [expr]] })
    (heval : evalExpr? cfg { solm with locals := ∅ } evm expr = .ok value) :
    ExecStmt cfg solm evm (.internalCall name [] retVar)
      (.ok { solm with locals := solm.locals.insert retVar value } evm) := by
  exact ExecStmt.internalCallReturn (calleeSolm := { solm with locals := ∅ })
    (value := some [value]) (by rfl) hlookup rfl
    (ExecFuncBody.execBlockRet (ABlock.start.returns heval))

-- LIBRARY CANDIDATE: a low-bit mask bounds its result at the requested word width.
theorem maskedWord_lt (w : UInt256) (bits : Nat) (hbits : bits ≤ 256) :
    (UInt256.land w (UInt256.ofNat (2 ^ bits - 1))).toNat < 2 ^ bits := by
  have hpow : 2 ^ bits ≤ UInt256.size :=
    Nat.pow_le_pow_right (by decide) hbits
  have hpos : 0 < 2 ^ bits := by positivity
  rw [u256_land_toNat, ulit_toNat' _ (by omega)]
  have := nat_land_le_right w.toNat (2 ^ bits - 1)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

-- GENERALIZES Reasoning.WordArithmetic.rpowShiftRight128_toNat to any bounded shift.
theorem wordShiftRight_toNat (w : UInt256) (bits : Nat) (hbits : bits < 256) :
    (UInt256.shiftRight w (UInt256.ofNat bits)).toNat = w.toNat / 2 ^ bits := by
  have hbound : bits < UInt256.size := lt_trans hbits (by decide)
  simp [UInt256.shiftRight, UInt256.toNat, UInt256.ofNat, Id.run, Fin.ofNat,
    Fin.le_def, Nat.mod_eq_of_lt hbound, show 256 % UInt256.size = 256 from by decide,
    Nat.not_le_of_lt hbits, Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]

-- LIBRARY CANDIDATE: an already canonical address word needs no further masking to encode.
theorem canonicalAddressReturnEncoding (w : UInt256) (hcanon : w.toNat < EVM.addressModulus) :
    encodeReturnValue? (.elem .address) (.address (AccountAddress.ofNat w.toNat)) =
      some w.toByteArray := by
  simpa only [solcAddrMask_clean hcanon] using solcAddressReturnEncoding rfl w

-- LIBRARY CANDIDATE: the high twenty bytes of an EVM word form a canonical address.
theorem shiftRight96_canonical (w : UInt256) :
    (UInt256.shiftRight w ⟨96⟩).toNat < EVM.addressModulus := by
  change (UInt256.shiftRight w (UInt256.ofNat 96)).toNat < 2 ^ 160
  rw [wordShiftRight_toNat w 96 (by decide)]
  exact (Nat.div_lt_iff_lt_mul (by decide)).mpr w.val.isLt

end Benchmarks.Morpho.MetaMorphoV1_1
