import Examples.Precompiles.Ripemd160.Fallback

/-!
# RIPEMD-160 compression runtime

Loop invariants for the optimized block parser and dual-line compression routine.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def runtimeMloadAw (aw addr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat addr.toNat 32)

def runtimeMloadValue (mem : ByteArray) (aw addr : UInt256) : UInt256 :=
  if addr.toNat ≥ mem.size ∨ addr ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding addr.toNat 32))

def runtimeMloadCost (aw addr : UInt256) : Nat :=
  Cₘ (runtimeMloadAw aw addr) - Cₘ aw

/-- Gas-erasing reachability rule used by implementations that share this runtime memory model. -/
theorem RD.runtimeMload {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {addr : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (addr :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MLOAD, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (runtimeMloadValue mem aw addr :: t)
      mem (runtimeMloadAw aw addr) rdata acc (k + 1)
      (C + (runtimeMloadCost aw addr + 3)) := by
  apply RD.mload (runtimeMloadCost aw addr) (runtimeMloadValue mem aw addr)
    (runtimeMloadAw aw addr) h hdec
  · intro s haws hstk
    simp [runtimeMloadCost, runtimeMloadAw, memoryExpansionCost,
      memoryExpansionCost.μᵢ', haws, hstk]
  · rfl
  · rfl
  · exact hov

theorem RDx.runtimeMload {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {addr : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (addr :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MLOAD, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (runtimeMloadValue mem aw addr :: t)
      mem (runtimeMloadAw aw addr) rdata acc (k + 1)
      (C + (runtimeMloadCost aw addr + 3)) := by
  apply RDx.mload (runtimeMloadCost aw addr) (runtimeMloadValue mem aw addr)
    (runtimeMloadAw aw addr) h hdec
  · intro s haws hstk
    simp [runtimeMloadCost, runtimeMloadAw, memoryExpansionCost,
      memoryExpansionCost.μᵢ', haws, hstk]
  · rfl
  · rfl
  · exact hov

def runtimeMstoreMem (mem : ByteArray) (addr value : UInt256) : ByteArray :=
  value.toByteArray.write 0 mem addr.toNat 32

def runtimeMstoreAw (aw addr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat addr.toNat 32)

def runtimeMstoreCost (aw addr : UInt256) : Nat :=
  Cₘ (runtimeMstoreAw aw addr) - Cₘ aw

/-- Gas-erasing reachability rule used by implementations that share this runtime memory model. -/
theorem RD.runtimeMstore {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {addr value : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (addr :: value :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE, .none)) (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t
      (runtimeMstoreMem mem addr value) (runtimeMstoreAw aw addr)
      rdata acc (k + 1) (C + (runtimeMstoreCost aw addr + 3)) := by
  apply RD.mstore (runtimeMstoreCost aw addr) (runtimeMstoreMem mem addr value)
    (runtimeMstoreAw aw addr) h hdec
  · intro s haws hstk
    simp [runtimeMstoreCost, runtimeMstoreAw, memoryExpansionCost,
      memoryExpansionCost.μᵢ', haws, hstk]
  · rfl
  · rfl
  · exact hov

theorem RDx.runtimeMstore {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {addr value : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (addr :: value :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE, .none)) (hov : t.length ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) t
      (runtimeMstoreMem mem addr value) (runtimeMstoreAw aw addr)
      rdata acc (k + 1) (C + (runtimeMstoreCost aw addr + 3)) := by
  apply RDx.mstore (runtimeMstoreCost aw addr) (runtimeMstoreMem mem addr value)
    (runtimeMstoreAw aw addr) h hdec
  · intro s haws hstk
    simp [runtimeMstoreCost, runtimeMstoreAw, memoryExpansionCost,
      memoryExpansionCost.μᵢ', haws, hstk]
  · rfl
  · rfl
  · exact hov

structure RuntimeChain where
  h0 : UInt256
  h1 : UInt256
  h2 : UInt256
  h3 : UInt256
  h4 : UInt256
deriving DecidableEq, Repr

def runtimeInitialChain : RuntimeChain :=
  { h0 := ⟨0x67452301⟩
    h1 := ⟨0xefcdab89⟩
    h2 := ⟨0x98badcfe⟩
    h3 := ⟨0x10325476⟩
    h4 := ⟨0xc3d2e1f0⟩ }

def hashBlockCountWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (calldataSizeWord I + ⟨72⟩) ⟨6⟩

def hashBlockLoopStack (I : ExecutionEnv) (blk : UInt256)
    (h : RuntimeChain) : List UInt256 :=
  [hashPadPtr I, calldataSizeWord I + ⟨72⟩, hashScratchPtr I, blk,
    h.h0, h.h4, h.h3, h.h2, h.h1, ⟨122⟩]

def hashParseLoopStack (I : ExecutionEnv) (blk i : UInt256)
    (h : RuntimeChain) : List UInt256 :=
  [i, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
    hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]

structure RuntimeMemCursor where
  mem : ByteArray
  aw : UInt256

def hashParseAddress (I : ExecutionEnv) (blk i : UInt256) : UInt256 :=
  hashPadPtr I + UInt256.shiftLeft blk ⟨6⟩ + UInt256.shiftLeft i ⟨2⟩

def hashParseScratchAddress (I : ExecutionEnv) (i : UInt256) : UInt256 :=
  hashScratchPtr I + UInt256.shiftLeft i ⟨5⟩

def hashParseAw3 (c : RuntimeMemCursor) (addr : UInt256) : UInt256 :=
  runtimeMloadAw c.aw (addr + ⟨3⟩)

def hashParseV3 (c : RuntimeMemCursor) (addr : UInt256) : UInt256 :=
  runtimeMloadValue c.mem c.aw (addr + ⟨3⟩)

def hashParseAw2 (c : RuntimeMemCursor) (addr : UInt256) : UInt256 :=
  runtimeMloadAw (hashParseAw3 c addr) (addr + ⟨2⟩)

def hashParseV2 (c : RuntimeMemCursor) (addr : UInt256) : UInt256 :=
  runtimeMloadValue c.mem (hashParseAw3 c addr) (addr + ⟨2⟩)

def hashParseAw1 (c : RuntimeMemCursor) (addr : UInt256) : UInt256 :=
  runtimeMloadAw (hashParseAw2 c addr) (addr + ⟨1⟩)

def hashParseV1 (c : RuntimeMemCursor) (addr : UInt256) : UInt256 :=
  runtimeMloadValue c.mem (hashParseAw2 c addr) (addr + ⟨1⟩)

def hashParseAw0 (c : RuntimeMemCursor) (addr : UInt256) : UInt256 :=
  runtimeMloadAw (hashParseAw1 c addr) addr

def hashParseV0 (c : RuntimeMemCursor) (addr : UInt256) : UInt256 :=
  runtimeMloadValue c.mem (hashParseAw1 c addr) addr

def hashParseWord (c : RuntimeMemCursor) (addr : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.lor
      (UInt256.shiftLeft (UInt256.byteAt ⟨0⟩ (hashParseV3 c addr)) ⟨24⟩)
      (UInt256.shiftLeft (UInt256.byteAt ⟨0⟩ (hashParseV2 c addr)) ⟨16⟩))
    (UInt256.lor
      (UInt256.shiftLeft (UInt256.byteAt ⟨0⟩ (hashParseV1 c addr)) ⟨8⟩)
      (UInt256.byteAt ⟨0⟩ (hashParseV0 c addr)))

def hashParseStep (I : ExecutionEnv) (blk i : UInt256)
    (c : RuntimeMemCursor) : RuntimeMemCursor :=
  let addr := hashParseAddress I blk i
  let dst := hashParseScratchAddress I i
  let word := hashParseWord c addr
  { mem := runtimeMstoreMem c.mem dst word
    aw := runtimeMstoreAw (hashParseAw0 c addr) dst }

/-- Exact charge of one parser iteration: 181 fixed gas plus memory expansion. -/
def ripemd160ParseStepGas (I : ExecutionEnv) (blk i : UInt256)
    (c : RuntimeMemCursor) : Nat :=
  let addr := hashParseAddress I blk i
  let dst := hashParseScratchAddress I i
  181
    + runtimeMloadCost c.aw (addr + ⟨3⟩)
    + runtimeMloadCost (hashParseAw3 c addr) (addr + ⟨2⟩)
    + runtimeMloadCost (hashParseAw2 c addr) (addr + ⟨1⟩)
    + runtimeMloadCost (hashParseAw1 c addr) addr
    + runtimeMstoreCost (hashParseAw0 c addr) dst

/-- Take the outer block-loop guard and enter the word parser at index zero. -/
theorem ripemd160X_enterParseLoopGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {mem : ByteArray} {aw : UInt256} {k C : Nat}
    (hblk : UInt256.lt blk (hashBlockCountWord I) = ⟨1⟩)
    (rd1028 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1028⟩ (hashBlockLoopStack I blk h) mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩ (hashParseLoopStack I blk ⟨0⟩ h)
      mem aw ByteArray.empty (cA, σ) k' (C + 59) := by
  have rd1028' : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1028⟩
      [hashPadPtr I, calldataSizeWord I + ⟨72⟩, hashScratchPtr I, blk,
        h.h0, h.h4, h.h3, h.h2, h.h1, ⟨122⟩]
      mem aw ByteArray.empty (cA, σ) k C := by
    simpa [hashBlockLoopStack] using rd1028
  have rd1293 := evm_run rd1028' with [
    jumpdest, dup2, push1 ⟨6⟩, shr, dup5, lt, push2 ⟨1293⟩,
    jumpiT (by rw [show UInt256.lt blk
      (UInt256.shiftRight (calldataSizeWord I + ⟨72⟩) ⟨6⟩) = ⟨1⟩ from hblk]; decide)
      (by jump_dest) ]
  have rd1304 := evm_run rd1293 with [
    jumpdest, swap1, swap2, swap3, swap4, swap6, swap8,
    push0, swap8, swap6, swap8 ]
  exact ⟨k + 19, by
    simpa [hashBlockLoopStack, hashParseLoopStack] using
      (show RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1304⟩ _ mem aw ByteArray.empty (cA, σ) (k + 19) (C + 59) from by
          convert rd1304 using 1 <;> omega)⟩

theorem ripemd160X_enterParseLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {mem : ByteArray} {aw : UInt256} {k C : Nat}
    (hblk : UInt256.lt blk (hashBlockCountWord I) = ⟨1⟩)
    (rd1028 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1028⟩ (hashBlockLoopStack I blk h) mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩ (hashParseLoopStack I blk ⟨0⟩ h)
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_enterParseLoopGas hblk rd1028
  exact ⟨k', C + 59, h'⟩

/-- One iteration of the 16-word little-endian block parser. -/
theorem ripemd160X_parseLoopBodyGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk i : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (hi : UInt256.lt i ⟨16⟩ = ⟨1⟩)
    (rd1304 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩ (hashParseLoopStack I blk i h) c.mem c.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩ (hashParseLoopStack I blk (i + ⟨1⟩) h)
      (hashParseStep I blk i c).mem (hashParseStep I blk i c).aw
      ByteArray.empty (cA, σ) k' (C + ripemd160ParseStepGas I blk i c) := by
  have rd1304' : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩
      [i, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k C := by
    simpa [hashParseLoopStack] using rd1304
  have rd2123 := evm_run rd1304' with [
    jumpdest, push1 ⟨16⟩, dup2, lt, push2 ⟨2123⟩,
    jumpiT (by rw [hi]; decide) (by jump_dest) ]
  have rd2142 := evm_run rd2123 with [
    jumpdest, dup1, push1 ⟨1⟩, swap2, push1 ⟨2⟩, shl,
    dup8, push1 ⟨6⟩, shl, dup6, add, add,
    push1 ⟨3⟩, dup2, add ]
  have rd2143 := RDx.runtimeMload rd2142 (by native_decide) (by simp)
  have rd2152pre := evm_run rd2143 with [
    push0, byte, push1 ⟨24⟩, shl,
    push1 ⟨2⟩, dup3, add ]
  have rd2153 := RDx.runtimeMload rd2152pre (by native_decide) (by simp)
  have rd2163pre := evm_run rd2153 with [
    push0, byte, push1 ⟨16⟩, shl, or, swap1, dup4, dup2, add ]
  have rd2164 := RDx.runtimeMload rd2163pre (by native_decide) (by simp)
  have rd2170pre := evm_run rd2164 with [
    push0, byte, push1 ⟨8⟩, shl, swap1 ]
  have rd2171 := RDx.runtimeMload rd2170pre (by native_decide) (by simp)
  have rd2181pre := evm_run rd2171 with [
    push0, byte, or, or, dup2, push1 ⟨5⟩, shl, dup8, add ]
  have rd2182 := RDx.runtimeMstore rd2181pre (by native_decide) (by simp)
  have rd1304next := evm_run rd2182 with [
    add, push2 ⟨1304⟩, jump (by jump_dest) ]
  have rdExact := RDx.withIndices rd1304next (k' := k + 59)
    (C' := C + ripemd160ParseStepGas I blk i c) (by omega) (by
      simp only [ripemd160ParseStepGas, hashParseAddress, hashParseScratchAddress,
        hashParseAw3, hashParseAw2, hashParseAw1, hashParseAw0]
      omega)
  exact ⟨k + 59, by
    simpa [hashParseLoopStack, hashParseStep, hashParseAddress,
      hashParseScratchAddress, hashParseWord, hashParseV3, hashParseV2,
      hashParseV1, hashParseV0, hashParseAw3, hashParseAw2,
      hashParseAw1, hashParseAw0, u256_add_comm, u256_lor_comm] using rdExact⟩

theorem ripemd160X_parseLoopBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk i : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (hi : UInt256.lt i ⟨16⟩ = ⟨1⟩)
    (rd1304 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩ (hashParseLoopStack I blk i h) c.mem c.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩ (hashParseLoopStack I blk (i + ⟨1⟩) h)
      (hashParseStep I blk i c).mem (hashParseStep I blk i c).aw
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_parseLoopBodyGas hi rd1304
  exact ⟨k', _, h'⟩

def hashParseCursor (I : ExecutionEnv) (blk : UInt256)
    (initial : RuntimeMemCursor) : Nat → RuntimeMemCursor
  | 0 => initial
  | n + 1 => hashParseStep I blk (UInt256.ofNat n) (hashParseCursor I blk initial n)

/-- Remaining exact parser gas, including the 25-gas loop exit. -/
def ripemd160ParseGas (I : ExecutionEnv) (blk : UInt256)
    (initial : RuntimeMemCursor) : Nat → Nat → Nat
  | 0, _ => 25
  | v + 1, i =>
      ripemd160ParseStepGas I blk (UInt256.ofNat i) (hashParseCursor I blk initial i)
        + ripemd160ParseGas I blk initial v (i + 1)

def runtimeStoreCursor (c : RuntimeMemCursor) (addr value : UInt256) : RuntimeMemCursor :=
  { mem := runtimeMstoreMem c.mem addr value
    aw := runtimeMstoreAw c.aw addr }

def hashLeftInitCursor (I : ExecutionEnv) (h : RuntimeChain)
    (c : RuntimeMemCursor) : RuntimeMemCursor :=
  let c := runtimeStoreCursor c (hashScratchPtr I + ⟨512⟩) h.h0
  let c := runtimeStoreCursor c (hashScratchPtr I + ⟨544⟩) h.h1
  let c := runtimeStoreCursor c (hashScratchPtr I + ⟨576⟩) h.h2
  let c := runtimeStoreCursor c (hashScratchPtr I + ⟨608⟩) h.h3
  runtimeStoreCursor c (hashScratchPtr I + ⟨640⟩) h.h4

/-- Exact gas for the five-word line initialization sequence at offsets `base .. base+128`. -/
def ripemd160InitLineGas (c : RuntimeMemCursor) (base : UInt256) : Nat :=
  let aw1 := runtimeMstoreAw c.aw base
  let aw2 := runtimeMstoreAw aw1 (base + ⟨32⟩)
  let aw3 := runtimeMstoreAw aw2 (base + ⟨64⟩)
  let aw4 := runtimeMstoreAw aw3 (base + ⟨96⟩)
  77
    + runtimeMstoreCost c.aw base
    + runtimeMstoreCost aw1 (base + ⟨32⟩)
    + runtimeMstoreCost aw2 (base + ⟨64⟩)
    + runtimeMstoreCost aw3 (base + ⟨96⟩)
    + runtimeMstoreCost aw4 (base + ⟨128⟩)

def leftWordRowWord (group : Nat) : UInt256 :=
  UInt256.ofNat (Model.leftWordRow group)

def leftRotationRowWord (group : Nat) : UInt256 :=
  UInt256.ofNat (Model.leftRotationRow group)

def leftConstantWord (group : Nat) : UInt256 :=
  UInt256.ofNat (Model.leftConstant group)

/-- Exact gas of any of the compiler-generated five-way row-selector helpers. -/
def ripemd160RowSelectorGas : Nat → Nat
  | 0 => 47
  | 1 => 69
  | 2 => 91
  | 3 => 113
  | _ => 130

/-- Exact gas of the left Boolean-function selector. -/
def ripemd160LeftSelectGas : Nat → Nat
  | 0 => 89
  | 1 => 120
  | 2 => 139
  | 3 => 167
  | _ => 172

def mask32Word : UInt256 := ⟨0xffffffff⟩

def runtimeRoundAwA (c : RuntimeMemCursor) (lineBase : UInt256) : UInt256 :=
  runtimeMloadAw c.aw lineBase

def runtimeRoundA (c : RuntimeMemCursor) (lineBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem c.aw lineBase

def runtimeRoundAwB (c : RuntimeMemCursor) (lineBase : UInt256) : UInt256 :=
  runtimeMloadAw (runtimeRoundAwA c lineBase) (lineBase + ⟨32⟩)

def runtimeRoundB (c : RuntimeMemCursor) (lineBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem (runtimeRoundAwA c lineBase) (lineBase + ⟨32⟩)

def runtimeRoundAwC (c : RuntimeMemCursor) (lineBase : UInt256) : UInt256 :=
  runtimeMloadAw (runtimeRoundAwB c lineBase) (lineBase + ⟨64⟩)

def runtimeRoundC (c : RuntimeMemCursor) (lineBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem (runtimeRoundAwB c lineBase) (lineBase + ⟨64⟩)

def runtimeRoundAwD (c : RuntimeMemCursor) (lineBase : UInt256) : UInt256 :=
  runtimeMloadAw (runtimeRoundAwC c lineBase) (lineBase + ⟨96⟩)

def runtimeRoundD (c : RuntimeMemCursor) (lineBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem (runtimeRoundAwC c lineBase) (lineBase + ⟨96⟩)

def runtimeRoundAwE (c : RuntimeMemCursor) (lineBase : UInt256) : UInt256 :=
  runtimeMloadAw (runtimeRoundAwD c lineBase) (lineBase + ⟨128⟩)

def runtimeRoundE (c : RuntimeMemCursor) (lineBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem (runtimeRoundAwD c lineBase) (lineBase + ⟨128⟩)

def runtimeRowEntry (row round : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.shiftRight row (⟨60⟩ - UInt256.shiftLeft (UInt256.land round ⟨15⟩) ⟨2⟩))
    ⟨15⟩

def runtimeRoundMessageAddr (messageBase row round : UInt256) : UInt256 :=
  messageBase + UInt256.shiftLeft (runtimeRowEntry row round) ⟨5⟩

def runtimeRoundAwX (c : RuntimeMemCursor) (lineBase messageBase row round : UInt256) : UInt256 :=
  runtimeMloadAw (runtimeRoundAwE c lineBase)
    (runtimeRoundMessageAddr messageBase row round)

def runtimeRoundX (c : RuntimeMemCursor) (lineBase messageBase row round : UInt256) : UInt256 :=
  runtimeMloadValue c.mem (runtimeRoundAwE c lineBase)
    (runtimeRoundMessageAddr messageBase row round)

def runtimeRoundSum (c : RuntimeMemCursor) (lineBase messageBase round row boolF constant : UInt256) : UInt256 :=
  UInt256.land mask32Word
    (UInt256.land mask32Word boolF + runtimeRoundA c lineBase +
      runtimeRoundX c lineBase messageBase row round + constant)

def runtimeRol32 (value shift : UInt256) : UInt256 :=
  UInt256.land mask32Word
    (UInt256.lor (UInt256.shiftLeft value shift)
      (UInt256.shiftRight value (⟨32⟩ - shift)))

def runtimeRoundNext (c : RuntimeMemCursor)
    (lineBase messageBase round row rotationRow boolF constant : UInt256) : UInt256 :=
  UInt256.land mask32Word
    (runtimeRol32 (runtimeRoundSum c lineBase messageBase round row boolF constant)
      (runtimeRowEntry rotationRow round) + runtimeRoundE c lineBase)

def runtimeRoundCursor (c : RuntimeMemCursor)
    (lineBase messageBase round row rotationRow boolF constant : UInt256) : RuntimeMemCursor :=
  let c1 := runtimeStoreCursor
    { mem := c.mem, aw := runtimeRoundAwX c lineBase messageBase row round }
    lineBase (runtimeRoundE c lineBase)
  let c2 := runtimeStoreCursor c1 (lineBase + ⟨128⟩) (runtimeRoundD c lineBase)
  let c3 := runtimeStoreCursor c2 (lineBase + ⟨96⟩)
    (runtimeRol32 (runtimeRoundC c lineBase) ⟨10⟩)
  let c4 := runtimeStoreCursor c3 (lineBase + ⟨64⟩) (runtimeRoundB c lineBase)
  runtimeStoreCursor c4 (lineBase + ⟨32⟩)
    (runtimeRoundNext c lineBase messageBase round row rotationRow boolF constant)

/-- Exact gas of the shared round kernel, including all memory expansion charges. -/
def ripemd160RoundKernelGas (c : RuntimeMemCursor)
    (lineBase messageBase round row : UInt256) : Nat :=
  let awA := runtimeRoundAwA c lineBase
  let awB := runtimeRoundAwB c lineBase
  let awC := runtimeRoundAwC c lineBase
  let awD := runtimeRoundAwD c lineBase
  let awE := runtimeRoundAwE c lineBase
  let xaddr := UInt256.shiftLeft
      (UInt256.land
        (UInt256.shiftRight row
          (UInt256.sub ⟨60⟩ (UInt256.shiftLeft (UInt256.land round ⟨15⟩) ⟨2⟩)))
        ⟨15⟩) ⟨5⟩ + messageBase
  let awX := runtimeMloadAw awE xaddr
  let aw1 := runtimeMstoreAw awX lineBase
  let aw2 := runtimeMstoreAw aw1 (lineBase + ⟨128⟩)
  let aw3 := runtimeMstoreAw aw2 (lineBase + ⟨96⟩)
  let aw4 := runtimeMstoreAw aw3 (lineBase + ⟨64⟩)
  333
    + runtimeMloadCost c.aw lineBase
    + runtimeMloadCost awA (lineBase + ⟨32⟩)
    + runtimeMloadCost awB (lineBase + ⟨64⟩)
    + runtimeMloadCost awC (lineBase + ⟨96⟩)
    + runtimeMloadCost awD (lineBase + ⟨128⟩)
    + runtimeMloadCost awE xaddr
    + runtimeMstoreCost awX lineBase
    + runtimeMstoreCost aw1 (lineBase + ⟨128⟩)
    + runtimeMstoreCost aw2 (lineBase + ⟨96⟩)
    + runtimeMstoreCost aw3 (lineBase + ⟨64⟩)
    + runtimeMstoreCost aw4 (lineBase + ⟨32⟩)

def runtimeLeftF (group : Nat) (b c d : UInt256) : UInt256 :=
  match group with
  | 0 => UInt256.xor (UInt256.xor b c) d
  | 1 => UInt256.lor (UInt256.land b c) (UInt256.land (UInt256.lnot b) d)
  | 2 => UInt256.xor (UInt256.lor b (UInt256.lnot c)) d
  | 3 => UInt256.lor (UInt256.land b d) (UInt256.land c (UInt256.lnot d))
  | _ => UInt256.xor (UInt256.lor c (UInt256.lnot d)) b

def runtimeRoundPreludeCursor (c : RuntimeMemCursor) (messageBase : UInt256) :
    RuntimeMemCursor :=
  { mem := c.mem
    aw := runtimeMloadAw
      (runtimeMloadAw (runtimeMloadAw c.aw (messageBase + ⟨544⟩))
        (messageBase + ⟨576⟩)) (messageBase + ⟨608⟩) }

def runtimePreludeB (c : RuntimeMemCursor) (messageBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem c.aw (messageBase + ⟨544⟩)

def runtimePreludeC (c : RuntimeMemCursor) (messageBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem (runtimeMloadAw c.aw (messageBase + ⟨544⟩))
    (messageBase + ⟨576⟩)

def runtimePreludeD (c : RuntimeMemCursor) (messageBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem
    (runtimeMloadAw (runtimeMloadAw c.aw (messageBase + ⟨544⟩))
      (messageBase + ⟨576⟩)) (messageBase + ⟨608⟩)

/-- Select the left-line Boolean function and enter the shared round kernel. -/
theorem ripemd160X_selectLeftFGas {cA σ I} {g : Sat256} {s0 : State}
    {messageBase round row rotationRow constant : UInt256}
    {b c d : UInt256} {group : Nat} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5)
    (hov : t.length + 32 ≤ 1024)
    (rd1936 : RDx ripemd160RuntimeBytecode I g s0 ⟨1936⟩
      (d :: c :: b :: messageBase :: round :: row :: rotationRow ::
        UInt256.ofNat group :: constant :: ⟨1988⟩ :: round :: ⟨1⟩ ::
        row :: rotationRow :: constant :: UInt256.ofNat group :: t)
      mem aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ⟨630⟩
      ((messageBase + ⟨512⟩) :: messageBase :: round :: row :: rotationRow ::
        runtimeLeftF group b c d :: constant :: ⟨1988⟩ :: round :: ⟨1⟩ ::
        row :: rotationRow :: constant :: UInt256.ofNat group :: t)
      mem aw rdata (cA, σ) k' (C + ripemd160LeftSelectGas group) := by
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · have rd2058 := evm_run rd1936 with [
      push0, swap8, dup1, push0, eq, push2 ⟨2058⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd630 := evm_run rd2058 with [
      jumpdest, pop, swap2, xor, xor, swap5, pop, push0, dup1, dup1,
      push2 ⟨1975⟩, jump (by jump_dest), jumpdest, pop, pop, pop,
      push2 ⟨512⟩, dup2, add, push2 ⟨630⟩, jump (by jump_dest) ]
    exact ⟨k + 28, by simpa [runtimeLeftF, u256_add_comm] using
      (RDx.withIndices rd630 (k' := k + 28) (C' := C + ripemd160LeftSelectGas 0)
        (by omega) (by norm_num [ripemd160LeftSelectGas]))⟩
  · have rd2041 := evm_run rd1936 with [
      push0, swap8, dup1, push0, eq, push2 ⟨2058⟩,
      jumpiNT (by native_decide), dup1, dup14, eq, push2 ⟨2041⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd630 := evm_run rd2041 with [
      jumpdest, pop, dup3, not, and, swap2, and, or, swap5, pop,
      push0, dup1, dup1, push2 ⟨1975⟩, jump (by jump_dest),
      jumpdest, pop, pop, pop, push2 ⟨512⟩, dup2, add,
      push2 ⟨630⟩, jump (by jump_dest) ]
    exact ⟨k + 36, by simpa [runtimeLeftF, u256_add_comm, u256_land_comm,
      u256_lor_comm] using
      (RDx.withIndices rd630 (k' := k + 36) (C' := C + ripemd160LeftSelectGas 1)
        (by omega) (by norm_num [ripemd160LeftSelectGas]))⟩
  · have rd2025 := evm_run rd1936 with [
      push0, swap8, dup1, push0, eq, push2 ⟨2058⟩,
      jumpiNT (by native_decide), dup1, dup14, eq, push2 ⟨2041⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨2025⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd630 := evm_run rd2025 with [
      jumpdest, pop, swap3, swap7, pop, not, or, xor, swap4,
      push0, dup1, dup1, push2 ⟨1975⟩, jump (by jump_dest),
      jumpdest, pop, pop, pop, push2 ⟨512⟩, dup2, add,
      push2 ⟨630⟩, jump (by jump_dest) ]
    exact ⟨k + 40, by simpa [runtimeLeftF, u256_add_comm, u256_lor_comm] using
      (RDx.withIndices rd630 (k' := k + 40) (C' := C + ripemd160LeftSelectGas 2)
        (by omega) (by norm_num [ripemd160LeftSelectGas]))⟩
  · have rd2007 := evm_run rd1936 with [
      push0, swap8, dup1, push0, eq, push2 ⟨2058⟩,
      jumpiNT (by native_decide), dup1, dup14, eq, push2 ⟨2041⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨2025⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨2007⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd630 := evm_run rd2007 with [
      jumpdest, pop, swap2, dup3, and, swap2, not, and, or, swap5, pop,
      push0, dup1, dup1, push2 ⟨1975⟩, jump (by jump_dest),
      jumpdest, pop, pop, pop, push2 ⟨512⟩, dup2, add,
      push2 ⟨630⟩, jump (by jump_dest) ]
    exact ⟨k + 47, by simpa [runtimeLeftF, u256_add_comm, u256_land_comm,
      u256_lor_comm] using
      (RDx.withIndices rd630 (k' := k + 47) (C' := C + ripemd160LeftSelectGas 3)
        (by omega) (by norm_num [ripemd160LeftSelectGas]))⟩
  · have rd1994 := evm_run rd1936 with [
      push0, swap8, dup1, push0, eq, push2 ⟨2058⟩,
      jumpiNT (by native_decide), dup1, dup14, eq, push2 ⟨2041⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨2025⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨2007⟩,
      jumpiNT (by native_decide), push1 ⟨4⟩, eq, push2 ⟨1994⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd630 := evm_run rd1994 with [
      jumpdest, not, or, xor, swap5, pop, push0, dup1, dup1,
      push2 ⟨1975⟩, jump (by jump_dest), jumpdest, pop, pop, pop,
      push2 ⟨512⟩, dup2, add, push2 ⟨630⟩, jump (by jump_dest) ]
    exact ⟨k + 46, by simpa [runtimeLeftF, u256_add_comm, u256_lor_comm] using
      (RDx.withIndices rd630 (k' := k + 46) (C' := C + ripemd160LeftSelectGas 4)
        (by omega) (by norm_num [ripemd160LeftSelectGas]))⟩

theorem ripemd160X_selectLeftF {cA σ I} {g : Sat256} {s0 : State}
    {messageBase round row rotationRow constant : UInt256}
    {b c d : UInt256} {group : Nat} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hov : t.length + 32 ≤ 1024)
    (rd1936 : RDx ripemd160RuntimeBytecode I g s0 ⟨1936⟩
      (d :: c :: b :: messageBase :: round :: row :: rotationRow ::
        UInt256.ofNat group :: constant :: ⟨1988⟩ :: round :: ⟨1⟩ ::
        row :: rotationRow :: constant :: UInt256.ofNat group :: t)
      mem aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ⟨630⟩
      ((messageBase + ⟨512⟩) :: messageBase :: round :: row :: rotationRow ::
        runtimeLeftF group b c d :: constant :: ⟨1988⟩ :: round :: ⟨1⟩ ::
        row :: rotationRow :: constant :: UInt256.ofNat group :: t)
      mem aw rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_selectLeftFGas hgroup hov rd1936
  exact ⟨k', _, h'⟩

/-- The shared compiler-generated RIPEMD round kernel at PC 630. -/
theorem ripemd160X_roundKernelGas {cA σ I} {g : Sat256} {s0 : State}
    {lineBase messageBase round row rotationRow boolF constant ret : UInt256}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 32 ≤ 1024)
    (hret : (D_J ripemd160RuntimeBytecode 0).contains ret = true)
    (rd630 : RDx ripemd160RuntimeBytecode I g s0 ⟨630⟩
      (lineBase :: messageBase :: round :: row :: rotationRow :: boolF ::
        constant :: ret :: t)
      c.mem c.aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ret t
      (runtimeRoundCursor c lineBase messageBase round row rotationRow boolF constant).mem
      (runtimeRoundCursor c lineBase messageBase round row rotationRow boolF constant).aw
      rdata (cA, σ) k'
        (C + ripemd160RoundKernelGas c lineBase messageBase round row) := by
  have rd639pre := evm_run rd630 with [
    jumpdest, swap4, swap5, swap1, swap6, swap3, swap2, swap3, dup5 ]
  have rd640 := RDx.runtimeMload rd639pre (by native_decide) (by simp; omega)
  have rd646pre := evm_run rd640 with [
    push1 ⟨32⟩, dup7, add, swap8, dup9 ]
  have rd647 := RDx.runtimeMload rd646pre (by native_decide) (by simp; omega)
  have rd654pre := evm_run rd647 with [
    swap6, push1 ⟨64⟩, dup9, add, swap6, dup7 ]
  have rd655 := RDx.runtimeMload rd654pre (by native_decide) (by simp; omega)
  have rd662pre := evm_run rd655 with [
    swap5, push1 ⟨96⟩, dup11, add, swap7, dup8 ]
  have rd663 := RDx.runtimeMload rd662pre (by native_decide) (by simp; omega)
  have rd670pre := evm_run rd663 with [
    swap6, push1 ⟨128⟩, dup13, add, swap6, dup7 ]
  have rd671 := RDx.runtimeMload rd670pre (by native_decide) (by simp; omega)
  have rd696 := evm_run rd671 with [
    swap14, push1 ⟨15⟩, dup16, swap8, and, swap6, dup7,
    push2 ⟨696⟩, swap2, push1 ⟨15⟩, swap2, push1 ⟨2⟩, shl,
    push1 ⟨60⟩, sub, shr, and, swap1, jump (by jump_dest) ]
  have rd713pre := evm_run rd696 with [
    jumpdest, swap6, push1 ⟨2⟩, shl, push1 ⟨60⟩, sub, shr,
    push1 ⟨15⟩, and, swap5, push1 ⟨5⟩, shl, add ]
  have rd714 := RDx.runtimeMload rd713pre (by native_decide) (by simp; omega)
  have rd746pre := evm_run rd714 with [
    swap2, push4 ⟨0xffffffff⟩, and, add, add, add,
    push4 ⟨0xffffffff⟩, and, dup1, dup3, push1 ⟨32⟩, sub, shr,
    swap2, shl, or, push4 ⟨0xffffffff⟩, and, swap8 ]
  have rd747 := RDx.runtimeMstore rd746pre (by native_decide) (by simp; omega)
  have rd748 := RDx.runtimeMstore rd747 (by native_decide) (by simp; omega)
  have rd764pre := evm_run rd748 with [
    dup1, push1 ⟨22⟩, shr, swap1, push1 ⟨10⟩, shl, or,
    push4 ⟨0xffffffff⟩, and, swap1 ]
  have rd765 := RDx.runtimeMstore rd764pre (by native_decide) (by simp; omega)
  have rd766 := RDx.runtimeMstore rd765 (by native_decide) (by simp; omega)
  have rd774pre := evm_run rd766 with [
    add, push4 ⟨0xffffffff⟩, and, swap1 ]
  have rd775 := RDx.runtimeMstore rd774pre (by native_decide) (by simp; omega)
  have rdret := evm_run rd775 with [jump hret]
  have rdExact := RDx.withIndices rdret (k' := k + 109)
    (C' := C + ripemd160RoundKernelGas c lineBase messageBase round row) (by omega) (by
      simp only [ripemd160RoundKernelGas, runtimeRoundAwA, runtimeRoundAwB,
        runtimeRoundAwC, runtimeRoundAwD, runtimeRoundAwE]
      omega)
  exact ⟨k + 109, by
    simpa [runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, mask32Word,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rdExact⟩

theorem ripemd160X_roundKernel {cA σ I} {g : Sat256} {s0 : State}
    {lineBase messageBase round row rotationRow boolF constant ret : UInt256}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 32 ≤ 1024)
    (hret : (D_J ripemd160RuntimeBytecode 0).contains ret = true)
    (rd630 : RDx ripemd160RuntimeBytecode I g s0 ⟨630⟩
      (lineBase :: messageBase :: round :: row :: rotationRow :: boolF ::
        constant :: ret :: t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ret t
      (runtimeRoundCursor c lineBase messageBase round row rotationRow boolF constant).mem
      (runtimeRoundCursor c lineBase messageBase round row rotationRow boolF constant).aw
      rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_roundKernelGas hov hret rd630
  exact ⟨k', _, h'⟩

def runtimeLeftRoundCursor (c : RuntimeMemCursor) (messageBase : UInt256)
    (group round : Nat) : RuntimeMemCursor :=
  let prelude := runtimeRoundPreludeCursor c messageBase
  runtimeRoundCursor prelude (messageBase + ⟨512⟩) messageBase
    (UInt256.ofNat round) (leftWordRowWord group) (leftRotationRowWord group)
    (runtimeLeftF group (runtimePreludeB c messageBase) (runtimePreludeC c messageBase)
      (runtimePreludeD c messageBase)) (leftConstantWord group)

/-- Exact gas from a left-round header through the three Boolean-function input loads. -/
def ripemd160LeftRoundPreludeGas (c : RuntimeMemCursor) (messageBase : UInt256) : Nat :=
  90
    + runtimeMloadCost c.aw (messageBase + ⟨544⟩)
    + runtimeMloadCost (runtimeMloadAw c.aw (messageBase + ⟨544⟩))
        (messageBase + ⟨576⟩)
    + runtimeMloadCost
        (runtimeMloadAw (runtimeMloadAw c.aw (messageBase + ⟨544⟩))
          (messageBase + ⟨576⟩)) (messageBase + ⟨608⟩)

/-- Exact gas of one left-line round. -/
def ripemd160LeftRoundGas (c : RuntimeMemCursor) (messageBase : UInt256)
    (group round : Nat) : Nat :=
  ripemd160LeftRoundPreludeGas c messageBase + ripemd160LeftSelectGas group
    + ripemd160RoundKernelGas (runtimeRoundPreludeCursor c messageBase)
        (messageBase + ⟨512⟩) messageBase (UInt256.ofNat round)
        (leftWordRowWord group) + 15

/-- Execute one left-line round and return to its inner-loop header. -/
theorem ripemd160X_leftRoundGas {cA σ I} {g : Sat256} {s0 : State}
    {messageBase h1 pad len : UInt256} {group round : Nat} {t : List UInt256}
    {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hround : round < 16)
    (hov : t.length + 64 ≤ 1024)
    (rd1883 : RDx ripemd160RuntimeBytecode I g s0 ⟨1883⟩
      (UInt256.ofNat round :: leftWordRowWord group :: leftRotationRowWord group ::
        leftConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
        messageBase :: t)
      c.mem c.aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ⟨1883⟩
      (UInt256.ofNat (round + 1) :: leftWordRowWord group ::
        leftRotationRowWord group :: leftConstantWord group :: UInt256.ofNat group ::
        h1 :: pad :: len :: messageBase :: t)
      (runtimeLeftRoundCursor c messageBase group round).mem
      (runtimeLeftRoundCursor c messageBase group round).aw
      rdata (cA, σ) k' (C + ripemd160LeftRoundGas c messageBase group round) := by
  have hlt : UInt256.lt (UInt256.ofNat round) ⟨16⟩ = ⟨1⟩ := by
    apply ult_one
    rw [UInt256.toNat_ofNat_of_lt
      (lt_trans hround (by norm_num [UInt256.size] : 16 < UInt256.size))]
    norm_num
    exact hround
  have rd1905 := evm_run rd1883 with [
    jumpdest, dup9, push1 ⟨16⟩, dup3, lt, push2 ⟨1905⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest) ]
  have rd1923pre := evm_run rd1905 with [
    jumpdest, swap1, push2 ⟨1988⟩, dup6, dup8, dup7, dup7, dup6, dup8,
    push2 ⟨544⟩, push1 ⟨1⟩, swap10, add ]
  have rd1924 := RDx.runtimeMload rd1923pre (by native_decide) (by simp; omega)
  have rd1929pre := evm_run rd1924 with [push2 ⟨576⟩, dup3, add]
  have rd1930 := RDx.runtimeMload rd1929pre (by native_decide) (by simp; omega)
  have rd1935pre := evm_run rd1930 with [push2 ⟨608⟩, dup4, add]
  have rd1936 := RDx.runtimeMload rd1935pre (by native_decide) (by simp; omega)
  have rd1936Gas := RDx.withIndices rd1936
    (C' := C + ripemd160LeftRoundPreludeGas c messageBase) (by rfl) (by
    simp only [ripemd160LeftRoundPreludeGas]
    omega)
  obtain ⟨k630, rd630⟩ := ripemd160X_selectLeftFGas
    (group := group) (t := h1 :: pad :: len :: messageBase :: t)
    hgroup (by simp; omega) rd1936Gas
  have rd630' : RDx ripemd160RuntimeBytecode I g s0 ⟨630⟩
      ((messageBase + ⟨512⟩) :: messageBase :: UInt256.ofNat round ::
        leftWordRowWord group :: leftRotationRowWord group ::
        runtimeLeftF group (runtimePreludeB c messageBase) (runtimePreludeC c messageBase)
          (runtimePreludeD c messageBase) :: leftConstantWord group :: ⟨1988⟩ ::
        UInt256.ofNat round :: ⟨1⟩ :: leftWordRowWord group ::
        leftRotationRowWord group :: leftConstantWord group :: UInt256.ofNat group ::
        h1 :: pad :: len :: messageBase :: t)
      (runtimeRoundPreludeCursor c messageBase).mem
      (runtimeRoundPreludeCursor c messageBase).aw rdata (cA, σ) k630
        (C + ripemd160LeftRoundPreludeGas c messageBase
          + ripemd160LeftSelectGas group) := by
    simpa [runtimeRoundPreludeCursor, runtimePreludeB, runtimePreludeC,
      runtimePreludeD] using rd630
  obtain ⟨_, rd1988⟩ := ripemd160X_roundKernelGas
    (c := runtimeRoundPreludeCursor c messageBase)
    (ret := ⟨1988⟩)
    (t := UInt256.ofNat round :: ⟨1⟩ :: leftWordRowWord group ::
      leftRotationRowWord group :: leftConstantWord group :: UInt256.ofNat group ::
      h1 :: pad :: len :: messageBase :: t)
    (by simp; omega) (by jump_dest) rd630'
  have rd1883next := evm_run rd1988 with [
    jumpdest, add, push2 ⟨1883⟩, jump (by jump_dest) ]
  have rdExact := RDx.withIndices rd1883next
    (C' := C + ripemd160LeftRoundGas c messageBase group round) (by rfl) (by
      simp only [ripemd160LeftRoundGas]
      omega)
  exact ⟨_, by
    simpa [runtimeLeftRoundCursor, runtimeRoundPreludeCursor, runtimePreludeB,
      runtimePreludeC, runtimePreludeD, u256_add_comm, u256_one_add_ofNat] using
      rdExact⟩

theorem ripemd160X_leftRound {cA σ I} {g : Sat256} {s0 : State}
    {messageBase h1 pad len : UInt256} {group round : Nat} {t : List UInt256}
    {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hround : round < 16) (hov : t.length + 64 ≤ 1024)
    (rd1883 : RDx ripemd160RuntimeBytecode I g s0 ⟨1883⟩
      (UInt256.ofNat round :: leftWordRowWord group :: leftRotationRowWord group ::
        leftConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
        messageBase :: t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ⟨1883⟩
      (UInt256.ofNat (round + 1) :: leftWordRowWord group ::
        leftRotationRowWord group :: leftConstantWord group :: UInt256.ofNat group ::
        h1 :: pad :: len :: messageBase :: t)
      (runtimeLeftRoundCursor c messageBase group round).mem
      (runtimeLeftRoundCursor c messageBase group round).aw
      rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_leftRoundGas hgroup hround hov rd1883
  exact ⟨k', _, h'⟩

def runtimeLeftGroupCursor (initial : RuntimeMemCursor) (messageBase : UInt256)
    (group : Nat) : Nat → RuntimeMemCursor
  | 0 => initial
  | round + 1 => runtimeLeftRoundCursor
      (runtimeLeftGroupCursor initial messageBase group round) messageBase group round

def ripemd160LeftGroupGas (initial : RuntimeMemCursor) (messageBase : UInt256)
    (group : Nat) : Nat → Nat → Nat
  | 0, _ => 53
  | v + 1, round =>
      ripemd160LeftRoundGas (runtimeLeftGroupCursor initial messageBase group round)
          messageBase group round
        + ripemd160LeftGroupGas initial messageBase group v (round + 1)

/-- Execute all sixteen rounds in one left-line group. -/
theorem ripemd160X_leftGroupGas {cA σ I} {g : Sat256} {s0 : State}
    {messageBase h1 pad len : UInt256} {group : Nat} {t : List UInt256}
    {initial : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hov : t.length + 64 ≤ 1024)
    (rd1883 : RDx ripemd160RuntimeBytecode I g s0 ⟨1883⟩
      (UInt256.ofNat 0 :: leftWordRowWord group :: leftRotationRowWord group ::
        leftConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
        messageBase :: t)
      initial.mem initial.aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ⟨1350⟩
      (UInt256.ofNat (group + 1) :: h1 :: pad :: len :: messageBase :: t)
      (runtimeLeftGroupCursor initial messageBase group 16).mem
      (runtimeLeftGroupCursor initial messageBase group 16).aw
      rdata (cA, σ) k'
        (C + ripemd160LeftGroupGas initial messageBase group 16 0) := by
  let Inv : Nat → Nat → Prop := fun v round => round + v = 16
  let stk : Nat → List UInt256 := fun round =>
    UInt256.ofNat round :: leftWordRowWord group :: leftRotationRowWord group ::
      leftConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
      messageBase :: t
  let cursor : Nat → RuntimeMemCursor :=
    runtimeLeftGroupCursor initial messageBase group
  let exitStk : Nat → List UInt256 := fun _ =>
    UInt256.ofNat (group + 1) :: h1 :: pad :: len :: messageBase :: t
  have hexit : ∀ round, Inv 0 round → ∀ k C,
      RDx ripemd160RuntimeBytecode I g s0 ⟨1883⟩ (stk round)
        (cursor round).mem (cursor round).aw rdata (cA, σ) k C →
      ∃ k', RDx ripemd160RuntimeBytecode I g s0 ⟨1350⟩ (exitStk round)
        (cursor round).mem (cursor round).aw rdata (cA, σ) k'
          (C + ripemd160LeftGroupGas initial messageBase group 0 round) := by
    intro round hi k C rd
    have hre : round = 16 := by dsimp [Inv] at hi; omega
    subst round
    have rd' : RDx ripemd160RuntimeBytecode I g s0 ⟨1883⟩
        (UInt256.ofNat 16 :: leftWordRowWord group :: leftRotationRowWord group ::
          leftConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
          messageBase :: t)
        (cursor 16).mem (cursor 16).aw rdata (cA, σ) k C := by
      simpa [stk] using rd
    have rd1350 := evm_run rd' with [
      jumpdest, dup9, push1 ⟨16⟩, dup3, lt, push2 ⟨1905⟩,
      jumpiNT (by native_decide), pop, pop, pop, pop, pop,
      push1 ⟨1⟩, add, push2 ⟨1350⟩, jump (by jump_dest) ]
    exact ⟨k + 16, by
      simpa [stk, exitStk, u256_add_comm, u256_one_add_ofNat,
        ripemd160LeftGroupGas] using
        (RDx.withIndices rd1350 (k' := k + 16) (C' := C + 53)
          (by omega) (by omega))⟩
  have hbody : ∀ v round, Inv (v + 1) round → ∀ k C,
      RDx ripemd160RuntimeBytecode I g s0 ⟨1883⟩ (stk round)
        (cursor round).mem (cursor round).aw rdata (cA, σ) k C →
      ∃ round' k' dC, Inv v round' ∧
        ripemd160LeftGroupGas initial messageBase group (v + 1) round =
          dC + ripemd160LeftGroupGas initial messageBase group v round' ∧
        RDx ripemd160RuntimeBytecode I g s0 ⟨1883⟩ (stk round')
          (cursor round').mem (cursor round').aw rdata (cA, σ) k' (C + dC) := by
    intro v round hi k C rd
    have hr : round < 16 := by dsimp [Inv] at hi; omega
    obtain ⟨k', rd'⟩ := ripemd160X_leftRoundGas hgroup hr hov
      (by simpa [stk] using rd)
    refine ⟨round + 1, k',
      ripemd160LeftRoundGas (cursor round) messageBase group round, ?_, ?_, ?_⟩
    · dsimp [Inv] at hi ⊢; omega
    · rfl
    · simpa [stk, cursor, runtimeLeftGroupCursor] using rd'
  obtain ⟨round, k', hi, rd'⟩ :=
    RDx.whileLoopCarryGas (code := ripemd160RuntimeBytecode) (ee := I) (g := g)
      (s0 := s0) (rdata := rdata) (acc := (cA, σ)) (α := Nat)
      ⟨1883⟩ ⟨1350⟩ Inv stk (fun round => (cursor round).mem)
      (fun round => (cursor round).aw) exitStk
      (ripemd160LeftGroupGas initial messageBase group) hexit hbody 16 0
      (by simp [Inv]) k C (by simpa [stk, cursor] using rd1883)
  have hre : round = 16 := by dsimp [Inv] at hi; omega
  subst round
  exact ⟨k', by simpa [cursor, exitStk] using rd'⟩

theorem ripemd160X_leftGroup {cA σ I} {g : Sat256} {s0 : State}
    {messageBase h1 pad len : UInt256} {group : Nat} {t : List UInt256}
    {initial : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hov : t.length + 64 ≤ 1024)
    (rd1883 : RDx ripemd160RuntimeBytecode I g s0 ⟨1883⟩
      (UInt256.ofNat 0 :: leftWordRowWord group :: leftRotationRowWord group ::
        leftConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
        messageBase :: t) initial.mem initial.aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ⟨1350⟩
      (UInt256.ofNat (group + 1) :: h1 :: pad :: len :: messageBase :: t)
      (runtimeLeftGroupCursor initial messageBase group 16).mem
      (runtimeLeftGroupCursor initial messageBase group 16).aw
      rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_leftGroupGas hgroup hov rd1883
  exact ⟨k', _, h'⟩

/-- The compiler-generated left message-index row selector at PC 186. -/
theorem ripemd160X_leftWordRowGas {cA σ I} {g : Sat256}
    {s0 : State} {ret : UInt256} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {group : Nat}
    (hgroup : group < 5)
    (hov : t.length + 5 ≤ 1024)
    (hret : (D_J ripemd160RuntimeBytecode 0).contains ret = true)
    (rd186 : RDx ripemd160RuntimeBytecode I g s0 ⟨186⟩
      (UInt256.ofNat group :: ret :: t) mem aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ret
      (leftWordRowWord group :: t) mem aw rdata (cA, σ) k'
        (C + ripemd160RowSelectorGas group) := by
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · have rd283 := evm_run rd186 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨283⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd283 with [
      jumpdest, pop, push8 ⟨0x0123456789abcdef⟩, swap2, pop,
      jump hret ]
    exact ⟨k + 14, by simpa [leftWordRowWord, Model.leftWordRow] using
      (RDx.withIndices rdret (k' := k + 14) (C' := C + ripemd160RowSelectorGas 0)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩

  · have rd269 := evm_run rd186 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨283⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨269⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd269 with [
      jumpdest, pop, push8 ⟨0x74d1a6f3c0952eb8⟩, swap2, pop,
      jump hret ]
    exact ⟨k + 19, by simpa [leftWordRowWord, Model.leftWordRow] using
      (RDx.withIndices rdret (k' := k + 19) (C' := C + ripemd160RowSelectorGas 1)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd255 := evm_run rd186 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨283⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨269⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨255⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd255 with [
      jumpdest, pop, push8 ⟨0x3ae49f812706db5c⟩, swap2, pop,
      jump hret ]
    exact ⟨k + 24, by simpa [leftWordRowWord, Model.leftWordRow] using
      (RDx.withIndices rdret (k' := k + 24) (C' := C + ripemd160RowSelectorGas 2)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd241 := evm_run rd186 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨283⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨269⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨255⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨241⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd241 with [
      jumpdest, pop, push8 ⟨0x19ba08c4d37fe562⟩, swap2, pop,
      jump hret ]
    exact ⟨k + 29, by simpa [leftWordRowWord, Model.leftWordRow] using
      (RDx.withIndices rdret (k' := k + 29) (C' := C + ripemd160RowSelectorGas 3)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd228 := evm_run rd186 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨283⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨269⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨255⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨241⟩,
      jumpiNT (by native_decide), push1 ⟨4⟩, eq, push2 ⟨228⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd228 with [
      jumpdest, push8 ⟨0x40597c2ae138b6fd⟩, swap2, pop,
      jump hret ]
    exact ⟨k + 32, by simpa [leftWordRowWord, Model.leftWordRow] using
      (RDx.withIndices rdret (k' := k + 32) (C' := C + ripemd160RowSelectorGas 4)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩

theorem ripemd160X_leftWordRow {cA σ I} {g : Sat256}
    {s0 : State} {ret : UInt256} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {group : Nat} (hgroup : group < 5) (hov : t.length + 5 ≤ 1024)
    (hret : (D_J ripemd160RuntimeBytecode 0).contains ret = true)
    (rd186 : RDx ripemd160RuntimeBytecode I g s0 ⟨186⟩
      (UInt256.ofNat group :: ret :: t) mem aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ret
      (leftWordRowWord group :: t) mem aw rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_leftWordRowGas hgroup hov hret rd186
  exact ⟨k', _, h'⟩

/-- The compiler-generated left rotation row selector at PC 297. -/
theorem ripemd160X_leftRotationRowGas {cA σ I} {g : Sat256}
    {s0 : State} {ret : UInt256} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {group : Nat}
    (hgroup : group < 5)
    (hov : t.length + 5 ≤ 1024)
    (hret : (D_J ripemd160RuntimeBytecode 0).contains ret = true)
    (rd297 : RDx ripemd160RuntimeBytecode I g s0 ⟨297⟩
      (UInt256.ofNat group :: ret :: t) mem aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ret
      (leftRotationRowWord group :: t) mem aw rdata (cA, σ) k'
        (C + ripemd160RowSelectorGas group) := by
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · have rd394 := evm_run rd297 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨394⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd394 with [
      jumpdest, pop, push8 ⟨0xbefc5879bdef6798⟩, swap2, pop, jump hret ]
    exact ⟨k + 14, by simpa [leftRotationRowWord, Model.leftRotationRow] using
      (RDx.withIndices rdret (k' := k + 14) (C' := C + ripemd160RowSelectorGas 0)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd380 := evm_run rd297 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨394⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨380⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd380 with [
      jumpdest, pop, push8 ⟨0x768db97f7cf9b7dc⟩, swap2, pop, jump hret ]
    exact ⟨k + 19, by simpa [leftRotationRowWord, Model.leftRotationRow] using
      (RDx.withIndices rdret (k' := k + 19) (C' := C + ripemd160RowSelectorGas 1)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd366 := evm_run rd297 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨394⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨380⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨366⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd366 with [
      jumpdest, pop, push8 ⟨0xbd67e9dfe8d65c75⟩, swap2, pop, jump hret ]
    exact ⟨k + 24, by simpa [leftRotationRowWord, Model.leftRotationRow] using
      (RDx.withIndices rdret (k' := k + 24) (C' := C + ripemd160RowSelectorGas 2)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd352 := evm_run rd297 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨394⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨380⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨366⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨352⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd352 with [
      jumpdest, pop, push8 ⟨0xbcefef989e56865c⟩, swap2, pop, jump hret ]
    exact ⟨k + 29, by simpa [leftRotationRowWord, Model.leftRotationRow] using
      (RDx.withIndices rdret (k' := k + 29) (C' := C + ripemd160RowSelectorGas 3)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd339 := evm_run rd297 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨394⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨380⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨366⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨352⟩,
      jumpiNT (by native_decide), push1 ⟨4⟩, eq, push2 ⟨339⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd339 with [
      jumpdest, push8 ⟨0x9f5b68dc5cdeb856⟩, swap2, pop, jump hret ]
    exact ⟨k + 32, by simpa [leftRotationRowWord, Model.leftRotationRow] using
      (RDx.withIndices rdret (k' := k + 32) (C' := C + ripemd160RowSelectorGas 4)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩

theorem ripemd160X_leftRotationRow {cA σ I} {g : Sat256}
    {s0 : State} {ret : UInt256} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {group : Nat} (hgroup : group < 5) (hov : t.length + 5 ≤ 1024)
    (hret : (D_J ripemd160RuntimeBytecode 0).contains ret = true)
    (rd297 : RDx ripemd160RuntimeBytecode I g s0 ⟨297⟩
      (UInt256.ofNat group :: ret :: t) mem aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ret
      (leftRotationRowWord group :: t) mem aw rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_leftRotationRowGas hgroup hov hret rd297
  exact ⟨k', _, h'⟩

def hashLeftGroupStack (I : ExecutionEnv) (blk : UInt256)
    (h : RuntimeChain) (group : Nat) : List UInt256 :=
  [UInt256.ofNat group, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
    hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]

def hashLeftRoundStack (I : ExecutionEnv) (blk : UInt256)
    (h : RuntimeChain) (group round : Nat) : List UInt256 :=
  [UInt256.ofNat round, leftWordRowWord group, leftRotationRowWord group,
    leftConstantWord group, UInt256.ofNat group, h.h1, hashPadPtr I,
    calldataSizeWord I + ⟨72⟩, hashScratchPtr I, blk, h.h2, h.h0,
    h.h4, h.h3, ⟨122⟩]

def ripemd160LeftConstantControlGas : Nat → Nat
  | 0 => 97
  | 1 => 56
  | 2 => 78
  | 3 => 100
  | _ => 117

def ripemd160EnterLeftGas (group : Nat) : Nat :=
  59 + ripemd160RowSelectorGas group + ripemd160RowSelectorGas group
    + ripemd160LeftConstantControlGas group

/-- Select a left-line group's rows and additive constant, then enter its round loop. -/
theorem ripemd160X_enterLeftRoundsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor}
    {group : Nat} {k C : Nat}
    (hgroup : group < 5)
    (rd1350 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1350⟩ (hashLeftGroupStack I blk h group) c.mem c.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1883⟩ (hashLeftRoundStack I blk h group 0) c.mem c.aw
      ByteArray.empty (cA, σ) k' (C + ripemd160EnterLeftGas group) := by
  have hiWord : UInt256.lt (UInt256.ofNat group) ⟨5⟩ = ⟨1⟩ := by
    apply ult_one
    rw [UInt256.toNat_ofNat_of_lt
      (lt_trans hgroup (by norm_num [UInt256.size] : 5 < UInt256.size))]
    norm_num
    exact hgroup
  have rd1350' : RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [UInt256.ofNat group, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k C := by
    simpa [hashLeftGroupStack] using rd1350
  have rd1828 := evm_run rd1350' with [
    jumpdest, push1 ⟨5⟩, dup2, lt, push2 ⟨1828⟩,
    jumpiT (by rw [hiWord]; decide) (by jump_dest) ]
  have rd186 := evm_run rd1828 with [
    jumpdest, push2 ⟨1837⟩, dup2, push2 ⟨186⟩, jump (by jump_dest) ]
  have rd186Gas := RDx.withIndices rd186 (C' := C + 41) (by rfl) (by omega)
  obtain ⟨_, rd1837⟩ := ripemd160X_leftWordRowGas hgroup (by simp)
    (by jump_dest) rd186Gas
  have rd297 := evm_run rd1837 with [
    jumpdest, push2 ⟨1846⟩, dup3, push2 ⟨297⟩, jump (by jump_dest) ]
  obtain ⟨_, rd1846⟩ := ripemd160X_leftRotationRowGas hgroup (by simp)
    (by jump_dest) rd297
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · have rd1881 := evm_run rd1846 with [
      jumpdest, push0, swap2, dup4,
      dup1, push1 ⟨1⟩, eq, push2 ⟨2110⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨2⟩, eq, push2 ⟨2097⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨3⟩, eq, push2 ⟨2084⟩, jumpiNT (by native_decide),
      push1 ⟨4⟩, eq, push2 ⟨2072⟩, jumpiNT (by native_decide),
      jumpdest, push0 ]
    exact ⟨_, by simpa [hashLeftRoundStack, leftConstantWord, Model.leftConstant] using
      (RDx.withIndices rd1881 (by rfl) (by
        norm_num [ripemd160EnterLeftGas, ripemd160RowSelectorGas,
          ripemd160LeftConstantControlGas]))⟩
  · have rd2110 := evm_run rd1846 with [
      jumpdest, push0, swap2, dup4,
      dup1, push1 ⟨1⟩, eq, push2 ⟨2110⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd1881 := evm_run rd2110 with [
      jumpdest, pop, push4 ⟨0x5a827999⟩, swap3, pop,
      push2 ⟨1881⟩, jump (by jump_dest), jumpdest, push0 ]
    exact ⟨_, by simpa [hashLeftRoundStack, leftConstantWord, Model.leftConstant] using
      (RDx.withIndices rd1881 (by rfl) (by
        norm_num [ripemd160EnterLeftGas, ripemd160RowSelectorGas,
          ripemd160LeftConstantControlGas]))⟩
  · have rd2097 := evm_run rd1846 with [
      jumpdest, push0, swap2, dup4,
      dup1, push1 ⟨1⟩, eq, push2 ⟨2110⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨2⟩, eq, push2 ⟨2097⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd1881 := evm_run rd2097 with [
      jumpdest, pop, push4 ⟨0x6ed9eba1⟩, swap3, pop,
      push2 ⟨1881⟩, jump (by jump_dest), jumpdest, push0 ]
    exact ⟨_, by simpa [hashLeftRoundStack, leftConstantWord, Model.leftConstant] using
      (RDx.withIndices rd1881 (by rfl) (by
        norm_num [ripemd160EnterLeftGas, ripemd160RowSelectorGas,
          ripemd160LeftConstantControlGas]))⟩
  · have rd2084 := evm_run rd1846 with [
      jumpdest, push0, swap2, dup4,
      dup1, push1 ⟨1⟩, eq, push2 ⟨2110⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨2⟩, eq, push2 ⟨2097⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨3⟩, eq, push2 ⟨2084⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd1881 := evm_run rd2084 with [
      jumpdest, pop, push4 ⟨0x8f1bbcdc⟩, swap3, pop,
      push2 ⟨1881⟩, jump (by jump_dest), jumpdest, push0 ]
    exact ⟨_, by simpa [hashLeftRoundStack, leftConstantWord, Model.leftConstant] using
      (RDx.withIndices rd1881 (by rfl) (by
        norm_num [ripemd160EnterLeftGas, ripemd160RowSelectorGas,
          ripemd160LeftConstantControlGas]))⟩
  · have rd2072 := evm_run rd1846 with [
      jumpdest, push0, swap2, dup4,
      dup1, push1 ⟨1⟩, eq, push2 ⟨2110⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨2⟩, eq, push2 ⟨2097⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨3⟩, eq, push2 ⟨2084⟩, jumpiNT (by native_decide),
      push1 ⟨4⟩, eq, push2 ⟨2072⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd1881 := evm_run rd2072 with [
      jumpdest, push4 ⟨0xa953fd4e⟩, swap3, pop,
      push2 ⟨1881⟩, jump (by jump_dest), jumpdest, push0 ]
    exact ⟨_, by simpa [hashLeftRoundStack, leftConstantWord, Model.leftConstant] using
      (RDx.withIndices rd1881 (by rfl) (by
        norm_num [ripemd160EnterLeftGas, ripemd160RowSelectorGas,
          ripemd160LeftConstantControlGas]))⟩

theorem ripemd160X_enterLeftRounds {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor}
    {group : Nat} {k C : Nat} (hgroup : group < 5)
    (rd1350 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1350⟩ (hashLeftGroupStack I blk h group) c.mem c.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1883⟩ (hashLeftRoundStack I blk h group 0) c.mem c.aw
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_enterLeftRoundsGas hgroup rd1350
  exact ⟨k', _, h'⟩

/-- Exit the parser after all sixteen words have been written. -/
theorem ripemd160X_parseLoopExitGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd1304 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩ (hashParseLoopStack I blk ⟨16⟩ h) c.mem c.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1314⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k' (C + 25) := by
  have rd1304' : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩
      [⟨16⟩, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k C := by
    simpa [hashParseLoopStack] using rd1304
  have rd1314 := evm_run rd1304' with [
    jumpdest, push1 ⟨16⟩, dup2, lt, push2 ⟨2123⟩,
    jumpiNT (by native_decide), pop ]
  exact ⟨k + 7, by convert rd1314 using 1 <;> omega⟩

theorem ripemd160X_parseLoopExit {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd1304 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩ (hashParseLoopStack I blk ⟨16⟩ h) c.mem c.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1314⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_parseLoopExitGas rd1304
  exact ⟨k', C + 25, h'⟩

/-- Run the complete fixed-size little-endian parser for one message block. -/
theorem ripemd160X_parseBlockGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (rd1304 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩ (hashParseLoopStack I blk ⟨0⟩ h) initial.mem initial.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1314⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      (hashParseCursor I blk initial 16).mem
      (hashParseCursor I blk initial 16).aw
      ByteArray.empty (cA, σ) k' (C + ripemd160ParseGas I blk initial 16 0) := by
  let Inv : Nat → Nat → Prop := fun v i => i + v = 16
  let stk : Nat → List UInt256 := fun i =>
    hashParseLoopStack I blk (UInt256.ofNat i) h
  let cursor : Nat → RuntimeMemCursor := hashParseCursor I blk initial
  let exitStk : Nat → List UInt256 := fun _ =>
    [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
      hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
  have hexit : ∀ i, Inv 0 i → ∀ k C,
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1304⟩ (stk i) (cursor i).mem (cursor i).aw
        ByteArray.empty (cA, σ) k C →
      ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1314⟩ (exitStk i) (cursor i).mem (cursor i).aw
        ByteArray.empty (cA, σ) k' (C + ripemd160ParseGas I blk initial 0 i) := by
    intro i hi k C rd
    have hieq : i = 16 := by dsimp [Inv] at hi; omega
    subst i
    simpa [stk, exitStk, ripemd160ParseGas] using
      ripemd160X_parseLoopExitGas (by simpa [stk] using rd)
  have hbody : ∀ v i, Inv (v + 1) i → ∀ k C,
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1304⟩ (stk i) (cursor i).mem (cursor i).aw
        ByteArray.empty (cA, σ) k C →
      ∃ i' k' dC, Inv v i' ∧
        ripemd160ParseGas I blk initial (v + 1) i =
          dC + ripemd160ParseGas I blk initial v i' ∧
        RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨1304⟩ (stk i') (cursor i').mem (cursor i').aw
          ByteArray.empty (cA, σ) k' (C + dC) := by
    intro v i hi k C rd
    have hit : i < 16 := by dsimp [Inv] at hi; omega
    have hiWord : UInt256.lt (UInt256.ofNat i) ⟨16⟩ = ⟨1⟩ := by
      apply ult_one
      rw [UInt256.toNat_ofNat_of_lt
        (lt_trans hit (by norm_num [UInt256.size] : 16 < UInt256.size))]
      norm_num
      exact hit
    obtain ⟨k', rd'⟩ := ripemd160X_parseLoopBodyGas hiWord (by simpa [stk] using rd)
    refine ⟨i + 1, k',
      ripemd160ParseStepGas I blk (UInt256.ofNat i) (cursor i), ?_, ?_, ?_⟩
    · dsimp [Inv] at hi ⊢; omega
    · rfl
    · simpa [stk, cursor, hashParseCursor, u256_add_comm, u256_one_add_ofNat] using rd'
  obtain ⟨i, k', hi, rd'⟩ :=
    RDx.whileLoopCarryGas (code := ripemd160RuntimeBytecode) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty)
      (acc := (cA, σ)) (α := Nat) ⟨1304⟩ ⟨1314⟩ Inv stk
      (fun i => (cursor i).mem) (fun i => (cursor i).aw) exitStk
      (ripemd160ParseGas I blk initial) hexit hbody 16 0
      (by simp [Inv]) k C (by simpa [stk, cursor] using rd1304)
  have hieq : i = 16 := by dsimp [Inv] at hi; omega
  subst i
  exact ⟨k', by simpa [cursor, exitStk] using rd'⟩

theorem ripemd160X_parseBlock {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (rd1304 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1304⟩ (hashParseLoopStack I blk ⟨0⟩ h) initial.mem initial.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1314⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      (hashParseCursor I blk initial 16).mem
      (hashParseCursor I blk initial 16).aw
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_parseBlockGas rd1304
  exact ⟨k', _, h'⟩

/-- Store the left-line initial state and enter its five-group loop. -/
theorem ripemd160X_reachLeftGroupsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd1314 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1314⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1350⟩
      [⟨0⟩, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      (hashLeftInitCursor I h c).mem (hashLeftInitCursor I h c).aw
      ByteArray.empty (cA, σ) k'
        (C + ripemd160InitLineGas c (hashScratchPtr I + ⟨512⟩)) := by
  have rd1319 := evm_run rd1314 with [dup7, push2 ⟨512⟩, dup6, add]
  have rd1321 := RDx.runtimeMstore rd1319 (by native_decide) (by simp)
  have rd1326 := evm_run rd1321 with [dup1, push2 ⟨544⟩, dup6, add]
  have rd1328 := RDx.runtimeMstore rd1326 (by native_decide) (by simp)
  have rd1333 := evm_run rd1328 with [dup6, push2 ⟨576⟩, dup6, add]
  have rd1335 := RDx.runtimeMstore rd1333 (by native_decide) (by simp)
  have rd1340 := evm_run rd1335 with [dup9, push2 ⟨608⟩, dup6, add]
  have rd1342 := RDx.runtimeMstore rd1340 (by native_decide) (by simp)
  have rd1347 := evm_run rd1342 with [dup8, push2 ⟨640⟩, dup6, add]
  have rd1349 := RDx.runtimeMstore rd1347 (by native_decide) (by simp)
  have rd1350 := evm_run rd1349 with [push0]
  have rdExact := RDx.withIndices rd1350 (k' := k + 26)
    (C' := C + ripemd160InitLineGas c (hashScratchPtr I + ⟨512⟩)) (by omega) (by
      simp only [ripemd160InitLineGas]
      norm_num [show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide,
        show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide,
        show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide,
        show (⟨512⟩ : UInt256) + ⟨128⟩ = ⟨640⟩ by native_decide,
        u256_add_assoc]
      omega)
  exact ⟨k + 26, by
    simpa [hashLeftInitCursor, runtimeStoreCursor, u256_add_comm] using rdExact⟩

theorem ripemd160X_reachLeftGroups {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd1314 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1314⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1350⟩
      [⟨0⟩, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      (hashLeftInitCursor I h c).mem (hashLeftInitCursor I h c).aw
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_reachLeftGroupsGas rd1314
  exact ⟨k', _, h'⟩

def runtimeLeftLineCursor (initial : RuntimeMemCursor) (messageBase : UInt256) :
    Nat → RuntimeMemCursor
  | 0 => initial
  | group + 1 => runtimeLeftGroupCursor
      (runtimeLeftLineCursor initial messageBase group) messageBase group 16

def ripemd160LeftLineGas (initial : RuntimeMemCursor) (messageBase : UInt256) :
    Nat → Nat → Nat
  | 0, _ => 25
  | v + 1, group =>
      ripemd160EnterLeftGas group
        + ripemd160LeftGroupGas (runtimeLeftLineCursor initial messageBase group)
            messageBase group 16 0
        + ripemd160LeftLineGas initial messageBase v (group + 1)

/-- Execute all five left-line groups and stop before right-line initialization. -/
theorem ripemd160X_leftLineGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (rd1350 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1350⟩ (hashLeftGroupStack I blk h 0) initial.mem initial.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1360⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      (runtimeLeftLineCursor initial (hashScratchPtr I) 5).mem
      (runtimeLeftLineCursor initial (hashScratchPtr I) 5).aw
      ByteArray.empty (cA, σ) k'
        (C + ripemd160LeftLineGas initial (hashScratchPtr I) 5 0) := by
  let Inv : Nat → Nat → Prop := fun v group => group + v = 5
  let stk : Nat → List UInt256 := fun group => hashLeftGroupStack I blk h group
  let cursor : Nat → RuntimeMemCursor :=
    runtimeLeftLineCursor initial (hashScratchPtr I)
  let exitStk : Nat → List UInt256 := fun _ =>
    [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
      hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
  have hexit : ∀ group, Inv 0 group → ∀ k C,
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1350⟩ (stk group) (cursor group).mem (cursor group).aw
        ByteArray.empty (cA, σ) k C →
      ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1360⟩ (exitStk group) (cursor group).mem (cursor group).aw
        ByteArray.empty (cA, σ) k'
          (C + ripemd160LeftLineGas initial (hashScratchPtr I) 0 group) := by
    intro group hi k C rd
    have hge : group = 5 := by dsimp [Inv] at hi; omega
    subst group
    have rd' : RDx ripemd160RuntimeBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
        [⟨5⟩, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
          hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
        (cursor 5).mem (cursor 5).aw ByteArray.empty (cA, σ) k C := by
      simpa [stk, hashLeftGroupStack] using rd
    have rd1360 := evm_run rd' with [
      jumpdest, push1 ⟨5⟩, dup2, lt, push2 ⟨1828⟩,
      jumpiNT (by native_decide), pop ]
    exact ⟨k + 7, by simpa [exitStk, ripemd160LeftLineGas] using
      (RDx.withIndices rd1360 (k' := k + 7) (C' := C + 25)
        (by omega) (by omega))⟩
  have hbody : ∀ v group, Inv (v + 1) group → ∀ k C,
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1350⟩ (stk group) (cursor group).mem (cursor group).aw
        ByteArray.empty (cA, σ) k C →
      ∃ group' k' dC, Inv v group' ∧
        ripemd160LeftLineGas initial (hashScratchPtr I) (v + 1) group =
          dC + ripemd160LeftLineGas initial (hashScratchPtr I) v group' ∧
        RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨1350⟩ (stk group') (cursor group').mem (cursor group').aw
          ByteArray.empty (cA, σ) k' (C + dC) := by
    intro v group hi k C rd
    have hg : group < 5 := by dsimp [Inv] at hi; omega
    obtain ⟨_, rd1883⟩ := ripemd160X_enterLeftRoundsGas hg
      (by simpa [stk] using rd)
    obtain ⟨k', rdNext⟩ := ripemd160X_leftGroupGas
      (t := [blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]) hg (by simp)
      (by simpa [hashLeftRoundStack] using rd1883)
    refine ⟨group + 1, k',
      ripemd160EnterLeftGas group
        + ripemd160LeftGroupGas (cursor group) (hashScratchPtr I) group 16 0,
      ?_, ?_, ?_⟩
    · dsimp [Inv] at hi ⊢; omega
    · rfl
    · have hcursor : cursor (group + 1) =
          runtimeLeftGroupCursor (cursor group) (hashScratchPtr I) group 16 := rfl
      rw [hcursor]
      simpa only [stk, hashLeftGroupStack, Nat.add_assoc] using rdNext
  obtain ⟨group, k', hi, rd'⟩ :=
    RDx.whileLoopCarryGas (code := ripemd160RuntimeBytecode) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty)
      (acc := (cA, σ)) (α := Nat) ⟨1350⟩ ⟨1360⟩ Inv stk
      (fun group => (cursor group).mem) (fun group => (cursor group).aw) exitStk
      (ripemd160LeftLineGas initial (hashScratchPtr I))
      hexit hbody 5 0 (by simp [Inv]) k C (by simpa [stk, cursor] using rd1350)
  have hge : group = 5 := by dsimp [Inv] at hi; omega
  subst group
  exact ⟨k', by simpa [cursor, exitStk] using rd'⟩

theorem ripemd160X_leftLine {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (rd1350 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1350⟩ (hashLeftGroupStack I blk h 0) initial.mem initial.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1360⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      (runtimeLeftLineCursor initial (hashScratchPtr I) 5).mem
      (runtimeLeftLineCursor initial (hashScratchPtr I) 5).aw
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_leftLineGas rd1350
  exact ⟨k', _, h'⟩

def hashRightInitCursor (I : ExecutionEnv) (h : RuntimeChain)
    (c : RuntimeMemCursor) : RuntimeMemCursor :=
  let c := runtimeStoreCursor c (hashScratchPtr I + ⟨672⟩) h.h0
  let c := runtimeStoreCursor c (hashScratchPtr I + ⟨704⟩) h.h1
  let c := runtimeStoreCursor c (hashScratchPtr I + ⟨736⟩) h.h2
  let c := runtimeStoreCursor c (hashScratchPtr I + ⟨768⟩) h.h3
  runtimeStoreCursor c (hashScratchPtr I + ⟨800⟩) h.h4

/-- Initialize the right line and enter its five-group loop. -/
theorem ripemd160X_reachRightGroupsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd1360 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1360⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1396⟩
      [⟨0⟩, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      (hashRightInitCursor I h c).mem (hashRightInitCursor I h c).aw
      ByteArray.empty (cA, σ) k'
        (C + ripemd160InitLineGas c (hashScratchPtr I + ⟨672⟩)) := by
  have rd1366pre := evm_run rd1360 with [dup7, push2 ⟨672⟩, dup6, add]
  have rd1367 := RDx.runtimeMstore rd1366pre (by native_decide) (by simp)
  have rd1373pre := evm_run rd1367 with [dup1, push2 ⟨704⟩, dup6, add]
  have rd1374 := RDx.runtimeMstore rd1373pre (by native_decide) (by simp)
  have rd1380pre := evm_run rd1374 with [dup6, push2 ⟨736⟩, dup6, add]
  have rd1381 := RDx.runtimeMstore rd1380pre (by native_decide) (by simp)
  have rd1387pre := evm_run rd1381 with [dup9, push2 ⟨768⟩, dup6, add]
  have rd1388 := RDx.runtimeMstore rd1387pre (by native_decide) (by simp)
  have rd1394pre := evm_run rd1388 with [dup8, push2 ⟨800⟩, dup6, add]
  have rd1395 := RDx.runtimeMstore rd1394pre (by native_decide) (by simp)
  have rd1396 := evm_run rd1395 with [push0]
  have rdExact := RDx.withIndices rd1396 (k' := k + 26)
    (C' := C + ripemd160InitLineGas c (hashScratchPtr I + ⟨672⟩)) (by omega) (by
      simp only [ripemd160InitLineGas]
      norm_num [show (⟨672⟩ : UInt256) + ⟨32⟩ = ⟨704⟩ by native_decide,
        show (⟨672⟩ : UInt256) + ⟨64⟩ = ⟨736⟩ by native_decide,
        show (⟨672⟩ : UInt256) + ⟨96⟩ = ⟨768⟩ by native_decide,
        show (⟨672⟩ : UInt256) + ⟨128⟩ = ⟨800⟩ by native_decide,
        u256_add_assoc]
      omega)
  exact ⟨k + 26, by
    simpa [hashRightInitCursor, runtimeStoreCursor, u256_add_comm] using rdExact⟩

theorem ripemd160X_reachRightGroups {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd1360 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1360⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1396⟩
      [⟨0⟩, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      (hashRightInitCursor I h c).mem (hashRightInitCursor I h c).aw
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_reachRightGroupsGas rd1360
  exact ⟨k', _, h'⟩

def rightWordRowWord (group : Nat) : UInt256 :=
  UInt256.ofNat (Model.rightWordRow group)

def rightRotationRowWord (group : Nat) : UInt256 :=
  UInt256.ofNat (Model.rightRotationRow group)

def rightConstantWord (group : Nat) : UInt256 :=
  UInt256.ofNat (Model.rightConstant group)

/-- The compiler-generated right message-index row selector at PC 408. -/
theorem ripemd160X_rightWordRowGas {cA σ I} {g : Sat256}
    {s0 : State} {ret : UInt256} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {group : Nat} (hgroup : group < 5) (hov : t.length + 5 ≤ 1024)
    (hret : (D_J ripemd160RuntimeBytecode 0).contains ret = true)
    (rd408 : RDx ripemd160RuntimeBytecode I g s0 ⟨408⟩
      (UInt256.ofNat group :: ret :: t) mem aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ret
      (rightWordRowWord group :: t) mem aw rdata (cA, σ) k'
        (C + ripemd160RowSelectorGas group) := by
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · have rd505 := evm_run rd408 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨505⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd505 with [
      jumpdest, pop, push8 ⟨0x5e7092b4d6f81a3c⟩, swap2, pop, jump hret ]
    exact ⟨k + 14, by simpa [rightWordRowWord, Model.rightWordRow] using
      (RDx.withIndices rdret (k' := k + 14) (C' := C + ripemd160RowSelectorGas 0)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd491 := evm_run rd408 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨505⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨491⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd491 with [
      jumpdest, pop, push8 ⟨0x6b370d5aef8c4912⟩, swap2, pop, jump hret ]
    exact ⟨k + 19, by simpa [rightWordRowWord, Model.rightWordRow] using
      (RDx.withIndices rdret (k' := k + 19) (C' := C + ripemd160RowSelectorGas 1)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd477 := evm_run rd408 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨505⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨491⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨477⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd477 with [
      jumpdest, pop, push8 ⟨0xf5137e69b8c2a04d⟩, swap2, pop, jump hret ]
    exact ⟨k + 24, by simpa [rightWordRowWord, Model.rightWordRow] using
      (RDx.withIndices rdret (k' := k + 24) (C' := C + ripemd160RowSelectorGas 2)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd463 := evm_run rd408 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨505⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨491⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨477⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨463⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd463 with [
      jumpdest, pop, push8 ⟨0x86413bf05c2d97ae⟩, swap2, pop, jump hret ]
    exact ⟨k + 29, by simpa [rightWordRowWord, Model.rightWordRow] using
      (RDx.withIndices rdret (k' := k + 29) (C' := C + ripemd160RowSelectorGas 3)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd450 := evm_run rd408 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨505⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨491⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨477⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨463⟩,
      jumpiNT (by native_decide), push1 ⟨4⟩, eq, push2 ⟨450⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd450 with [
      jumpdest, push8 ⟨0xcfa4158762de039b⟩, swap2, pop, jump hret ]
    exact ⟨k + 32, by simpa [rightWordRowWord, Model.rightWordRow] using
      (RDx.withIndices rdret (k' := k + 32) (C' := C + ripemd160RowSelectorGas 4)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩

theorem ripemd160X_rightWordRow {cA σ I} {g : Sat256}
    {s0 : State} {ret : UInt256} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {group : Nat} (hgroup : group < 5) (hov : t.length + 5 ≤ 1024)
    (hret : (D_J ripemd160RuntimeBytecode 0).contains ret = true)
    (rd408 : RDx ripemd160RuntimeBytecode I g s0 ⟨408⟩
      (UInt256.ofNat group :: ret :: t) mem aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ret
      (rightWordRowWord group :: t) mem aw rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_rightWordRowGas hgroup hov hret rd408
  exact ⟨k', _, h'⟩

/-- The compiler-generated right rotation-row selector at PC 519. -/
theorem ripemd160X_rightRotationRowGas {cA σ I} {g : Sat256}
    {s0 : State} {ret : UInt256} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {group : Nat} (hgroup : group < 5) (hov : t.length + 5 ≤ 1024)
    (hret : (D_J ripemd160RuntimeBytecode 0).contains ret = true)
    (rd519 : RDx ripemd160RuntimeBytecode I g s0 ⟨519⟩
      (UInt256.ofNat group :: ret :: t) mem aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ret
      (rightRotationRowWord group :: t) mem aw rdata (cA, σ) k'
        (C + ripemd160RowSelectorGas group) := by
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · have rd616 := evm_run rd519 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨616⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd616 with [
      jumpdest, pop, push8 ⟨0x899bdff5778beec6⟩, swap2, pop, jump hret ]
    exact ⟨k + 14, by simpa [rightRotationRowWord, Model.rightRotationRow] using
      (RDx.withIndices rdret (k' := k + 14) (C' := C + ripemd160RowSelectorGas 0)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd602 := evm_run rd519 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨616⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨602⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd602 with [
      jumpdest, pop, push8 ⟨0x9df7c89b77c76fdb⟩, swap2, pop, jump hret ]
    exact ⟨k + 19, by simpa [rightRotationRowWord, Model.rightRotationRow] using
      (RDx.withIndices rdret (k' := k + 19) (C' := C + ripemd160RowSelectorGas 1)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd588 := evm_run rd519 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨616⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨602⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨588⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd588 with [
      jumpdest, pop, push8 ⟨0x97fb866ecd5edd75⟩, swap2, pop, jump hret ]
    exact ⟨k + 24, by simpa [rightRotationRowWord, Model.rightRotationRow] using
      (RDx.withIndices rdret (k' := k + 24) (C' := C + ripemd160RowSelectorGas 2)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd574 := evm_run rd519 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨616⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨602⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨588⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨574⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd574 with [
      jumpdest, pop, push8 ⟨0xf58bee6e69c9c5f8⟩, swap2, pop, jump hret ]
    exact ⟨k + 29, by simpa [rightRotationRowWord, Model.rightRotationRow] using
      (RDx.withIndices rdret (k' := k + 29) (C' := C + ripemd160RowSelectorGas 3)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩
  · have rd561 := evm_run rd519 with [
      jumpdest, push0, swap2, swap1, dup1, iszero, push2 ⟨616⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨1⟩, eq, push2 ⟨602⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨588⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨574⟩,
      jumpiNT (by native_decide), push1 ⟨4⟩, eq, push2 ⟨561⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rdret := evm_run rd561 with [
      jumpdest, push8 ⟨0x85c9c5e68d65fdbb⟩, swap2, pop, jump hret ]
    exact ⟨k + 32, by simpa [rightRotationRowWord, Model.rightRotationRow] using
      (RDx.withIndices rdret (k' := k + 32) (C' := C + ripemd160RowSelectorGas 4)
        (by omega) (by norm_num [ripemd160RowSelectorGas]))⟩

theorem ripemd160X_rightRotationRow {cA σ I} {g : Sat256}
    {s0 : State} {ret : UInt256} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {group : Nat} (hgroup : group < 5) (hov : t.length + 5 ≤ 1024)
    (hret : (D_J ripemd160RuntimeBytecode 0).contains ret = true)
    (rd519 : RDx ripemd160RuntimeBytecode I g s0 ⟨519⟩
      (UInt256.ofNat group :: ret :: t) mem aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ret
      (rightRotationRowWord group :: t) mem aw rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_rightRotationRowGas hgroup hov hret rd519
  exact ⟨k', _, h'⟩

def hashRightGroupStack (I : ExecutionEnv) (blk : UInt256)
    (h : RuntimeChain) (group : Nat) : List UInt256 :=
  [UInt256.ofNat group, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
    hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]

def hashRightRoundStack (I : ExecutionEnv) (blk : UInt256)
    (h : RuntimeChain) (group round : Nat) : List UInt256 :=
  [UInt256.ofNat round, rightWordRowWord group, rightRotationRowWord group,
    rightConstantWord group, UInt256.ofNat group, h.h1, hashPadPtr I,
    calldataSizeWord I + ⟨72⟩, hashScratchPtr I, blk, h.h2, h.h0,
    h.h4, h.h3, ⟨122⟩]

def ripemd160RightConstantControlGas : Nat → Nat
  | 0 => 98
  | 1 => 57
  | 2 => 79
  | 3 => 101
  | _ => 117

def ripemd160EnterRightGas (group : Nat) : Nat :=
  59 + ripemd160RowSelectorGas group + ripemd160RowSelectorGas group
    + ripemd160RightConstantControlGas group

/-- Select a right-line group's rows and additive constant, then enter its round loop. -/
theorem ripemd160X_enterRightRoundsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor}
    {group : Nat} {k C : Nat} (hgroup : group < 5)
    (rd1396 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1396⟩ (hashRightGroupStack I blk h group) c.mem c.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1590⟩ (hashRightRoundStack I blk h group 0) c.mem c.aw
      ByteArray.empty (cA, σ) k' (C + ripemd160EnterRightGas group) := by
  have hiWord : UInt256.lt (UInt256.ofNat group) ⟨5⟩ = ⟨1⟩ := by
    apply ult_one
    rw [UInt256.toNat_ofNat_of_lt
      (lt_trans hgroup (by norm_num [UInt256.size] : 5 < UInt256.size))]
    norm_num
    exact hgroup
  have rd1396' : RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1396⟩
      [UInt256.ofNat group, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k C := by
    simpa [hashRightGroupStack] using rd1396
  have rd1531 := evm_run rd1396' with [
    jumpdest, push1 ⟨5⟩, dup2, lt, push2 ⟨1531⟩,
    jumpiT (by rw [hiWord]; decide) (by jump_dest) ]
  have rd408 := evm_run rd1531 with [
    jumpdest, push2 ⟨1540⟩, dup2, push2 ⟨408⟩, jump (by jump_dest) ]
  have rd408Gas := RDx.withIndices rd408 (C' := C + 41) (by rfl) (by omega)
  obtain ⟨_, rd1540⟩ := ripemd160X_rightWordRowGas hgroup (by simp)
    (by jump_dest) rd408Gas
  have rd519 := evm_run rd1540 with [
    jumpdest, push2 ⟨1549⟩, dup3, push2 ⟨519⟩, jump (by jump_dest) ]
  obtain ⟨_, rd1549⟩ := ripemd160X_rightRotationRowGas hgroup (by simp)
    (by jump_dest) rd519
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · have rd1590 := evm_run rd1549 with [
      jumpdest, push4 ⟨0x50a28be6⟩, swap2, dup4,
      dup1, push1 ⟨1⟩, eq, push2 ⟨1815⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨2⟩, eq, push2 ⟨1802⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨3⟩, eq, push2 ⟨1789⟩, jumpiNT (by native_decide),
      push1 ⟨4⟩, eq, push2 ⟨1781⟩, jumpiNT (by native_decide),
      jumpdest, push0 ]
    exact ⟨_, by simpa [hashRightRoundStack, rightConstantWord,
      Model.rightConstant] using (RDx.withIndices rd1590 (by rfl) (by
        norm_num [ripemd160EnterRightGas, ripemd160RowSelectorGas,
          ripemd160RightConstantControlGas]))⟩
  · have rd1815 := evm_run rd1549 with [
      jumpdest, push4 ⟨0x50a28be6⟩, swap2, dup4,
      dup1, push1 ⟨1⟩, eq, push2 ⟨1815⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd1590 := evm_run rd1815 with [
      jumpdest, pop, push4 ⟨0x5c4dd124⟩, swap3, pop,
      push2 ⟨1588⟩, jump (by jump_dest), jumpdest, push0 ]
    exact ⟨_, by simpa [hashRightRoundStack, rightConstantWord,
      Model.rightConstant] using (RDx.withIndices rd1590 (by rfl) (by
        norm_num [ripemd160EnterRightGas, ripemd160RowSelectorGas,
          ripemd160RightConstantControlGas]))⟩
  · have rd1802 := evm_run rd1549 with [
      jumpdest, push4 ⟨0x50a28be6⟩, swap2, dup4,
      dup1, push1 ⟨1⟩, eq, push2 ⟨1815⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨2⟩, eq, push2 ⟨1802⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd1590 := evm_run rd1802 with [
      jumpdest, pop, push4 ⟨0x6d703ef3⟩, swap3, pop,
      push2 ⟨1588⟩, jump (by jump_dest), jumpdest, push0 ]
    exact ⟨_, by simpa [hashRightRoundStack, rightConstantWord,
      Model.rightConstant] using (RDx.withIndices rd1590 (by rfl) (by
        norm_num [ripemd160EnterRightGas, ripemd160RowSelectorGas,
          ripemd160RightConstantControlGas]))⟩
  · have rd1789 := evm_run rd1549 with [
      jumpdest, push4 ⟨0x50a28be6⟩, swap2, dup4,
      dup1, push1 ⟨1⟩, eq, push2 ⟨1815⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨2⟩, eq, push2 ⟨1802⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨3⟩, eq, push2 ⟨1789⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd1590 := evm_run rd1789 with [
      jumpdest, pop, push4 ⟨0x7a6d76e9⟩, swap3, pop,
      push2 ⟨1588⟩, jump (by jump_dest), jumpdest, push0 ]
    exact ⟨_, by simpa [hashRightRoundStack, rightConstantWord,
      Model.rightConstant] using (RDx.withIndices rd1590 (by rfl) (by
        norm_num [ripemd160EnterRightGas, ripemd160RowSelectorGas,
          ripemd160RightConstantControlGas]))⟩
  · have rd1781 := evm_run rd1549 with [
      jumpdest, push4 ⟨0x50a28be6⟩, swap2, dup4,
      dup1, push1 ⟨1⟩, eq, push2 ⟨1815⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨2⟩, eq, push2 ⟨1802⟩, jumpiNT (by native_decide),
      dup1, push1 ⟨3⟩, eq, push2 ⟨1789⟩, jumpiNT (by native_decide),
      push1 ⟨4⟩, eq, push2 ⟨1781⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd1590 := evm_run rd1781 with [
      jumpdest, push0, swap3, pop, push2 ⟨1588⟩,
      jump (by jump_dest), jumpdest, push0 ]
    exact ⟨_, by simpa [hashRightRoundStack, rightConstantWord,
      Model.rightConstant] using (RDx.withIndices rd1590 (by rfl) (by
        norm_num [ripemd160EnterRightGas, ripemd160RowSelectorGas,
          ripemd160RightConstantControlGas]))⟩

theorem ripemd160X_enterRightRounds {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {c : RuntimeMemCursor}
    {group : Nat} {k C : Nat} (hgroup : group < 5)
    (rd1396 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1396⟩ (hashRightGroupStack I blk h group) c.mem c.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1590⟩ (hashRightRoundStack I blk h group 0) c.mem c.aw
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_enterRightRoundsGas hgroup rd1396
  exact ⟨k', _, h'⟩

def runtimeRightF (group : Nat) (b c d : UInt256) : UInt256 :=
  match group with
  | 0 => UInt256.xor (UInt256.lor (UInt256.lnot d) c) b
  | 1 => UInt256.lor (UInt256.land (UInt256.lnot d) c) (UInt256.land d b)
  | 2 => UInt256.xor (UInt256.lor (UInt256.lnot c) b) d
  | 3 => UInt256.lor (UInt256.land d (UInt256.lnot b)) (UInt256.land b c)
  | _ => UInt256.xor (UInt256.xor b c) d

def runtimeRightPreludeCursor (c : RuntimeMemCursor) (messageBase : UInt256) :
    RuntimeMemCursor :=
  { mem := c.mem
    aw := runtimeMloadAw
      (runtimeMloadAw (runtimeMloadAw c.aw (messageBase + ⟨704⟩))
        (messageBase + ⟨736⟩)) (messageBase + ⟨768⟩) }

def runtimeRightPreludeB (c : RuntimeMemCursor) (messageBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem c.aw (messageBase + ⟨704⟩)

def runtimeRightPreludeC (c : RuntimeMemCursor) (messageBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem (runtimeMloadAw c.aw (messageBase + ⟨704⟩))
    (messageBase + ⟨736⟩)

def runtimeRightPreludeD (c : RuntimeMemCursor) (messageBase : UInt256) : UInt256 :=
  runtimeMloadValue c.mem
    (runtimeMloadAw (runtimeMloadAw c.aw (messageBase + ⟨704⟩))
      (messageBase + ⟨736⟩)) (messageBase + ⟨768⟩)

def ripemd160RightSelectGas : Nat → Nat
  | 0 => 95
  | 1 => 123
  | 2 => 139
  | 3 => 176
  | _ => 172

/-- Select the right-line Boolean function and enter the shared round kernel. -/
theorem ripemd160X_selectRightFGas {cA σ I} {g : Sat256} {s0 : State}
    {messageBase round row rotationRow constant : UInt256}
    {b c d : UInt256} {group : Nat} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hov : t.length + 32 ≤ 1024)
    (rd1643 : RDx ripemd160RuntimeBytecode I g s0 ⟨1643⟩
      (d :: c :: b :: messageBase :: round :: row :: rotationRow ::
        UInt256.ofNat group :: constant :: ⟨1696⟩ :: round :: ⟨1⟩ ::
        row :: rotationRow :: constant :: UInt256.ofNat group :: t)
      mem aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ⟨630⟩
      ((messageBase + ⟨672⟩) :: messageBase :: round :: row :: rotationRow ::
        runtimeRightF group b c d :: constant :: ⟨1696⟩ :: round :: ⟨1⟩ ::
        row :: rotationRow :: constant :: UInt256.ofNat group :: t)
      mem aw rdata (cA, σ) k' (C + ripemd160RightSelectGas group) := by
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · have rd1766 := evm_run rd1643 with [
      swap2, push0, swap8, dup1, push0, eq, push2 ⟨1766⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd630 := evm_run rd1766 with [
      jumpdest, pop, swap2, not, or, xor, swap5, pop, push0, dup1, dup1,
      push2 ⟨1683⟩, jump (by jump_dest), jumpdest, pop, pop, pop,
      push2 ⟨672⟩, dup2, add, push2 ⟨630⟩, jump (by jump_dest) ]
    exact ⟨_, by simpa [runtimeRightF, u256_add_comm, u256_lor_comm] using
      (RDx.withIndices rd630 (by rfl) (by norm_num [ripemd160RightSelectGas]))⟩
  · have rd1749 := evm_run rd1643 with [
      swap2, push0, swap8, dup1, push0, eq, push2 ⟨1766⟩,
      jumpiNT (by native_decide), dup1, dup14, eq, push2 ⟨1749⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd630 := evm_run rd1749 with [
      jumpdest, pop, dup3, and, swap2, not, and, or, swap5, pop,
      push0, dup1, dup1, push2 ⟨1683⟩, jump (by jump_dest),
      jumpdest, pop, pop, pop, push2 ⟨672⟩, dup2, add,
      push2 ⟨630⟩, jump (by jump_dest) ]
    exact ⟨_, by simpa [runtimeRightF, u256_add_comm, u256_land_comm,
      u256_lor_comm] using
      (RDx.withIndices rd630 (by rfl) (by norm_num [ripemd160RightSelectGas]))⟩
  · have rd1734 := evm_run rd1643 with [
      swap2, push0, swap8, dup1, push0, eq, push2 ⟨1766⟩,
      jumpiNT (by native_decide), dup1, dup14, eq, push2 ⟨1749⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨1734⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd630 := evm_run rd1734 with [
      jumpdest, pop, swap1, not, or, xor, swap5, pop,
      push0, dup1, dup1, push2 ⟨1683⟩, jump (by jump_dest),
      jumpdest, pop, pop, pop, push2 ⟨672⟩, dup2, add,
      push2 ⟨630⟩, jump (by jump_dest) ]
    exact ⟨_, by simpa [runtimeRightF, u256_add_comm, u256_lor_comm] using
      (RDx.withIndices rd630 (by rfl) (by norm_num [ripemd160RightSelectGas]))⟩
  · have rd1714 := evm_run rd1643 with [
      swap2, push0, swap8, dup1, push0, eq, push2 ⟨1766⟩,
      jumpiNT (by native_decide), dup1, dup14, eq, push2 ⟨1749⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨1734⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨1714⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd630 := evm_run rd1714 with [
      jumpdest, pop, swap1, dup2, and, swap1, not, swap1, swap2, and, or,
      swap5, pop, push0, dup1, dup1, push2 ⟨1683⟩, jump (by jump_dest),
      jumpdest, pop, pop, pop, push2 ⟨672⟩, dup2, add,
      push2 ⟨630⟩, jump (by jump_dest) ]
    exact ⟨_, by simpa [runtimeRightF, u256_add_comm, u256_land_comm,
      u256_lor_comm] using
      (RDx.withIndices rd630 (by rfl) (by norm_num [ripemd160RightSelectGas]))⟩
  · have rd1702 := evm_run rd1643 with [
      swap2, push0, swap8, dup1, push0, eq, push2 ⟨1766⟩,
      jumpiNT (by native_decide), dup1, dup14, eq, push2 ⟨1749⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨2⟩, eq, push2 ⟨1734⟩,
      jumpiNT (by native_decide), dup1, push1 ⟨3⟩, eq, push2 ⟨1714⟩,
      jumpiNT (by native_decide), push1 ⟨4⟩, eq, push2 ⟨1702⟩,
      jumpiT (by native_decide) (by jump_dest) ]
    have rd630 := evm_run rd1702 with [
      jumpdest, xor, xor, swap5, pop, push0, dup1, dup1,
      push2 ⟨1683⟩, jump (by jump_dest), jumpdest, pop, pop, pop,
      push2 ⟨672⟩, dup2, add, push2 ⟨630⟩, jump (by jump_dest) ]
    exact ⟨_, by simpa [runtimeRightF, u256_add_comm] using
      (RDx.withIndices rd630 (by rfl) (by norm_num [ripemd160RightSelectGas]))⟩

theorem ripemd160X_selectRightF {cA σ I} {g : Sat256} {s0 : State}
    {messageBase round row rotationRow constant : UInt256}
    {b c d : UInt256} {group : Nat} {t : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hov : t.length + 32 ≤ 1024)
    (rd1643 : RDx ripemd160RuntimeBytecode I g s0 ⟨1643⟩
      (d :: c :: b :: messageBase :: round :: row :: rotationRow ::
        UInt256.ofNat group :: constant :: ⟨1696⟩ :: round :: ⟨1⟩ ::
        row :: rotationRow :: constant :: UInt256.ofNat group :: t)
      mem aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ⟨630⟩
      ((messageBase + ⟨672⟩) :: messageBase :: round :: row :: rotationRow ::
        runtimeRightF group b c d :: constant :: ⟨1696⟩ :: round :: ⟨1⟩ ::
        row :: rotationRow :: constant :: UInt256.ofNat group :: t)
      mem aw rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_selectRightFGas hgroup hov rd1643
  exact ⟨k', _, h'⟩

def runtimeRightRoundCursor (c : RuntimeMemCursor) (messageBase : UInt256)
    (group round : Nat) : RuntimeMemCursor :=
  let prelude := runtimeRightPreludeCursor c messageBase
  runtimeRoundCursor prelude (messageBase + ⟨672⟩) messageBase
    (UInt256.ofNat round) (rightWordRowWord group) (rightRotationRowWord group)
    (runtimeRightF group (runtimeRightPreludeB c messageBase)
      (runtimeRightPreludeC c messageBase) (runtimeRightPreludeD c messageBase))
    (rightConstantWord group)

def ripemd160RightRoundPreludeGas (c : RuntimeMemCursor) (messageBase : UInt256) : Nat :=
  90
    + runtimeMloadCost c.aw (messageBase + ⟨704⟩)
    + runtimeMloadCost (runtimeMloadAw c.aw (messageBase + ⟨704⟩))
        (messageBase + ⟨736⟩)
    + runtimeMloadCost
        (runtimeMloadAw (runtimeMloadAw c.aw (messageBase + ⟨704⟩))
          (messageBase + ⟨736⟩)) (messageBase + ⟨768⟩)

def ripemd160RightRoundGas (c : RuntimeMemCursor) (messageBase : UInt256)
    (group round : Nat) : Nat :=
  ripemd160RightRoundPreludeGas c messageBase + ripemd160RightSelectGas group
    + ripemd160RoundKernelGas (runtimeRightPreludeCursor c messageBase)
        (messageBase + ⟨672⟩) messageBase (UInt256.ofNat round)
        (rightWordRowWord group) + 15

/-- Execute one right-line round and return to its inner-loop header. -/
theorem ripemd160X_rightRoundGas {cA σ I} {g : Sat256} {s0 : State}
    {messageBase h1 pad len : UInt256} {group round : Nat} {t : List UInt256}
    {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hround : round < 16) (hov : t.length + 64 ≤ 1024)
    (rd1590 : RDx ripemd160RuntimeBytecode I g s0 ⟨1590⟩
      (UInt256.ofNat round :: rightWordRowWord group :: rightRotationRowWord group ::
        rightConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
        messageBase :: t)
      c.mem c.aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ⟨1590⟩
      (UInt256.ofNat (round + 1) :: rightWordRowWord group ::
        rightRotationRowWord group :: rightConstantWord group :: UInt256.ofNat group ::
        h1 :: pad :: len :: messageBase :: t)
      (runtimeRightRoundCursor c messageBase group round).mem
      (runtimeRightRoundCursor c messageBase group round).aw
      rdata (cA, σ) k' (C + ripemd160RightRoundGas c messageBase group round) := by
  have hlt : UInt256.lt (UInt256.ofNat round) ⟨16⟩ = ⟨1⟩ := by
    apply ult_one
    rw [UInt256.toNat_ofNat_of_lt
      (lt_trans hround (by norm_num [UInt256.size] : 16 < UInt256.size))]
    norm_num
    exact hround
  have rd1612 := evm_run rd1590 with [
    jumpdest, dup9, push1 ⟨16⟩, dup3, lt, push2 ⟨1612⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest) ]
  have rd1629pre := evm_run rd1612 with [
    jumpdest, swap1, push2 ⟨1696⟩, dup6, dup8, dup7, dup7, dup6, dup8,
    push2 ⟨704⟩, push1 ⟨1⟩, swap10, add ]
  have rd1630 := RDx.runtimeMload rd1629pre (by native_decide) (by simp; omega)
  have rd1635pre := evm_run rd1630 with [push2 ⟨736⟩, dup3, add]
  have rd1636 := RDx.runtimeMload rd1635pre (by native_decide) (by simp; omega)
  have rd1641pre := evm_run rd1636 with [push2 ⟨768⟩, dup4, add]
  have rd1642 := RDx.runtimeMload rd1641pre (by native_decide) (by simp; omega)
  have rd1642Gas := RDx.withIndices rd1642
    (C' := C + ripemd160RightRoundPreludeGas c messageBase) (by rfl) (by
      simp only [ripemd160RightRoundPreludeGas]
      omega)
  obtain ⟨k630, rd630⟩ := ripemd160X_selectRightFGas
    (group := group) (t := h1 :: pad :: len :: messageBase :: t)
    hgroup (by simp; omega) rd1642Gas
  have rd630' : RDx ripemd160RuntimeBytecode I g s0 ⟨630⟩
      ((messageBase + ⟨672⟩) :: messageBase :: UInt256.ofNat round ::
        rightWordRowWord group :: rightRotationRowWord group ::
        runtimeRightF group (runtimeRightPreludeB c messageBase)
          (runtimeRightPreludeC c messageBase) (runtimeRightPreludeD c messageBase) ::
        rightConstantWord group :: ⟨1696⟩ :: UInt256.ofNat round :: ⟨1⟩ ::
        rightWordRowWord group :: rightRotationRowWord group :: rightConstantWord group ::
        UInt256.ofNat group :: h1 :: pad :: len :: messageBase :: t)
      (runtimeRightPreludeCursor c messageBase).mem
      (runtimeRightPreludeCursor c messageBase).aw rdata (cA, σ) k630
        (C + ripemd160RightRoundPreludeGas c messageBase
          + ripemd160RightSelectGas group) := by
    simpa [runtimeRightPreludeCursor, runtimeRightPreludeB, runtimeRightPreludeC,
      runtimeRightPreludeD] using rd630
  obtain ⟨_, rd1696⟩ := ripemd160X_roundKernelGas
    (c := runtimeRightPreludeCursor c messageBase) (ret := ⟨1696⟩)
    (t := UInt256.ofNat round :: ⟨1⟩ :: rightWordRowWord group ::
      rightRotationRowWord group :: rightConstantWord group :: UInt256.ofNat group ::
      h1 :: pad :: len :: messageBase :: t)
    (by simp; omega) (by jump_dest) rd630'
  have rd1590next := evm_run rd1696 with [
    jumpdest, add, push2 ⟨1590⟩, jump (by jump_dest) ]
  have rdExact := RDx.withIndices rd1590next
    (C' := C + ripemd160RightRoundGas c messageBase group round) (by rfl) (by
      simp only [ripemd160RightRoundGas]
      omega)
  exact ⟨_, by
    simpa [runtimeRightRoundCursor, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      u256_add_comm, u256_one_add_ofNat] using rdExact⟩

theorem ripemd160X_rightRound {cA σ I} {g : Sat256} {s0 : State}
    {messageBase h1 pad len : UInt256} {group round : Nat} {t : List UInt256}
    {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hround : round < 16) (hov : t.length + 64 ≤ 1024)
    (rd1590 : RDx ripemd160RuntimeBytecode I g s0 ⟨1590⟩
      (UInt256.ofNat round :: rightWordRowWord group :: rightRotationRowWord group ::
        rightConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
        messageBase :: t)
      c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ⟨1590⟩
      (UInt256.ofNat (round + 1) :: rightWordRowWord group ::
        rightRotationRowWord group :: rightConstantWord group :: UInt256.ofNat group ::
        h1 :: pad :: len :: messageBase :: t)
      (runtimeRightRoundCursor c messageBase group round).mem
      (runtimeRightRoundCursor c messageBase group round).aw
      rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_rightRoundGas hgroup hround hov rd1590
  exact ⟨k', _, h'⟩

def runtimeRightGroupCursor (initial : RuntimeMemCursor) (messageBase : UInt256)
    (group : Nat) : Nat → RuntimeMemCursor
  | 0 => initial
  | round + 1 => runtimeRightRoundCursor
      (runtimeRightGroupCursor initial messageBase group round) messageBase group round

def ripemd160RightGroupGas (initial : RuntimeMemCursor) (messageBase : UInt256)
    (group : Nat) : Nat → Nat → Nat
  | 0, _ => 53
  | v + 1, round =>
      ripemd160RightRoundGas (runtimeRightGroupCursor initial messageBase group round)
          messageBase group round
        + ripemd160RightGroupGas initial messageBase group v (round + 1)

/-- Execute all sixteen rounds in one right-line group. -/
theorem ripemd160X_rightGroupGas {cA σ I} {g : Sat256} {s0 : State}
    {messageBase h1 pad len : UInt256} {group : Nat} {t : List UInt256}
    {initial : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hov : t.length + 64 ≤ 1024)
    (rd1590 : RDx ripemd160RuntimeBytecode I g s0 ⟨1590⟩
      (UInt256.ofNat 0 :: rightWordRowWord group :: rightRotationRowWord group ::
        rightConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
        messageBase :: t)
      initial.mem initial.aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ⟨1396⟩
      (UInt256.ofNat (group + 1) :: h1 :: pad :: len :: messageBase :: t)
      (runtimeRightGroupCursor initial messageBase group 16).mem
      (runtimeRightGroupCursor initial messageBase group 16).aw
      rdata (cA, σ) k' (C + ripemd160RightGroupGas initial messageBase group 16 0) := by
  let Inv : Nat → Nat → Prop := fun v round => round + v = 16
  let stk : Nat → List UInt256 := fun round =>
    UInt256.ofNat round :: rightWordRowWord group :: rightRotationRowWord group ::
      rightConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
      messageBase :: t
  let cursor : Nat → RuntimeMemCursor :=
    runtimeRightGroupCursor initial messageBase group
  let exitStk : Nat → List UInt256 := fun _ =>
    UInt256.ofNat (group + 1) :: h1 :: pad :: len :: messageBase :: t
  have hexit : ∀ round, Inv 0 round → ∀ k C,
      RDx ripemd160RuntimeBytecode I g s0 ⟨1590⟩ (stk round)
        (cursor round).mem (cursor round).aw rdata (cA, σ) k C →
      ∃ k', RDx ripemd160RuntimeBytecode I g s0 ⟨1396⟩ (exitStk round)
        (cursor round).mem (cursor round).aw rdata (cA, σ) k'
          (C + ripemd160RightGroupGas initial messageBase group 0 round) := by
    intro round hi k C rd
    have hre : round = 16 := by dsimp [Inv] at hi; omega
    subst round
    have rd' : RDx ripemd160RuntimeBytecode I g s0 ⟨1590⟩
        (UInt256.ofNat 16 :: rightWordRowWord group :: rightRotationRowWord group ::
          rightConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
          messageBase :: t)
        (cursor 16).mem (cursor 16).aw rdata (cA, σ) k C := by
      simpa [stk] using rd
    have rd1396 := evm_run rd' with [
      jumpdest, dup9, push1 ⟨16⟩, dup3, lt, push2 ⟨1612⟩,
      jumpiNT (by native_decide), pop, pop, pop, pop, pop,
      push1 ⟨1⟩, add, push2 ⟨1396⟩, jump (by jump_dest) ]
    exact ⟨k + 16, by
      simpa [stk, exitStk, u256_add_comm, u256_one_add_ofNat,
        ripemd160RightGroupGas] using
        (RDx.withIndices rd1396 (k' := k + 16) (C' := C + 53)
          (by omega) (by omega))⟩
  have hbody : ∀ v round, Inv (v + 1) round → ∀ k C,
      RDx ripemd160RuntimeBytecode I g s0 ⟨1590⟩ (stk round)
        (cursor round).mem (cursor round).aw rdata (cA, σ) k C →
      ∃ round' k' dC, Inv v round' ∧
        ripemd160RightGroupGas initial messageBase group (v + 1) round =
          dC + ripemd160RightGroupGas initial messageBase group v round' ∧
        RDx ripemd160RuntimeBytecode I g s0 ⟨1590⟩ (stk round')
          (cursor round').mem (cursor round').aw rdata (cA, σ) k' (C + dC) := by
    intro v round hi k C rd
    have hr : round < 16 := by dsimp [Inv] at hi; omega
    obtain ⟨k', rd'⟩ := ripemd160X_rightRoundGas hgroup hr hov
      (by simpa [stk] using rd)
    refine ⟨round + 1, k',
      ripemd160RightRoundGas (cursor round) messageBase group round, ?_, ?_, ?_⟩
    · dsimp [Inv] at hi ⊢; omega
    · rfl
    · simpa [stk, cursor, runtimeRightGroupCursor] using rd'
  obtain ⟨round, k', hi, rd'⟩ :=
    RDx.whileLoopCarryGas (code := ripemd160RuntimeBytecode) (ee := I) (g := g)
      (s0 := s0) (rdata := rdata) (acc := (cA, σ)) (α := Nat)
      ⟨1590⟩ ⟨1396⟩ Inv stk (fun round => (cursor round).mem)
      (fun round => (cursor round).aw) exitStk
      (ripemd160RightGroupGas initial messageBase group) hexit hbody 16 0
      (by simp [Inv]) k C (by simpa [stk, cursor] using rd1590)
  have hre : round = 16 := by dsimp [Inv] at hi; omega
  subst round
  exact ⟨k', by simpa [cursor, exitStk] using rd'⟩

theorem ripemd160X_rightGroup {cA σ I} {g : Sat256} {s0 : State}
    {messageBase h1 pad len : UInt256} {group : Nat} {t : List UInt256}
    {initial : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hgroup : group < 5) (hov : t.length + 64 ≤ 1024)
    (rd1590 : RDx ripemd160RuntimeBytecode I g s0 ⟨1590⟩
      (UInt256.ofNat 0 :: rightWordRowWord group :: rightRotationRowWord group ::
        rightConstantWord group :: UInt256.ofNat group :: h1 :: pad :: len ::
        messageBase :: t)
      initial.mem initial.aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ⟨1396⟩
      (UInt256.ofNat (group + 1) :: h1 :: pad :: len :: messageBase :: t)
      (runtimeRightGroupCursor initial messageBase group 16).mem
      (runtimeRightGroupCursor initial messageBase group 16).aw
      rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_rightGroupGas hgroup hov rd1590
  exact ⟨k', _, h'⟩

def runtimeRightLineCursor (initial : RuntimeMemCursor) (messageBase : UInt256) :
    Nat → RuntimeMemCursor
  | 0 => initial
  | group + 1 => runtimeRightGroupCursor
      (runtimeRightLineCursor initial messageBase group) messageBase group 16

def ripemd160RightLineGas (initial : RuntimeMemCursor) (messageBase : UInt256) :
    Nat → Nat → Nat
  | 0, _ => 25
  | v + 1, group =>
      ripemd160EnterRightGas group
        + ripemd160RightGroupGas (runtimeRightLineCursor initial messageBase group)
            messageBase group 16 0
        + ripemd160RightLineGas initial messageBase v (group + 1)

/-- Execute all five right-line groups and stop before state recombination. -/
theorem ripemd160X_rightLineGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (rd1396 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1396⟩ (hashRightGroupStack I blk h 0) initial.mem initial.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1406⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      (runtimeRightLineCursor initial (hashScratchPtr I) 5).mem
      (runtimeRightLineCursor initial (hashScratchPtr I) 5).aw
      ByteArray.empty (cA, σ) k'
        (C + ripemd160RightLineGas initial (hashScratchPtr I) 5 0) := by
  let Inv : Nat → Nat → Prop := fun v group => group + v = 5
  let stk : Nat → List UInt256 := fun group => hashRightGroupStack I blk h group
  let cursor : Nat → RuntimeMemCursor :=
    runtimeRightLineCursor initial (hashScratchPtr I)
  let exitStk : Nat → List UInt256 := fun _ =>
    [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
      hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
  have hexit : ∀ group, Inv 0 group → ∀ k C,
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1396⟩ (stk group) (cursor group).mem (cursor group).aw
        ByteArray.empty (cA, σ) k C →
      ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1406⟩ (exitStk group) (cursor group).mem (cursor group).aw
        ByteArray.empty (cA, σ) k'
          (C + ripemd160RightLineGas initial (hashScratchPtr I) 0 group) := by
    intro group hi k C rd
    have hge : group = 5 := by dsimp [Inv] at hi; omega
    subst group
    have rd' : RDx ripemd160RuntimeBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1396⟩
        [⟨5⟩, h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
          hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
        (cursor 5).mem (cursor 5).aw ByteArray.empty (cA, σ) k C := by
      simpa [stk, hashRightGroupStack] using rd
    have rd1406 := evm_run rd' with [
      jumpdest, push1 ⟨5⟩, dup2, lt, push2 ⟨1531⟩,
      jumpiNT (by native_decide), pop ]
    exact ⟨k + 7, by simpa [exitStk, ripemd160RightLineGas] using
      (RDx.withIndices rd1406 (k' := k + 7) (C' := C + 25)
        (by omega) (by omega))⟩
  have hbody : ∀ v group, Inv (v + 1) group → ∀ k C,
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1396⟩ (stk group) (cursor group).mem (cursor group).aw
        ByteArray.empty (cA, σ) k C →
      ∃ group' k' dC, Inv v group' ∧
        ripemd160RightLineGas initial (hashScratchPtr I) (v + 1) group =
          dC + ripemd160RightLineGas initial (hashScratchPtr I) v group' ∧
        RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨1396⟩ (stk group') (cursor group').mem (cursor group').aw
          ByteArray.empty (cA, σ) k' (C + dC) := by
    intro v group hi k C rd
    have hg : group < 5 := by dsimp [Inv] at hi; omega
    obtain ⟨_, rd1590⟩ := ripemd160X_enterRightRoundsGas hg
      (by simpa [stk] using rd)
    obtain ⟨k', rdNext⟩ := ripemd160X_rightGroupGas
      (t := [blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]) hg (by simp)
      (by simpa [hashRightRoundStack] using rd1590)
    refine ⟨group + 1, k',
      ripemd160EnterRightGas group
        + ripemd160RightGroupGas (cursor group) (hashScratchPtr I) group 16 0,
      ?_, ?_, ?_⟩
    · dsimp [Inv] at hi ⊢; omega
    · rfl
    · have hcursor : cursor (group + 1) =
          runtimeRightGroupCursor (cursor group) (hashScratchPtr I) group 16 := rfl
      rw [hcursor]
      simpa only [stk, hashRightGroupStack, Nat.add_assoc] using rdNext
  obtain ⟨group, k', hi, rd'⟩ :=
    RDx.whileLoopCarryGas (code := ripemd160RuntimeBytecode) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty)
      (acc := (cA, σ)) (α := Nat) ⟨1396⟩ ⟨1406⟩ Inv stk
      (fun group => (cursor group).mem) (fun group => (cursor group).aw) exitStk
      (ripemd160RightLineGas initial (hashScratchPtr I))
      hexit hbody 5 0 (by simp [Inv]) k C (by simpa [stk, cursor] using rd1396)
  have hge : group = 5 := by dsimp [Inv] at hi; omega
  subst group
  exact ⟨k', by simpa [cursor, exitStk] using rd'⟩

theorem ripemd160X_rightLine {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (rd1396 : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1396⟩ (hashRightGroupStack I blk h 0) initial.mem initial.aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1406⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      (runtimeRightLineCursor initial (hashScratchPtr I) 5).mem
      (runtimeRightLineCursor initial (hashScratchPtr I) 5).aw
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_rightLineGas rd1396
  exact ⟨k', _, h'⟩

end Ripemd160
