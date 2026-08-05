import Examples.Precompiles.Modexp.Allocation
import Examples.Precompiles.Modexp.Spec

/-!
# Exact multi-limb dispatcher prefixes for ModExp

The remaining ModExp proof obligation is the nontrivial multi-limb backend.  This file records the
checked bytecode prefix common to that work: from the wide precompile entry, through exponent/base
tests, operand copying, and the odd/even dispatcher branch.

These theorems intentionally stop at the backend entry PCs:

* PC 1925: Montgomery backend for odd moduli;
* PC 1549: Barrett backend for even moduli.

They do not claim final functional correctness of those backends.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def wideMultiLimbOddDispatcherGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  79 + cdRangeGas I (wideExponentOffset baseSize) (wideModulusOffset baseSize exponentSize) +
    wideBaseGtOneGas I baseSize +
    operandSetupGas I baseSize exponentSize modulusSize +
    modulusLastByteMloadGas
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize +
    198

def wideMultiLimbEvenDispatcherGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  79 + cdRangeGas I (wideExponentOffset baseSize) (wideModulusOffset baseSize exponentSize) +
    wideBaseGtOneGas I baseSize +
    operandSetupGas I baseSize exponentSize modulusSize +
    modulusLastByteMloadGas
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize +
    199

def wideMultiLimbOddDispatcherTotalGas (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  wideEntryGas I.calldata + wideMultiLimbOddDispatcherGas I l.base l.exponent l.modulus

def wideMultiLimbEvenDispatcherTotalGas (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  wideEntryGas I.calldata + wideMultiLimbEvenDispatcherGas I l.base l.exponent l.modulus

def wideMultiLimbBackendStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat operandBasePtr,
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    ⟨1271⟩, ⟨173⟩]

def wideMultiLimbBackendMemory (ctx : BytecodeContext) : ByteArray :=
  let l := lengths ctx.executionEnv.calldata
  operandCopiedMemory ctx.executionEnv l.base l.exponent l.modulus

def wideMultiLimbBackendAw (ctx : BytecodeContext) : UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  modulusLastByteMloadAw
    (operandModulusActiveWords l.base l.exponent l.modulus)
    l.base l.exponent l.modulus

def wideMultiLimbOddAllocationGas (ctx : BytecodeContext) : Nat :=
  let l := lengths ctx.executionEnv.calldata
  55 + newBytesGas (wideMultiLimbBackendAw ctx)
    (operandFreePtr l.base l.exponent l.modulus) l.modulus

def wideMultiLimbEvenAllocationGas (ctx : BytecodeContext) : Nat :=
  let l := lengths ctx.executionEnv.calldata
  55 + newBytesGas (wideMultiLimbBackendAw ctx)
    (operandFreePtr l.base l.exponent l.modulus) l.modulus

def wideMultiLimbOddPostAllocationStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat l.modulus,
    ⟨1271⟩, UInt256.ofNat operandBasePtr, ⟨173⟩]

def wideMultiLimbEvenPostAllocationStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨1271⟩,
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat operandBasePtr, ⟨173⟩]

def wideMultiLimbPostAllocationMemory (ctx : BytecodeContext) : ByteArray :=
  let l := lengths ctx.executionEnv.calldata
  wideWordResultMemory ctx.executionEnv l.base l.exponent l.modulus

def wideMultiLimbPostAllocationAw (ctx : BytecodeContext) : UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  wideWordResultWords l.base l.exponent l.modulus

def wideMultiLimbChecksGas (ctx : BytecodeContext) : Nat :=
  let l := lengths ctx.executionEnv.calldata
  wideWordChecksGas (wideMultiLimbPostAllocationMemory ctx)
    (wideMultiLimbPostAllocationAw ctx)
    (operandModulusPtr l.base l.exponent) l.modulus

def wideMultiLimbOddPostChecksStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat operandBasePtr,
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat l.modulus,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddBodyStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat l.modulus,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddFirstCallStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat ((l.modulus + 31) / 32),
    ⟨2006⟩,
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddAllocatorCallStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat ((l.modulus + 31) / 32),
    ⟨2847⟩,
    ⟨2006⟩,
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddWordArrayLength (ctx : BytecodeContext) : Nat :=
  let l := lengths ctx.executionEnv.calldata
  (l.modulus + 31) / 32

def wideMultiLimbOddWordArrayPtr (ctx : BytecodeContext) : Nat :=
  let l := lengths ctx.executionEnv.calldata
  operandFreePtr l.base l.exponent l.modulus + bytesAllocationSize l.modulus

def wideMultiLimbOddPostAllocatorMemory (ctx : BytecodeContext) : ByteArray :=
  let fp := wideMultiLimbOddWordArrayPtr ctx
  let words := wideMultiLimbOddWordArrayLength ctx
  storeBytesLength
    (setFreePtr (wideMultiLimbPostAllocationMemory ctx)
      (fp + wordArrayAllocationSize words))
    fp words

def wideMultiLimbOddPostAllocatorAw (ctx : BytecodeContext) : UInt256 :=
  newWordArrayWords (wideMultiLimbPostAllocationAw ctx)
    (wideMultiLimbOddWordArrayPtr ctx)
    (wideMultiLimbOddWordArrayLength ctx)

def wideMultiLimbOddPostAllocatorStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    ⟨2006⟩,
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddLoopEntryStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨0⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddFirstCopyAddStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨0⟩,
    ⟨2926⟩,
    ⟨2931⟩,
    ⟨2937⟩,
    ⟨32⟩,
    ⟨0⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddFirstCopyAddReturnStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨1⟩,
    ⟨2931⟩,
    ⟨2937⟩,
    ⟨32⟩,
    ⟨0⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddFirstCopyReadStack (ctx : BytecodeContext) : List UInt256 :=
  wideMultiLimbOddFirstCopyAddReturnStack ctx

def wideMultiLimbOddFirstCopyStoreStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat (l.modulus - 32),
    ⟨32⟩,
    ⟨0⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddFirstCopyLoadedWord (ctx : BytecodeContext) : UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  wideLoadWord
    (wideMultiLimbOddPostAllocatorMemory ctx)
    (wideMultiLimbOddPostAllocatorAw ctx)
    (UInt256.ofNat (operandModulusPtr l.base l.exponent + l.modulus))

def wideMultiLimbOddFirstCopyStoredMemory (ctx : BytecodeContext) : ByteArray :=
  let dst := wideMultiLimbOddWordArrayPtr ctx + 32
  (wideMultiLimbOddFirstCopyLoadedWord ctx).toByteArray.write 0
    (wideMultiLimbOddPostAllocatorMemory ctx) dst 32

def wideMultiLimbOddFirstCopyLoopBackStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddSecondCopyAddStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨1⟩,
    ⟨2926⟩,
    ⟨2931⟩,
    ⟨2937⟩,
    ⟨32⟩,
    ⟨1⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddSecondCopyAddReturnStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨2⟩,
    ⟨2931⟩,
    ⟨2937⟩,
    ⟨32⟩,
    ⟨1⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddSecondCopyReadStack (ctx : BytecodeContext) : List UInt256 :=
  wideMultiLimbOddSecondCopyAddReturnStack ctx

def wideMultiLimbOddSecondCopyStoreStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat (l.modulus - 64),
    ⟨32⟩,
    ⟨1⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddSecondCopyLoadedWord (ctx : BytecodeContext) : UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  wideLoadWord
    (wideMultiLimbOddFirstCopyStoredMemory ctx)
    (wideMultiLimbOddPostAllocatorAw ctx)
    (UInt256.ofNat (operandModulusPtr l.base l.exponent + (l.modulus - 64) + 32))

def wideMultiLimbOddSecondCopyStoredMemory (ctx : BytecodeContext) : ByteArray :=
  let dst := wideMultiLimbOddWordArrayPtr ctx + 64
  (wideMultiLimbOddSecondCopyLoadedWord ctx).toByteArray.write 0
    (wideMultiLimbOddFirstCopyStoredMemory ctx) dst 32

def wideMultiLimbOddSecondCopyLoopBackStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨2⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddThirdCopyAddStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨2⟩,
    ⟨2926⟩,
    ⟨2931⟩,
    ⟨2937⟩,
    ⟨32⟩,
    ⟨2⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddThirdCopyAddReturnStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨3⟩,
    ⟨2931⟩,
    ⟨2937⟩,
    ⟨32⟩,
    ⟨2⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddThirdCopyReadStack (ctx : BytecodeContext) : List UInt256 :=
  wideMultiLimbOddThirdCopyAddReturnStack ctx

def wideMultiLimbOddThirdCopyStoreStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat (l.modulus - 96),
    ⟨32⟩,
    ⟨2⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddThirdCopyLoadedWord (ctx : BytecodeContext) : UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  wideLoadWord
    (wideMultiLimbOddSecondCopyStoredMemory ctx)
    (wideMultiLimbOddPostAllocatorAw ctx)
    (UInt256.ofNat (operandModulusPtr l.base l.exponent + (l.modulus - 96) + 32))

def wideMultiLimbOddThirdCopyStoredMemory (ctx : BytecodeContext) : ByteArray :=
  let dst := wideMultiLimbOddWordArrayPtr ctx + 96
  (wideMultiLimbOddThirdCopyLoadedWord ctx).toByteArray.write 0
    (wideMultiLimbOddSecondCopyStoredMemory ctx) dst 32

def wideMultiLimbOddThirdCopyLoopBackStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨3⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddFourthCopyAddStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨3⟩,
    ⟨2926⟩,
    ⟨2931⟩,
    ⟨2937⟩,
    ⟨32⟩,
    ⟨3⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddFourthCopyAddReturnStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [⟨4⟩,
    ⟨2931⟩,
    ⟨2937⟩,
    ⟨32⟩,
    ⟨3⟩,
    ⟨1⟩,
    UInt256.ofNat (l.modulus / 32),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨2006⟩,
    UInt256.ofNat (wideMultiLimbOddWordArrayPtr ctx),
    UInt256.ofNat operandBasePtr,
    UInt256.ofNat ((l.modulus + 31) / 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat l.modulus,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    ⟨173⟩]

def wideMultiLimbOddFourthCopyReadStack (ctx : BytecodeContext) : List UInt256 :=
  wideMultiLimbOddFourthCopyAddReturnStack ctx

def wideMultiLimbEvenPostChecksStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat operandBasePtr,
    ⟨173⟩]

def wideMultiLimbEvenScanStack (ctx : BytecodeContext) : List UInt256 :=
  let l := lengths ctx.executionEnv.calldata
  [UInt256.ofNat (operandModulusPtr l.base l.exponent + 32),
    UInt256.ofNat (operandExponentPtr l.base),
    UInt256.ofNat (operandModulusPtr l.base l.exponent),
    UInt256.ofNat l.modulus,
    ⟨1271⟩,
    UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus),
    UInt256.ofNat (operandModulusPtr l.base l.exponent + l.modulus + 31),
    UInt256.ofNat operandBasePtr,
    ⟨173⟩]

def wideMultiLimbOddNontrivialInputs (ctx : BytecodeContext) : Prop :=
  wideMultiLimbOddMontgomeryInputs ctx ∧
  1 < wideModulusNat ctx.executionEnv

def wideMultiLimbEvenNontrivialInputs (ctx : BytecodeContext) : Prop :=
  wideMultiLimbEvenBarrettInputs ctx ∧
  1 < wideModulusNat ctx.executionEnv

def wideMultiLimbLeOneInputs (ctx : BytecodeContext) : Prop :=
  wideMultiLimbBackendInputs ctx ∧
  wideModulusNat ctx.executionEnv ≤ 1

def WideMultiLimbOddBackendSuffixExact
    (backendGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddMontgomeryInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1925⟩
      (wideMultiLimbBackendStack ctx)
      (wideMultiLimbBackendMemory ctx) (wideMultiLimbBackendAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv + backendGas ctx)

def WideMultiLimbEvenBackendSuffixExact
    (backendGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbEvenBarrettInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1549⟩
      (wideMultiLimbBackendStack ctx)
      (wideMultiLimbBackendMemory ctx) (wideMultiLimbBackendAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv + backendGas ctx)

def WideMultiLimbOddPostAllocationSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddMontgomeryInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1946⟩
      (wideMultiLimbOddPostAllocationStack ctx)
      (wideMultiLimbPostAllocationMemory ctx) (wideMultiLimbPostAllocationAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + suffixGas ctx)

def WideMultiLimbEvenPostAllocationSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbEvenBarrettInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1570⟩
      (wideMultiLimbEvenPostAllocationStack ctx)
      (wideMultiLimbPostAllocationMemory ctx) (wideMultiLimbPostAllocationAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbEvenAllocationGas ctx) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbEvenAllocationGas ctx + suffixGas ctx)

def WideMultiLimbOddPostChecksSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1968⟩
      (wideMultiLimbOddPostChecksStack ctx)
      (wideMultiLimbPostAllocationMemory ctx) (wideMultiLimbPostAllocationAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + suffixGas ctx)

def WideMultiLimbOddBodySuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1989⟩
      (wideMultiLimbOddBodyStack ctx)
      (wideMultiLimbPostAllocationMemory ctx) (wideMultiLimbPostAllocationAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + suffixGas ctx)

def WideMultiLimbOddFirstCallSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2836⟩
      (wideMultiLimbOddFirstCallStack ctx)
      (wideMultiLimbPostAllocationMemory ctx) (wideMultiLimbPostAllocationAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 +
          suffixGas ctx)

def WideMultiLimbOddAllocatorCallSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1487⟩
      (wideMultiLimbOddAllocatorCallStack ctx)
      (wideMultiLimbPostAllocationMemory ctx) (wideMultiLimbPostAllocationAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          suffixGas ctx)

def WideMultiLimbOddPostAllocatorSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2847⟩
      (wideMultiLimbOddPostAllocatorStack ctx)
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx)) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) +
          suffixGas ctx)

def WideMultiLimbOddLoopEntrySuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2906⟩
      (wideMultiLimbOddLoopEntryStack ctx)
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 +
          suffixGas ctx)

def WideMultiLimbOddFirstCopyAddSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1323⟩
      (wideMultiLimbOddFirstCopyAddStack ctx)
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 +
          suffixGas ctx)

def WideMultiLimbOddFirstCopyAddReturnSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2926⟩
      (wideMultiLimbOddFirstCopyAddReturnStack ctx)
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 +
          suffixGas ctx)

def WideMultiLimbOddFirstCopyReadSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1903⟩
      (wideMultiLimbOddFirstCopyReadStack ctx)
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 +
          suffixGas ctx)

def WideMultiLimbOddFirstCopyStoreSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2937⟩
      (wideMultiLimbOddFirstCopyStoreStack ctx)
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 +
          suffixGas ctx)

def WideMultiLimbOddFirstCopyLoopBackSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2857⟩
      (wideMultiLimbOddFirstCopyLoopBackStack ctx)
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 +
          suffixGas ctx)

/-- Continuation obligation after the first Montgomery full-word copy guard takes the loop-back
branch.  The stack and memory are the post-first-copy state; the only extra assumption is that
there is another full word to copy. -/
def WideMultiLimbOddFirstCopyContinueSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    1 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2906⟩
      (wideMultiLimbOddFirstCopyLoopBackStack ctx)
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 +
          suffixGas ctx)

/-- Obligation after the second Montgomery copy-loop call-frame setup reaches the checked-add
helper.  This is the `i = 1` analogue of `WideMultiLimbOddFirstCopyAddSuffixExact`. -/
def WideMultiLimbOddSecondCopyAddSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    1 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1323⟩
      (wideMultiLimbOddSecondCopyAddStack ctx)
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          suffixGas ctx)

def WideMultiLimbOddSecondCopyAddReturnSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    1 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2926⟩
      (wideMultiLimbOddSecondCopyAddReturnStack ctx)
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + suffixGas ctx)

def WideMultiLimbOddSecondCopyReadSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    1 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1903⟩
      (wideMultiLimbOddSecondCopyReadStack ctx)
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + suffixGas ctx)

def WideMultiLimbOddSecondCopyStoreSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    1 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2937⟩
      (wideMultiLimbOddSecondCopyStoreStack ctx)
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + suffixGas ctx)

def WideMultiLimbOddSecondCopyLoopBackSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    1 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2857⟩
      (wideMultiLimbOddSecondCopyLoopBackStack ctx)
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + suffixGas ctx)

def WideMultiLimbOddSecondCopyContinueSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    2 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2906⟩
      (wideMultiLimbOddSecondCopyLoopBackStack ctx)
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + suffixGas ctx)

def WideMultiLimbOddThirdCopyAddSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    2 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1323⟩
      (wideMultiLimbOddThirdCopyAddStack ctx)
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + suffixGas ctx)

def WideMultiLimbOddThirdCopyAddReturnSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    2 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2926⟩
      (wideMultiLimbOddThirdCopyAddReturnStack ctx)
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + suffixGas ctx)

def WideMultiLimbOddThirdCopyReadSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    2 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1903⟩
      (wideMultiLimbOddThirdCopyReadStack ctx)
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + suffixGas ctx)

def WideMultiLimbOddThirdCopyStoreSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    2 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2937⟩
      (wideMultiLimbOddThirdCopyStoreStack ctx)
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + suffixGas ctx)

def WideMultiLimbOddThirdCopyLoopBackSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    2 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2857⟩
      (wideMultiLimbOddThirdCopyLoopBackStack ctx)
      (wideMultiLimbOddThirdCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + suffixGas ctx)

def WideMultiLimbOddThirdCopyContinueSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    3 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2906⟩
      (wideMultiLimbOddThirdCopyLoopBackStack ctx)
      (wideMultiLimbOddThirdCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23 + suffixGas ctx)

def WideMultiLimbOddThirdCopyExitSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    2 < (lengths ctx.executionEnv.calldata).modulus / 32 →
    ¬ 3 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2865⟩
      (wideMultiLimbOddThirdCopyLoopBackStack ctx)
      (wideMultiLimbOddThirdCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23 + suffixGas ctx)

def WideMultiLimbOddFourthCopyAddSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    3 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1323⟩
      (wideMultiLimbOddFourthCopyAddStack ctx)
      (wideMultiLimbOddThirdCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23 + 33) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23 + 33 + suffixGas ctx)

def WideMultiLimbOddFourthCopyAddReturnSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    3 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2926⟩
      (wideMultiLimbOddFourthCopyAddReturnStack ctx)
      (wideMultiLimbOddThirdCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23 + 33 + 43) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23 + 33 + 43 + suffixGas ctx)

def WideMultiLimbOddFourthCopyReadSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    3 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1903⟩
      (wideMultiLimbOddFourthCopyReadStack ctx)
      (wideMultiLimbOddThirdCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23 + 33 + 43 + 12) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + suffixGas ctx)

def WideMultiLimbOddSecondCopyExitSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    1 < (lengths ctx.executionEnv.calldata).modulus / 32 →
    ¬ 2 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2865⟩
      (wideMultiLimbOddSecondCopyLoopBackStack ctx)
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + suffixGas ctx)

/-- Exit obligation after the first Montgomery full-word copy guard falls through.  This is the
case where the first copied word was the only full word in the modulus payload. -/
def WideMultiLimbOddFirstCopyExitSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbOddNontrivialInputs ctx →
    ¬ 1 < (lengths ctx.executionEnv.calldata).modulus / 32 → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2865⟩
      (wideMultiLimbOddFirstCopyLoopBackStack ctx)
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 +
          suffixGas ctx)

def WideMultiLimbEvenPostChecksSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbEvenNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1592⟩
      (wideMultiLimbEvenPostChecksStack ctx)
      (wideMultiLimbPostAllocationMemory ctx) (wideMultiLimbPostAllocationAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbEvenAllocationGas ctx + wideMultiLimbChecksGas ctx) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbEvenAllocationGas ctx + wideMultiLimbChecksGas ctx + suffixGas ctx)

def WideMultiLimbEvenScanSuffixExact
    (suffixGas : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext, wideMultiLimbEvenNontrivialInputs ctx → ∀ k : Nat,
    RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1603⟩
      (wideMultiLimbEvenScanStack ctx)
      (wideMultiLimbPostAllocationMemory ctx) (wideMultiLimbPostAllocationAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbEvenAllocationGas ctx + wideMultiLimbChecksGas ctx + 27) →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (Model.output ctx.executionEnv.calldata)
      (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbEvenAllocationGas ctx + wideMultiLimbChecksGas ctx + 27 + suffixGas ctx)

def wideMultiLimbOddEnsures (backendGas : BytecodeContext → Nat)
    (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
    (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv + backendGas ctx) result

def wideMultiLimbEvenEnsures (backendGas : BytecodeContext → Nat)
    (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
    (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv + backendGas ctx) result

def wideMultiLimbLeOneTotalGas (ctx : BytecodeContext) : Nat :=
  let l := lengths ctx.executionEnv.calldata
  wideEntryGas ctx.executionEnv.calldata +
    wideSmallModulusValueGas ctx.executionEnv l.base l.exponent l.modulus

/-- Exact prefix from the wide entry PC to the odd-modulus Montgomery backend entry. -/
theorem wideMultiLimbOddDispatcherFromEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hodd : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨1⟩)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ :: ⟨173⟩ :: [])
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (modulusLastByteMloadAw
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize)
      ByteArray.empty acc k'
        (C + wideMultiLimbOddDispatcherGas I baseSize exponentSize modulusSize) := by
  obtain ⟨kExp, rd89⟩ := reachWideExponentNonzero
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega)
    hexp rd0
  obtain ⟨kBase, rd105⟩ := reachWideBaseGtOne
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega)
    hbase rd89
  have rd1183 := prepareOperandsExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (tail := []) hb he hm hcalldata (by simp)
    (by
      simpa [wideModulusOffset, wideExponentOffset] using rd105)
  obtain ⟨kDisp, rd1925⟩ := reachMontgomeryDispatcherOddAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := 173) (tail := [])
    (by omega : 0 < modulusSize) hm
    (by
      rw [UInt256.toNat_ofNat_of_lt (by
        apply lt_of_le_of_lt
          (show operandModulusPtr baseSize exponentSize ≤ 2272 by
            unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
            omega)
          (by decide))]
      unfold operandModulusActiveWords
      rw [UInt256.toNat_ofNat_of_lt (by
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide))]
      rw [operandModulusPtr_eq]
      unfold operandModulusWords bytesAllocationWords
      have hround := bytesSize_le_roundedPayload modulusSize
      omega)
    (operandCopiedWideLoadModulusLength I baseSize exponentSize modulusSize hb he hm)
    hodd (by simp) rd1183
  refine ⟨kDisp, rd1925.withIndices rfl ?_⟩
  unfold wideMultiLimbOddDispatcherGas wideExponentOffset wideModulusOffset
  omega

/-- Exact prefix from the wide entry PC to the even-modulus Barrett backend entry. -/
theorem wideMultiLimbEvenDispatcherFromEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨0⟩)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1549⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ :: ⟨173⟩ :: [])
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (modulusLastByteMloadAw
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize)
      ByteArray.empty acc k'
        (C + wideMultiLimbEvenDispatcherGas I baseSize exponentSize modulusSize) := by
  obtain ⟨kExp, rd89⟩ := reachWideExponentNonzero
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega)
    hexp rd0
  obtain ⟨kBase, rd105⟩ := reachWideBaseGtOne
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega)
    hbase rd89
  have rd1183 := prepareOperandsExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (tail := []) hb he hm hcalldata (by simp)
    (by
      simpa [wideModulusOffset, wideExponentOffset] using rd105)
  obtain ⟨kDisp, rd1549⟩ := reachBarrettDispatcherEvenAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := 173) (tail := [])
    (by omega : 0 < modulusSize) hm
    (by
      rw [UInt256.toNat_ofNat_of_lt (by
        apply lt_of_le_of_lt
          (show operandModulusPtr baseSize exponentSize ≤ 2272 by
            unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
            omega)
          (by decide))]
      unfold operandModulusActiveWords
      rw [UInt256.toNat_ofNat_of_lt (by
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide))]
      rw [operandModulusPtr_eq]
      unfold operandModulusWords bytesAllocationWords
      have hround := bytesSize_le_roundedPayload modulusSize
      omega)
    (operandCopiedWideLoadModulusLength I baseSize exponentSize modulusSize hb he hm)
    heven (by simp) rd1183
  refine ⟨kDisp, rd1549.withIndices rfl ?_⟩
  unfold wideMultiLimbEvenDispatcherGas wideExponentOffset wideModulusOffset
  omega

/-- Usable context-level prefix theorem for the odd multi-limb residual: from the normal precompile
entry to the Montgomery backend entry. -/
theorem wideMultiLimbOddDispatcherPrefixExact
    {ctx : BytecodeContext}
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (hinput : wideMultiLimbOddMontgomeryInputs ctx) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas
      (initState ctx.createdAccounts ctx.genesisBlockHeader ctx.blocks ctx.accountMap
        ctx.originalAccountMap ctx.gas ctx.substate ctx.executionEnv)
      ⟨1925⟩
      (UInt256.ofNat operandBasePtr ::
        UInt256.ofNat (operandExponentPtr (lengths ctx.executionEnv.calldata).base) ::
        UInt256.ofNat
          (operandModulusPtr (lengths ctx.executionEnv.calldata).base
            (lengths ctx.executionEnv.calldata).exponent) ::
        ⟨1271⟩ :: ⟨173⟩ :: [])
      (operandCopiedMemory ctx.executionEnv
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent
        (lengths ctx.executionEnv.calldata).modulus)
      (modulusLastByteMloadAw
        (operandModulusActiveWords
          (lengths ctx.executionEnv.calldata).base
          (lengths ctx.executionEnv.calldata).exponent
          (lengths ctx.executionEnv.calldata).modulus)
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent
        (lengths ctx.executionEnv.calldata).modulus)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
        (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv) := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  rcases hinput with ⟨hmulti, hodd⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, hcalldata, hnotWord, hexp, hbase⟩
  rcases haccepts with ⟨hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  obtain ⟨kEntry, rd62⟩ := reachWideEntry
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (g := ctx.gas) hcode hvalue hvalid hnotWord
  have hprefix := wideMultiLimbOddDispatcherFromEntryExact
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hb he hm hmodLarge hexp hbase hcalldata
    (by
      simpa [wideModulusParity, I, l] using hodd)
    rd62
  simpa [wideMultiLimbOddDispatcherTotalGas, I, l] using hprefix

/-- Usable context-level prefix theorem for the odd multi-limb residual after Montgomery has
allocated its result bytes object.  This is the next backend boundary after PC 1925. -/
theorem wideMultiLimbOddAllocationPrefixExact
    {ctx : BytecodeContext}
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (hinput : wideMultiLimbOddMontgomeryInputs ctx) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas
      (initState ctx.createdAccounts ctx.genesisBlockHeader ctx.blocks ctx.accountMap
        ctx.originalAccountMap ctx.gas ctx.substate ctx.executionEnv)
      ⟨1946⟩
      (UInt256.ofNat
          (operandFreePtr (lengths ctx.executionEnv.calldata).base
            (lengths ctx.executionEnv.calldata).exponent
            (lengths ctx.executionEnv.calldata).modulus) ::
        UInt256.ofNat
          (operandModulusPtr (lengths ctx.executionEnv.calldata).base
            (lengths ctx.executionEnv.calldata).exponent) ::
        UInt256.ofNat (operandExponentPtr (lengths ctx.executionEnv.calldata).base) ::
        UInt256.ofNat (lengths ctx.executionEnv.calldata).modulus ::
        ⟨1271⟩ :: UInt256.ofNat operandBasePtr :: ⟨173⟩ :: [])
      (wideWordResultMemory ctx.executionEnv
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent
        (lengths ctx.executionEnv.calldata).modulus)
      (wideWordResultWords
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent
        (lengths ctx.executionEnv.calldata).modulus)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
        (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
          wideMultiLimbOddAllocationGas ctx) := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  have hinputCopy := hinput
  rcases hinput with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  have hbL : l.base ≤ 1024 := by simpa [l] using hb
  have heL : l.exponent ≤ 1024 := by simpa [l] using he
  have hmL : l.modulus ≤ 1024 := by simpa [l] using hm
  have hmodPos : 0 < l.modulus := by
    have : 0 < (lengths ctx.executionEnv.calldata).modulus := by omega
    simpa [l, I] using this
  obtain ⟨k1925, rd1925⟩ := wideMultiLimbOddDispatcherPrefixExact
    (ctx := ctx) hcode hinputCopy
  let oldAw := operandModulusActiveWords l.base l.exponent l.modulus
  let aw1 := modulusLastByteMloadAw oldAw l.base l.exponent l.modulus
  have hmodPtrNat :
      (UInt256.ofNat (operandModulusPtr l.base l.exponent)).toNat =
        operandModulusPtr l.base l.exponent := by
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusPtr l.base l.exponent ≤ 2240 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          have := hbL
          have := heL
          omega)
        (by decide))]
  have holdNat : oldAw.toNat =
      operandModulusWords l.base l.exponent l.modulus := by
    dsimp only [oldAw]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords l.base l.exponent l.modulus ≤ 103 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          have := hbL
          have := heL
          have := hmL
          omega)
        (by decide))]
  have hmodAccessOld :
      (UInt256.ofNat (operandModulusPtr l.base l.exponent)).toNat + 32 ≤
        32 * oldAw.toNat := by
    rw [hmodPtrNat, holdNat, operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    omega
  have hawLe : oldAw.toNat ≤ aw1.toNat := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_ge_operand hb he hmodPos hm
  have hawBound :
      aw1.toNat ≤ operandModulusWords l.base l.exponent l.modulus + 1 := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_bound hb he hmodPos hm
  have holdNoWrap : oldAw.toNat * 32 < UInt256.size := by
    rw [holdNat]
    apply lt_of_le_of_lt
      (show operandModulusWords l.base l.exponent l.modulus * 32 ≤ 3296 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        have := hbL
        have := heL
        have := hmL
        omega)
      (by decide)
  have hawNoWrap : aw1.toNat * 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show aw1.toNat * 32 ≤
          (operandModulusWords l.base l.exponent l.modulus + 1) * 32 by
        nlinarith)
    apply lt_of_le_of_lt
      (show (operandModulusWords l.base l.exponent l.modulus + 1) * 32 ≤ 3328 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        have := hbL
        have := heL
        have := hmL
        omega)
      (by decide)
  have hmodAccess :
      (UInt256.ofNat (operandModulusPtr l.base l.exponent)).toNat + 32 ≤
        32 * aw1.toNat := by
    nlinarith
  have hbelowOld :
      ¬ UInt256.ofNat (operandModulusPtr l.base l.exponent) ≥ oldAw * ⟨32⟩ :=
    not_ge_mul32_of_access hmodAccessOld holdNoWrap
  have hbelow1 :
      ¬ UInt256.ofNat (operandModulusPtr l.base l.exponent) ≥ aw1 * ⟨32⟩ :=
    not_ge_mul32_of_access hmodAccess hawNoWrap
  have hmodLengthOld : wideLoadWord
      (operandCopiedMemory I l.base l.exponent l.modulus) oldAw
      (UInt256.ofNat (operandModulusPtr l.base l.exponent)) =
        UInt256.ofNat l.modulus := by
    dsimp only [oldAw]
    exact operandCopiedWideLoadModulusLength I l.base l.exponent l.modulus hb he hm
  have hmodLength : wideLoadWord
      (operandCopiedMemory I l.base l.exponent l.modulus) aw1
      (UInt256.ofNat (operandModulusPtr l.base l.exponent)) =
        UInt256.ofNat l.modulus := by
    rw [wideLoadWord_eq_decode_bounded hbelow1]
    rw [← wideLoadWord_eq_decode_bounded hbelowOld]
    exact hmodLengthOld
  have hawThree : 3 ≤ aw1.toNat := by
    have holdThree : 3 ≤ oldAw.toNat := by
      rw [holdNat]
      unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega
    omega
  have hresultWords :
      newBytesWords aw1 (operandFreePtr l.base l.exponent l.modulus) l.modulus =
        wideWordResultWords l.base l.exponent l.modulus := by
    dsimp only [oldAw, aw1]
    exact newBytesWords_lastByteMloadAw_eq_result hb he hmodPos hm
  have rd1946 := allocateMontgomeryResultExactFromAw
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (ret := 1271) (tail := [⟨173⟩]) (aw0 := aw1)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hb he hmodPos hm hcalldata hmodAccess hmodLength hawThree
    (wordMul32_not_le64_of_ge3 hawThree hawNoWrap)
    hresultWords (by simp) rd1925
  refine ⟨k1925 + 99, ?_⟩
  simpa [I, l, oldAw, aw1, wideMultiLimbOddAllocationGas, wideMultiLimbBackendAw,
    Nat.add_assoc] using rd1946

/-- Usable context-level prefix theorem for the even multi-limb residual: from the normal
precompile entry to the Barrett backend entry. -/
theorem wideMultiLimbEvenDispatcherPrefixExact
    {ctx : BytecodeContext}
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (hinput : wideMultiLimbEvenBarrettInputs ctx) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas
      (initState ctx.createdAccounts ctx.genesisBlockHeader ctx.blocks ctx.accountMap
        ctx.originalAccountMap ctx.gas ctx.substate ctx.executionEnv)
      ⟨1549⟩
      (UInt256.ofNat operandBasePtr ::
        UInt256.ofNat (operandExponentPtr (lengths ctx.executionEnv.calldata).base) ::
        UInt256.ofNat
          (operandModulusPtr (lengths ctx.executionEnv.calldata).base
            (lengths ctx.executionEnv.calldata).exponent) ::
        ⟨1271⟩ :: ⟨173⟩ :: [])
      (operandCopiedMemory ctx.executionEnv
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent
        (lengths ctx.executionEnv.calldata).modulus)
      (modulusLastByteMloadAw
        (operandModulusActiveWords
          (lengths ctx.executionEnv.calldata).base
          (lengths ctx.executionEnv.calldata).exponent
          (lengths ctx.executionEnv.calldata).modulus)
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent
        (lengths ctx.executionEnv.calldata).modulus)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
        (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv) := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  rcases hinput with ⟨hmulti, heven⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, hcalldata, hnotWord, hexp, hbase⟩
  rcases haccepts with ⟨hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  obtain ⟨kEntry, rd62⟩ := reachWideEntry
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (g := ctx.gas) hcode hvalue hvalid hnotWord
  have hprefix := wideMultiLimbEvenDispatcherFromEntryExact
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hb he hm hmodLarge hexp hbase hcalldata
    (by
      simpa [wideModulusParity, I, l] using heven)
    rd62
  simpa [wideMultiLimbEvenDispatcherTotalGas, I, l] using hprefix

/-- Usable context-level prefix theorem for the even multi-limb residual after Barrett has
allocated its result bytes object.  This is the next backend boundary after PC 1549. -/
theorem wideMultiLimbEvenAllocationPrefixExact
    {ctx : BytecodeContext}
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (hinput : wideMultiLimbEvenBarrettInputs ctx) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas
      (initState ctx.createdAccounts ctx.genesisBlockHeader ctx.blocks ctx.accountMap
        ctx.originalAccountMap ctx.gas ctx.substate ctx.executionEnv)
      ⟨1570⟩
      (UInt256.ofNat
          (operandFreePtr (lengths ctx.executionEnv.calldata).base
            (lengths ctx.executionEnv.calldata).exponent
            (lengths ctx.executionEnv.calldata).modulus) ::
        UInt256.ofNat (lengths ctx.executionEnv.calldata).modulus ::
        ⟨1271⟩ ::
        UInt256.ofNat
          (operandModulusPtr (lengths ctx.executionEnv.calldata).base
            (lengths ctx.executionEnv.calldata).exponent) ::
        UInt256.ofNat (operandExponentPtr (lengths ctx.executionEnv.calldata).base) ::
        UInt256.ofNat operandBasePtr :: ⟨173⟩ :: [])
      (wideWordResultMemory ctx.executionEnv
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent
        (lengths ctx.executionEnv.calldata).modulus)
      (wideWordResultWords
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent
        (lengths ctx.executionEnv.calldata).modulus)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
        (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
          wideMultiLimbEvenAllocationGas ctx) := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  have hinputCopy := hinput
  rcases hinput with ⟨hmulti, _heven⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  have hbL : l.base ≤ 1024 := by simpa [l] using hb
  have heL : l.exponent ≤ 1024 := by simpa [l] using he
  have hmL : l.modulus ≤ 1024 := by simpa [l] using hm
  have hmodPos : 0 < l.modulus := by
    have : 0 < (lengths ctx.executionEnv.calldata).modulus := by omega
    simpa [l, I] using this
  obtain ⟨k1549, rd1549⟩ := wideMultiLimbEvenDispatcherPrefixExact
    (ctx := ctx) hcode hinputCopy
  let oldAw := operandModulusActiveWords l.base l.exponent l.modulus
  let aw1 := modulusLastByteMloadAw oldAw l.base l.exponent l.modulus
  have hmodPtrNat :
      (UInt256.ofNat (operandModulusPtr l.base l.exponent)).toNat =
        operandModulusPtr l.base l.exponent := by
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusPtr l.base l.exponent ≤ 2240 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          have := hbL
          have := heL
          omega)
        (by decide))]
  have holdNat : oldAw.toNat =
      operandModulusWords l.base l.exponent l.modulus := by
    dsimp only [oldAw]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords l.base l.exponent l.modulus ≤ 103 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          have := hbL
          have := heL
          have := hmL
          omega)
        (by decide))]
  have hmodAccessOld :
      (UInt256.ofNat (operandModulusPtr l.base l.exponent)).toNat + 32 ≤
        32 * oldAw.toNat := by
    rw [hmodPtrNat, holdNat, operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    omega
  have hawLe : oldAw.toNat ≤ aw1.toNat := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_ge_operand hb he hmodPos hm
  have hawBound :
      aw1.toNat ≤ operandModulusWords l.base l.exponent l.modulus + 1 := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_bound hb he hmodPos hm
  have holdNoWrap : oldAw.toNat * 32 < UInt256.size := by
    rw [holdNat]
    apply lt_of_le_of_lt
      (show operandModulusWords l.base l.exponent l.modulus * 32 ≤ 3296 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        have := hbL
        have := heL
        have := hmL
        omega)
      (by decide)
  have hawNoWrap : aw1.toNat * 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show aw1.toNat * 32 ≤
          (operandModulusWords l.base l.exponent l.modulus + 1) * 32 by
        nlinarith)
    apply lt_of_le_of_lt
      (show (operandModulusWords l.base l.exponent l.modulus + 1) * 32 ≤ 3328 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        have := hbL
        have := heL
        have := hmL
        omega)
      (by decide)
  have hmodAccess :
      (UInt256.ofNat (operandModulusPtr l.base l.exponent)).toNat + 32 ≤
        32 * aw1.toNat := by
    nlinarith
  have hbelowOld :
      ¬ UInt256.ofNat (operandModulusPtr l.base l.exponent) ≥ oldAw * ⟨32⟩ :=
    not_ge_mul32_of_access hmodAccessOld holdNoWrap
  have hbelow1 :
      ¬ UInt256.ofNat (operandModulusPtr l.base l.exponent) ≥ aw1 * ⟨32⟩ :=
    not_ge_mul32_of_access hmodAccess hawNoWrap
  have hmodLengthOld : wideLoadWord
      (operandCopiedMemory I l.base l.exponent l.modulus) oldAw
      (UInt256.ofNat (operandModulusPtr l.base l.exponent)) =
        UInt256.ofNat l.modulus := by
    dsimp only [oldAw]
    exact operandCopiedWideLoadModulusLength I l.base l.exponent l.modulus hb he hm
  have hmodLength : wideLoadWord
      (operandCopiedMemory I l.base l.exponent l.modulus) aw1
      (UInt256.ofNat (operandModulusPtr l.base l.exponent)) =
        UInt256.ofNat l.modulus := by
    rw [wideLoadWord_eq_decode_bounded hbelow1]
    rw [← wideLoadWord_eq_decode_bounded hbelowOld]
    exact hmodLengthOld
  have hawThree : 3 ≤ aw1.toNat := by
    have holdThree : 3 ≤ oldAw.toNat := by
      rw [holdNat]
      unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega
    omega
  have hresultWords :
      newBytesWords aw1 (operandFreePtr l.base l.exponent l.modulus) l.modulus =
        wideWordResultWords l.base l.exponent l.modulus := by
    dsimp only [oldAw, aw1]
    exact newBytesWords_lastByteMloadAw_eq_result hb he hmodPos hm
  have rd1570 := allocateBarrettResultExactFromAw
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (ret := 173) (tail := []) (aw0 := aw1)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hb he hmodPos hm hcalldata hmodAccess hmodLength hawThree
    (wordMul32_not_le64_of_ge3 hawThree hawNoWrap)
    hresultWords (by simp) rd1549
  refine ⟨k1549 + 99, ?_⟩
  simpa [I, l, oldAw, aw1, wideMultiLimbEvenAllocationGas, wideMultiLimbBackendAw,
    Nat.add_assoc] using rd1570

theorem wideMultiLimbOddPostChecksPrefixExact
    {ctx : BytecodeContext}
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (hinput : wideMultiLimbOddNontrivialInputs ctx) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas
      (initState ctx.createdAccounts ctx.genesisBlockHeader ctx.blocks ctx.accountMap
        ctx.originalAccountMap ctx.gas ctx.substate ctx.executionEnv)
      ⟨1968⟩
      (wideMultiLimbOddPostChecksStack ctx)
      (wideMultiLimbPostAllocationMemory ctx) (wideMultiLimbPostAllocationAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
        (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
          wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx) := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  rcases hinput with ⟨hbranch, hmodGtOne⟩
  have hbranchCopy := hbranch
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  have hmodPos : 0 < l.modulus := by
    have : 0 < (lengths ctx.executionEnv.calldata).modulus := by omega
    simpa [l, I] using this
  have hmodTrusted :
      1 < Model.bytesToNatPadded I.calldata
        (96 + l.base + l.exponent) l.modulus := by
    simpa [wideModulusNat, wideModulusOffset, I, l] using hmodGtOne
  obtain ⟨k1946, rd1946⟩ := wideMultiLimbOddAllocationPrefixExact
    (ctx := ctx) hcode hbranchCopy
  obtain ⟨k1968, rd1968⟩ := reachMontgomeryNontrivialChecksTrusted
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (ret := 1271) (tail := [⟨173⟩])
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hb he hmodPos hm hmodTrusted (by simp) (by
      simpa [I, l, wideMultiLimbOddPostAllocationStack,
        wideMultiLimbPostAllocationMemory, wideMultiLimbPostAllocationAw] using rd1946)
  refine ⟨k1968, ?_⟩
  simpa [I, l, wideMultiLimbOddPostChecksStack, wideMultiLimbPostAllocationMemory,
    wideMultiLimbPostAllocationAw, wideMultiLimbChecksGas, Nat.add_assoc] using rd1968

theorem wideMultiLimbEvenPostChecksPrefixExact
    {ctx : BytecodeContext}
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (hinput : wideMultiLimbEvenNontrivialInputs ctx) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas
      (initState ctx.createdAccounts ctx.genesisBlockHeader ctx.blocks ctx.accountMap
        ctx.originalAccountMap ctx.gas ctx.substate ctx.executionEnv)
      ⟨1592⟩
      (wideMultiLimbEvenPostChecksStack ctx)
      (wideMultiLimbPostAllocationMemory ctx) (wideMultiLimbPostAllocationAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
        (wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
          wideMultiLimbEvenAllocationGas ctx + wideMultiLimbChecksGas ctx) := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  rcases hinput with ⟨hbranch, hmodGtOne⟩
  have hbranchCopy := hbranch
  rcases hbranch with ⟨hmulti, _heven⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  have hmodPos : 0 < l.modulus := by
    have : 0 < (lengths ctx.executionEnv.calldata).modulus := by omega
    simpa [l, I] using this
  have hmodTrusted :
      1 < Model.bytesToNatPadded I.calldata
        (96 + l.base + l.exponent) l.modulus := by
    simpa [wideModulusNat, wideModulusOffset, I, l] using hmodGtOne
  obtain ⟨k1570, rd1570⟩ := wideMultiLimbEvenAllocationPrefixExact
    (ctx := ctx) hcode hbranchCopy
  obtain ⟨k1592, rd1592⟩ := reachBarrettNontrivialChecksTrusted
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (ret := 1271) (tail := [⟨173⟩])
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hb he hmodPos hm hmodTrusted (by simp) (by
      simpa [I, l, wideMultiLimbEvenPostAllocationStack,
        wideMultiLimbPostAllocationMemory, wideMultiLimbPostAllocationAw] using rd1570)
  refine ⟨k1592, ?_⟩
  simpa [I, l, wideMultiLimbEvenPostChecksStack, wideMultiLimbPostAllocationMemory,
    wideMultiLimbPostAllocationAw, wideMultiLimbChecksGas, Nat.add_assoc] using rd1592

theorem wideMultiLimbOddPostChecksSuffixExact_of_bodySuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddBodySuffixExact suffixGas) :
    WideMultiLimbOddPostChecksSuffixExact (fun ctx => 107 + suffixGas ctx) := by
  intro ctx hinput k rd1968
  let I := ctx.executionEnv
  let l := lengths I.calldata
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨_hb, _he, hm⟩
  obtain ⟨k1989, rd1989⟩ := reachMontgomeryMultiLimbBody
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (basePtr := operandBasePtr) (exponentPtr := operandExponentPtr l.base)
    (modulusPtr := operandModulusPtr l.base l.exponent)
    (resultPtr := operandFreePtr l.base l.exponent l.modulus)
    (modulusSize := l.modulus) (ret := 1271) (tail := [⟨173⟩])
    (mem := wideMultiLimbPostAllocationMemory ctx)
    (aw := wideMultiLimbPostAllocationAw ctx) (rdata := ByteArray.empty)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    (k := k)
    (C := wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
      wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx)
    (by simpa [I, l] using hmodLarge)
    (by simpa [I, l] using hm)
    (by simp)
    (by
      simpa [I, l, wideMultiLimbOddPostChecksStack, wideMultiLimbPostAllocationMemory,
        wideMultiLimbPostAllocationAw] using rd1968)
  simpa [I, l, wideMultiLimbOddBodyStack, Nat.add_assoc] using
    (hsuffix ctx hinputCopy k1989 (by
      simpa [I, l, wideMultiLimbOddBodyStack, wideMultiLimbPostAllocationMemory,
        wideMultiLimbPostAllocationAw, Nat.add_assoc] using rd1989))

theorem wideMultiLimbEvenPostChecksSuffixExact_of_scanSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbEvenScanSuffixExact suffixGas) :
    WideMultiLimbEvenPostChecksSuffixExact (fun ctx => 27 + suffixGas ctx) := by
  intro ctx hinput k rd1592
  let I := ctx.executionEnv
  let l := lengths I.calldata
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _heven⟩
  rcases hmulti with ⟨hwide, _hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  have hbl : l.base ≤ 1024 := by simpa [I, l] using hb
  have hel : l.exponent ≤ 1024 := by simpa [I, l] using he
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hbWords : (l.base + 31) / 32 ≤ 32 := by omega
  have heWords : (l.exponent + 31) / 32 ≤ 32 := by omega
  have hp32 :
      operandModulusPtr l.base l.exponent + 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusPtr l.base l.exponent + 32 ≤ 2272 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hpend :
      operandModulusPtr l.base l.exponent + l.modulus + 31 < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusPtr l.base l.exponent + l.modulus + 31 ≤ 3295 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have rd1603 := reachBarrettScanSetup
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (p := operandModulusPtr l.base l.exponent) (m := l.modulus)
    (retBar := 1271) (result := operandFreePtr l.base l.exponent l.modulus)
    (exp := operandExponentPtr l.base) (base := operandBasePtr) (ret := 173)
    (tail := [])
    (mem := wideMultiLimbPostAllocationMemory ctx)
    (aw := wideMultiLimbPostAllocationAw ctx) (rdata := ByteArray.empty)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    (k := k)
    (C := wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
      wideMultiLimbEvenAllocationGas ctx + wideMultiLimbChecksGas ctx)
    hp32 hpend (by simp)
    (by
      simpa [I, l, wideMultiLimbEvenPostChecksStack, wideMultiLimbPostAllocationMemory,
        wideMultiLimbPostAllocationAw] using rd1592)
  simpa [I, l, wideMultiLimbEvenScanStack, Nat.add_assoc] using
    (hsuffix ctx hinputCopy (k + 9) (by
      simpa [I, l, wideMultiLimbEvenScanStack, wideMultiLimbPostAllocationMemory,
        wideMultiLimbPostAllocationAw, Nat.add_assoc] using rd1603))

theorem wideMultiLimbOddBodySuffixExact_of_firstCallSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddFirstCallSuffixExact suffixGas) :
    WideMultiLimbOddBodySuffixExact (fun ctx => 38 + suffixGas ctx) := by
  intro ctx hinput k rd1989
  let I := ctx.executionEnv
  let l := lengths I.calldata
  obtain ⟨k2836, rd2836⟩ := reachMontgomeryMultiLimbFirstCall
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (basePtr := operandBasePtr) (exponentPtr := operandExponentPtr l.base)
    (modulusPtr := operandModulusPtr l.base l.exponent)
    (resultPtr := operandFreePtr l.base l.exponent l.modulus)
    (words := (l.modulus + 31) / 32) (modulusSize := l.modulus)
    (ret := 1271) (tail := [⟨173⟩])
    (mem := wideMultiLimbPostAllocationMemory ctx)
    (aw := wideMultiLimbPostAllocationAw ctx) (rdata := ByteArray.empty)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    (k := k)
    (C := wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
      wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107)
    (by simp)
    (by
      simpa [I, l, wideMultiLimbOddBodyStack, wideMultiLimbPostAllocationMemory,
        wideMultiLimbPostAllocationAw] using rd1989)
  simpa [I, l, wideMultiLimbOddFirstCallStack, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput k2836 (by
      simpa [I, l, wideMultiLimbOddFirstCallStack, wideMultiLimbPostAllocationMemory,
        wideMultiLimbPostAllocationAw, Nat.add_assoc] using rd2836))

theorem wideMultiLimbOddFirstCallSuffixExact_of_allocatorCallSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddAllocatorCallSuffixExact suffixGas) :
    WideMultiLimbOddFirstCallSuffixExact (fun ctx => 24 + suffixGas ctx) := by
  intro ctx hinput k rd2836
  let I := ctx.executionEnv
  let l := lengths I.calldata
  obtain ⟨k1487, rd1487⟩ := reachMontgomeryMultiLimbAllocatorCall
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (basePtr := operandBasePtr) (exponentPtr := operandExponentPtr l.base)
    (modulusPtr := operandModulusPtr l.base l.exponent)
    (resultPtr := operandFreePtr l.base l.exponent l.modulus)
    (words := (l.modulus + 31) / 32) (modulusSize := l.modulus)
    (ret := 805) (innerRet := 2006)
    (tail := [⟨1271⟩, UInt256.ofNat (operandFreePtr l.base l.exponent l.modulus), ⟨173⟩])
    (mem := wideMultiLimbPostAllocationMemory ctx)
    (aw := wideMultiLimbPostAllocationAw ctx) (rdata := ByteArray.empty)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    (k := k)
    (C := wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
      wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38)
    (by simp)
    (by
      simpa [I, l, wideMultiLimbOddFirstCallStack, wideMultiLimbPostAllocationMemory,
        wideMultiLimbPostAllocationAw] using rd2836)
  simpa [I, l, wideMultiLimbOddAllocatorCallStack, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    (hsuffix ctx hinput k1487 (by
      simpa [I, l, wideMultiLimbOddAllocatorCallStack, wideMultiLimbPostAllocationMemory,
        wideMultiLimbPostAllocationAw, Nat.add_assoc] using rd1487))

private theorem wideWordResultMemory_read64_nextFreePtr
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (wideWordResultMemory I baseSize exponentSize modulusSize).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat
          (operandFreePtr baseSize exponentSize modulusSize +
            bytesAllocationSize modulusSize)) := by
  let oldMem := operandCopiedMemory I baseSize exponentSize modulusSize
  let oldFp := operandFreePtr baseSize exponentSize modulusSize
  have holdMem96 : 96 ≤ oldMem.size := by
    have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    have hptr : 96 ≤ operandModulusPtr baseSize exponentSize + 32 := by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    exact hptr.trans hge
  have hsetSize :
      (setFreePtr oldMem (oldFp + bytesAllocationSize modulusSize)).size = oldMem.size :=
    setFreePtr_size holdMem96
  have hgapOld :
      oldFp -
        (setFreePtr oldMem (oldFp + bytesAllocationSize modulusSize)).size < USize.size := by
    rw [hsetSize]
    exact lt_usize _ (by
      apply lt_of_le_of_lt (Nat.sub_le oldFp oldMem.size)
      apply lt_of_le_of_lt
        (show oldFp ≤ 3296 by
          unfold oldFp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
        (by decide))
  have holdFp96 : 96 ≤ oldFp := by
    unfold oldFp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  dsimp [wideWordResultMemory, oldMem, oldFp]
  rw [storeBytesLength_read64]
  · exact setFreePtr_read64 holdMem96
  · rw [hsetSize]
    exact holdMem96
  · exact holdFp96
  · exact hgapOld

theorem wideMultiLimbOddAllocatorCallSuffixExact_of_postAllocatorSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddPostAllocatorSuffixExact suffixGas) :
    WideMultiLimbOddAllocatorCallSuffixExact
      (fun ctx =>
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) +
        suffixGas ctx) := by
  intro ctx hinput k rd1487
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  have hbl : l.base ≤ 1024 := by simpa [I, l] using hb
  have hel : l.exponent ≤ 1024 := by simpa [I, l] using he
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hn : words ≤ 32 := by
    dsimp [words]
    omega
  have hfp96 : 96 ≤ fp := by
    dsimp [fp, resultPtr]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hbound : fp + wordArrayAllocationSize words < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (show fp + wordArrayAllocationSize words ≤ 5408 by
        dsimp [fp, resultPtr, words]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize wordArrayAllocationSize wordArrayPayloadSize
        omega)
      (by decide)
  have hmemSizeEq :
      (wideMultiLimbPostAllocationMemory ctx).size = resultPtr + 32 := by
    simpa [I, l, resultPtr, wideMultiLimbPostAllocationMemory] using
      (wideWordResultMemory_size I hbl hel hml)
  have hmemSize : 96 ≤ (wideMultiLimbPostAllocationMemory ctx).size := by
    rw [hmemSizeEq]
    dsimp [resultPtr]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hmemLe : (wideMultiLimbPostAllocationMemory ctx).size ≤ fp := by
    rw [hmemSizeEq]
    dsimp [fp]
    unfold bytesAllocationSize
    omega
  have hgap : fp - (wideMultiLimbPostAllocationMemory ctx).size < USize.size := by
    rw [hmemSizeEq]
    exact lt_usize _ (by
      dsimp [fp]
      unfold bytesAllocationSize
      omega)
  have haw3 : 3 ≤ (wideMultiLimbPostAllocationAw ctx).toNat := by
    dsimp [wideMultiLimbPostAllocationAw]
    rw [wideWordResultWords_toNat hbl hel hml]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥ wideMultiLimbPostAllocationAw ctx * ⟨32⟩ := by
    intro h
    change ((wideMultiLimbPostAllocationAw ctx) * ⟨32⟩).toNat ≤
      (⟨64⟩ : UInt256).toNat at h
    rw [show (⟨64⟩ : UInt256).toNat = 64 by decide] at h
    rw [show ((wideMultiLimbPostAllocationAw ctx) * ⟨32⟩).toNat =
        resultPtr + bytesAllocationSize l.modulus by
      simpa [I, l, resultPtr, wideMultiLimbPostAllocationAw] using
        (resultActiveBytes_toNat hbl hel hml)] at h
    dsimp [resultPtr] at h
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize at h
    omega
  have hread :
      (wideMultiLimbPostAllocationMemory ctx).readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat fp) := by
    simpa [I, l, fp, resultPtr, wideMultiLimbPostAllocationMemory] using
      (wideWordResultMemory_read64_nextFreePtr I hbl hel hml
        (modulusSize := l.modulus))
  have rd2847 := newWordArrayExact
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := I) (g := ctx.gas)
    (n := words) (fp := fp) (ret := 2847)
    (tail := [⟨2006⟩, UInt256.ofNat (operandModulusPtr l.base l.exponent),
      UInt256.ofNat operandBasePtr, UInt256.ofNat words,
      UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
      UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩])
    (mem := wideMultiLimbPostAllocationMemory ctx)
    (aw := wideMultiLimbPostAllocationAw ctx)
    (rdata := ByteArray.empty) (acc := (ctx.createdAccounts, ctx.accountMap))
    (k := k)
    (C := wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
      wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24)
    hn hfp96 hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata
    (by simp) (by native_decide)
    (by
      simpa [I, l, words, resultPtr, wideMultiLimbOddAllocatorCallStack,
        wideMultiLimbPostAllocationMemory, wideMultiLimbPostAllocationAw] using rd1487)
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddPostAllocatorStack,
    wideMultiLimbOddPostAllocatorMemory, wideMultiLimbOddPostAllocatorAw,
    wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinputCopy (k + 78) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddPostAllocatorStack,
        wideMultiLimbOddPostAllocatorMemory, wideMultiLimbOddPostAllocatorAw,
        wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2847))

private theorem montgomeryPostAllocatorLoopEntryDecodes :
    [decode runtimeBytecode ⟨2847⟩, decode runtimeBytecode ⟨2848⟩,
      decode runtimeBytecode ⟨2849⟩, decode runtimeBytecode ⟨2850⟩,
      decode runtimeBytecode ⟨2851⟩, decode runtimeBytecode ⟨2852⟩,
      decode runtimeBytecode ⟨2853⟩, decode runtimeBytecode ⟨2855⟩,
      decode runtimeBytecode ⟨2856⟩, decode runtimeBytecode ⟨2857⟩,
      decode runtimeBytecode ⟨2858⟩, decode runtimeBytecode ⟨2859⟩,
      decode runtimeBytecode ⟨2860⟩, decode runtimeBytecode ⟨2861⟩,
      decode runtimeBytecode ⟨2864⟩] =
    [some (.JUMPDEST, .none), some (.SWAP2, .none), some (.DUP1, .none),
      some (.MLOAD, .none), some (.SWAP1, .none), some (.DUP2, .none),
      some (.Push .PUSH1, some (⟨5⟩, 1)), some (.SHR, .none),
      some (.PUSH0, .none), some (.JUMPDEST, .none), some (.DUP2, .none),
      some (.DUP2, .none), some (.LT, .none),
      some (.Push .PUSH2, some (⟨2906⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem jumpDest_2906_montgomery :
    (D_J runtimeBytecode 0).contains ⟨2906⟩ = true := by native_decide

private theorem newWordArrayWords_toNat_small {aw : UInt256} {fp n : Nat}
    (haw : aw.toNat ≤ 136) (hfp : fp ≤ 4352) (hn : n ≤ 32) (hnpos : 0 < n) :
    (newWordArrayWords aw fp n).toNat =
      MachineState.M (MachineState.M aw.toNat fp 32) (fp + 32) (wordArrayPayloadSize n) := by
  have hstore :
      MachineState.M aw.toNat fp 32 ≤ 138 := by
    have hceil : (fp + 32 + 31) / 32 ≤ 138 := by
      rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
      omega
    unfold MachineState.M
    simp
    exact ⟨le_trans haw (by decide), hceil⟩
  have hcopy :
      MachineState.M (MachineState.M aw.toNat fp 32) (fp + 32) (wordArrayPayloadSize n) ≤
        169 := by
    have hceilStore : (fp + 32 + 31) / 32 ≤ 138 := by
      rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
      omega
    have hceilCopy : (fp + 32 + 32 * n + 31) / 32 ≤ 169 := by
      rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
      omega
    have hpayloadNe : 32 * n ≠ 0 := by omega
    unfold MachineState.M wordArrayPayloadSize
    simp [hpayloadNe]
    exact ⟨le_trans haw (by decide),
      ⟨le_trans hceilStore (by decide), hceilCopy⟩⟩
  have hstoreLt :
      MachineState.M aw.toNat fp 32 < UInt256.size := by
    exact lt_of_le_of_lt hstore (by decide)
  have hcopyLt :
      MachineState.M (MachineState.M aw.toNat fp 32) (fp + 32) (wordArrayPayloadSize n) <
        UInt256.size := by
    exact lt_of_le_of_lt hcopy (by decide)
  unfold newWordArrayWords newBytesStoreWords
  rw [show (UInt256.ofNat (MachineState.M aw.toNat fp 32)).toNat =
      MachineState.M aw.toNat fp 32 by
    exact UInt256.toNat_ofNat_of_lt hstoreLt]
  exact UInt256.toNat_ofNat_of_lt hcopyLt

private theorem machineM_covers_access (s f l : Nat) (hl : 0 < l) :
    f + l ≤ 32 * MachineState.M s f l := by
  unfold MachineState.M
  cases l with
  | zero =>
      omega
  | succ l =>
      simp only
      have hceil : f + (l + 1) ≤ 32 * ((f + (l + 1) + 31) / 32) := by
        have hdiv :
            (f + (l + 1) + 31) / 32 ≤ (f + (l + 1) + 31) / 32 := le_rfl
        rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)] at hdiv
        omega
      have hmax :
          (f + (l + 1) + 31) / 32 ≤ max s ((f + (l + 1) + 31) / 32) :=
        Nat.le_max_right _ _
      nlinarith

private theorem wideMultiLimbOddPostAllocatorMemory_readModulusLength
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (storeBytesLength
      (setFreePtr (wideWordResultMemory I baseSize exponentSize modulusSize)
        (operandFreePtr baseSize exponentSize modulusSize + bytesAllocationSize modulusSize +
          wordArrayAllocationSize ((modulusSize + 31) / 32)))
      (operandFreePtr baseSize exponentSize modulusSize + bytesAllocationSize modulusSize)
      ((modulusSize + 31) / 32)).readWithPadding
        (operandModulusPtr baseSize exponentSize) 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
  let oldMem := wideWordResultMemory I baseSize exponentSize modulusSize
  let fp := operandFreePtr baseSize exponentSize modulusSize + bytesAllocationSize modulusSize
  let words := (modulusSize + 31) / 32
  have holdSize : oldMem.size = operandFreePtr baseSize exponentSize modulusSize + 32 := by
    simpa [oldMem] using wideWordResultMemory_size I hb he hm
  have holdMem96 : 96 ≤ oldMem.size := by
    rw [holdSize]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hsetSize :
      (setFreePtr oldMem (fp + wordArrayAllocationSize words)).size = oldMem.size :=
    setFreePtr_size holdMem96
  have hgap : fp - (setFreePtr oldMem (fp + wordArrayAllocationSize words)).size <
      USize.size := by
    rw [hsetSize, holdSize]
    exact lt_usize _ (by
      dsimp [fp]
      unfold bytesAllocationSize
      omega)
  have hbelow : operandModulusPtr baseSize exponentSize + 32 ≤ fp := by
    dsimp [fp]
    unfold operandFreePtr bytesAllocationSize
    omega
  have hread96 : 96 ≤ operandModulusPtr baseSize exponentSize := by
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hbelowOld :
      operandModulusPtr baseSize exponentSize + 32 ≤
        operandFreePtr baseSize exponentSize modulusSize := by
    unfold operandFreePtr bytesAllocationSize
    omega
  rw [storeBytesLength_read_below_padded]
  · rw [setFreePtr_read_above_len_padded]
    · rw [wideWordResultMemory_readOperand I hb he hm hread96 hbelowOld]
      exact operandCopiedMemory_readModulusLength I baseSize exponentSize modulusSize hb he
    · exact holdMem96
    · exact hread96
    · decide
    · decide
  · rw [hsetSize]
    omega
  · exact hbelow
  · exact hgap

private theorem shiftRight_modulus_div32 {m : Nat} (hm : m ≤ 1024) :
    UInt256.shiftRight (UInt256.ofNat m) ⟨5⟩ = UInt256.ofNat (m / 32) := by
  have hmWord : m < UInt256.size :=
    lt_trans (lt_of_le_of_lt hm (by decide : 1024 < 2 ^ 64)) (by decide)
  have hdivWord : m / 32 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_le_self m 32) hmWord
  apply u256_inj
  rw [shiftRight_toNat_of_lt256 _ _ (by decide),
    UInt256.toNat_ofNat_of_lt hmWord,
    show (⟨5⟩ : UInt256).toNat = 5 by decide,
    UInt256.toNat_ofNat_of_lt hdivWord]
  norm_num

theorem wideMultiLimbOddPostAllocatorSuffixExact_of_loopEntrySuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddLoopEntrySuffixExact suffixGas) :
    WideMultiLimbOddPostAllocatorSuffixExact (fun ctx => 47 + suffixGas ctx) := by
  intro ctx hinput k rd2847
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  have hbl : l.base ≤ 1024 := by simpa [I, l] using hb
  have hel : l.exponent ≤ 1024 := by simpa [I, l] using he
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hmodLargeL : 32 < l.modulus := by simpa [I, l] using hmodLarge
  have hmodPtrWord : operandModulusPtr l.base l.exponent < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusPtr l.base l.exponent ≤ 2240 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hpostMemSize :
      (wideMultiLimbOddPostAllocatorMemory ctx).size = fp + 32 := by
    have holdSize :
        (wideMultiLimbPostAllocationMemory ctx).size = resultPtr + 32 := by
      simpa [I, l, resultPtr, wideMultiLimbPostAllocationMemory] using
        (wideWordResultMemory_size I hbl hel hml)
    have holdMem96 : 96 ≤ (wideMultiLimbPostAllocationMemory ctx).size := by
      rw [holdSize]
      dsimp [resultPtr]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    have hsetSize :
        (setFreePtr (wideMultiLimbPostAllocationMemory ctx)
          (fp + wordArrayAllocationSize words)).size =
            (wideMultiLimbPostAllocationMemory ctx).size :=
      setFreePtr_size holdMem96
    have hmemLe :
        (setFreePtr (wideMultiLimbPostAllocationMemory ctx)
          (fp + wordArrayAllocationSize words)).size ≤ fp := by
      rw [hsetSize, holdSize]
      dsimp [fp]
      unfold bytesAllocationSize
      omega
    have hgap :
        fp -
          (setFreePtr (wideMultiLimbPostAllocationMemory ctx)
            (fp + wordArrayAllocationSize words)).size < USize.size := by
      rw [hsetSize, holdSize]
      exact lt_usize _ (by
        dsimp [fp]
        unfold bytesAllocationSize
        omega)
    simpa [wideMultiLimbOddPostAllocatorMemory, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, I, l, fp, words] using
      (storeBytesLength_size
        (mem := setFreePtr (wideMultiLimbPostAllocationMemory ctx)
          (fp + wordArrayAllocationSize words))
        (fp := fp) (n := words) hmemLe hgap)
  have hmodPtrMem : (UInt256.ofNat (operandModulusPtr l.base l.exponent)).toNat <
      (wideMultiLimbOddPostAllocatorMemory ctx).size := by
    rw [UInt256.toNat_ofNat_of_lt hmodPtrWord, hpostMemSize]
    dsimp [fp, resultPtr]
    unfold operandFreePtr bytesAllocationSize
    omega
  have hread :
      (wideMultiLimbOddPostAllocatorMemory ctx).readWithPadding
          (operandModulusPtr l.base l.exponent) 32 =
        UInt256.toByteArray (UInt256.ofNat l.modulus) := by
    simpa [I, l, wideMultiLimbOddPostAllocatorMemory, wideMultiLimbPostAllocationMemory,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength, resultPtr, fp, words,
      Nat.add_assoc] using
      (wideMultiLimbOddPostAllocatorMemory_readModulusLength I hbl hel hml)
  have hawOld : (wideMultiLimbPostAllocationAw ctx).toNat ≤ 136 := by
    dsimp [wideMultiLimbPostAllocationAw]
    rw [wideWordResultWords_toNat hbl hel hml]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have hfpBound : fp ≤ 4352 := by
    dsimp [fp, resultPtr]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hn : words ≤ 32 := by
    dsimp [words]
    omega
  have hnpos : 0 < words := by
    dsimp [words]
    exact Nat.div_pos (by omega : 32 ≤ l.modulus + 31) (by decide : 0 < 32)
  have hpostAwNat :
      (wideMultiLimbOddPostAllocatorAw ctx).toNat =
        MachineState.M
          (MachineState.M (wideMultiLimbPostAllocationAw ctx).toNat fp 32)
          (fp + 32) (wordArrayPayloadSize words) := by
    simpa [I, l, fp, words, wideMultiLimbOddPostAllocatorAw,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength] using
      (newWordArrayWords_toNat_small (aw := wideMultiLimbPostAllocationAw ctx)
        (fp := fp) (n := words) hawOld hfpBound hn hnpos)
  have hpostAwLe : (wideMultiLimbOddPostAllocatorAw ctx).toNat ≤ 169 := by
    rw [hpostAwNat]
    have hstore :
        MachineState.M (wideMultiLimbPostAllocationAw ctx).toNat fp 32 ≤ 138 := by
      have hceil : (fp + 32 + 31) / 32 ≤ 138 := by
        rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
        omega
      unfold MachineState.M
      simp
      exact ⟨le_trans hawOld (by decide), hceil⟩
    have hceilCopy : (fp + 32 + 32 * words + 31) / 32 ≤ 169 := by
      rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
      omega
    have hpayloadNe : 32 * words ≠ 0 := by omega
    unfold MachineState.M wordArrayPayloadSize
    simp [hpayloadNe]
    exact ⟨le_trans hawOld (by decide),
      ⟨le_trans (by
          rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
          omega : (fp + 32 + 31) / 32 ≤ 138) (by decide),
        hceilCopy⟩⟩
  have haccess : (UInt256.ofNat (operandModulusPtr l.base l.exponent)).toNat + 32 ≤
      32 * (wideMultiLimbOddPostAllocatorAw ctx).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hmodPtrWord, hpostAwNat]
    have hpayloadPos : 0 < wordArrayPayloadSize words := by
      unfold wordArrayPayloadSize
      omega
    have hcover := machineM_covers_access
      (MachineState.M (wideMultiLimbPostAllocationAw ctx).toNat fp 32)
      (fp + 32) (wordArrayPayloadSize words) hpayloadPos
    apply le_trans _ hcover
    dsimp [fp, resultPtr]
    unfold operandFreePtr bytesAllocationSize wordArrayPayloadSize
    omega
  have hpostAwNoWrap : (wideMultiLimbOddPostAllocatorAw ctx).toNat * 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show (wideMultiLimbOddPostAllocatorAw ctx).toNat * 32 ≤ 169 * 32 by
        nlinarith)
      (by decide)
  have hload :
      wideLoadWord (wideMultiLimbOddPostAllocatorMemory ctx)
          (wideMultiLimbOddPostAllocatorAw ctx)
          (UInt256.ofNat (operandModulusPtr l.base l.exponent)) =
        UInt256.ofNat l.modulus := by
    apply wideLoadWord_eq_of_read
    · exact hmodPtrMem
    · exact not_ge_mul32_of_access haccess hpostAwNoWrap
    · rw [UInt256.toNat_ofNat_of_lt hmodPtrWord]
      exact hread
  have hshift :
      UInt256.shiftRight (UInt256.ofNat l.modulus) ⟨5⟩ =
        UInt256.ofNat (l.modulus / 32) :=
    shiftRight_modulus_div32 hml
  have hqWord : l.modulus / 32 < UInt256.size := by
    apply lt_of_le_of_lt (Nat.div_le_self l.modulus 32)
    exact lt_trans (lt_of_le_of_lt hml (by decide : 1024 < 2 ^ 64)) (by decide)
  have hlt : UInt256.lt (⟨0⟩ : UInt256) (UInt256.ofNat (l.modulus / 32)) = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨0⟩ : UInt256).toNat = 0 by decide,
      UInt256.toNat_ofNat_of_lt hqWord]
    exact Nat.div_pos (by omega : 32 ≤ l.modulus) (by decide : 0 < 32)
  have hltNe : UInt256.lt (⟨0⟩ : UInt256) (UInt256.ofNat (l.modulus / 32)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have hgasEq :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx) fp words := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simpa [I, l, fp, resultPtr, words, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hgasEq
  have hd := montgomeryPostAllocatorLoopEntryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩
  have rd2847Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2847⟩
      [UInt256.ofNat fp, ⟨2006⟩,
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx)) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddPostAllocatorStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2847
  have rd2850 := evm_run rd2847Explicit with [known jumpdest h0, known swap2 h1, known dup1 h2]
  have rd2851 := RDx.mloadWithin rd2850 h3 haccess
    (by norm_num)
  rw [hload] at rd2851
  have rd2857 := evm_run rd2851 with [known swap1 h4, known dup2 h5,
    known push1 h6 ⟨5⟩, known shr h7, known push0 h8]
  rw [hshift] at rd2857
  have rd2906 := evm_run rd2857 with [known jumpdest h9, known dup2 h10,
    known dup2 h11, known lt h12, known push2 h13 ⟨2906⟩,
    known jumpiT h14 hltNe jumpDest_2906_montgomery]
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddLoopEntryStack,
    wideMultiLimbOddPostAllocatorStack, wideMultiLimbOddPostAllocatorMemory,
    wideMultiLimbOddPostAllocatorAw, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinputCopy (k + 15) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddLoopEntryStack,
        wideMultiLimbOddPostAllocatorStack, wideMultiLimbOddPostAllocatorMemory,
        wideMultiLimbOddPostAllocatorAw, wideMultiLimbOddWordArrayPtr,
        wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd2906.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

private theorem montgomeryFirstCopyCallDecodes :
    [decode runtimeBytecode ⟨2906⟩, decode runtimeBytecode ⟨2907⟩,
      decode runtimeBytecode ⟨2908⟩, decode runtimeBytecode ⟨2910⟩,
      decode runtimeBytecode ⟨2913⟩, decode runtimeBytecode ⟨2916⟩,
      decode runtimeBytecode ⟨2919⟩, decode runtimeBytecode ⟨2921⟩,
      decode runtimeBytecode ⟨2922⟩, decode runtimeBytecode ⟨2925⟩] =
    [some (.JUMPDEST, .none), some (.DUP1, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.Push .PUSH2, some (⟨2937⟩, 2)),
      some (.Push .PUSH2, some (⟨2931⟩, 2)),
      some (.Push .PUSH2, some (⟨2926⟩, 2)),
      some (.Push .PUSH1, some (⟨1⟩, 1)),
      some (.SWAP6, .none),
      some (.Push .PUSH2, some (⟨1323⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1323_montgomery :
    (D_J runtimeBytecode 0).contains ⟨1323⟩ = true := by native_decide

private theorem montgomeryFirstCopyAddDecodes :
    [decode runtimeBytecode ⟨1323⟩, decode runtimeBytecode ⟨1324⟩,
      decode runtimeBytecode ⟨1325⟩, decode runtimeBytecode ⟨1327⟩,
      decode runtimeBytecode ⟨1328⟩, decode runtimeBytecode ⟨1329⟩,
      decode runtimeBytecode ⟨1330⟩, decode runtimeBytecode ⟨1331⟩,
      decode runtimeBytecode ⟨1332⟩, decode runtimeBytecode ⟨1335⟩,
      decode runtimeBytecode ⟨1336⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.DUP3, .none),
      some (.ADD, .none), some (.DUP1, .none), some (.SWAP3, .none),
      some (.GT, .none), some (.Push .PUSH2, some (⟨1037⟩, 2)),
      some (.JUMPI, .none), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_2926_montgomery :
    (D_J runtimeBytecode 0).contains ⟨2926⟩ = true := by native_decide

private theorem montgomeryFirstCopyReadCallDecodes :
    [decode runtimeBytecode ⟨2926⟩, decode runtimeBytecode ⟨2927⟩,
      decode runtimeBytecode ⟨2930⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨1903⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1903_montgomery :
    (D_J runtimeBytecode 0).contains ⟨1903⟩ = true := by native_decide

private theorem montgomeryFirstCopyReadGuardDecodes :
    [decode runtimeBytecode ⟨1903⟩, decode runtimeBytecode ⟨1904⟩,
      decode runtimeBytecode ⟨1905⟩, decode runtimeBytecode ⟨1906⟩,
      decode runtimeBytecode ⟨1908⟩, decode runtimeBytecode ⟨1909⟩,
      decode runtimeBytecode ⟨1910⟩, decode runtimeBytecode ⟨1911⟩,
      decode runtimeBytecode ⟨1912⟩, decode runtimeBytecode ⟨1913⟩,
      decode runtimeBytecode ⟨1915⟩, decode runtimeBytecode ⟨1916⟩,
      decode runtimeBytecode ⟨1917⟩, decode runtimeBytecode ⟨1918⟩,
      decode runtimeBytecode ⟨1919⟩, decode runtimeBytecode ⟨1920⟩,
      decode runtimeBytecode ⟨1923⟩, decode runtimeBytecode ⟨1924⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.DUP2, .none),
      some (.Push .PUSH1, some (⟨5⟩, 1)), some (.SHL, .none),
      some (.SWAP2, .none), some (.DUP1, .none), some (.DUP4, .none),
      some (.DIV, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.EQ, .none), some (.SWAP1, .none), some (.ISZERO, .none),
      some (.OR, .none), some (.ISZERO, .none),
      some (.Push .PUSH2, some (⟨1037⟩, 2)), some (.JUMPI, .none),
      some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_2931_montgomery :
    (D_J runtimeBytecode 0).contains ⟨2931⟩ = true := by native_decide

private theorem montgomeryFirstCopySubCallDecodes :
    [decode runtimeBytecode ⟨2931⟩, decode runtimeBytecode ⟨2932⟩,
      decode runtimeBytecode ⟨2933⟩, decode runtimeBytecode ⟨2936⟩] =
    [some (.JUMPDEST, .none), some (.DUP8, .none),
      some (.Push .PUSH2, some (⟨1103⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1103_montgomery :
    (D_J runtimeBytecode 0).contains ⟨1103⟩ = true := by native_decide

private theorem montgomeryFirstCopySubDecodes :
    [decode runtimeBytecode ⟨1103⟩, decode runtimeBytecode ⟨1104⟩,
      decode runtimeBytecode ⟨1105⟩, decode runtimeBytecode ⟨1106⟩,
      decode runtimeBytecode ⟨1107⟩, decode runtimeBytecode ⟨1108⟩,
      decode runtimeBytecode ⟨1109⟩, decode runtimeBytecode ⟨1110⟩,
      decode runtimeBytecode ⟨1111⟩, decode runtimeBytecode ⟨1114⟩,
      decode runtimeBytecode ⟨1115⟩] =
    [some (.JUMPDEST, .none), some (.SWAP2, .none), some (.SWAP1, .none),
      some (.DUP3, .none), some (.SUB, .none), some (.SWAP2, .none),
      some (.DUP3, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨1037⟩, 2)), some (.JUMPI, .none),
      some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_2937_montgomery :
    (D_J runtimeBytecode 0).contains ⟨2937⟩ = true := by native_decide

private theorem montgomeryFirstCopyStoreDecodes :
    [decode runtimeBytecode ⟨2937⟩, decode runtimeBytecode ⟨2938⟩,
      decode runtimeBytecode ⟨2939⟩, decode runtimeBytecode ⟨2940⟩,
      decode runtimeBytecode ⟨2941⟩, decode runtimeBytecode ⟨2942⟩,
      decode runtimeBytecode ⟨2944⟩, decode runtimeBytecode ⟨2945⟩,
      decode runtimeBytecode ⟨2947⟩, decode runtimeBytecode ⟨2948⟩,
      decode runtimeBytecode ⟨2949⟩, decode runtimeBytecode ⟨2950⟩,
      decode runtimeBytecode ⟨2951⟩, decode runtimeBytecode ⟨2952⟩,
      decode runtimeBytecode ⟨2953⟩, decode runtimeBytecode ⟨2956⟩] =
    [some (.JUMPDEST, .none), some (.DUP6, .none), some (.ADD, .none),
      some (.ADD, .none), some (.MLOAD, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP3, .none),
      some (.Push .PUSH1, some (⟨5⟩, 1)), some (.SHL, .none),
      some (.DUP10, .none), some (.ADD, .none), some (.ADD, .none),
      some (.MSTORE, .none), some (.ADD, .none),
      some (.Push .PUSH2, some (⟨2857⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_2857_montgomery :
    (D_J runtimeBytecode 0).contains ⟨2857⟩ = true := by native_decide

theorem wideMultiLimbOddLoopEntrySuffixExact_of_firstCopyAddSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddFirstCopyAddSuffixExact suffixGas) :
    WideMultiLimbOddLoopEntrySuffixExact (fun ctx => 33 + suffixGas ctx) := by
  intro ctx hinput k rd2906
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have rd2906Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2906⟩
      [⟨0⟩, UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddLoopEntryStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2906
  have rd1323 := evm_run rd2906Explicit with [
    known jumpdest h0, known dup1 h1, known push1 h2 ⟨32⟩,
    known push2 h3 ⟨2937⟩, known push2 h4 ⟨2931⟩,
    known push2 h5 ⟨2926⟩, known push1 h6 ⟨1⟩,
    known swap6 h7, known push2 h8 ⟨1323⟩,
    known jump h9 jumpDest_1323_montgomery]
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddLoopEntryStack,
    wideMultiLimbOddFirstCopyAddStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (k + 10) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyAddStack,
        wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1323.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddFirstCopyAddSuffixExact_of_returnSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddFirstCopyAddReturnSuffixExact suffixGas) :
    WideMultiLimbOddFirstCopyAddSuffixExact (fun ctx => 43 + suffixGas ctx) := by
  intro ctx hinput k rd1323
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyAddDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  have rd1323Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1323⟩
      [⟨0⟩, ⟨2926⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨0⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyAddStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd1323
  have hadd : (⟨0⟩ : UInt256) + ⟨1⟩ = ⟨1⟩ := by native_decide
  have hgt : UInt256.gt (⟨0⟩ : UInt256) ((⟨0⟩ : UInt256) + ⟨1⟩) = ⟨0⟩ := by
    rw [hadd]
    native_decide
  have rd1336raw := evm_run rd1323Explicit with [
    known jumpdest h0, known swap1 h1, known push1 h2 ⟨1⟩,
    known dup3 h3, known add h4, known dup1 h5, known swap3 h6,
    known gt h7, known push2 h8 ⟨1037⟩, known jumpiNT h9 hgt,
    known jump h10 jumpDest_2926_montgomery]
  rw [hadd] at rd1336raw
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyAddStack,
    wideMultiLimbOddFirstCopyAddReturnStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (k + 11) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyAddReturnStack,
        wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1336raw.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddFirstCopyAddReturnSuffixExact_of_readSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddFirstCopyReadSuffixExact suffixGas) :
    WideMultiLimbOddFirstCopyAddReturnSuffixExact (fun ctx => 12 + suffixGas ctx) := by
  intro ctx hinput k rd2926
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyReadCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rd2926Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2926⟩
      [⟨1⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨0⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyAddReturnStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2926
  have rd1903 := evm_run rd2926Explicit with [
    known jumpdest h0, known push2 h1 ⟨1903⟩,
    known jump h2 jumpDest_1903_montgomery]
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyAddReturnStack,
    wideMultiLimbOddFirstCopyReadStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (k + 3) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyReadStack,
        wideMultiLimbOddFirstCopyAddReturnStack, wideMultiLimbOddWordArrayPtr,
        wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1903.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddFirstCopyReadSuffixExact_of_storeSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddFirstCopyStoreSuffixExact suffixGas) :
    WideMultiLimbOddFirstCopyReadSuffixExact (fun ctx => 124 + suffixGas ctx) := by
  intro ctx hinput k rd1903
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨_hb, _he, hm⟩
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hmodLargeL : 32 < l.modulus := by simpa [I, l] using hmodLarge
  have hmodWord : l.modulus < UInt256.size :=
    lt_of_le_of_lt hml (by decide : 1024 < UInt256.size)
  have hremWord : l.modulus - 32 < UInt256.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) hmodWord
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hdRead := montgomeryFirstCopyReadGuardDecodes
  simp only [List.cons.injEq, and_true] at hdRead
  rcases hdRead with
    ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17⟩
  have rd1903Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1903⟩
      [⟨1⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨0⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyReadStack,
      wideMultiLimbOddFirstCopyAddReturnStack, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      rd1903
  have hshl : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨5⟩ = ⟨32⟩ := by native_decide
  have hdiv : UInt256.div (⟨32⟩ : UInt256) ⟨1⟩ = ⟨32⟩ := by native_decide
  have heq : UInt256.eq (⟨32⟩ : UInt256) ⟨32⟩ = ⟨1⟩ := by native_decide
  have hiszero1 : UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ := by native_decide
  have hor : UInt256.lor (⟨0⟩ : UInt256) ⟨1⟩ = ⟨1⟩ := by native_decide
  have rd1909 := evm_run rd1903Explicit with [
    known jumpdest r0, known swap1 r1, known dup2 r2,
    known push1 r3 ⟨5⟩, known shl r4]
  rw [hshl] at rd1909
  have rd1916 := evm_run rd1909 with [
    known swap2 r5, known dup1 r6, known dup4 r7,
    known div r8, known push1 r9 ⟨32⟩, known eq r10]
  rw [hdiv, heq] at rd1916
  have rd1923 := evm_run rd1916 with [
    known swap1 r11, known iszero r12, known or r13,
    known iszero r14, known push2 r15 ⟨1037⟩]
  rw [hiszero1, hor, hiszero1] at rd1923
  have rd1924 := rd1923.jumpiNT r16 (by native_decide) (by evm_ov)
  have rd2931 := rd1924.jump r17 jumpDest_2931_montgomery (by evm_ov)
  have hdSubCall := montgomeryFirstCopySubCallDecodes
  simp only [List.cons.injEq, and_true] at hdSubCall
  rcases hdSubCall with ⟨c0,c1,c2,c3⟩
  have rd1103 := evm_run rd2931 with [
    known jumpdest c0, known dup8 c1, known push2 c2 ⟨1103⟩,
    known jump c3 jumpDest_1103_montgomery]
  have hdSub := montgomeryFirstCopySubDecodes
  simp only [List.cons.injEq, and_true] at hdSub
  rcases hdSub with ⟨s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10⟩
  have hsub : UInt256.sub (UInt256.ofNat l.modulus) ⟨32⟩ =
      UInt256.ofNat (l.modulus - 32) := by
    apply u256_inj
    rw [usub_toNat]
    · rw [UInt256.toNat_ofNat_of_lt hmodWord,
        show (⟨32⟩ : UInt256).toNat = 32 by decide,
        UInt256.toNat_ofNat_of_lt hremWord]
    · rw [UInt256.toNat_ofNat_of_lt hmodWord,
        show (⟨32⟩ : UInt256).toNat = 32 by decide]
      omega
  have hgt : UInt256.gt (UInt256.ofNat (l.modulus - 32))
      (UInt256.ofNat l.modulus) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hremWord, UInt256.toNat_ofNat_of_lt hmodWord]
    omega
  have rd1114raw := evm_run rd1103 with [
    known jumpdest s0, known swap2 s1, known swap1 s2, known dup3 s3,
    known sub s4, known swap2 s5, known dup3 s6, known gt s7,
    known push2 s8 ⟨1037⟩]
  rw [hsub, hgt] at rd1114raw
  have rd1115 := rd1114raw.jumpiNT s9 (by native_decide) (by evm_ov)
  have rd2937 := rd1115.jump s10 jumpDest_2937_montgomery (by evm_ov)
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyReadStack,
    wideMultiLimbOddFirstCopyAddReturnStack, wideMultiLimbOddFirstCopyStoreStack,
    wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinputCopy (k + 33) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyStoreStack,
        wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd2937.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddFirstCopyStoreSuffixExact_of_loopBackSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddFirstCopyLoopBackSuffixExact suffixGas) :
    WideMultiLimbOddFirstCopyStoreSuffixExact (fun ctx => 51 + suffixGas ctx) := by
  intro ctx hinput k rd2937
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  let src := operandModulusPtr l.base l.exponent + l.modulus
  let dst := fp + 32
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  have hbl : l.base ≤ 1024 := by simpa [I, l] using hb
  have hel : l.exponent ≤ 1024 := by simpa [I, l] using he
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hmodLargeL : 32 < l.modulus := by simpa [I, l] using hmodLarge
  have hsrcWord : src < UInt256.size := by
    apply lt_of_le_of_lt
      (show src ≤ 3296 by
        dsimp [src]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hdstWord : dst < UInt256.size := by
    apply lt_of_le_of_lt
      (show dst ≤ 5440 by
        dsimp [dst, fp, resultPtr]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hmptrRemWord :
      operandModulusPtr l.base l.exponent + (l.modulus - 32) < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusPtr l.base l.exponent + (l.modulus - 32) ≤ 3264 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hsrcAdd₁ :
      UInt256.ofNat (operandModulusPtr l.base l.exponent) +
          UInt256.ofNat (l.modulus - 32) =
        UInt256.ofNat (operandModulusPtr l.base l.exponent + (l.modulus - 32)) := by
    exact ofNat_add_bounded hmptrRemWord
  have hsrcAdd₂ :
      UInt256.ofNat (operandModulusPtr l.base l.exponent + (l.modulus - 32)) +
          (⟨32⟩ : UInt256) =
        UInt256.ofNat src := by
    change UInt256.ofNat (operandModulusPtr l.base l.exponent + (l.modulus - 32)) +
        UInt256.ofNat 32 = UInt256.ofNat src
    have hsum :
        operandModulusPtr l.base l.exponent + (l.modulus - 32) + 32 = src := by
      dsimp [src]
      omega
    rw [ofNat_add_bounded (by rw [hsum]; exact hsrcWord)]
    rw [hsum]
  have hfpWord : fp < UInt256.size := by
    apply lt_of_le_of_lt
      (show fp ≤ 5408 by
        dsimp [fp, resultPtr]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hdstAdd₁ : UInt256.ofNat fp + (⟨0⟩ : UInt256) = UInt256.ofNat fp := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hfpWord,
      show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.add_zero,
      Nat.mod_eq_of_lt hfpWord]
  have hdstAdd₂ : UInt256.ofNat fp + (⟨32⟩ : UInt256) = UInt256.ofNat dst := by
    change UInt256.ofNat fp + UInt256.ofNat 32 = UInt256.ofNat dst
    rw [ofNat_add_bounded (by simpa [dst] using hdstWord)]
  have hadd : (⟨0⟩ : UInt256) + ⟨1⟩ = ⟨1⟩ := by native_decide
  have hshl : UInt256.shiftLeft (⟨0⟩ : UInt256) ⟨5⟩ = ⟨0⟩ := by native_decide
  have hawOld : (wideMultiLimbPostAllocationAw ctx).toNat ≤ 136 := by
    dsimp [wideMultiLimbPostAllocationAw]
    rw [wideWordResultWords_toNat hbl hel hml]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have hfpBound : fp ≤ 4352 := by
    dsimp [fp, resultPtr]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hn : words ≤ 32 := by
    dsimp [words]
    omega
  have hnpos : 0 < words := by
    dsimp [words]
    exact Nat.div_pos (by omega : 32 ≤ l.modulus + 31) (by decide : 0 < 32)
  have hpostAwNat :
      (wideMultiLimbOddPostAllocatorAw ctx).toNat =
        MachineState.M
          (MachineState.M (wideMultiLimbPostAllocationAw ctx).toNat fp 32)
          (fp + 32) (wordArrayPayloadSize words) := by
    simpa [I, l, fp, words, wideMultiLimbOddPostAllocatorAw,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength] using
      (newWordArrayWords_toNat_small (aw := wideMultiLimbPostAllocationAw ctx)
        (fp := fp) (n := words) hawOld hfpBound hn hnpos)
  have hpayloadPos : 0 < wordArrayPayloadSize words := by
    unfold wordArrayPayloadSize
    omega
  have hcover := machineM_covers_access
    (MachineState.M (wideMultiLimbPostAllocationAw ctx).toNat fp 32)
    (fp + 32) (wordArrayPayloadSize words) hpayloadPos
  have hsrcAccess : (UInt256.ofNat src).toNat + 32 ≤
      32 * (wideMultiLimbOddPostAllocatorAw ctx).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hsrcWord, hpostAwNat]
    apply le_trans _ hcover
    dsimp [src, fp, resultPtr]
    unfold operandFreePtr bytesAllocationSize wordArrayPayloadSize
    have hround := bytesSize_le_roundedPayload l.modulus
    omega
  have hdstAccess : (UInt256.ofNat dst).toNat + 32 ≤
      32 * (wideMultiLimbOddPostAllocatorAw ctx).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hdstWord, hpostAwNat]
    apply le_trans _ hcover
    dsimp [dst]
    unfold wordArrayPayloadSize
    omega
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyStoreDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with
    ⟨d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15⟩
  have rd2937Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2937⟩
      [UInt256.ofNat (l.modulus - 32), ⟨32⟩, ⟨0⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddPostAllocatorMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyStoreStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2937
  have rd2941raw := evm_run rd2937Explicit with [
    known jumpdest d0, known dup6 d1, known add d2, known add d3]
  rw [hsrcAdd₁, hsrcAdd₂] at rd2941raw
  have rd2942 := RDx.mloadWithin rd2941raw d4 hsrcAccess (by evm_ov)
  have rd2951raw := evm_run rd2942 with [
    known push1 d5 ⟨32⟩, known dup3 d6, known push1 d7 ⟨5⟩,
    known shl d8, known dup10 d9, known add d10, known add d11]
  rw [hshl, hdstAdd₁, hdstAdd₂] at rd2951raw
  have hmstoreCostZero :
      Cₘ (UInt256.ofNat
          (MachineState.M (wideMultiLimbOddPostAllocatorAw ctx).toNat
            (UInt256.ofNat dst).toNat 32)) -
        Cₘ (wideMultiLimbOddPostAllocatorAw ctx) = 0 := by
    rw [machineM_eq_of_access hdstAccess, u256_ofNat_toNat]
    omega
  have rd2952 := RDx.mstore 0 (wideMultiLimbOddFirstCopyStoredMemory ctx)
      (wideMultiLimbOddPostAllocatorAw ctx) rd2951raw d12
    (by
      intro s hsaw hstk
      exact mstoreCost_of_stack hsaw hstk hmstoreCostZero)
    (by
      rw [UInt256.toNat_ofNat_of_lt hdstWord]
      rfl)
    (by
      rw [machineM_eq_of_access hdstAccess, u256_ofNat_toNat])
    (by evm_ov)
  have rd2857raw := evm_run rd2952 with [
    known add d13, known push2 d14 ⟨2857⟩,
    known jump d15 jumpDest_2857_montgomery]
  rw [hadd] at rd2857raw
  simpa [I, l, words, resultPtr, fp, src, dst,
    wideMultiLimbOddFirstCopyStoreStack, wideMultiLimbOddFirstCopyLoopBackStack,
    wideMultiLimbOddFirstCopyStoredMemory, wideMultiLimbOddFirstCopyLoadedWord,
    wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinputCopy (k + 16) (by
      simpa [I, l, words, resultPtr, fp, src, dst,
        wideMultiLimbOddFirstCopyLoopBackStack, wideMultiLimbOddFirstCopyStoredMemory,
        wideMultiLimbOddFirstCopyLoadedWord, wideMultiLimbOddWordArrayPtr,
        wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd2857raw.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddFirstCopyLoopBackSuffixExact_of_guardSuffixes
    (continueGas exitGas : BytecodeContext → Nat)
    (hcontinue : WideMultiLimbOddFirstCopyContinueSuffixExact continueGas)
    (hexit : WideMultiLimbOddFirstCopyExitSuffixExact exitGas) :
    WideMultiLimbOddFirstCopyLoopBackSuffixExact
      (fun ctx =>
        23 + if 1 < (lengths ctx.executionEnv.calldata).modulus / 32 then
          continueGas ctx
        else
          exitGas ctx) := by
  intro ctx hinput k rd2857
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, _hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨_hb, _he, hm⟩
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hqWord : l.modulus / 32 < UInt256.size := by
    apply lt_of_le_of_lt (Nat.div_le_self l.modulus 32)
    exact lt_trans (lt_of_le_of_lt hml (by decide : 1024 < 2 ^ 64)) (by decide)
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryPostAllocatorLoopEntryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨_h0,_h1,_h2,_h3,_h4,_h5,_h6,_h7,_h8,h9,h10,h11,h12,h13,h14⟩
  have rd2857Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2857⟩
      [⟨1⟩, UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyLoopBackStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2857
  have rd2864raw := evm_run rd2857Explicit with [
    known jumpdest h9, known dup2 h10, known dup2 h11,
    known lt h12, known push2 h13 ⟨2906⟩]
  by_cases hmore : 1 < l.modulus / 32
  · have hlt : UInt256.lt (⟨1⟩ : UInt256)
        (UInt256.ofNat (l.modulus / 32)) = ⟨1⟩ := by
      apply ult_one
      rw [show (⟨1⟩ : UInt256).toNat = 1 by decide,
        UInt256.toNat_ofNat_of_lt hqWord]
      exact hmore
    have hltNe : UInt256.lt (⟨1⟩ : UInt256)
        (UInt256.ofNat (l.modulus / 32)) ≠ ⟨0⟩ := by
      rw [hlt]
      decide
    rw [hlt] at rd2864raw
    have rd2906 := rd2864raw.jumpiT h14 (by native_decide)
      jumpDest_2906_montgomery (by evm_ov)
    simpa [I, l, words, resultPtr, fp, hmore,
      wideMultiLimbOddFirstCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hcontinue ctx hinputCopy
        (by simpa [I, l] using hmore) (k + 6) (by
          simpa [I, l, words, resultPtr, fp,
            wideMultiLimbOddFirstCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
            wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            rd2906.withIndices (by omega) (by
              rw [← hgasEqExpanded]
              omega)))
  · have hlt : UInt256.lt (⟨1⟩ : UInt256)
        (UInt256.ofNat (l.modulus / 32)) = ⟨0⟩ := by
      apply ult_zero
      rw [show (⟨1⟩ : UInt256).toNat = 1 by decide,
        UInt256.toNat_ofNat_of_lt hqWord]
      omega
    rw [hlt] at rd2864raw
    have rd2865 := rd2864raw.jumpiNT h14 (by native_decide) (by evm_ov)
    simpa [I, l, words, resultPtr, fp, hmore,
      wideMultiLimbOddFirstCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hexit ctx hinputCopy
        (by simpa [I, l] using hmore) (k + 6) (by
          simpa [I, l, words, resultPtr, fp,
            wideMultiLimbOddFirstCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
            wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            rd2865.withIndices (by omega) (by
              rw [← hgasEqExpanded]
              omega)))

theorem wideMultiLimbOddFirstCopyContinueSuffixExact_of_secondCopyAddSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddSecondCopyAddSuffixExact suffixGas) :
    WideMultiLimbOddFirstCopyContinueSuffixExact (fun ctx => 33 + suffixGas ctx) := by
  intro ctx hinput hmore k rd2906
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have rd2906Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2906⟩
      [⟨1⟩, UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyLoopBackStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2906
  have rd1323 := evm_run rd2906Explicit with [
    known jumpdest h0, known dup1 h1, known push1 h2 ⟨32⟩,
    known push2 h3 ⟨2937⟩, known push2 h4 ⟨2931⟩,
    known push2 h5 ⟨2926⟩, known push1 h6 ⟨1⟩,
    known swap6 h7, known push2 h8 ⟨1323⟩,
    known jump h9 jumpDest_1323_montgomery]
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFirstCopyLoopBackStack,
    wideMultiLimbOddSecondCopyAddStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (by simpa [I, l] using hmore) (k + 10) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyAddStack,
        wideMultiLimbOddFirstCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
        wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1323.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddSecondCopyAddSuffixExact_of_returnSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddSecondCopyAddReturnSuffixExact suffixGas) :
    WideMultiLimbOddSecondCopyAddSuffixExact (fun ctx => 43 + suffixGas ctx) := by
  intro ctx hinput hmore k rd1323
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyAddDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  have rd1323Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1323⟩
      [⟨1⟩, ⟨2926⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨1⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyAddStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd1323
  have hadd : (⟨1⟩ : UInt256) + ⟨1⟩ = ⟨2⟩ := by native_decide
  have hgt : UInt256.gt (⟨1⟩ : UInt256) ((⟨1⟩ : UInt256) + ⟨1⟩) = ⟨0⟩ := by
    rw [hadd]
    native_decide
  have rd1336raw := evm_run rd1323Explicit with [
    known jumpdest h0, known swap1 h1, known push1 h2 ⟨1⟩,
    known dup3 h3, known add h4, known dup1 h5, known swap3 h6,
    known gt h7, known push2 h8 ⟨1037⟩, known jumpiNT h9 hgt,
    known jump h10 jumpDest_2926_montgomery]
  rw [hadd] at rd1336raw
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyAddStack,
    wideMultiLimbOddSecondCopyAddReturnStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (by simpa [I, l] using hmore) (k + 11) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyAddReturnStack,
        wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1336raw.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddSecondCopyAddReturnSuffixExact_of_readSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddSecondCopyReadSuffixExact suffixGas) :
    WideMultiLimbOddSecondCopyAddReturnSuffixExact (fun ctx => 12 + suffixGas ctx) := by
  intro ctx hinput hmore k rd2926
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyReadCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rd2926Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2926⟩
      [⟨2⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨1⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyAddReturnStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2926
  have rd1903 := evm_run rd2926Explicit with [
    known jumpdest h0, known push2 h1 ⟨1903⟩,
    known jump h2 jumpDest_1903_montgomery]
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyAddReturnStack,
    wideMultiLimbOddSecondCopyReadStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (by simpa [I, l] using hmore) (k + 3) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyReadStack,
        wideMultiLimbOddSecondCopyAddReturnStack, wideMultiLimbOddWordArrayPtr,
        wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1903.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddSecondCopyReadSuffixExact_of_storeSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddSecondCopyStoreSuffixExact suffixGas) :
    WideMultiLimbOddSecondCopyReadSuffixExact (fun ctx => 124 + suffixGas ctx) := by
  intro ctx hinput hmore k rd1903
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, _hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨_hb, _he, hm⟩
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hmoreL : 1 < l.modulus / 32 := by simpa [I, l] using hmore
  have hge64 : 64 ≤ l.modulus := by
    have hle : 2 ≤ l.modulus / 32 := by omega
    have hmul : 2 * 32 ≤ (l.modulus / 32) * 32 :=
      Nat.mul_le_mul_right 32 hle
    have hdivmul : (l.modulus / 32) * 32 ≤ l.modulus :=
      Nat.div_mul_le_self l.modulus 32
    omega
  have hmodWord : l.modulus < UInt256.size :=
    lt_of_le_of_lt hml (by decide : 1024 < UInt256.size)
  have hremWord : l.modulus - 64 < UInt256.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) hmodWord
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hdRead := montgomeryFirstCopyReadGuardDecodes
  simp only [List.cons.injEq, and_true] at hdRead
  rcases hdRead with
    ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17⟩
  have rd1903Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1903⟩
      [⟨2⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨1⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyReadStack,
      wideMultiLimbOddSecondCopyAddReturnStack, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      rd1903
  have hshl : UInt256.shiftLeft (⟨2⟩ : UInt256) ⟨5⟩ = ⟨64⟩ := by native_decide
  have hdiv : UInt256.div (⟨64⟩ : UInt256) ⟨2⟩ = ⟨32⟩ := by native_decide
  have heq : UInt256.eq (⟨32⟩ : UInt256) ⟨32⟩ = ⟨1⟩ := by native_decide
  have hiszero2 : UInt256.isZero (⟨2⟩ : UInt256) = ⟨0⟩ := by native_decide
  have hiszero1 : UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ := by native_decide
  have hor : UInt256.lor (⟨0⟩ : UInt256) ⟨1⟩ = ⟨1⟩ := by native_decide
  have rd1909 := evm_run rd1903Explicit with [
    known jumpdest r0, known swap1 r1, known dup2 r2,
    known push1 r3 ⟨5⟩, known shl r4]
  rw [hshl] at rd1909
  have rd1916 := evm_run rd1909 with [
    known swap2 r5, known dup1 r6, known dup4 r7,
    known div r8, known push1 r9 ⟨32⟩, known eq r10]
  rw [hdiv, heq] at rd1916
  have rd1923 := evm_run rd1916 with [
    known swap1 r11, known iszero r12, known or r13,
    known iszero r14, known push2 r15 ⟨1037⟩]
  rw [hiszero2, hor, hiszero1] at rd1923
  have rd1924 := rd1923.jumpiNT r16 (by native_decide) (by evm_ov)
  have rd2931 := rd1924.jump r17 jumpDest_2931_montgomery (by evm_ov)
  have hdSubCall := montgomeryFirstCopySubCallDecodes
  simp only [List.cons.injEq, and_true] at hdSubCall
  rcases hdSubCall with ⟨c0,c1,c2,c3⟩
  have rd1103 := evm_run rd2931 with [
    known jumpdest c0, known dup8 c1, known push2 c2 ⟨1103⟩,
    known jump c3 jumpDest_1103_montgomery]
  have hdSub := montgomeryFirstCopySubDecodes
  simp only [List.cons.injEq, and_true] at hdSub
  rcases hdSub with ⟨s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10⟩
  have hsub : UInt256.sub (UInt256.ofNat l.modulus) ⟨64⟩ =
      UInt256.ofNat (l.modulus - 64) := by
    apply u256_inj
    rw [usub_toNat]
    · rw [UInt256.toNat_ofNat_of_lt hmodWord,
        show (⟨64⟩ : UInt256).toNat = 64 by decide,
        UInt256.toNat_ofNat_of_lt hremWord]
    · rw [UInt256.toNat_ofNat_of_lt hmodWord,
        show (⟨64⟩ : UInt256).toNat = 64 by decide]
      omega
  have hgt : UInt256.gt (UInt256.ofNat (l.modulus - 64))
      (UInt256.ofNat l.modulus) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hremWord, UInt256.toNat_ofNat_of_lt hmodWord]
    omega
  have rd1114raw := evm_run rd1103 with [
    known jumpdest s0, known swap2 s1, known swap1 s2, known dup3 s3,
    known sub s4, known swap2 s5, known dup3 s6, known gt s7,
    known push2 s8 ⟨1037⟩]
  rw [hsub, hgt] at rd1114raw
  have rd1115 := rd1114raw.jumpiNT s9 (by native_decide) (by evm_ov)
  have rd2937 := rd1115.jump s10 jumpDest_2937_montgomery (by evm_ov)
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyReadStack,
    wideMultiLimbOddSecondCopyAddReturnStack, wideMultiLimbOddSecondCopyStoreStack,
    wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinputCopy (by simpa [I, l] using hmore) (k + 33) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyStoreStack,
        wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd2937.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddSecondCopyStoreSuffixExact_of_loopBackSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddSecondCopyLoopBackSuffixExact suffixGas) :
    WideMultiLimbOddSecondCopyStoreSuffixExact (fun ctx => 51 + suffixGas ctx) := by
  intro ctx hinput hmore k rd2937
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  let srcOff := l.modulus - 64
  let src := operandModulusPtr l.base l.exponent + srcOff + 32
  let dstMid := fp + 32
  let dst := fp + 64
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, _hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  have hbl : l.base ≤ 1024 := by simpa [I, l] using hb
  have hel : l.exponent ≤ 1024 := by simpa [I, l] using he
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hmoreL : 1 < l.modulus / 32 := by simpa [I, l] using hmore
  have hge64 : 64 ≤ l.modulus := by
    have hle : 2 ≤ l.modulus / 32 := by omega
    have hmul : 2 * 32 ≤ (l.modulus / 32) * 32 :=
      Nat.mul_le_mul_right 32 hle
    have hdivmul : (l.modulus / 32) * 32 ≤ l.modulus :=
      Nat.div_mul_le_self l.modulus 32
    omega
  have hsrcWord : src < UInt256.size := by
    apply lt_of_le_of_lt
      (show src ≤ 3296 by
        dsimp [src, srcOff]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hdstWord : dst < UInt256.size := by
    apply lt_of_le_of_lt
      (show dst ≤ 5440 by
        dsimp [dst, fp, resultPtr]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hmptrRemWord :
      operandModulusPtr l.base l.exponent + srcOff < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusPtr l.base l.exponent + srcOff ≤ 3264 by
        dsimp [srcOff]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hsrcAdd₁ :
      UInt256.ofNat (operandModulusPtr l.base l.exponent) +
          UInt256.ofNat srcOff =
        UInt256.ofNat (operandModulusPtr l.base l.exponent + srcOff) := by
    exact ofNat_add_bounded hmptrRemWord
  have hsrcAdd₂ :
      UInt256.ofNat (operandModulusPtr l.base l.exponent + srcOff) +
          (⟨32⟩ : UInt256) =
        UInt256.ofNat src := by
    change UInt256.ofNat (operandModulusPtr l.base l.exponent + srcOff) +
        UInt256.ofNat 32 = UInt256.ofNat src
    rw [ofNat_add_bounded (by simpa [src] using hsrcWord)]
  have hfpWord : fp < UInt256.size := by
    apply lt_of_le_of_lt
      (show fp ≤ 5408 by
        dsimp [fp, resultPtr]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hdstMidWord : dstMid < UInt256.size := by
    apply lt_of_le_of_lt
      (show dstMid ≤ 5440 by
        dsimp [dstMid, fp, resultPtr]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hdstAdd₁ : UInt256.ofNat fp + (⟨32⟩ : UInt256) = UInt256.ofNat dstMid := by
    change UInt256.ofNat fp + UInt256.ofNat 32 = UInt256.ofNat dstMid
    rw [ofNat_add_bounded (by simpa [dstMid] using hdstMidWord)]
  have hdstAdd₂ : UInt256.ofNat dstMid + (⟨32⟩ : UInt256) = UInt256.ofNat dst := by
    change UInt256.ofNat dstMid + UInt256.ofNat 32 = UInt256.ofNat dst
    rw [ofNat_add_bounded (by simpa [dstMid, dst, Nat.add_assoc] using hdstWord)]
  have hadd : (⟨1⟩ : UInt256) + ⟨1⟩ = ⟨2⟩ := by native_decide
  have hshl : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨5⟩ = ⟨32⟩ := by native_decide
  have hawOld : (wideMultiLimbPostAllocationAw ctx).toNat ≤ 136 := by
    dsimp [wideMultiLimbPostAllocationAw]
    rw [wideWordResultWords_toNat hbl hel hml]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have hfpBound : fp ≤ 4352 := by
    dsimp [fp, resultPtr]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hn : words ≤ 32 := by
    dsimp [words]
    omega
  have hnpos : 0 < words := by
    dsimp [words]
    exact Nat.div_pos (by omega : 32 ≤ l.modulus + 31) (by decide : 0 < 32)
  have hpostAwNat :
      (wideMultiLimbOddPostAllocatorAw ctx).toNat =
        MachineState.M
          (MachineState.M (wideMultiLimbPostAllocationAw ctx).toNat fp 32)
          (fp + 32) (wordArrayPayloadSize words) := by
    simpa [I, l, fp, words, wideMultiLimbOddPostAllocatorAw,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength] using
      (newWordArrayWords_toNat_small (aw := wideMultiLimbPostAllocationAw ctx)
        (fp := fp) (n := words) hawOld hfpBound hn hnpos)
  have hpayloadPos : 0 < wordArrayPayloadSize words := by
    unfold wordArrayPayloadSize
    omega
  have hcover := machineM_covers_access
    (MachineState.M (wideMultiLimbPostAllocationAw ctx).toNat fp 32)
    (fp + 32) (wordArrayPayloadSize words) hpayloadPos
  have hsrcAccess : (UInt256.ofNat src).toNat + 32 ≤
      32 * (wideMultiLimbOddPostAllocatorAw ctx).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hsrcWord, hpostAwNat]
    apply le_trans _ hcover
    dsimp [src, srcOff, fp, resultPtr]
    unfold operandFreePtr bytesAllocationSize wordArrayPayloadSize
    have hround := bytesSize_le_roundedPayload l.modulus
    omega
  have hdstAccess : (UInt256.ofNat dst).toNat + 32 ≤
      32 * (wideMultiLimbOddPostAllocatorAw ctx).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hdstWord, hpostAwNat]
    apply le_trans _ hcover
    dsimp [dst]
    unfold wordArrayPayloadSize
    omega
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyStoreDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with
    ⟨d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15⟩
  have rd2937Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2937⟩
      [UInt256.ofNat (l.modulus - 64), ⟨32⟩, ⟨1⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddFirstCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyStoreStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2937
  have rd2941raw := evm_run rd2937Explicit with [
    known jumpdest d0, known dup6 d1, known add d2, known add d3]
  rw [hsrcAdd₁, hsrcAdd₂] at rd2941raw
  have rd2942 := RDx.mloadWithin rd2941raw d4 hsrcAccess (by evm_ov)
  have rd2951raw := evm_run rd2942 with [
    known push1 d5 ⟨32⟩, known dup3 d6, known push1 d7 ⟨5⟩,
    known shl d8, known dup10 d9, known add d10, known add d11]
  rw [hshl, hdstAdd₁, hdstAdd₂] at rd2951raw
  have hmstoreCostZero :
      Cₘ (UInt256.ofNat
          (MachineState.M (wideMultiLimbOddPostAllocatorAw ctx).toNat
            (UInt256.ofNat dst).toNat 32)) -
        Cₘ (wideMultiLimbOddPostAllocatorAw ctx) = 0 := by
    rw [machineM_eq_of_access hdstAccess, u256_ofNat_toNat]
    omega
  have rd2952 := RDx.mstore 0 (wideMultiLimbOddSecondCopyStoredMemory ctx)
      (wideMultiLimbOddPostAllocatorAw ctx) rd2951raw d12
    (by
      intro s hsaw hstk
      exact mstoreCost_of_stack hsaw hstk hmstoreCostZero)
    (by
      rw [UInt256.toNat_ofNat_of_lt hdstWord]
      rfl)
    (by
      rw [machineM_eq_of_access hdstAccess, u256_ofNat_toNat])
    (by evm_ov)
  have rd2857raw := evm_run rd2952 with [
    known add d13, known push2 d14 ⟨2857⟩,
    known jump d15 jumpDest_2857_montgomery]
  rw [hadd] at rd2857raw
  simpa [I, l, words, resultPtr, fp, srcOff, src, dstMid, dst,
    wideMultiLimbOddSecondCopyStoreStack, wideMultiLimbOddSecondCopyLoopBackStack,
    wideMultiLimbOddSecondCopyStoredMemory, wideMultiLimbOddSecondCopyLoadedWord,
    wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinputCopy (by simpa [I, l] using hmore) (k + 16) (by
      simpa [I, l, words, resultPtr, fp, srcOff, src, dstMid, dst,
        wideMultiLimbOddSecondCopyLoopBackStack, wideMultiLimbOddSecondCopyStoredMemory,
        wideMultiLimbOddSecondCopyLoadedWord, wideMultiLimbOddWordArrayPtr,
        wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd2857raw.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddSecondCopyLoopBackSuffixExact_of_guardSuffixes
    (continueGas exitGas : BytecodeContext → Nat)
    (hcontinue : WideMultiLimbOddSecondCopyContinueSuffixExact continueGas)
    (hexit : WideMultiLimbOddSecondCopyExitSuffixExact exitGas) :
    WideMultiLimbOddSecondCopyLoopBackSuffixExact
      (fun ctx =>
        23 + if 2 < (lengths ctx.executionEnv.calldata).modulus / 32 then
          continueGas ctx
        else
          exitGas ctx) := by
  intro ctx hinput hfirstMore k rd2857
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, _hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨_hb, _he, hm⟩
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hqWord : l.modulus / 32 < UInt256.size := by
    apply lt_of_le_of_lt (Nat.div_le_self l.modulus 32)
    exact lt_trans (lt_of_le_of_lt hml (by decide : 1024 < 2 ^ 64)) (by decide)
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryPostAllocatorLoopEntryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨_h0,_h1,_h2,_h3,_h4,_h5,_h6,_h7,_h8,h9,h10,h11,h12,h13,h14⟩
  have rd2857Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2857⟩
      [⟨2⟩, UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyLoopBackStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2857
  have rd2864raw := evm_run rd2857Explicit with [
    known jumpdest h9, known dup2 h10, known dup2 h11,
    known lt h12, known push2 h13 ⟨2906⟩]
  by_cases hmore : 2 < l.modulus / 32
  · have hlt : UInt256.lt (⟨2⟩ : UInt256)
        (UInt256.ofNat (l.modulus / 32)) = ⟨1⟩ := by
      apply ult_one
      rw [show (⟨2⟩ : UInt256).toNat = 2 by decide,
        UInt256.toNat_ofNat_of_lt hqWord]
      exact hmore
    rw [hlt] at rd2864raw
    have rd2906 := rd2864raw.jumpiT h14 (by native_decide)
      jumpDest_2906_montgomery (by evm_ov)
    simpa [I, l, words, resultPtr, fp, hmore,
      wideMultiLimbOddSecondCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hcontinue ctx hinputCopy
        (by simpa [I, l] using hmore) (k + 6) (by
          simpa [I, l, words, resultPtr, fp,
            wideMultiLimbOddSecondCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
            wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            rd2906.withIndices (by omega) (by
              rw [← hgasEqExpanded]
              omega)))
  · have hlt : UInt256.lt (⟨2⟩ : UInt256)
        (UInt256.ofNat (l.modulus / 32)) = ⟨0⟩ := by
      apply ult_zero
      rw [show (⟨2⟩ : UInt256).toNat = 2 by decide,
        UInt256.toNat_ofNat_of_lt hqWord]
      omega
    rw [hlt] at rd2864raw
    have rd2865 := rd2864raw.jumpiNT h14 (by native_decide) (by evm_ov)
    simpa [I, l, words, resultPtr, fp, hmore,
      wideMultiLimbOddSecondCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hexit ctx hinputCopy
        (by simpa [I, l] using hfirstMore)
        (by simpa [I, l] using hmore) (k + 6) (by
          simpa [I, l, words, resultPtr, fp,
            wideMultiLimbOddSecondCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
            wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            rd2865.withIndices (by omega) (by
              rw [← hgasEqExpanded]
              omega)))

theorem wideMultiLimbOddThirdCopyLoopBackSuffixExact_of_guardSuffixes
    (continueGas exitGas : BytecodeContext → Nat)
    (hcontinue : WideMultiLimbOddThirdCopyContinueSuffixExact continueGas)
    (hexit : WideMultiLimbOddThirdCopyExitSuffixExact exitGas) :
    WideMultiLimbOddThirdCopyLoopBackSuffixExact
      (fun ctx =>
        23 + if 3 < (lengths ctx.executionEnv.calldata).modulus / 32 then
          continueGas ctx
        else
          exitGas ctx) := by
  intro ctx hinput hthirdMore k rd2857
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, _hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨_hb, _he, hm⟩
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hqWord : l.modulus / 32 < UInt256.size := by
    apply lt_of_le_of_lt (Nat.div_le_self l.modulus 32)
    exact lt_trans (lt_of_le_of_lt hml (by decide : 1024 < 2 ^ 64)) (by decide)
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryPostAllocatorLoopEntryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨_h0,_h1,_h2,_h3,_h4,_h5,_h6,_h7,_h8,h9,h10,h11,h12,h13,h14⟩
  have rd2857Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2857⟩
      [⟨3⟩, UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddThirdCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyLoopBackStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2857
  have rd2864raw := evm_run rd2857Explicit with [
    known jumpdest h9, known dup2 h10, known dup2 h11,
    known lt h12, known push2 h13 ⟨2906⟩]
  by_cases hmore : 3 < l.modulus / 32
  · have hlt : UInt256.lt (⟨3⟩ : UInt256)
        (UInt256.ofNat (l.modulus / 32)) = ⟨1⟩ := by
      apply ult_one
      rw [show (⟨3⟩ : UInt256).toNat = 3 by decide,
        UInt256.toNat_ofNat_of_lt hqWord]
      exact hmore
    rw [hlt] at rd2864raw
    have rd2906 := rd2864raw.jumpiT h14 (by native_decide)
      jumpDest_2906_montgomery (by evm_ov)
    simpa [I, l, words, resultPtr, fp, hmore,
      wideMultiLimbOddThirdCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hcontinue ctx hinputCopy
        (by simpa [I, l] using hmore) (k + 6) (by
          simpa [I, l, words, resultPtr, fp,
            wideMultiLimbOddThirdCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
            wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            rd2906.withIndices (by omega) (by
              rw [← hgasEqExpanded]
              omega)))
  · have hlt : UInt256.lt (⟨3⟩ : UInt256)
        (UInt256.ofNat (l.modulus / 32)) = ⟨0⟩ := by
      apply ult_zero
      rw [show (⟨3⟩ : UInt256).toNat = 3 by decide,
        UInt256.toNat_ofNat_of_lt hqWord]
      omega
    rw [hlt] at rd2864raw
    have rd2865 := rd2864raw.jumpiNT h14 (by native_decide) (by evm_ov)
    simpa [I, l, words, resultPtr, fp, hmore,
      wideMultiLimbOddThirdCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hexit ctx hinputCopy
        (by simpa [I, l] using hthirdMore)
        (by simpa [I, l] using hmore) (k + 6) (by
          simpa [I, l, words, resultPtr, fp,
            wideMultiLimbOddThirdCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
            wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            rd2865.withIndices (by omega) (by
              rw [← hgasEqExpanded]
              omega)))

theorem wideMultiLimbOddThirdCopyContinueSuffixExact_of_fourthCopyAddSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddFourthCopyAddSuffixExact suffixGas) :
    WideMultiLimbOddThirdCopyContinueSuffixExact (fun ctx => 33 + suffixGas ctx) := by
  intro ctx hinput hmore k rd2906
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have rd2906Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2906⟩
      [⟨3⟩, UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddThirdCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyLoopBackStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2906
  have rd1323 := evm_run rd2906Explicit with [
    known jumpdest h0, known dup1 h1, known push1 h2 ⟨32⟩,
    known push2 h3 ⟨2937⟩, known push2 h4 ⟨2931⟩,
    known push2 h5 ⟨2926⟩, known push1 h6 ⟨1⟩,
    known swap6 h7, known push2 h8 ⟨1323⟩,
    known jump h9 jumpDest_1323_montgomery]
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyLoopBackStack,
    wideMultiLimbOddFourthCopyAddStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (by simpa [I, l] using hmore) (k + 10) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFourthCopyAddStack,
        wideMultiLimbOddThirdCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
        wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1323.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddFourthCopyAddSuffixExact_of_returnSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddFourthCopyAddReturnSuffixExact suffixGas) :
    WideMultiLimbOddFourthCopyAddSuffixExact (fun ctx => 43 + suffixGas ctx) := by
  intro ctx hinput hmore k rd1323
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyAddDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  have rd1323Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1323⟩
      [⟨3⟩, ⟨2926⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨3⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddThirdCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23 + 33) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFourthCopyAddStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd1323
  have hadd : (⟨3⟩ : UInt256) + ⟨1⟩ = ⟨4⟩ := by native_decide
  have hgt : UInt256.gt (⟨3⟩ : UInt256) ((⟨3⟩ : UInt256) + ⟨1⟩) = ⟨0⟩ := by
    rw [hadd]
    native_decide
  have rd1336raw := evm_run rd1323Explicit with [
    known jumpdest h0, known swap1 h1, known push1 h2 ⟨1⟩,
    known dup3 h3, known add h4, known dup1 h5, known swap3 h6,
    known gt h7, known push2 h8 ⟨1037⟩, known jumpiNT h9 hgt,
    known jump h10 jumpDest_2926_montgomery]
  rw [hadd] at rd1336raw
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFourthCopyAddStack,
    wideMultiLimbOddFourthCopyAddReturnStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (by simpa [I, l] using hmore) (k + 11) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFourthCopyAddReturnStack,
        wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1336raw.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddFourthCopyAddReturnSuffixExact_of_readSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddFourthCopyReadSuffixExact suffixGas) :
    WideMultiLimbOddFourthCopyAddReturnSuffixExact (fun ctx => 12 + suffixGas ctx) := by
  intro ctx hinput hmore k rd2926
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyReadCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rd2926Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2926⟩
      [⟨4⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨3⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddThirdCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124 + 51 + 23 + 33 + 43) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFourthCopyAddReturnStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2926
  have rd1903 := evm_run rd2926Explicit with [
    known jumpdest h0, known push2 h1 ⟨1903⟩,
    known jump h2 jumpDest_1903_montgomery]
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFourthCopyAddReturnStack,
    wideMultiLimbOddFourthCopyReadStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (by simpa [I, l] using hmore) (k + 3) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddFourthCopyReadStack,
        wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1903.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddSecondCopyContinueSuffixExact_of_thirdCopyAddSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddThirdCopyAddSuffixExact suffixGas) :
    WideMultiLimbOddSecondCopyContinueSuffixExact (fun ctx => 33 + suffixGas ctx) := by
  intro ctx hinput hmore k rd2906
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have rd2906Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2906⟩
      [⟨2⟩, UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyLoopBackStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2906
  have rd1323 := evm_run rd2906Explicit with [
    known jumpdest h0, known dup1 h1, known push1 h2 ⟨32⟩,
    known push2 h3 ⟨2937⟩, known push2 h4 ⟨2931⟩,
    known push2 h5 ⟨2926⟩, known push1 h6 ⟨1⟩,
    known swap6 h7, known push2 h8 ⟨1323⟩,
    known jump h9 jumpDest_1323_montgomery]
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddSecondCopyLoopBackStack,
    wideMultiLimbOddThirdCopyAddStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (by simpa [I, l] using hmore) (k + 10) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyAddStack,
        wideMultiLimbOddSecondCopyLoopBackStack, wideMultiLimbOddWordArrayPtr,
        wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1323.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddThirdCopyAddSuffixExact_of_returnSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddThirdCopyAddReturnSuffixExact suffixGas) :
    WideMultiLimbOddThirdCopyAddSuffixExact (fun ctx => 43 + suffixGas ctx) := by
  intro ctx hinput hmore k rd1323
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyAddDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  have rd1323Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1323⟩
      [⟨2⟩, ⟨2926⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨2⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyAddStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd1323
  have hadd : (⟨2⟩ : UInt256) + ⟨1⟩ = ⟨3⟩ := by native_decide
  have hgt : UInt256.gt (⟨2⟩ : UInt256) ((⟨2⟩ : UInt256) + ⟨1⟩) = ⟨0⟩ := by
    rw [hadd]
    native_decide
  have rd1336raw := evm_run rd1323Explicit with [
    known jumpdest h0, known swap1 h1, known push1 h2 ⟨1⟩,
    known dup3 h3, known add h4, known dup1 h5, known swap3 h6,
    known gt h7, known push2 h8 ⟨1037⟩, known jumpiNT h9 hgt,
    known jump h10 jumpDest_2926_montgomery]
  rw [hadd] at rd1336raw
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyAddStack,
    wideMultiLimbOddThirdCopyAddReturnStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (by simpa [I, l] using hmore) (k + 11) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyAddReturnStack,
        wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1336raw.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddThirdCopyAddReturnSuffixExact_of_readSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddThirdCopyReadSuffixExact suffixGas) :
    WideMultiLimbOddThirdCopyAddReturnSuffixExact (fun ctx => 12 + suffixGas ctx) := by
  intro ctx hinput hmore k rd2926
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyReadCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rd2926Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2926⟩
      [⟨3⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨2⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyAddReturnStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2926
  have rd1903 := evm_run rd2926Explicit with [
    known jumpdest h0, known push2 h1 ⟨1903⟩,
    known jump h2 jumpDest_1903_montgomery]
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyAddReturnStack,
    wideMultiLimbOddThirdCopyReadStack, wideMultiLimbOddWordArrayPtr,
    wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinput (by simpa [I, l] using hmore) (k + 3) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyReadStack,
        wideMultiLimbOddThirdCopyAddReturnStack, wideMultiLimbOddWordArrayPtr,
        wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd1903.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddThirdCopyReadSuffixExact_of_storeSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddThirdCopyStoreSuffixExact suffixGas) :
    WideMultiLimbOddThirdCopyReadSuffixExact (fun ctx => 124 + suffixGas ctx) := by
  intro ctx hinput hmore k rd1903
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, _hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨_hb, _he, hm⟩
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hmoreL : 2 < l.modulus / 32 := by simpa [I, l] using hmore
  have hge96 : 96 ≤ l.modulus := by
    have hle : 3 ≤ l.modulus / 32 := by omega
    have hmul : 3 * 32 ≤ (l.modulus / 32) * 32 :=
      Nat.mul_le_mul_right 32 hle
    have hdivmul : (l.modulus / 32) * 32 ≤ l.modulus :=
      Nat.div_mul_le_self l.modulus 32
    omega
  have hmodWord : l.modulus < UInt256.size :=
    lt_of_le_of_lt hml (by decide : 1024 < UInt256.size)
  have hremWord : l.modulus - 96 < UInt256.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) hmodWord
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hdRead := montgomeryFirstCopyReadGuardDecodes
  simp only [List.cons.injEq, and_true] at hdRead
  rcases hdRead with
    ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17⟩
  have rd1903Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨1903⟩
      [⟨3⟩, ⟨2931⟩, ⟨2937⟩, ⟨32⟩, ⟨2⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyReadStack,
      wideMultiLimbOddThirdCopyAddReturnStack, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      rd1903
  have hshl : UInt256.shiftLeft (⟨3⟩ : UInt256) ⟨5⟩ = ⟨96⟩ := by native_decide
  have hdiv : UInt256.div (⟨96⟩ : UInt256) ⟨3⟩ = ⟨32⟩ := by native_decide
  have heq : UInt256.eq (⟨32⟩ : UInt256) ⟨32⟩ = ⟨1⟩ := by native_decide
  have hiszero3 : UInt256.isZero (⟨3⟩ : UInt256) = ⟨0⟩ := by native_decide
  have hiszero1 : UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ := by native_decide
  have hor : UInt256.lor (⟨0⟩ : UInt256) ⟨1⟩ = ⟨1⟩ := by native_decide
  have rd1909 := evm_run rd1903Explicit with [
    known jumpdest r0, known swap1 r1, known dup2 r2,
    known push1 r3 ⟨5⟩, known shl r4]
  rw [hshl] at rd1909
  have rd1916 := evm_run rd1909 with [
    known swap2 r5, known dup1 r6, known dup4 r7,
    known div r8, known push1 r9 ⟨32⟩, known eq r10]
  rw [hdiv, heq] at rd1916
  have rd1923 := evm_run rd1916 with [
    known swap1 r11, known iszero r12, known or r13,
    known iszero r14, known push2 r15 ⟨1037⟩]
  rw [hiszero3, hor, hiszero1] at rd1923
  have rd1924 := rd1923.jumpiNT r16 (by native_decide) (by evm_ov)
  have rd2931 := rd1924.jump r17 jumpDest_2931_montgomery (by evm_ov)
  have hdSubCall := montgomeryFirstCopySubCallDecodes
  simp only [List.cons.injEq, and_true] at hdSubCall
  rcases hdSubCall with ⟨c0,c1,c2,c3⟩
  have rd1103 := evm_run rd2931 with [
    known jumpdest c0, known dup8 c1, known push2 c2 ⟨1103⟩,
    known jump c3 jumpDest_1103_montgomery]
  have hdSub := montgomeryFirstCopySubDecodes
  simp only [List.cons.injEq, and_true] at hdSub
  rcases hdSub with ⟨s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10⟩
  have hsub : UInt256.sub (UInt256.ofNat l.modulus) ⟨96⟩ =
      UInt256.ofNat (l.modulus - 96) := by
    apply u256_inj
    rw [usub_toNat]
    · rw [UInt256.toNat_ofNat_of_lt hmodWord,
        show (⟨96⟩ : UInt256).toNat = 96 by decide,
        UInt256.toNat_ofNat_of_lt hremWord]
    · rw [UInt256.toNat_ofNat_of_lt hmodWord,
        show (⟨96⟩ : UInt256).toNat = 96 by decide]
      omega
  have hgt : UInt256.gt (UInt256.ofNat (l.modulus - 96))
      (UInt256.ofNat l.modulus) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hremWord, UInt256.toNat_ofNat_of_lt hmodWord]
    omega
  have rd1114raw := evm_run rd1103 with [
    known jumpdest s0, known swap2 s1, known swap1 s2, known dup3 s3,
    known sub s4, known swap2 s5, known dup3 s6, known gt s7,
    known push2 s8 ⟨1037⟩]
  rw [hsub, hgt] at rd1114raw
  have rd1115 := rd1114raw.jumpiNT s9 (by native_decide) (by evm_ov)
  have rd2937 := rd1115.jump s10 jumpDest_2937_montgomery (by evm_ov)
  simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyReadStack,
    wideMultiLimbOddThirdCopyAddReturnStack, wideMultiLimbOddThirdCopyStoreStack,
    wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinputCopy (by simpa [I, l] using hmore) (k + 33) (by
      simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyStoreStack,
        wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd2937.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddThirdCopyStoreSuffixExact_of_loopBackSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddThirdCopyLoopBackSuffixExact suffixGas) :
    WideMultiLimbOddThirdCopyStoreSuffixExact (fun ctx => 51 + suffixGas ctx) := by
  intro ctx hinput hmore k rd2937
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let words := (l.modulus + 31) / 32
  let resultPtr := operandFreePtr l.base l.exponent l.modulus
  let fp := resultPtr + bytesAllocationSize l.modulus
  let srcOff := l.modulus - 96
  let src := operandModulusPtr l.base l.exponent + srcOff + 32
  let dstMid := fp + 64
  let dst := fp + 96
  have hinputCopy := hinput
  rcases hinput with ⟨hbranch, _hmodGtOne⟩
  rcases hbranch with ⟨hmulti, _hodd⟩
  rcases hmulti with ⟨hwide, _hmodLarge⟩
  rcases hwide with ⟨haccepts, _hcalldata, _hnotWord, _hexp, _hbase⟩
  rcases haccepts with ⟨_hvalue, hvalid⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  have hbl : l.base ≤ 1024 := by simpa [I, l] using hb
  have hel : l.exponent ≤ 1024 := by simpa [I, l] using he
  have hml : l.modulus ≤ 1024 := by simpa [I, l] using hm
  have hmoreL : 2 < l.modulus / 32 := by simpa [I, l] using hmore
  have hge96 : 96 ≤ l.modulus := by
    have hle : 3 ≤ l.modulus / 32 := by omega
    have hmul : 3 * 32 ≤ (l.modulus / 32) * 32 :=
      Nat.mul_le_mul_right 32 hle
    have hdivmul : (l.modulus / 32) * 32 ≤ l.modulus :=
      Nat.div_mul_le_self l.modulus 32
    omega
  have hsrcWord : src < UInt256.size := by
    apply lt_of_le_of_lt
      (show src ≤ 3296 by
        dsimp [src, srcOff]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hdstWord : dst < UInt256.size := by
    apply lt_of_le_of_lt
      (show dst ≤ 5504 by
        dsimp [dst, fp, resultPtr]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hmptrRemWord :
      operandModulusPtr l.base l.exponent + srcOff < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusPtr l.base l.exponent + srcOff ≤ 3264 by
        dsimp [srcOff]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hsrcAdd₁ :
      UInt256.ofNat (operandModulusPtr l.base l.exponent) +
          UInt256.ofNat srcOff =
        UInt256.ofNat (operandModulusPtr l.base l.exponent + srcOff) := by
    exact ofNat_add_bounded hmptrRemWord
  have hsrcAdd₂ :
      UInt256.ofNat (operandModulusPtr l.base l.exponent + srcOff) +
          (⟨32⟩ : UInt256) =
        UInt256.ofNat src := by
    change UInt256.ofNat (operandModulusPtr l.base l.exponent + srcOff) +
        UInt256.ofNat 32 = UInt256.ofNat src
    rw [ofNat_add_bounded (by simpa [src] using hsrcWord)]
  have hfpWord : fp < UInt256.size := by
    apply lt_of_le_of_lt
      (show fp ≤ 5408 by
        dsimp [fp, resultPtr]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hdstMidWord : dstMid < UInt256.size := by
    apply lt_of_le_of_lt
      (show dstMid ≤ 5472 by
        dsimp [dstMid, fp, resultPtr]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hdstAdd₁ : UInt256.ofNat fp + (⟨64⟩ : UInt256) = UInt256.ofNat dstMid := by
    change UInt256.ofNat fp + UInt256.ofNat 64 = UInt256.ofNat dstMid
    rw [ofNat_add_bounded (by simpa [dstMid] using hdstMidWord)]
  have hdstAdd₂ : UInt256.ofNat dstMid + (⟨32⟩ : UInt256) = UInt256.ofNat dst := by
    change UInt256.ofNat dstMid + UInt256.ofNat 32 = UInt256.ofNat dst
    rw [ofNat_add_bounded (by simpa [dstMid, dst, Nat.add_assoc] using hdstWord)]
  have hadd : (⟨2⟩ : UInt256) + ⟨1⟩ = ⟨3⟩ := by native_decide
  have hshl : UInt256.shiftLeft (⟨2⟩ : UInt256) ⟨5⟩ = ⟨64⟩ := by native_decide
  have hawOld : (wideMultiLimbPostAllocationAw ctx).toNat ≤ 136 := by
    dsimp [wideMultiLimbPostAllocationAw]
    rw [wideWordResultWords_toNat hbl hel hml]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have hfpBound : fp ≤ 4352 := by
    dsimp [fp, resultPtr]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hn : words ≤ 32 := by
    dsimp [words]
    omega
  have hnpos : 0 < words := by
    dsimp [words]
    exact Nat.div_pos (by omega : 32 ≤ l.modulus + 31) (by decide : 0 < 32)
  have hpostAwNat :
      (wideMultiLimbOddPostAllocatorAw ctx).toNat =
        MachineState.M
          (MachineState.M (wideMultiLimbPostAllocationAw ctx).toNat fp 32)
          (fp + 32) (wordArrayPayloadSize words) := by
    simpa [I, l, fp, words, wideMultiLimbOddPostAllocatorAw,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength] using
      (newWordArrayWords_toNat_small (aw := wideMultiLimbPostAllocationAw ctx)
        (fp := fp) (n := words) hawOld hfpBound hn hnpos)
  have hpayloadPos : 0 < wordArrayPayloadSize words := by
    unfold wordArrayPayloadSize
    omega
  have hcover := machineM_covers_access
    (MachineState.M (wideMultiLimbPostAllocationAw ctx).toNat fp 32)
    (fp + 32) (wordArrayPayloadSize words) hpayloadPos
  have hsrcAccess : (UInt256.ofNat src).toNat + 32 ≤
      32 * (wideMultiLimbOddPostAllocatorAw ctx).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hsrcWord, hpostAwNat]
    apply le_trans _ hcover
    dsimp [src, srcOff, fp, resultPtr]
    unfold operandFreePtr bytesAllocationSize wordArrayPayloadSize
    have hround := bytesSize_le_roundedPayload l.modulus
    omega
  have hdstAccess : (UInt256.ofNat dst).toNat + 32 ≤
      32 * (wideMultiLimbOddPostAllocatorAw ctx).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hdstWord, hpostAwNat]
    apply le_trans _ hcover
    dsimp [dst]
    unfold wordArrayPayloadSize
    omega
  have hgasEqExpanded :
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (wideMultiLimbOddWordArrayPtr ctx)
          (wideMultiLimbOddWordArrayLength ctx) =
        newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
          (bytesAllocationSize (lengths ctx.executionEnv.calldata).modulus +
            operandFreePtr (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent
              (lengths ctx.executionEnv.calldata).modulus)
          (((lengths ctx.executionEnv.calldata).modulus + 31) / 32) := by
    simp [I, l, fp, resultPtr, words, wideMultiLimbOddWordArrayPtr,
      wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hd := montgomeryFirstCopyStoreDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with
    ⟨d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15⟩
  have rd2937Explicit : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState ⟨2937⟩
      [UInt256.ofNat (l.modulus - 96), ⟨32⟩, ⟨2⟩, ⟨1⟩,
        UInt256.ofNat (l.modulus / 32),
        UInt256.ofNat (operandModulusPtr l.base l.exponent),
        UInt256.ofNat l.modulus, ⟨2006⟩, UInt256.ofNat fp,
        UInt256.ofNat operandBasePtr, UInt256.ofNat words,
        UInt256.ofNat (operandExponentPtr l.base), UInt256.ofNat resultPtr,
        UInt256.ofNat l.modulus, ⟨805⟩, ⟨1271⟩, UInt256.ofNat resultPtr, ⟨173⟩]
      (wideMultiLimbOddSecondCopyStoredMemory ctx) (wideMultiLimbOddPostAllocatorAw ctx)
      ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
        wideMultiLimbOddAllocationGas ctx + wideMultiLimbChecksGas ctx + 107 + 38 + 24 +
          newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
            (wideMultiLimbOddWordArrayPtr ctx)
            (wideMultiLimbOddWordArrayLength ctx) + 47 + 33 + 43 + 12 + 124 + 51 + 23 + 33 +
          43 + 12 + 124 + 51 + 23 + 33 + 43 + 12 + 124) := by
    simpa [I, l, words, resultPtr, fp, wideMultiLimbOddThirdCopyStoreStack,
      wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd2937
  have rd2941raw := evm_run rd2937Explicit with [
    known jumpdest d0, known dup6 d1, known add d2, known add d3]
  rw [hsrcAdd₁, hsrcAdd₂] at rd2941raw
  have rd2942 := RDx.mloadWithin rd2941raw d4 hsrcAccess (by evm_ov)
  have rd2951raw := evm_run rd2942 with [
    known push1 d5 ⟨32⟩, known dup3 d6, known push1 d7 ⟨5⟩,
    known shl d8, known dup10 d9, known add d10, known add d11]
  rw [hshl, hdstAdd₁, hdstAdd₂] at rd2951raw
  have hmstoreCostZero :
      Cₘ (UInt256.ofNat
          (MachineState.M (wideMultiLimbOddPostAllocatorAw ctx).toNat
            (UInt256.ofNat dst).toNat 32)) -
        Cₘ (wideMultiLimbOddPostAllocatorAw ctx) = 0 := by
    rw [machineM_eq_of_access hdstAccess, u256_ofNat_toNat]
    omega
  have rd2952 := RDx.mstore 0 (wideMultiLimbOddThirdCopyStoredMemory ctx)
      (wideMultiLimbOddPostAllocatorAw ctx) rd2951raw d12
    (by
      intro s hsaw hstk
      exact mstoreCost_of_stack hsaw hstk hmstoreCostZero)
    (by
      rw [UInt256.toNat_ofNat_of_lt hdstWord]
      rfl)
    (by
      rw [machineM_eq_of_access hdstAccess, u256_ofNat_toNat])
    (by evm_ov)
  have rd2857raw := evm_run rd2952 with [
    known add d13, known push2 d14 ⟨2857⟩,
    known jump d15 jumpDest_2857_montgomery]
  rw [hadd] at rd2857raw
  simpa [I, l, words, resultPtr, fp, srcOff, src, dstMid, dst,
    wideMultiLimbOddThirdCopyStoreStack, wideMultiLimbOddThirdCopyLoopBackStack,
    wideMultiLimbOddThirdCopyStoredMemory, wideMultiLimbOddThirdCopyLoadedWord,
    wideMultiLimbOddWordArrayPtr, wideMultiLimbOddWordArrayLength,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hsuffix ctx hinputCopy (by simpa [I, l] using hmore) (k + 16) (by
      simpa [I, l, words, resultPtr, fp, srcOff, src, dstMid, dst,
        wideMultiLimbOddThirdCopyLoopBackStack, wideMultiLimbOddThirdCopyStoredMemory,
        wideMultiLimbOddThirdCopyLoadedWord, wideMultiLimbOddWordArrayPtr,
        wideMultiLimbOddWordArrayLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rd2857raw.withIndices (by omega) (by
          rw [← hgasEqExpanded]
          omega)))

theorem wideMultiLimbOddBytecodeSpec_of_backendSuffix
    (backendGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddBackendSuffixExact backendGas) :
    BytecodeSpec runtimeBytecode
      wideMultiLimbOddMontgomeryInputs (wideMultiLimbOddEnsures backendGas) := by
  simpa [wideMultiLimbOddEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideMultiLimbOddMontgomeryInputs)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx =>
        wideMultiLimbOddDispatcherTotalGas ctx.executionEnv + backendGas ctx)
      (fun ctx hcode hinput => by
        obtain ⟨k, rd⟩ := wideMultiLimbOddDispatcherPrefixExact
          (ctx := ctx) hcode hinput
        exact hsuffix ctx hinput k (by
          simpa [wideMultiLimbBackendStack, wideMultiLimbBackendMemory,
            wideMultiLimbBackendAw] using rd)))

theorem wideMultiLimbEvenBytecodeSpec_of_backendSuffix
    (backendGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbEvenBackendSuffixExact backendGas) :
    BytecodeSpec runtimeBytecode
      wideMultiLimbEvenBarrettInputs (wideMultiLimbEvenEnsures backendGas) := by
  simpa [wideMultiLimbEvenEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideMultiLimbEvenBarrettInputs)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx =>
        wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv + backendGas ctx)
      (fun ctx hcode hinput => by
        obtain ⟨k, rd⟩ := wideMultiLimbEvenDispatcherPrefixExact
          (ctx := ctx) hcode hinput
        exact hsuffix ctx hinput k (by
          simpa [wideMultiLimbBackendStack, wideMultiLimbBackendMemory,
            wideMultiLimbBackendAw] using rd)))

theorem wideMultiLimbOddBytecodeSpec_of_postAllocationSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddPostAllocationSuffixExact suffixGas) :
    BytecodeSpec runtimeBytecode
      wideMultiLimbOddMontgomeryInputs
      (wideMultiLimbOddEnsures
        (fun ctx => wideMultiLimbOddAllocationGas ctx + suffixGas ctx)) := by
  simpa [wideMultiLimbOddEnsures, Nat.add_assoc] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideMultiLimbOddMontgomeryInputs)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx =>
        wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
          (wideMultiLimbOddAllocationGas ctx + suffixGas ctx))
      (fun ctx hcode hinput => by
        obtain ⟨k, rd⟩ := wideMultiLimbOddAllocationPrefixExact
          (ctx := ctx) hcode hinput
        simpa [Nat.add_assoc] using (hsuffix ctx hinput k (by
          simpa [wideMultiLimbOddPostAllocationStack,
            wideMultiLimbPostAllocationMemory, wideMultiLimbPostAllocationAw] using rd))))

theorem wideMultiLimbEvenBytecodeSpec_of_postAllocationSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbEvenPostAllocationSuffixExact suffixGas) :
    BytecodeSpec runtimeBytecode
      wideMultiLimbEvenBarrettInputs
      (wideMultiLimbEvenEnsures
        (fun ctx => wideMultiLimbEvenAllocationGas ctx + suffixGas ctx)) := by
  simpa [wideMultiLimbEvenEnsures, Nat.add_assoc] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideMultiLimbEvenBarrettInputs)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx =>
        wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
          (wideMultiLimbEvenAllocationGas ctx + suffixGas ctx))
      (fun ctx hcode hinput => by
        obtain ⟨k, rd⟩ := wideMultiLimbEvenAllocationPrefixExact
          (ctx := ctx) hcode hinput
        simpa [Nat.add_assoc] using (hsuffix ctx hinput k (by
          simpa [wideMultiLimbEvenPostAllocationStack,
            wideMultiLimbPostAllocationMemory, wideMultiLimbPostAllocationAw] using rd))))

theorem wideMultiLimbOddBytecodeSpec_of_postChecksSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbOddPostChecksSuffixExact suffixGas) :
    BytecodeSpec runtimeBytecode
      wideMultiLimbOddNontrivialInputs
      (wideMultiLimbOddEnsures
        (fun ctx => wideMultiLimbOddAllocationGas ctx +
          wideMultiLimbChecksGas ctx + suffixGas ctx)) := by
  simpa [wideMultiLimbOddEnsures, Nat.add_assoc] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideMultiLimbOddNontrivialInputs)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx =>
        wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
          (wideMultiLimbOddAllocationGas ctx +
            wideMultiLimbChecksGas ctx + suffixGas ctx))
      (fun ctx hcode hinput => by
        obtain ⟨k, rd⟩ := wideMultiLimbOddPostChecksPrefixExact
          (ctx := ctx) hcode hinput
        simpa [Nat.add_assoc] using (hsuffix ctx hinput k (by
          simpa [wideMultiLimbOddPostChecksStack, wideMultiLimbPostAllocationMemory,
            wideMultiLimbPostAllocationAw] using rd))))

theorem wideMultiLimbEvenBytecodeSpec_of_postChecksSuffix
    (suffixGas : BytecodeContext → Nat)
    (hsuffix : WideMultiLimbEvenPostChecksSuffixExact suffixGas) :
    BytecodeSpec runtimeBytecode
      wideMultiLimbEvenNontrivialInputs
      (wideMultiLimbEvenEnsures
        (fun ctx => wideMultiLimbEvenAllocationGas ctx +
          wideMultiLimbChecksGas ctx + suffixGas ctx)) := by
  simpa [wideMultiLimbEvenEnsures, Nat.add_assoc] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideMultiLimbEvenNontrivialInputs)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx =>
        wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
          (wideMultiLimbEvenAllocationGas ctx +
            wideMultiLimbChecksGas ctx + suffixGas ctx))
      (fun ctx hcode hinput => by
        obtain ⟨k, rd⟩ := wideMultiLimbEvenPostChecksPrefixExact
          (ctx := ctx) hcode hinput
        simpa [Nat.add_assoc] using (hsuffix ctx hinput k (by
          simpa [wideMultiLimbEvenPostChecksStack, wideMultiLimbPostAllocationMemory,
            wideMultiLimbPostAllocationAw] using rd))))

theorem wideMultiLimbLeOneExactGasSpec :
    BytecodeSpec runtimeBytecode wideMultiLimbLeOneInputs
      (fun ctx result => ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
        (wideMultiLimbLeOneTotalGas ctx) result) := by
  simpa using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideMultiLimbLeOneInputs)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := wideMultiLimbLeOneTotalGas)
      (fun ctx hcode hinput => by
        let I := ctx.executionEnv
        let l := lengths I.calldata
        rcases hinput with ⟨hmulti, hmodLe⟩
        rcases hmulti with ⟨hwide, hmodLarge⟩
        rcases hwide with ⟨haccepts, hcalldata, hnotWord, hexp, hbase⟩
        rcases haccepts with ⟨hvalue, hvalid⟩
        have hv := hvalid
        unfold validOsaka at hv
        change (lengths I.calldata).base ≤ 1024 ∧
            (lengths I.calldata).exponent ≤ 1024 ∧
            (lengths I.calldata).modulus ≤ 1024 at hv
        rcases hv with ⟨hb, he, hm⟩
        have hmodPos : 0 < l.modulus := by
          have : 0 < (lengths ctx.executionEnv.calldata).modulus := by omega
          simpa [I, l] using this
        obtain ⟨kEntry, rd62⟩ := reachWideEntry
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (g := ctx.gas) hcode hvalue hvalid hnotWord
        have hret := wideSmallModulusValueFromEntryModelExact
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := I) (g := ctx.gas)
          (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
          (acc := (ctx.createdAccounts, ctx.accountMap))
          hb he hmodPos hm
          (by simpa [I, l, wideExponentOffset] using hexp)
          (by simpa [I, l] using hbase)
          (by simpa [I, l, wideModulusNat] using hmodLe)
          hcalldata rd62
        have hout := model_output_eq_zero_of_small_modulus I l.base l.exponent l.modulus
          (by rfl : Model.bytesToNatPadded I.calldata 0 32 = l.base)
          (by rfl : Model.bytesToNatPadded I.calldata 32 32 = l.exponent)
          (by rfl : Model.bytesToNatPadded I.calldata 64 32 = l.modulus)
          (by simpa [I, l, wideModulusNat] using hmodLe)
        change RDxRet runtimeBytecode ctx.gas ctx.initialState
          (ctx.createdAccounts, ctx.accountMap)
          (Model.output ctx.executionEnv.calldata) (wideMultiLimbLeOneTotalGas ctx)
        rw [hout]
        simpa [I, l, wideMultiLimbLeOneTotalGas, wideSmallModulusValueTotalGas]
          using hret))

theorem wideMultiLimbLeOneBytecodeSpec :
    BytecodeSpec runtimeBytecode wideMultiLimbLeOneInputs modexpSomeExactGasEnsures :=
  BytecodeSpec.mono wideMultiLimbLeOneExactGasSpec
    (by
      intro ctx result _hinput hpost
      exact ⟨wideMultiLimbLeOneTotalGas ctx, hpost⟩)

/-- Full ModExp spec from exact suffix proofs for the two remaining multi-limb backends.  This is
the final assembly interface for the current proof architecture. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbBackendSuffix
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddBackendGas evenBackendGas : BytecodeContext → Nat)
    (hoddSuffix : WideMultiLimbOddBackendSuffixExact oddBackendGas)
    (hevenSuffix : WideMultiLimbEvenBackendSuffixExact evenBackendGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  constructor
  intro ctx hcode haccepts
  by_cases hword : wordSized ctx.executionEnv.calldata
  · have hcovered := wordSized_coveredAccepts haccepts hword
    exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
  · have hcalldata := hbounded ctx haccepts
    by_cases hfast : wideFastCondition ctx.executionEnv.calldata
    · have hcovered := wideFast_coveredAccepts haccepts hcalldata hword hfast
      exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
    · have hwide : wideNontrivialInputs ctx := by
        refine ⟨haccepts, hcalldata, hword, ?_, ?_⟩
        · intro hexp
          exact hfast (Or.inl (by
            simpa [wideExponentOffset] using hexp))
        · by_contra hbaseNot
          have hbaseLe :
              Model.bytesToNatPadded ctx.executionEnv.calldata 96
                (lengths ctx.executionEnv.calldata).base ≤ 1 := by
            omega
          exact hfast (Or.inr hbaseLe)
      by_cases hzero : wideZeroModulusLengthCondition ctx.executionEnv
      · have hcovered := wideZeroModulusLength_coveredAccepts haccepts hcalldata hword hzero
        exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
      · by_cases hsmall : wideSmallModulusValueCondition ctx.executionEnv
        · have hcovered := wideSmallModulusValue_coveredAccepts haccepts hcalldata hword hsmall
          exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
        · by_cases hone : wideOneWordBackendInputs ctx
          · have hcovered := wideOneWordBackend_coveredAccepts hone
            exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
          · have hmulti : wideMultiLimbBackendInputs ctx :=
              wideNontrivial_not_oneWord_notSmall_split hwide hone hzero hsmall
            rcases wideMultiLimbBackendInputs_split hmulti with hevenCase | hoddCase
            · have hspec := wideMultiLimbEvenBytecodeSpec_of_backendSuffix
                evenBackendGas hevenSuffix
              have hpost := hspec.run ctx hcode hevenCase
              exact ⟨wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
                evenBackendGas ctx, hpost⟩
            · have hspec := wideMultiLimbOddBytecodeSpec_of_backendSuffix
                oddBackendGas hoddSuffix
              have hpost := hspec.run ctx hcode hoddCase
              exact ⟨wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
                oddBackendGas ctx, hpost⟩

/-- Full ModExp spec from exact suffix proofs that start after the shared multi-limb result
allocation blocks.  Compared with `modexpSomeExactGasSpec_of_bounded_multiLimbBackendSuffix`, this
pushes the remaining proof obligation from PC 1925/1549 to PC 1946/1570 and includes the exact
allocation gas in the assembled gas expression. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbPostAllocationSuffix
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddSuffixGas evenSuffixGas : BytecodeContext → Nat)
    (hoddSuffix : WideMultiLimbOddPostAllocationSuffixExact oddSuffixGas)
    (hevenSuffix : WideMultiLimbEvenPostAllocationSuffixExact evenSuffixGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  constructor
  intro ctx hcode haccepts
  by_cases hword : wordSized ctx.executionEnv.calldata
  · have hcovered := wordSized_coveredAccepts haccepts hword
    exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
  · have hcalldata := hbounded ctx haccepts
    by_cases hfast : wideFastCondition ctx.executionEnv.calldata
    · have hcovered := wideFast_coveredAccepts haccepts hcalldata hword hfast
      exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
    · have hwide : wideNontrivialInputs ctx := by
        refine ⟨haccepts, hcalldata, hword, ?_, ?_⟩
        · intro hexp
          exact hfast (Or.inl (by
            simpa [wideExponentOffset] using hexp))
        · by_contra hbaseNot
          have hbaseLe :
              Model.bytesToNatPadded ctx.executionEnv.calldata 96
                (lengths ctx.executionEnv.calldata).base ≤ 1 := by
            omega
          exact hfast (Or.inr hbaseLe)
      by_cases hzero : wideZeroModulusLengthCondition ctx.executionEnv
      · have hcovered := wideZeroModulusLength_coveredAccepts haccepts hcalldata hword hzero
        exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
      · by_cases hsmall : wideSmallModulusValueCondition ctx.executionEnv
        · have hcovered := wideSmallModulusValue_coveredAccepts haccepts hcalldata hword hsmall
          exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
        · by_cases hone : wideOneWordBackendInputs ctx
          · have hcovered := wideOneWordBackend_coveredAccepts hone
            exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
          · have hmulti : wideMultiLimbBackendInputs ctx :=
              wideNontrivial_not_oneWord_notSmall_split hwide hone hzero hsmall
            rcases wideMultiLimbBackendInputs_split hmulti with hevenCase | hoddCase
            · have hspec := wideMultiLimbEvenBytecodeSpec_of_postAllocationSuffix
                evenSuffixGas hevenSuffix
              have hpost := hspec.run ctx hcode hevenCase
              exact ⟨wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
                (wideMultiLimbEvenAllocationGas ctx + evenSuffixGas ctx), hpost⟩
            · have hspec := wideMultiLimbOddBytecodeSpec_of_postAllocationSuffix
                oddSuffixGas hoddSuffix
              have hpost := hspec.run ctx hcode hoddCase
              exact ⟨wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
                (wideMultiLimbOddAllocationGas ctx + oddSuffixGas ctx), hpost⟩

/-- Full ModExp spec from exact suffix proofs that start after the multi-limb allocation and
nontrivial-modulus checks.  Multi-limb declared modulus lengths that decode to value zero or one
are discharged by `wideMultiLimbLeOneBytecodeSpec`; the only remaining assumptions are the two
true backend suffixes after the checks have established `modulus > 1`. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbPostChecksSuffix
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddSuffixGas evenSuffixGas : BytecodeContext → Nat)
    (hoddSuffix : WideMultiLimbOddPostChecksSuffixExact oddSuffixGas)
    (hevenSuffix : WideMultiLimbEvenPostChecksSuffixExact evenSuffixGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  constructor
  intro ctx hcode haccepts
  by_cases hword : wordSized ctx.executionEnv.calldata
  · have hcovered := wordSized_coveredAccepts haccepts hword
    exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
  · have hcalldata := hbounded ctx haccepts
    by_cases hfast : wideFastCondition ctx.executionEnv.calldata
    · have hcovered := wideFast_coveredAccepts haccepts hcalldata hword hfast
      exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
    · have hwide : wideNontrivialInputs ctx := by
        refine ⟨haccepts, hcalldata, hword, ?_, ?_⟩
        · intro hexp
          exact hfast (Or.inl (by
            simpa [wideExponentOffset] using hexp))
        · by_contra hbaseNot
          have hbaseLe :
              Model.bytesToNatPadded ctx.executionEnv.calldata 96
                (lengths ctx.executionEnv.calldata).base ≤ 1 := by
            omega
          exact hfast (Or.inr hbaseLe)
      by_cases hzero : wideZeroModulusLengthCondition ctx.executionEnv
      · have hcovered := wideZeroModulusLength_coveredAccepts haccepts hcalldata hword hzero
        exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
      · by_cases hsmall : wideSmallModulusValueCondition ctx.executionEnv
        · have hcovered := wideSmallModulusValue_coveredAccepts haccepts hcalldata hword hsmall
          exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
        · by_cases hone : wideOneWordBackendInputs ctx
          · have hcovered := wideOneWordBackend_coveredAccepts hone
            exact coveredBytecodeSomeExactGasSpec.run ctx hcode hcovered
          · have hmulti : wideMultiLimbBackendInputs ctx :=
              wideNontrivial_not_oneWord_notSmall_split hwide hone hzero hsmall
            by_cases hmodGtOne : 1 < wideModulusNat ctx.executionEnv
            · rcases wideMultiLimbBackendInputs_split hmulti with hevenCase | hoddCase
              · have hspec := wideMultiLimbEvenBytecodeSpec_of_postChecksSuffix
                  evenSuffixGas hevenSuffix
                have hpost := hspec.run ctx hcode ⟨hevenCase, hmodGtOne⟩
                exact ⟨wideMultiLimbEvenDispatcherTotalGas ctx.executionEnv +
                  (wideMultiLimbEvenAllocationGas ctx +
                    wideMultiLimbChecksGas ctx + evenSuffixGas ctx), hpost⟩
              · have hspec := wideMultiLimbOddBytecodeSpec_of_postChecksSuffix
                  oddSuffixGas hoddSuffix
                have hpost := hspec.run ctx hcode ⟨hoddCase, hmodGtOne⟩
                exact ⟨wideMultiLimbOddDispatcherTotalGas ctx.executionEnv +
                  (wideMultiLimbOddAllocationGas ctx +
                    wideMultiLimbChecksGas ctx + oddSuffixGas ctx), hpost⟩
            · have hle : wideModulusNat ctx.executionEnv ≤ 1 := by omega
              exact wideMultiLimbLeOneBytecodeSpec.run ctx hcode ⟨hmulti, hle⟩

/-- Same full-spec reduction as `modexpSomeExactGasSpec_of_bounded_multiLimbPostChecksSuffix`,
but with the odd Montgomery residual starting at the real multi-limb body after the word-dispatch
block.  The PC 1968 dispatch is discharged by `reachMontgomeryMultiLimbBody`; the even Barrett
residual is unchanged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbOddBody_evenPostChecksSuffix
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddBodyGas evenSuffixGas : BytecodeContext → Nat)
    (hoddBody : WideMultiLimbOddBodySuffixExact oddBodyGas)
    (hevenSuffix : WideMultiLimbEvenPostChecksSuffixExact evenSuffixGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbPostChecksSuffix
    hbounded (fun ctx => 107 + oddBodyGas ctx) evenSuffixGas
    (wideMultiLimbOddPostChecksSuffixExact_of_bodySuffix oddBodyGas hoddBody)
    hevenSuffix

/-- Full-spec reduction with both deterministic post-check dispatch/setup blocks discharged.
The remaining true backend obligations start at:

* odd Montgomery: PC 1989, after the one-word dispatch;
* even Barrett: PC 1603, at the leading-zero scan loop cursor. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbBodySuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddBodyGas evenScanGas : BytecodeContext → Nat)
    (hoddBody : WideMultiLimbOddBodySuffixExact oddBodyGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbPostChecksSuffix
    hbounded (fun ctx => 107 + oddBodyGas ctx) (fun ctx => 27 + evenScanGas ctx)
    (wideMultiLimbOddPostChecksSuffixExact_of_bodySuffix oddBodyGas hoddBody)
    (wideMultiLimbEvenPostChecksSuffixExact_of_scanSuffix evenScanGas hevenScan)

/-- Full-spec reduction with the odd Montgomery residual pushed through its first deterministic
multi-limb helper call.  The remaining true backend obligations start at:

* odd Montgomery: PC 2836, at the first helper call from the multi-limb body;
* even Barrett: PC 1603, at the leading-zero scan loop cursor. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbCallSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddFirstCallGas evenScanGas : BytecodeContext → Nat)
    (hoddFirstCall : WideMultiLimbOddFirstCallSuffixExact oddFirstCallGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbBodySuffixes
    hbounded (fun ctx => 38 + oddFirstCallGas ctx) evenScanGas
    (wideMultiLimbOddBodySuffixExact_of_firstCallSuffix oddFirstCallGas hoddFirstCall)
    hevenScan

/-- Full-spec reduction with the odd Montgomery residual pushed to the bytes allocator/helper
called by the first multi-limb body block.  The remaining true backend obligations start at:

* odd Montgomery: PC 1487, allocating the first temporary bytes array;
* even Barrett: PC 1603, at the leading-zero scan loop cursor. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbAllocatorSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddAllocatorGas evenScanGas : BytecodeContext → Nat)
    (hoddAllocator : WideMultiLimbOddAllocatorCallSuffixExact oddAllocatorGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbCallSuffixes
    hbounded (fun ctx => 24 + oddAllocatorGas ctx) evenScanGas
    (wideMultiLimbOddFirstCallSuffixExact_of_allocatorCallSuffix oddAllocatorGas hoddAllocator)
    hevenScan

/-- Full-spec reduction with the first odd Montgomery word-array allocation discharged.  The
remaining true backend obligations start at:

* odd Montgomery: PC 2847, after the first temporary word-array allocation;
* even Barrett: PC 1603, at the leading-zero scan loop cursor. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbPostAllocatorSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddPostAllocatorGas evenScanGas : BytecodeContext → Nat)
    (hoddPostAllocator : WideMultiLimbOddPostAllocatorSuffixExact oddPostAllocatorGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbAllocatorSuffixes
    hbounded
    (fun ctx =>
      newWordArrayGas (wideMultiLimbPostAllocationAw ctx)
        (wideMultiLimbOddWordArrayPtr ctx)
        (wideMultiLimbOddWordArrayLength ctx) +
      oddPostAllocatorGas ctx)
    evenScanGas
    (wideMultiLimbOddAllocatorCallSuffixExact_of_postAllocatorSuffix
      oddPostAllocatorGas hoddPostAllocator)
    hevenScan

/-- Full-spec reduction with the first odd Montgomery word-array allocation and its first
loop-entry test discharged.  The remaining true backend obligations start at:

* odd Montgomery: PC 2906, the first full-word copy-loop body;
* even Barrett: PC 1603, at the leading-zero scan loop cursor. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbLoopEntrySuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddLoopGas evenScanGas : BytecodeContext → Nat)
    (hoddLoop : WideMultiLimbOddLoopEntrySuffixExact oddLoopGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbPostAllocatorSuffixes
    hbounded (fun ctx => 47 + oddLoopGas ctx) evenScanGas
    (wideMultiLimbOddPostAllocatorSuffixExact_of_loopEntrySuffix oddLoopGas hoddLoop)
    hevenScan

/-- Full-spec reduction with the first odd Montgomery full-word copy-loop call frame discharged.
The remaining true backend obligations start at:

* odd Montgomery: PC 1323, the checked-add helper called by the first copy-loop body;
* even Barrett: PC 1603, at the leading-zero scan loop cursor. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyAddSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddCopyAddGas evenScanGas : BytecodeContext → Nat)
    (hoddCopyAdd : WideMultiLimbOddFirstCopyAddSuffixExact oddCopyAddGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbLoopEntrySuffixes
    hbounded (fun ctx => 33 + oddCopyAddGas ctx) evenScanGas
    (wideMultiLimbOddLoopEntrySuffixExact_of_firstCopyAddSuffix oddCopyAddGas hoddCopyAdd)
    hevenScan

/-- Full-spec reduction with the checked-add helper called by the first odd Montgomery full-word
copy-loop body discharged.  The remaining true backend obligations start at:

* odd Montgomery: PC 2926, after the first copy-loop index increment has returned;
* even Barrett: PC 1603, at the leading-zero scan loop cursor. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyAddReturnSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddCopyAddReturnGas evenScanGas : BytecodeContext → Nat)
    (hoddCopyAddReturn :
      WideMultiLimbOddFirstCopyAddReturnSuffixExact oddCopyAddReturnGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyAddSuffixes
    hbounded (fun ctx => 43 + oddCopyAddReturnGas ctx) evenScanGas
    (wideMultiLimbOddFirstCopyAddSuffixExact_of_returnSuffix
      oddCopyAddReturnGas hoddCopyAddReturn)
    hevenScan

/-- Full-spec reduction with the jump from the first odd Montgomery checked-add return point into
the next helper discharged.  The remaining true backend obligations start at:

* odd Montgomery: PC 1903, the read/full-word helper body for the first copy-loop iteration;
* even Barrett: PC 1603, at the leading-zero scan loop cursor. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyReadSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddCopyReadGas evenScanGas : BytecodeContext → Nat)
    (hoddCopyRead : WideMultiLimbOddFirstCopyReadSuffixExact oddCopyReadGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyAddReturnSuffixes
    hbounded (fun ctx => 12 + oddCopyReadGas ctx) evenScanGas
    (wideMultiLimbOddFirstCopyAddReturnSuffixExact_of_readSuffix
      oddCopyReadGas hoddCopyRead)
    hevenScan

/-- Full-spec reduction with the first odd Montgomery read-offset guard and checked
`modulusSize - 32` subtraction discharged.  The remaining true backend obligations start at:

* odd Montgomery: PC 2937, the memory-copy store body for the first full-word copy iteration;
* even Barrett: PC 1603, at the leading-zero scan loop cursor. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyStoreSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddCopyStoreGas evenScanGas : BytecodeContext → Nat)
    (hoddCopyStore : WideMultiLimbOddFirstCopyStoreSuffixExact oddCopyStoreGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyReadSuffixes
    hbounded (fun ctx => 124 + oddCopyStoreGas ctx) evenScanGas
    (wideMultiLimbOddFirstCopyReadSuffixExact_of_storeSuffix
      oddCopyStoreGas hoddCopyStore)
    hevenScan

/-- Full-spec reduction with the first odd Montgomery full-word copy store discharged.  The
remaining true backend obligations start at:

* odd Montgomery: PC 2857, the copy-loop test after one full-word iteration;
* even Barrett: PC 1603, at the leading-zero scan loop cursor. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyLoopBackSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddCopyLoopBackGas evenScanGas : BytecodeContext → Nat)
    (hoddCopyLoopBack :
      WideMultiLimbOddFirstCopyLoopBackSuffixExact oddCopyLoopBackGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyStoreSuffixes
    hbounded (fun ctx => 51 + oddCopyLoopBackGas ctx) evenScanGas
    (wideMultiLimbOddFirstCopyStoreSuffixExact_of_loopBackSuffix
      oddCopyLoopBackGas hoddCopyLoopBack)
    hevenScan

/-- Full-spec reduction with the first odd Montgomery full-word copy loop guard discharged.  The
remaining odd obligation is split by whether the first copied word was the only full word in the
modulus payload. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyGuardSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddContinueGas oddExitGas evenScanGas : BytecodeContext → Nat)
    (hoddContinue :
      WideMultiLimbOddFirstCopyContinueSuffixExact oddContinueGas)
    (hoddExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyLoopBackSuffixes
    hbounded
    (fun ctx =>
      23 + if 1 < (lengths ctx.executionEnv.calldata).modulus / 32 then
        oddContinueGas ctx
      else
        oddExitGas ctx)
    evenScanGas
    (wideMultiLimbOddFirstCopyLoopBackSuffixExact_of_guardSuffixes
      oddContinueGas oddExitGas hoddContinue hoddExit)
    hevenScan

/-- Full-spec reduction with the taken branch of the first odd Montgomery copy-loop guard pushed
through the second iteration's call-frame setup into the checked-add helper. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyAddSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddSecondAddGas oddExitGas evenScanGas : BytecodeContext → Nat)
    (hoddSecondAdd :
      WideMultiLimbOddSecondCopyAddSuffixExact oddSecondAddGas)
    (hoddExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbFirstCopyGuardSuffixes
    hbounded
    (fun ctx => 33 + oddSecondAddGas ctx)
    oddExitGas
    evenScanGas
    (wideMultiLimbOddFirstCopyContinueSuffixExact_of_secondCopyAddSuffix
      oddSecondAddGas hoddSecondAdd)
    hoddExit
    hevenScan

/-- Full-spec reduction with the second copy iteration's checked-add helper discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyAddReturnSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddSecondAddReturnGas oddExitGas evenScanGas : BytecodeContext → Nat)
    (hoddSecondAddReturn :
      WideMultiLimbOddSecondCopyAddReturnSuffixExact oddSecondAddReturnGas)
    (hoddExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyAddSuffixes
    hbounded
    (fun ctx => 43 + oddSecondAddReturnGas ctx)
    oddExitGas
    evenScanGas
    (wideMultiLimbOddSecondCopyAddSuffixExact_of_returnSuffix
      oddSecondAddReturnGas hoddSecondAddReturn)
    hoddExit
    hevenScan

/-- Full-spec reduction with the second copy iteration's jump back to the read-offset helper
discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyReadSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddSecondReadGas oddExitGas evenScanGas : BytecodeContext → Nat)
    (hoddSecondRead :
      WideMultiLimbOddSecondCopyReadSuffixExact oddSecondReadGas)
    (hoddExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyAddReturnSuffixes
    hbounded
    (fun ctx => 12 + oddSecondReadGas ctx)
    oddExitGas
    evenScanGas
    (wideMultiLimbOddSecondCopyAddReturnSuffixExact_of_readSuffix
      oddSecondReadGas hoddSecondRead)
    hoddExit
    hevenScan

/-- Full-spec reduction with the second copy iteration's read-offset helper and checked
subtraction discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyStoreSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddSecondStoreGas oddExitGas evenScanGas : BytecodeContext → Nat)
    (hoddSecondStore :
      WideMultiLimbOddSecondCopyStoreSuffixExact oddSecondStoreGas)
    (hoddExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyReadSuffixes
    hbounded
    (fun ctx => 124 + oddSecondStoreGas ctx)
    oddExitGas
    evenScanGas
    (wideMultiLimbOddSecondCopyReadSuffixExact_of_storeSuffix
      oddSecondStoreGas hoddSecondStore)
    hoddExit
    hevenScan

/-- Full-spec reduction with the second full-word copy store discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyLoopBackSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddSecondLoopBackGas oddExitGas evenScanGas : BytecodeContext → Nat)
    (hoddSecondLoopBack :
      WideMultiLimbOddSecondCopyLoopBackSuffixExact oddSecondLoopBackGas)
    (hoddExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyStoreSuffixes
    hbounded
    (fun ctx => 51 + oddSecondLoopBackGas ctx)
    oddExitGas
    evenScanGas
    (wideMultiLimbOddSecondCopyStoreSuffixExact_of_loopBackSuffix
      oddSecondLoopBackGas hoddSecondLoopBack)
    hoddExit
    hevenScan

/-- Full-spec reduction with the loop guard after the second full-word copy discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyGuardSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddSecondContinueGas oddSecondExitGas oddFirstExitGas evenScanGas : BytecodeContext → Nat)
    (hoddSecondContinue :
      WideMultiLimbOddSecondCopyContinueSuffixExact oddSecondContinueGas)
    (hoddSecondExit :
      WideMultiLimbOddSecondCopyExitSuffixExact oddSecondExitGas)
    (hoddFirstExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddFirstExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyLoopBackSuffixes
    hbounded
    (fun ctx =>
      23 + if 2 < (lengths ctx.executionEnv.calldata).modulus / 32 then
        oddSecondContinueGas ctx
      else
        oddSecondExitGas ctx)
    oddFirstExitGas
    evenScanGas
    (wideMultiLimbOddSecondCopyLoopBackSuffixExact_of_guardSuffixes
      oddSecondContinueGas oddSecondExitGas hoddSecondContinue hoddSecondExit)
    hoddFirstExit
    hevenScan

/-- Full-spec reduction with the third full-word copy's call-frame setup discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyAddSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddThirdAddGas oddSecondExitGas oddFirstExitGas evenScanGas : BytecodeContext → Nat)
    (hoddThirdAdd :
      WideMultiLimbOddThirdCopyAddSuffixExact oddThirdAddGas)
    (hoddSecondExit :
      WideMultiLimbOddSecondCopyExitSuffixExact oddSecondExitGas)
    (hoddFirstExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddFirstExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbSecondCopyGuardSuffixes
    hbounded
    (fun ctx => 33 + oddThirdAddGas ctx)
    oddSecondExitGas
    oddFirstExitGas
    evenScanGas
    (wideMultiLimbOddSecondCopyContinueSuffixExact_of_thirdCopyAddSuffix
      oddThirdAddGas hoddThirdAdd)
    hoddSecondExit
    hoddFirstExit
    hevenScan

/-- Full-spec reduction with the third copy iteration's checked-add helper discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyAddReturnSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddThirdAddReturnGas oddSecondExitGas oddFirstExitGas evenScanGas : BytecodeContext → Nat)
    (hoddThirdAddReturn :
      WideMultiLimbOddThirdCopyAddReturnSuffixExact oddThirdAddReturnGas)
    (hoddSecondExit :
      WideMultiLimbOddSecondCopyExitSuffixExact oddSecondExitGas)
    (hoddFirstExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddFirstExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyAddSuffixes
    hbounded
    (fun ctx => 43 + oddThirdAddReturnGas ctx)
    oddSecondExitGas
    oddFirstExitGas
    evenScanGas
    (wideMultiLimbOddThirdCopyAddSuffixExact_of_returnSuffix
      oddThirdAddReturnGas hoddThirdAddReturn)
    hoddSecondExit
    hoddFirstExit
    hevenScan

/-- Full-spec reduction with the third copy iteration's read-offset helper call discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyReadSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddThirdReadGas oddSecondExitGas oddFirstExitGas evenScanGas : BytecodeContext → Nat)
    (hoddThirdRead :
      WideMultiLimbOddThirdCopyReadSuffixExact oddThirdReadGas)
    (hoddSecondExit :
      WideMultiLimbOddSecondCopyExitSuffixExact oddSecondExitGas)
    (hoddFirstExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddFirstExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyAddReturnSuffixes
    hbounded
    (fun ctx => 12 + oddThirdReadGas ctx)
    oddSecondExitGas
    oddFirstExitGas
    evenScanGas
    (wideMultiLimbOddThirdCopyAddReturnSuffixExact_of_readSuffix
      oddThirdReadGas hoddThirdRead)
    hoddSecondExit
    hoddFirstExit
    hevenScan

/-- Full-spec reduction with the third copy iteration's read-offset/subtraction helper discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyStoreSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddThirdStoreGas oddSecondExitGas oddFirstExitGas evenScanGas : BytecodeContext → Nat)
    (hoddThirdStore :
      WideMultiLimbOddThirdCopyStoreSuffixExact oddThirdStoreGas)
    (hoddSecondExit :
      WideMultiLimbOddSecondCopyExitSuffixExact oddSecondExitGas)
    (hoddFirstExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddFirstExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyReadSuffixes
    hbounded
    (fun ctx => 124 + oddThirdStoreGas ctx)
    oddSecondExitGas
    oddFirstExitGas
    evenScanGas
    (wideMultiLimbOddThirdCopyReadSuffixExact_of_storeSuffix
      oddThirdStoreGas hoddThirdStore)
    hoddSecondExit
    hoddFirstExit
    hevenScan

/-- Full-spec reduction with the third full-word copy store block discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyLoopBackSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddThirdLoopBackGas oddSecondExitGas oddFirstExitGas evenScanGas : BytecodeContext → Nat)
    (hoddThirdLoopBack :
      WideMultiLimbOddThirdCopyLoopBackSuffixExact oddThirdLoopBackGas)
    (hoddSecondExit :
      WideMultiLimbOddSecondCopyExitSuffixExact oddSecondExitGas)
    (hoddFirstExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddFirstExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyStoreSuffixes
    hbounded
    (fun ctx => 51 + oddThirdLoopBackGas ctx)
    oddSecondExitGas
    oddFirstExitGas
    evenScanGas
    (wideMultiLimbOddThirdCopyStoreSuffixExact_of_loopBackSuffix
      oddThirdLoopBackGas hoddThirdLoopBack)
    hoddSecondExit
    hoddFirstExit
    hevenScan

/-- Full-spec reduction with the third full-word copy loop guard discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyGuardSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddThirdContinueGas oddThirdExitGas oddSecondExitGas oddFirstExitGas evenScanGas :
      BytecodeContext → Nat)
    (hoddThirdContinue :
      WideMultiLimbOddThirdCopyContinueSuffixExact oddThirdContinueGas)
    (hoddThirdExit :
      WideMultiLimbOddThirdCopyExitSuffixExact oddThirdExitGas)
    (hoddSecondExit :
      WideMultiLimbOddSecondCopyExitSuffixExact oddSecondExitGas)
    (hoddFirstExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddFirstExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyLoopBackSuffixes
    hbounded
    (fun ctx =>
      23 + if 3 < (lengths ctx.executionEnv.calldata).modulus / 32 then
        oddThirdContinueGas ctx
      else
        oddThirdExitGas ctx)
    oddSecondExitGas
    oddFirstExitGas
    evenScanGas
    (wideMultiLimbOddThirdCopyLoopBackSuffixExact_of_guardSuffixes
      oddThirdContinueGas oddThirdExitGas hoddThirdContinue hoddThirdExit)
    hoddSecondExit
    hoddFirstExit
    hevenScan

/-- Full-spec reduction with the third guard's taken-branch call-frame setup discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbFourthCopyAddSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddFourthAddGas oddThirdExitGas oddSecondExitGas oddFirstExitGas evenScanGas :
      BytecodeContext → Nat)
    (hoddFourthAdd :
      WideMultiLimbOddFourthCopyAddSuffixExact oddFourthAddGas)
    (hoddThirdExit :
      WideMultiLimbOddThirdCopyExitSuffixExact oddThirdExitGas)
    (hoddSecondExit :
      WideMultiLimbOddSecondCopyExitSuffixExact oddSecondExitGas)
    (hoddFirstExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddFirstExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbThirdCopyGuardSuffixes
    hbounded
    (fun ctx => 33 + oddFourthAddGas ctx)
    oddThirdExitGas
    oddSecondExitGas
    oddFirstExitGas
    evenScanGas
    (wideMultiLimbOddThirdCopyContinueSuffixExact_of_fourthCopyAddSuffix
      oddFourthAddGas hoddFourthAdd)
    hoddThirdExit
    hoddSecondExit
    hoddFirstExit
    hevenScan

/-- Full-spec reduction with the fourth copy iteration's checked-add helper discharged. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbFourthCopyAddReturnSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddFourthAddReturnGas oddThirdExitGas oddSecondExitGas oddFirstExitGas evenScanGas :
      BytecodeContext → Nat)
    (hoddFourthAddReturn :
      WideMultiLimbOddFourthCopyAddReturnSuffixExact oddFourthAddReturnGas)
    (hoddThirdExit :
      WideMultiLimbOddThirdCopyExitSuffixExact oddThirdExitGas)
    (hoddSecondExit :
      WideMultiLimbOddSecondCopyExitSuffixExact oddSecondExitGas)
    (hoddFirstExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddFirstExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbFourthCopyAddSuffixes
    hbounded
    (fun ctx => 43 + oddFourthAddReturnGas ctx)
    oddThirdExitGas
    oddSecondExitGas
    oddFirstExitGas
    evenScanGas
    (wideMultiLimbOddFourthCopyAddSuffixExact_of_returnSuffix
      oddFourthAddReturnGas hoddFourthAddReturn)
    hoddThirdExit
    hoddSecondExit
    hoddFirstExit
    hevenScan

/-- Full-spec reduction with the fourth copy iteration's read-offset call dispatched. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbFourthCopyReadSuffixes
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (oddFourthReadGas oddThirdExitGas oddSecondExitGas oddFirstExitGas evenScanGas :
      BytecodeContext → Nat)
    (hoddFourthRead :
      WideMultiLimbOddFourthCopyReadSuffixExact oddFourthReadGas)
    (hoddThirdExit :
      WideMultiLimbOddThirdCopyExitSuffixExact oddThirdExitGas)
    (hoddSecondExit :
      WideMultiLimbOddSecondCopyExitSuffixExact oddSecondExitGas)
    (hoddFirstExit :
      WideMultiLimbOddFirstCopyExitSuffixExact oddFirstExitGas)
    (hevenScan : WideMultiLimbEvenScanSuffixExact evenScanGas) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  exact modexpSomeExactGasSpec_of_bounded_multiLimbFourthCopyAddReturnSuffixes
    hbounded
    (fun ctx => 12 + oddFourthReadGas ctx)
    oddThirdExitGas
    oddSecondExitGas
    oddFirstExitGas
    evenScanGas
    (wideMultiLimbOddFourthCopyAddReturnSuffixExact_of_readSuffix
      oddFourthReadGas hoddFourthRead)
    hoddThirdExit
    hoddSecondExit
    hoddFirstExit
    hevenScan

end Modexp
