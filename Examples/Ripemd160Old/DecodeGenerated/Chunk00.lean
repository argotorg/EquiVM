import Examples.Ripemd160Old.JumpFallback

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes0 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨254⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨255⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨257⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨258⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨259⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨260⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨262⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨263⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.RETURN), none)),
  (⟨264⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨265⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨266⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨267⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨268⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨269⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨270⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4))),
  (⟨275⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨276⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨277⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨278⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨280⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨281⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨282⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨283⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨284⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨285⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨286⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨287⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨288⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨289⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨291⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨292⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨526⟩, 2))),
  (⟨295⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨10⟩, 1))),
  (⟨297⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4))),
  (⟨302⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨303⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨304⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨305⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨306⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨307⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨308⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨309⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨310⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨311⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨313⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨314⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨315⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨316⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨317⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨511⟩, 2))),
  (⟨320⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨322⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP10), none)),
  (⟨323⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨324⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨325⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨326⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨327⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP10), none)),
  (⟨328⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1))),
  (⟨330⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none)),
  (⟨331⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨332⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨333⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP14), none)),
  (⟨334⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨335⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨336⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨337⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨339⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨340⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.DIV), none)),
  (⟨341⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨342⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨343⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨344⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none)),
  (⟨345⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none)),
  (⟨346⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨347⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨348⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP11), none)),
  (⟨349⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨350⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨351⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨352⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨353⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4108⟩, 2))),
  (⟨356⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨357⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨358⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨359⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨361⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨362⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4081⟩, 2))),
  (⟨365⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨366⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨367⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨369⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨370⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4058⟩, 2))),
  (⟨373⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨374⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨375⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨376⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨377⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨379⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨380⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4032⟩, 2))),
  (⟨383⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨384⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨386⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none))
]

private theorem generatedDecodes0_correct : ∀ i : Fin generatedDecodes0.size,
    decode runtimeBytecode generatedDecodes0[i].1 = generatedDecodes0[i].2 := by
  native_decide

theorem decode_254 : decode runtimeBytecode ⟨254⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨0, by decide⟩
theorem decode_255 : decode runtimeBytecode ⟨255⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨1, by decide⟩
theorem decode_257 : decode runtimeBytecode ⟨257⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨2, by decide⟩
theorem decode_258 : decode runtimeBytecode ⟨258⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨3, by decide⟩
theorem decode_259 : decode runtimeBytecode ⟨259⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨4, by decide⟩
theorem decode_260 : decode runtimeBytecode ⟨260⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨5, by decide⟩
theorem decode_262 : decode runtimeBytecode ⟨262⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨6, by decide⟩
theorem decode_263 : decode runtimeBytecode ⟨263⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.RETURN), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨7, by decide⟩
theorem decode_264 : decode runtimeBytecode ⟨264⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨8, by decide⟩
theorem decode_265 : decode runtimeBytecode ⟨265⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨9, by decide⟩
theorem decode_266 : decode runtimeBytecode ⟨266⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨10, by decide⟩
theorem decode_267 : decode runtimeBytecode ⟨267⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨11, by decide⟩
theorem decode_268 : decode runtimeBytecode ⟨268⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨12, by decide⟩
theorem decode_269 : decode runtimeBytecode ⟨269⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨13, by decide⟩
theorem decode_270 : decode runtimeBytecode ⟨270⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨14, by decide⟩
theorem decode_275 : decode runtimeBytecode ⟨275⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨15, by decide⟩
theorem decode_276 : decode runtimeBytecode ⟨276⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨16, by decide⟩
theorem decode_277 : decode runtimeBytecode ⟨277⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨17, by decide⟩
theorem decode_278 : decode runtimeBytecode ⟨278⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨18, by decide⟩
theorem decode_280 : decode runtimeBytecode ⟨280⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨19, by decide⟩
theorem decode_281 : decode runtimeBytecode ⟨281⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨20, by decide⟩
theorem decode_282 : decode runtimeBytecode ⟨282⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨21, by decide⟩
theorem decode_283 : decode runtimeBytecode ⟨283⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨22, by decide⟩
theorem decode_284 : decode runtimeBytecode ⟨284⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨23, by decide⟩
theorem decode_285 : decode runtimeBytecode ⟨285⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨24, by decide⟩
theorem decode_286 : decode runtimeBytecode ⟨286⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨25, by decide⟩
theorem decode_287 : decode runtimeBytecode ⟨287⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨26, by decide⟩
theorem decode_288 : decode runtimeBytecode ⟨288⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨27, by decide⟩
theorem decode_289 : decode runtimeBytecode ⟨289⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨28, by decide⟩
theorem decode_291 : decode runtimeBytecode ⟨291⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨29, by decide⟩
theorem decode_292 : decode runtimeBytecode ⟨292⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨526⟩, 2)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨30, by decide⟩
theorem decode_295 : decode runtimeBytecode ⟨295⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨10⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨31, by decide⟩
theorem decode_297 : decode runtimeBytecode ⟨297⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨32, by decide⟩
theorem decode_302 : decode runtimeBytecode ⟨302⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨33, by decide⟩
theorem decode_303 : decode runtimeBytecode ⟨303⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨34, by decide⟩
theorem decode_304 : decode runtimeBytecode ⟨304⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨35, by decide⟩
theorem decode_305 : decode runtimeBytecode ⟨305⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨36, by decide⟩
theorem decode_306 : decode runtimeBytecode ⟨306⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨37, by decide⟩
theorem decode_307 : decode runtimeBytecode ⟨307⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨38, by decide⟩
theorem decode_308 : decode runtimeBytecode ⟨308⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨39, by decide⟩
theorem decode_309 : decode runtimeBytecode ⟨309⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨40, by decide⟩
theorem decode_310 : decode runtimeBytecode ⟨310⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨41, by decide⟩
theorem decode_311 : decode runtimeBytecode ⟨311⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨42, by decide⟩
theorem decode_313 : decode runtimeBytecode ⟨313⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨43, by decide⟩
theorem decode_314 : decode runtimeBytecode ⟨314⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨44, by decide⟩
theorem decode_315 : decode runtimeBytecode ⟨315⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨45, by decide⟩
theorem decode_316 : decode runtimeBytecode ⟨316⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨46, by decide⟩
theorem decode_317 : decode runtimeBytecode ⟨317⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨511⟩, 2)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨47, by decide⟩
theorem decode_320 : decode runtimeBytecode ⟨320⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨48, by decide⟩
theorem decode_322 : decode runtimeBytecode ⟨322⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP10), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨49, by decide⟩
theorem decode_323 : decode runtimeBytecode ⟨323⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨50, by decide⟩
theorem decode_324 : decode runtimeBytecode ⟨324⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨51, by decide⟩
theorem decode_325 : decode runtimeBytecode ⟨325⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨52, by decide⟩
theorem decode_326 : decode runtimeBytecode ⟨326⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨53, by decide⟩
theorem decode_327 : decode runtimeBytecode ⟨327⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP10), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨54, by decide⟩
theorem decode_328 : decode runtimeBytecode ⟨328⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨55, by decide⟩
theorem decode_330 : decode runtimeBytecode ⟨330⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨56, by decide⟩
theorem decode_331 : decode runtimeBytecode ⟨331⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨57, by decide⟩
theorem decode_332 : decode runtimeBytecode ⟨332⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨58, by decide⟩
theorem decode_333 : decode runtimeBytecode ⟨333⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP14), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨59, by decide⟩
theorem decode_334 : decode runtimeBytecode ⟨334⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨60, by decide⟩
theorem decode_335 : decode runtimeBytecode ⟨335⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨61, by decide⟩
theorem decode_336 : decode runtimeBytecode ⟨336⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨62, by decide⟩
theorem decode_337 : decode runtimeBytecode ⟨337⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨63, by decide⟩
theorem decode_339 : decode runtimeBytecode ⟨339⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨64, by decide⟩
theorem decode_340 : decode runtimeBytecode ⟨340⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.DIV), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨65, by decide⟩
theorem decode_341 : decode runtimeBytecode ⟨341⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨66, by decide⟩
theorem decode_342 : decode runtimeBytecode ⟨342⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨67, by decide⟩
theorem decode_343 : decode runtimeBytecode ⟨343⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨68, by decide⟩
theorem decode_344 : decode runtimeBytecode ⟨344⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨69, by decide⟩
theorem decode_345 : decode runtimeBytecode ⟨345⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨70, by decide⟩
theorem decode_346 : decode runtimeBytecode ⟨346⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨71, by decide⟩
theorem decode_347 : decode runtimeBytecode ⟨347⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨72, by decide⟩
theorem decode_348 : decode runtimeBytecode ⟨348⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP11), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨73, by decide⟩
theorem decode_349 : decode runtimeBytecode ⟨349⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨74, by decide⟩
theorem decode_350 : decode runtimeBytecode ⟨350⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨75, by decide⟩
theorem decode_351 : decode runtimeBytecode ⟨351⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨76, by decide⟩
theorem decode_352 : decode runtimeBytecode ⟨352⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨77, by decide⟩
theorem decode_353 : decode runtimeBytecode ⟨353⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4108⟩, 2)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨78, by decide⟩
theorem decode_356 : decode runtimeBytecode ⟨356⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨79, by decide⟩
theorem decode_357 : decode runtimeBytecode ⟨357⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨80, by decide⟩
theorem decode_358 : decode runtimeBytecode ⟨358⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨81, by decide⟩
theorem decode_359 : decode runtimeBytecode ⟨359⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨82, by decide⟩
theorem decode_361 : decode runtimeBytecode ⟨361⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨83, by decide⟩
theorem decode_362 : decode runtimeBytecode ⟨362⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4081⟩, 2)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨84, by decide⟩
theorem decode_365 : decode runtimeBytecode ⟨365⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨85, by decide⟩
theorem decode_366 : decode runtimeBytecode ⟨366⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨86, by decide⟩
theorem decode_367 : decode runtimeBytecode ⟨367⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨87, by decide⟩
theorem decode_369 : decode runtimeBytecode ⟨369⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨88, by decide⟩
theorem decode_370 : decode runtimeBytecode ⟨370⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4058⟩, 2)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨89, by decide⟩
theorem decode_373 : decode runtimeBytecode ⟨373⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨90, by decide⟩
theorem decode_374 : decode runtimeBytecode ⟨374⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨91, by decide⟩
theorem decode_375 : decode runtimeBytecode ⟨375⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨92, by decide⟩
theorem decode_376 : decode runtimeBytecode ⟨376⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨93, by decide⟩
theorem decode_377 : decode runtimeBytecode ⟨377⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨94, by decide⟩
theorem decode_379 : decode runtimeBytecode ⟨379⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨95, by decide⟩
theorem decode_380 : decode runtimeBytecode ⟨380⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4032⟩, 2)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨96, by decide⟩
theorem decode_383 : decode runtimeBytecode ⟨383⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨97, by decide⟩
theorem decode_384 : decode runtimeBytecode ⟨384⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨98, by decide⟩
theorem decode_386 : decode runtimeBytecode ⟨386⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes0] using generatedDecodes0_correct ⟨99, by decide⟩

end Ripemd160Old
