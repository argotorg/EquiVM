import Examples.Ripemd160Old.DecodeGenerated.Chunk59

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes60 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨8274⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨255⟩, 1))),
  (⟨8276⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨8277⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨8279⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨8280⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8281⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨8283⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨8284⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨8285⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8286⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨255⟩, 1))),
  (⟨8288⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨8289⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨8290⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨8292⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨8293⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8294⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨8296⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨8297⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8298⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8299⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨24⟩, 1))),
  (⟨8301⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨8302⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨8303⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨8304⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8305⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8307⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8314⟩, 2))),
  (⟨8310⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨264⟩, 2))),
  (⟨8313⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8314⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8315⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8316⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨8318⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8319⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8320⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8321⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8322⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨8324⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨8325⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none)),
  (⟨8326⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨63⟩, 1))),
  (⟨8328⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.NOT), none)),
  (⟨8329⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨63⟩, 1))),
  (⟨8331⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨8333⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨8334⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8335⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8336⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8337⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8338⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8340⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8341⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8342⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8343⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8344⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8345⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8347⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8348⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨8349⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8350⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8351⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨8352⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨8353⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none)),
  (⟨8354⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨9070⟩, 2))),
  (⟨8357⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨8358⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8359⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8360⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8361⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8362⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none)),
  (⟨8363⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨9056⟩, 2))),
  (⟨8366⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨8367⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8368⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8369⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1))),
  (⟨8371⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨255⟩, 1))),
  (⟨8373⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8374⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8375⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8376⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none)),
  (⟨8377⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8378⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4))),
  (⟨8383⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨8384⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8385⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8386⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨8388⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨8389⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8390⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8391⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8392⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8393⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨8395⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8396⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨8397⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8398⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8399⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none)),
  (⟨8400⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8401⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8402⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨8404⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨8405⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none))
]

private theorem generatedDecodes60_correct : ∀ i : Fin generatedDecodes60.size,
    decode runtimeBytecode generatedDecodes60[i].1 = generatedDecodes60[i].2 := by
  native_decide

theorem decode_8274 : decode runtimeBytecode ⟨8274⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨255⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨0, by decide⟩
theorem decode_8276 : decode runtimeBytecode ⟨8276⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨1, by decide⟩
theorem decode_8277 : decode runtimeBytecode ⟨8277⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨2, by decide⟩
theorem decode_8279 : decode runtimeBytecode ⟨8279⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨3, by decide⟩
theorem decode_8280 : decode runtimeBytecode ⟨8280⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨4, by decide⟩
theorem decode_8281 : decode runtimeBytecode ⟨8281⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨5, by decide⟩
theorem decode_8283 : decode runtimeBytecode ⟨8283⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨6, by decide⟩
theorem decode_8284 : decode runtimeBytecode ⟨8284⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨7, by decide⟩
theorem decode_8285 : decode runtimeBytecode ⟨8285⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨8, by decide⟩
theorem decode_8286 : decode runtimeBytecode ⟨8286⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨255⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨9, by decide⟩
theorem decode_8288 : decode runtimeBytecode ⟨8288⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨10, by decide⟩
theorem decode_8289 : decode runtimeBytecode ⟨8289⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨11, by decide⟩
theorem decode_8290 : decode runtimeBytecode ⟨8290⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨12, by decide⟩
theorem decode_8292 : decode runtimeBytecode ⟨8292⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨13, by decide⟩
theorem decode_8293 : decode runtimeBytecode ⟨8293⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨14, by decide⟩
theorem decode_8294 : decode runtimeBytecode ⟨8294⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨15, by decide⟩
theorem decode_8296 : decode runtimeBytecode ⟨8296⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨16, by decide⟩
theorem decode_8297 : decode runtimeBytecode ⟨8297⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨17, by decide⟩
theorem decode_8298 : decode runtimeBytecode ⟨8298⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨18, by decide⟩
theorem decode_8299 : decode runtimeBytecode ⟨8299⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨24⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨19, by decide⟩
theorem decode_8301 : decode runtimeBytecode ⟨8301⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨20, by decide⟩
theorem decode_8302 : decode runtimeBytecode ⟨8302⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨21, by decide⟩
theorem decode_8303 : decode runtimeBytecode ⟨8303⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨22, by decide⟩
theorem decode_8304 : decode runtimeBytecode ⟨8304⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨23, by decide⟩
theorem decode_8305 : decode runtimeBytecode ⟨8305⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨24, by decide⟩
theorem decode_8307 : decode runtimeBytecode ⟨8307⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8314⟩, 2)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨25, by decide⟩
theorem decode_8310 : decode runtimeBytecode ⟨8310⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨264⟩, 2)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨26, by decide⟩
theorem decode_8313 : decode runtimeBytecode ⟨8313⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨27, by decide⟩
theorem decode_8314 : decode runtimeBytecode ⟨8314⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨28, by decide⟩
theorem decode_8315 : decode runtimeBytecode ⟨8315⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨29, by decide⟩
theorem decode_8316 : decode runtimeBytecode ⟨8316⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨30, by decide⟩
theorem decode_8318 : decode runtimeBytecode ⟨8318⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨31, by decide⟩
theorem decode_8319 : decode runtimeBytecode ⟨8319⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨32, by decide⟩
theorem decode_8320 : decode runtimeBytecode ⟨8320⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨33, by decide⟩
theorem decode_8321 : decode runtimeBytecode ⟨8321⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨34, by decide⟩
theorem decode_8322 : decode runtimeBytecode ⟨8322⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨35, by decide⟩
theorem decode_8324 : decode runtimeBytecode ⟨8324⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨36, by decide⟩
theorem decode_8325 : decode runtimeBytecode ⟨8325⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨37, by decide⟩
theorem decode_8326 : decode runtimeBytecode ⟨8326⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨63⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨38, by decide⟩
theorem decode_8328 : decode runtimeBytecode ⟨8328⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.NOT), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨39, by decide⟩
theorem decode_8329 : decode runtimeBytecode ⟨8329⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨63⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨40, by decide⟩
theorem decode_8331 : decode runtimeBytecode ⟨8331⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨41, by decide⟩
theorem decode_8333 : decode runtimeBytecode ⟨8333⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨42, by decide⟩
theorem decode_8334 : decode runtimeBytecode ⟨8334⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨43, by decide⟩
theorem decode_8335 : decode runtimeBytecode ⟨8335⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨44, by decide⟩
theorem decode_8336 : decode runtimeBytecode ⟨8336⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨45, by decide⟩
theorem decode_8337 : decode runtimeBytecode ⟨8337⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨46, by decide⟩
theorem decode_8338 : decode runtimeBytecode ⟨8338⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨47, by decide⟩
theorem decode_8340 : decode runtimeBytecode ⟨8340⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨48, by decide⟩
theorem decode_8341 : decode runtimeBytecode ⟨8341⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨49, by decide⟩
theorem decode_8342 : decode runtimeBytecode ⟨8342⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨50, by decide⟩
theorem decode_8343 : decode runtimeBytecode ⟨8343⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨51, by decide⟩
theorem decode_8344 : decode runtimeBytecode ⟨8344⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨52, by decide⟩
theorem decode_8345 : decode runtimeBytecode ⟨8345⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨53, by decide⟩
theorem decode_8347 : decode runtimeBytecode ⟨8347⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨54, by decide⟩
theorem decode_8348 : decode runtimeBytecode ⟨8348⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨55, by decide⟩
theorem decode_8349 : decode runtimeBytecode ⟨8349⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨56, by decide⟩
theorem decode_8350 : decode runtimeBytecode ⟨8350⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨57, by decide⟩
theorem decode_8351 : decode runtimeBytecode ⟨8351⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨58, by decide⟩
theorem decode_8352 : decode runtimeBytecode ⟨8352⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨59, by decide⟩
theorem decode_8353 : decode runtimeBytecode ⟨8353⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨60, by decide⟩
theorem decode_8354 : decode runtimeBytecode ⟨8354⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨9070⟩, 2)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨61, by decide⟩
theorem decode_8357 : decode runtimeBytecode ⟨8357⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨62, by decide⟩
theorem decode_8358 : decode runtimeBytecode ⟨8358⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨63, by decide⟩
theorem decode_8359 : decode runtimeBytecode ⟨8359⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨64, by decide⟩
theorem decode_8360 : decode runtimeBytecode ⟨8360⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨65, by decide⟩
theorem decode_8361 : decode runtimeBytecode ⟨8361⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨66, by decide⟩
theorem decode_8362 : decode runtimeBytecode ⟨8362⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨67, by decide⟩
theorem decode_8363 : decode runtimeBytecode ⟨8363⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨9056⟩, 2)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨68, by decide⟩
theorem decode_8366 : decode runtimeBytecode ⟨8366⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨69, by decide⟩
theorem decode_8367 : decode runtimeBytecode ⟨8367⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨70, by decide⟩
theorem decode_8368 : decode runtimeBytecode ⟨8368⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨71, by decide⟩
theorem decode_8369 : decode runtimeBytecode ⟨8369⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨72, by decide⟩
theorem decode_8371 : decode runtimeBytecode ⟨8371⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨255⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨73, by decide⟩
theorem decode_8373 : decode runtimeBytecode ⟨8373⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨74, by decide⟩
theorem decode_8374 : decode runtimeBytecode ⟨8374⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨75, by decide⟩
theorem decode_8375 : decode runtimeBytecode ⟨8375⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨76, by decide⟩
theorem decode_8376 : decode runtimeBytecode ⟨8376⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨77, by decide⟩
theorem decode_8377 : decode runtimeBytecode ⟨8377⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨78, by decide⟩
theorem decode_8378 : decode runtimeBytecode ⟨8378⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨79, by decide⟩
theorem decode_8383 : decode runtimeBytecode ⟨8383⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨80, by decide⟩
theorem decode_8384 : decode runtimeBytecode ⟨8384⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨81, by decide⟩
theorem decode_8385 : decode runtimeBytecode ⟨8385⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨82, by decide⟩
theorem decode_8386 : decode runtimeBytecode ⟨8386⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨83, by decide⟩
theorem decode_8388 : decode runtimeBytecode ⟨8388⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨84, by decide⟩
theorem decode_8389 : decode runtimeBytecode ⟨8389⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨85, by decide⟩
theorem decode_8390 : decode runtimeBytecode ⟨8390⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨86, by decide⟩
theorem decode_8391 : decode runtimeBytecode ⟨8391⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨87, by decide⟩
theorem decode_8392 : decode runtimeBytecode ⟨8392⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨88, by decide⟩
theorem decode_8393 : decode runtimeBytecode ⟨8393⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨89, by decide⟩
theorem decode_8395 : decode runtimeBytecode ⟨8395⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨90, by decide⟩
theorem decode_8396 : decode runtimeBytecode ⟨8396⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨91, by decide⟩
theorem decode_8397 : decode runtimeBytecode ⟨8397⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨92, by decide⟩
theorem decode_8398 : decode runtimeBytecode ⟨8398⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨93, by decide⟩
theorem decode_8399 : decode runtimeBytecode ⟨8399⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨94, by decide⟩
theorem decode_8400 : decode runtimeBytecode ⟨8400⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨95, by decide⟩
theorem decode_8401 : decode runtimeBytecode ⟨8401⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨96, by decide⟩
theorem decode_8402 : decode runtimeBytecode ⟨8402⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨97, by decide⟩
theorem decode_8404 : decode runtimeBytecode ⟨8404⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨98, by decide⟩
theorem decode_8405 : decode runtimeBytecode ⟨8405⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes60] using generatedDecodes60_correct ⟨99, by decide⟩

end Ripemd160Old
