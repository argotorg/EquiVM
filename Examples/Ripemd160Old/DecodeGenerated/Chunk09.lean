import Examples.Ripemd160Old.DecodeGenerated.Chunk08

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes9 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨1420⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨1422⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1423⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1424⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1425⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1426⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1427⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1430⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1431⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1432⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1433⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨1435⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1436⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1437⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨1438⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1439⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨1440⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1441⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨1442⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1443⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1858⟩, 2))),
  (⟨1446⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1447⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1448⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨1450⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1451⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1839⟩, 2))),
  (⟨1454⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1455⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1456⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨1458⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1459⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1820⟩, 2))),
  (⟨1462⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1463⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1464⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨1466⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1467⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1801⟩, 2))),
  (⟨1470⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1471⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1472⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨1474⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1475⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1782⟩, 2))),
  (⟨1478⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1479⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1480⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨1482⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1483⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1763⟩, 2))),
  (⟨1486⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1487⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1488⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨1490⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1491⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1744⟩, 2))),
  (⟨1494⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1495⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1496⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨1498⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1499⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1725⟩, 2))),
  (⟨1502⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1503⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1504⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨1506⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1507⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1706⟩, 2))),
  (⟨1510⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1511⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1512⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨1514⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1515⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1687⟩, 2))),
  (⟨1518⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1519⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1520⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨1521⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1522⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1668⟩, 2))),
  (⟨1525⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1526⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1527⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨1529⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1530⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1649⟩, 2))),
  (⟨1533⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1534⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1535⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨1537⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1538⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1630⟩, 2))),
  (⟨1541⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1542⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1543⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨1545⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1546⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1611⟩, 2))),
  (⟨1549⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1550⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1551⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨1553⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1554⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1592⟩, 2))),
  (⟨1557⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1558⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨1560⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1561⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1574⟩, 2))),
  (⟨1564⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1565⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1566⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1567⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1568⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1569⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none))
]

private theorem generatedDecodes9_correct : ∀ i : Fin generatedDecodes9.size,
    decode runtimeBytecode generatedDecodes9[i].1 = generatedDecodes9[i].2 := by
  native_decide

theorem decode_1420 : decode runtimeBytecode ⟨1420⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨0, by decide⟩
theorem decode_1422 : decode runtimeBytecode ⟨1422⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨1, by decide⟩
theorem decode_1423 : decode runtimeBytecode ⟨1423⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨2, by decide⟩
theorem decode_1424 : decode runtimeBytecode ⟨1424⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨3, by decide⟩
theorem decode_1425 : decode runtimeBytecode ⟨1425⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨4, by decide⟩
theorem decode_1426 : decode runtimeBytecode ⟨1426⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨5, by decide⟩
theorem decode_1427 : decode runtimeBytecode ⟨1427⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨6, by decide⟩
theorem decode_1430 : decode runtimeBytecode ⟨1430⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨7, by decide⟩
theorem decode_1431 : decode runtimeBytecode ⟨1431⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨8, by decide⟩
theorem decode_1432 : decode runtimeBytecode ⟨1432⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨9, by decide⟩
theorem decode_1433 : decode runtimeBytecode ⟨1433⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨10, by decide⟩
theorem decode_1435 : decode runtimeBytecode ⟨1435⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨11, by decide⟩
theorem decode_1436 : decode runtimeBytecode ⟨1436⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨12, by decide⟩
theorem decode_1437 : decode runtimeBytecode ⟨1437⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨13, by decide⟩
theorem decode_1438 : decode runtimeBytecode ⟨1438⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨14, by decide⟩
theorem decode_1439 : decode runtimeBytecode ⟨1439⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨15, by decide⟩
theorem decode_1440 : decode runtimeBytecode ⟨1440⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨16, by decide⟩
theorem decode_1441 : decode runtimeBytecode ⟨1441⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨17, by decide⟩
theorem decode_1442 : decode runtimeBytecode ⟨1442⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨18, by decide⟩
theorem decode_1443 : decode runtimeBytecode ⟨1443⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1858⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨19, by decide⟩
theorem decode_1446 : decode runtimeBytecode ⟨1446⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨20, by decide⟩
theorem decode_1447 : decode runtimeBytecode ⟨1447⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨21, by decide⟩
theorem decode_1448 : decode runtimeBytecode ⟨1448⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨22, by decide⟩
theorem decode_1450 : decode runtimeBytecode ⟨1450⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨23, by decide⟩
theorem decode_1451 : decode runtimeBytecode ⟨1451⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1839⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨24, by decide⟩
theorem decode_1454 : decode runtimeBytecode ⟨1454⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨25, by decide⟩
theorem decode_1455 : decode runtimeBytecode ⟨1455⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨26, by decide⟩
theorem decode_1456 : decode runtimeBytecode ⟨1456⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨27, by decide⟩
theorem decode_1458 : decode runtimeBytecode ⟨1458⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨28, by decide⟩
theorem decode_1459 : decode runtimeBytecode ⟨1459⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1820⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨29, by decide⟩
theorem decode_1462 : decode runtimeBytecode ⟨1462⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨30, by decide⟩
theorem decode_1463 : decode runtimeBytecode ⟨1463⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨31, by decide⟩
theorem decode_1464 : decode runtimeBytecode ⟨1464⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨32, by decide⟩
theorem decode_1466 : decode runtimeBytecode ⟨1466⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨33, by decide⟩
theorem decode_1467 : decode runtimeBytecode ⟨1467⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1801⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨34, by decide⟩
theorem decode_1470 : decode runtimeBytecode ⟨1470⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨35, by decide⟩
theorem decode_1471 : decode runtimeBytecode ⟨1471⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨36, by decide⟩
theorem decode_1472 : decode runtimeBytecode ⟨1472⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨37, by decide⟩
theorem decode_1474 : decode runtimeBytecode ⟨1474⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨38, by decide⟩
theorem decode_1475 : decode runtimeBytecode ⟨1475⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1782⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨39, by decide⟩
theorem decode_1478 : decode runtimeBytecode ⟨1478⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨40, by decide⟩
theorem decode_1479 : decode runtimeBytecode ⟨1479⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨41, by decide⟩
theorem decode_1480 : decode runtimeBytecode ⟨1480⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨42, by decide⟩
theorem decode_1482 : decode runtimeBytecode ⟨1482⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨43, by decide⟩
theorem decode_1483 : decode runtimeBytecode ⟨1483⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1763⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨44, by decide⟩
theorem decode_1486 : decode runtimeBytecode ⟨1486⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨45, by decide⟩
theorem decode_1487 : decode runtimeBytecode ⟨1487⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨46, by decide⟩
theorem decode_1488 : decode runtimeBytecode ⟨1488⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨47, by decide⟩
theorem decode_1490 : decode runtimeBytecode ⟨1490⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨48, by decide⟩
theorem decode_1491 : decode runtimeBytecode ⟨1491⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1744⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨49, by decide⟩
theorem decode_1494 : decode runtimeBytecode ⟨1494⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨50, by decide⟩
theorem decode_1495 : decode runtimeBytecode ⟨1495⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨51, by decide⟩
theorem decode_1496 : decode runtimeBytecode ⟨1496⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨52, by decide⟩
theorem decode_1498 : decode runtimeBytecode ⟨1498⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨53, by decide⟩
theorem decode_1499 : decode runtimeBytecode ⟨1499⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1725⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨54, by decide⟩
theorem decode_1502 : decode runtimeBytecode ⟨1502⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨55, by decide⟩
theorem decode_1503 : decode runtimeBytecode ⟨1503⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨56, by decide⟩
theorem decode_1504 : decode runtimeBytecode ⟨1504⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨57, by decide⟩
theorem decode_1506 : decode runtimeBytecode ⟨1506⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨58, by decide⟩
theorem decode_1507 : decode runtimeBytecode ⟨1507⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1706⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨59, by decide⟩
theorem decode_1510 : decode runtimeBytecode ⟨1510⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨60, by decide⟩
theorem decode_1511 : decode runtimeBytecode ⟨1511⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨61, by decide⟩
theorem decode_1512 : decode runtimeBytecode ⟨1512⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨62, by decide⟩
theorem decode_1514 : decode runtimeBytecode ⟨1514⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨63, by decide⟩
theorem decode_1515 : decode runtimeBytecode ⟨1515⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1687⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨64, by decide⟩
theorem decode_1518 : decode runtimeBytecode ⟨1518⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨65, by decide⟩
theorem decode_1519 : decode runtimeBytecode ⟨1519⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨66, by decide⟩
theorem decode_1520 : decode runtimeBytecode ⟨1520⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨67, by decide⟩
theorem decode_1521 : decode runtimeBytecode ⟨1521⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨68, by decide⟩
theorem decode_1522 : decode runtimeBytecode ⟨1522⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1668⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨69, by decide⟩
theorem decode_1525 : decode runtimeBytecode ⟨1525⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨70, by decide⟩
theorem decode_1526 : decode runtimeBytecode ⟨1526⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨71, by decide⟩
theorem decode_1527 : decode runtimeBytecode ⟨1527⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨72, by decide⟩
theorem decode_1529 : decode runtimeBytecode ⟨1529⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨73, by decide⟩
theorem decode_1530 : decode runtimeBytecode ⟨1530⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1649⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨74, by decide⟩
theorem decode_1533 : decode runtimeBytecode ⟨1533⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨75, by decide⟩
theorem decode_1534 : decode runtimeBytecode ⟨1534⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨76, by decide⟩
theorem decode_1535 : decode runtimeBytecode ⟨1535⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨77, by decide⟩
theorem decode_1537 : decode runtimeBytecode ⟨1537⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨78, by decide⟩
theorem decode_1538 : decode runtimeBytecode ⟨1538⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1630⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨79, by decide⟩
theorem decode_1541 : decode runtimeBytecode ⟨1541⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨80, by decide⟩
theorem decode_1542 : decode runtimeBytecode ⟨1542⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨81, by decide⟩
theorem decode_1543 : decode runtimeBytecode ⟨1543⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨82, by decide⟩
theorem decode_1545 : decode runtimeBytecode ⟨1545⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨83, by decide⟩
theorem decode_1546 : decode runtimeBytecode ⟨1546⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1611⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨84, by decide⟩
theorem decode_1549 : decode runtimeBytecode ⟨1549⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨85, by decide⟩
theorem decode_1550 : decode runtimeBytecode ⟨1550⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨86, by decide⟩
theorem decode_1551 : decode runtimeBytecode ⟨1551⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨87, by decide⟩
theorem decode_1553 : decode runtimeBytecode ⟨1553⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨88, by decide⟩
theorem decode_1554 : decode runtimeBytecode ⟨1554⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1592⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨89, by decide⟩
theorem decode_1557 : decode runtimeBytecode ⟨1557⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨90, by decide⟩
theorem decode_1558 : decode runtimeBytecode ⟨1558⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨91, by decide⟩
theorem decode_1560 : decode runtimeBytecode ⟨1560⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨92, by decide⟩
theorem decode_1561 : decode runtimeBytecode ⟨1561⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1574⟩, 2)) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨93, by decide⟩
theorem decode_1564 : decode runtimeBytecode ⟨1564⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨94, by decide⟩
theorem decode_1565 : decode runtimeBytecode ⟨1565⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨95, by decide⟩
theorem decode_1566 : decode runtimeBytecode ⟨1566⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨96, by decide⟩
theorem decode_1567 : decode runtimeBytecode ⟨1567⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨97, by decide⟩
theorem decode_1568 : decode runtimeBytecode ⟨1568⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨98, by decide⟩
theorem decode_1569 : decode runtimeBytecode ⟨1569⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes9] using generatedDecodes9_correct ⟨99, by decide⟩

end Ripemd160Old
