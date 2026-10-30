import AffineWordLog
import Lean

open Lean Elab Command in
run_cmd do
  let found := (← liftCoreM <| Lean.collectAxioms ``AffineWordLog.realIntervalDuality).toList
  let expected := [``propext, ``Classical.choice, ``Quot.sound]
  unless found.toArray.qsort Name.lt == expected.toArray.qsort Name.lt do
    throwError m!"Unexpected axiom dependencies: {found}"

#print axioms AffineWordLog.realIntervalDuality
