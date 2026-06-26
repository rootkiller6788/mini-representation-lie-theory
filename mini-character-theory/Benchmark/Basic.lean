/-
# MiniCharacterTheory.Benchmark.Basic

Benchmarking for character theory operations.
-/

import MiniCharacterTheory

open MiniCharacterTheory

def benchCharValueAdd (n : Nat) : IO Unit := do
  let x := CharValue.ofNat n
  let y := CharValue.ofInt (-(n : Int))
  let _ := x.add y
  IO.println s!"CharValue add {n}: OK"

#eval benchCharValueAdd 100
#eval "Benchmark.Basic complete"
