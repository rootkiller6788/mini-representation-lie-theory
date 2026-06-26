import MiniVertexAlgebras

open MiniVertexAlgebras

def main : IO Unit := do
  IO.println "═══ MiniVertexAlgebras Smoke Test ═══"
  
  -- Test 1: Vec structure
  let v := testVec
  IO.println s!"Test 1: Vec.add 1 2 = {v.add 1 2}"
  IO.println s!"Test 1: Vec.smul 3 4 = {v.smul 3 4}"
  IO.println s!"Test 1: Vec.neg 7 = {v.neg 7}"
  assert! v.add 1 2 == 3
  assert! v.smul 3 4 == 12
  assert! v.neg 7 == -7
  
  -- Test 2: BasicVertexAlgebra stubs
  IO.println "Test 2: BasicVertexAlgebra and VertexAlgebra types defined"
  
  -- Test 3: Axiom systems
  let axioms := fundamentalTheorems
  IO.println s!"Test 3: {axioms.axioms.axioms.length} fundamental theorems registered"
  assert! axioms.axioms.axioms.length == 9
  
  -- Test 4: Minimal models
  IO.println s!"Test 4: Ising model central charge = {isingModel.centralCharge}"
  assert! isingModel.centralCharge == 1/2
  
  IO.println "═══ All smoke tests passed ═══"
  IO.println ""
  
where
  assert! (cond : Bool) : IO Unit :=
    if cond then IO.println "  PASS" else IO.println "  FAIL" *> panic! "Assertion failed"
