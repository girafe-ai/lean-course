import Mathlib

-- set_option maxRecDepth 10000 in
theorem ex : (List.range 10000).length = 10000 := by
  native_decide

#print axioms ex

def foo : Bool :=
  true

@[implemented_by foo]
def bar : Bool :=
  false

theorem ex2 : bar = true := by
  native_decide

theorem ex3 : bar = false := by
  rfl

theorem ex4 : False := by
  have := ex2
  have := ex3
  contradiction

theorem ex5 (P : Prop) : P := by
  exfalso
  exact ex4

#print axioms ex5
