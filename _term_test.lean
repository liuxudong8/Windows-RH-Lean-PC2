def f : Nat → Nat :=
  fun n => if n = 0 then 0 else f (n - 1)
termination_by n => n

#eval f 1000000
