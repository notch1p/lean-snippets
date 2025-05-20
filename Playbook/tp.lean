def prog : IO Unit := do
  {                             let i := 1
; IO.println i
  }

def prog' : IO Unit := do
  let i := 1
  IO.println i
