import LayoutPrimitives
open IndependentIndices
def main : IO Unit := do
  for i in [0:136] do
    let literal := if i=0 then 0 else Data.parent[i-1]?.getD 0
    IO.println s!"{i} {parentAt i} {literal}"
