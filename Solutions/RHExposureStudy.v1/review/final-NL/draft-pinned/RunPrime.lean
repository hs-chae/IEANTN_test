import PrimeSieveExec
def main (args : List String) : IO Unit := do
  let xs := if args.isEmpty then [38358837682, 14111427770] else args.filterMap String.toNat?
  for n in xs do
    IO.println s!"count({n}) = {LocalPrimeSieve.count n}"
