import Hex0

/-- Writes what hex0 makes of a file: `lake env lean --run experiments/Decode.lean IN OUT`. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] =>
    let bytes <- IO.FS.readBinFile input
    IO.FS.writeBinFile output (ByteArray.mk (Hex0.decode bytes.toList).toArray)
    return 0
  | _ =>
    IO.eprintln "usage: Decode INPUT OUTPUT"
    return 1
