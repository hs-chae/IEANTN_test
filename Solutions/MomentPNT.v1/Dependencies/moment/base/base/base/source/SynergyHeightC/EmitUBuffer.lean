/- The actual eight initialized words provide exactly the platform's buffer bytes.
The buffer is obtained from source stores; no numerical output is a platform leaf. -/
import SynergyHeightC.EmitULoop
import ScopedIO.WorldContracts
namespace SynergyHeightC.EmitUBuffer
open ScopedC ScopedC.Machine
open SynergyHeightC.EmitUStorage
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def words (x : Int) : List Nat :=
  (List.range 8).map (fun i=>(EmitUWord64.part x i).toNat)

def bytes (x : Int) : List Nat := (words x).flatMap ScopedIO.WorldIO.wordBytes

theorem initialized_word (caller : State) (x : Int) (i : Nat) (hi : i<8) :
    ScopedIO.WorldIO.readWord64 (frame caller x 8)
      {wordsAddress caller with index:=(wordsAddress caller).index+i}=
      some (EmitUWord64.part x i).toNat := by
  have range := EmitUWord64.part_range x i
  simp [ScopedIO.WorldIO.readWord64,wordsAddress,heap_shape,arrayObject,partialCells,
    List.getElem?_map,List.getElem?_range,hi,EmitUWord64.value,EmitUWord64.type,range]
  simpa using range.2

theorem actual_bytes (caller : State) (x : Int) :
    ScopedIO.WorldIO.bufferBytes (frame caller x 8) (wordsAddress caller)=some (bytes x) := by
  have collected : (List.range 8).mapM (fun i=>ScopedIO.WorldIO.readWord64 (frame caller x 8)
      {wordsAddress caller with index:=(wordsAddress caller).index+i})=some (words x) := by
    have h := initialized_word caller x
    have h0 : ScopedIO.WorldIO.readWord64 (frame caller x 8) (wordsAddress caller)=
        some (EmitUWord64.part x 0).toNat := by
      simpa using initialized_word caller x 0 (by decide)
    simp [words,List.range_succ,h,h0]
  simp only [ScopedIO.WorldIO.bufferBytes,collected,Bind.bind,Option.bind,Pure.pure,bytes]

theorem bytes_length (x : Int) : (bytes x).length=64 := by
  simp [bytes,words,List.length_flatMap,ScopedIO.WorldIO.wordBytes_length,
    Function.comp_def,List.range_succ]

theorem bytes_valid (x : Int) : ∀ b∈bytes x,b<256 := by
  intro b hb
  obtain ⟨word,_,member⟩ := List.mem_flatMap.mp hb
  exact ScopedIO.WorldIO.wordBytes_valid word b member

/-- This implication reads the actual typed buffer proved above. It does not
assume that the write succeeds or that any application output is already correct. -/
theorem accepted_output_of_full_return (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (stream : ScopedIO.Stream)
    (caller : State) (x : Int) (after : ScopedIO.WorldIO.World)
    (actual_return : ScopedIO.WorldIO.stdio platform fault "fwrite"
      [.pointer (wordsAddress caller) true,
        .integer ⟨⟨true,32⟩,8⟩,.integer ⟨⟨true,32⟩,8⟩,
        ScopedIO.WorldIO.stdoutValue platform]
      ⟨frame caller x 8,stream⟩=some (ScopedIO.WorldIO.unsigned64 8,after)) :
    after.app=frame caller x 8 ∧ after.stream.accepted=stream.accepted++bytes x := by
  exact ScopedIO.WorldIO.fwrite_full platform fault _ true _ _ _ _
    rfl rfl (ScopedIO.WorldIO.stdout_handle platform) (actual_bytes caller x) actual_return

#print axioms initialized_word
#print axioms actual_bytes
#print axioms bytes_valid
#print axioms accepted_output_of_full_return
end SynergyHeightC.EmitUBuffer
