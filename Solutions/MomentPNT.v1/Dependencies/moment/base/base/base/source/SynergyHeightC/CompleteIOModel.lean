/- A concrete standard-I/O model scenario, not a trusted host-success fact.
The actual emitter service still executes source-proved buffers and checks all
returns. Concrete host/source/build/run association remains a separate receipt. -/
import SynergyHeightC.MainWorldFlush
namespace SynergyHeightC.CompleteIOModel
open ScopedC ScopedC.Machine ScopedNumerical ScopedIO
open SynergyHeightC.EmitUStorage
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

def policy : WorldIO.FaultPolicy := {
  succeed:=fun _ _=>true
  count:=fun _ _=>0}

def appendWord (stream : Stream) (x : Int) : Stream :=
  {stream with accepted:=stream.accepted++EmitUBuffer.bytes x}

theorem frame_stdout (caller : State) (x : Int) (i : Nat) :
    Machine.getVar (frame caller x i) "stdout"=caller.globals.lookup "stdout" := by
  simp [Machine.getVar,env_shape,frame,array,EmitUFrames.parameter,Machine.allocate,List.lookup]

theorem invoke_success (platform : WorldIO.Platform) (caller : State) (x : Int)
    (stream : Stream) (stdout : caller.globals.lookup "stdout"=none) :
    EmitUService.invoke platform policy x ⟨caller,stream⟩=
      some (.unit,⟨caller,appendWord stream x⟩) := by
  have unshadowed : Machine.getVar (frame caller x 8) "stdout"=none := by
    rw [frame_stdout,stdout]
  have io := WorldIO.fwrite_equation platform policy
    (⟨frame caller x 8,stream⟩ : WorldIO.World) (wordsAddress caller) true
    (.integer ⟨⟨true,32⟩,8⟩) (.integer ⟨⟨true,32⟩,8⟩)
    (WorldIO.stdoutValue platform) (EmitUBuffer.bytes x) rfl rfl
    (WorldIO.stdout_handle platform) (EmitUBuffer.actual_bytes caller x)
  unfold EmitUService.invoke
  simp only [unshadowed,ne_eq,not_true_eq_false,↓reduceIte,EmitUService.arguments]
  rw [io]
  rfl

theorem emitU_success (platform : WorldIO.Platform) (caller : State) (x : Int)
    (range : SynergyC.Word512.Range x) (stream : Stream)
    (stdout : caller.globals.lookup "stdout"=none) :
    EmitUService.call platform policy "emitU" [SynergyC.Word512.value x] ⟨caller,stream⟩=
      some (.unit,⟨caller,appendWord stream x⟩) :=
  (EmitISource.call_word platform policy x range ⟨caller,stream⟩).trans
    (invoke_success platform caller x stream stdout)

theorem emitI_frame_stdout (caller : State) (box : ProofBox) :
    (EmitISource.frame caller box).globals.lookup "stdout"=caller.globals.lookup "stdout" := by rfl

theorem emitI_success (platform : WorldIO.Platform) (caller : State) (box : ProofBox)
    (range : SynergyC.SourceIntervalMath.representable box) (stream : Stream)
    (stdout : caller.globals.lookup "stdout"=none) :
    EmitIService.call platform policy "emitI" [SynergyC.SourceIntervalMath.represented box]
      ⟨caller,stream⟩=some (.unit,⟨caller,appendWord (appendWord stream box.lo) box.hi⟩) := by
  rw [MainTotalOutput.call_represented platform policy box range.1 range.2]
  unfold EmitIService.invoke
  rw [emitU_success platform (EmitISource.frame caller box) box.lo range.1 stream
    (by rw [emitI_frame_stdout,stdout])]
  simp only [EmitIService.unitResult,StateWordEquality.valueEq,↓reduceIte,Bind.bind,Option.bind]
  rw [emitU_success platform (EmitISource.frame caller box) box.hi range.2
    (appendWord stream box.lo) (by rw [emitI_frame_stdout,stdout])]
  rfl

theorem flush_success (platform : WorldIO.Platform) (world : WorldIO.World) :
    WorldIO.stdio platform policy "fflush" [WorldIO.stdoutValue platform] world=
      some (WorldIO.signed32 0,
        ⟨world.app,{world.stream with delivered:=world.stream.accepted.length}⟩) := by
  rw [WorldIO.fflush_equation platform policy world _ (WorldIO.stdout_handle platform)]
  rfl

#print axioms frame_stdout
#print axioms invoke_success
#print axioms emitU_success
#print axioms emitI_success
#print axioms flush_success
end SynergyHeightC.CompleteIOModel
