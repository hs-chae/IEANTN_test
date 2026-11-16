/- Complete actual emitU body on the source's checked fwrite-return path.
This proves an implication from the observed external call, never an axiom
that application I/O succeeds. Partial/error writes are still modeled. -/
import SynergyHeightC.EmitUBuffer
import ScopedIO.WorldInstalled
namespace SynergyHeightC.EmitUSource
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyHeightC.EmitUStorage
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def noPure : Machine.Call := fun _ _ _=>none
def writeExpr : Expr := .call (.var "fwrite")
  [.var "words",.nat 8,.nat 8,.var "stdout"]
def checkedWrite : Stmt := .branch (.binary "!=" writeExpr (.nat 8))
  (.eval (.call (.var "fail") [])) .skip

theorem actual_body : Generated.f_emitU.body=.sequence
    (EmitUFrames.statements.take 2++[.whileLoop EmitUExpressions.guard EmitULoop.body,
      checkedWrite]) := by rfl

theorem pop_parameter (caller : State) (x : Int) :
    Machine.popScope (EmitUFrames.parameter caller x) (frame caller x 8)=
      EmitUFrames.parameter caller x := by
  simp [Machine.popScope,frame,array,EmitUFrames.parameter,Machine.allocate,List.append_assoc]
  rw [List.take_append]
  simp

theorem pop_caller (caller : State) (x : Int) :
    Machine.popScope caller (EmitUFrames.parameter caller x)=caller := by
  simp [Machine.popScope,EmitUFrames.parameter,Machine.allocate]

theorem world_seq_append {pure : Machine.Call} {service : ScopedIO.WorldIO.Call}
    {platform : ScopedIO.WorldIO.Platform} {ss tt : List Stmt}
    {s middle : ScopedIO.WorldIO.World} {out : Loops.Flow ScopedIO.WorldIO.World Value}
    (first : Loops.SeqRun (ScopedIO.WorldSource.Eval SynergyC.Header.layout pure service platform)
      (ScopedIO.WorldSource.Declare SynergyC.Header.layout pure) truth ScopedIO.WorldSource.Scope
      ss s (.continuing middle))
    (rest : Loops.SeqRun (ScopedIO.WorldSource.Eval SynergyC.Header.layout pure service platform)
      (ScopedIO.WorldSource.Declare SynergyC.Header.layout pure) truth ScopedIO.WorldSource.Scope
      tt middle out) :
    Loops.SeqRun (ScopedIO.WorldSource.Eval SynergyC.Header.layout pure service platform)
      (ScopedIO.WorldSource.Declare SynergyC.Header.layout pure) truth ScopedIO.WorldSource.Scope
      (ss++tt) s out := by
  induction ss generalizing s with
  | nil => cases first; exact rest
  | cons head tail ih =>
      cases first with
      | next hhead htail => exact Loops.SeqRun.next hhead (ih htail)

theorem write_arguments (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (caller : State) (x : Int) (stream : ScopedIO.Stream)
    (unshadowed : Machine.getVar (frame caller x 8) "stdout"=none) :
    ScopedIO.WorldSource.Arguments SynergyC.Header.layout noPure
      (ScopedIO.WorldIO.external platform fault) platform
      [.var "words",.nat 8,.nat 8,.var "stdout"]
      ⟨frame caller x 8,stream⟩ ⟨frame caller x 8,stream⟩
      [.pointer (wordsAddress caller) true,.integer ⟨⟨true,32⟩,8⟩,
        .integer ⟨⟨true,32⟩,8⟩,ScopedIO.WorldIO.stdoutValue platform] :=
  .cons (.pure (EmitUExpressions.eval_words noPure 0 caller x 8))
    (.cons (.pure (fuel:=1) rfl)
      (.cons (.pure (fuel:=1) rfl) (.cons (.stdout unshadowed) (.nil _))))

theorem checked_write_path (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (caller : State) (x : Int)
    (stream : ScopedIO.Stream) (after : ScopedIO.WorldIO.World)
    (unshadowed : Machine.getVar (frame caller x 8) "stdout"=none)
    (actual_return : ScopedIO.WorldIO.stdio platform fault "fwrite"
      [.pointer (wordsAddress caller) true,.integer ⟨⟨true,32⟩,8⟩,
        .integer ⟨⟨true,32⟩,8⟩,ScopedIO.WorldIO.stdoutValue platform]
      ⟨frame caller x 8,stream⟩=some (ScopedIO.WorldIO.unsigned64 8,after)) :
    ScopedIO.WorldSource.Run SynergyC.Header.layout noPure
      (ScopedIO.WorldIO.external platform fault) platform checkedWrite
      ⟨frame caller x 8,stream⟩ (.continuing after) := by
  have external : ScopedIO.WorldIO.external platform fault "fwrite"
      [.pointer (wordsAddress caller) true,.integer ⟨⟨true,32⟩,8⟩,
        .integer ⟨⟨true,32⟩,8⟩,ScopedIO.WorldIO.stdoutValue platform]
      ⟨frame caller x 8,stream⟩=some (ScopedIO.WorldIO.unsigned64 8,after) := by
    simpa [ScopedIO.WorldIO.external,RuntimeCore.call,RuntimeCore.binaryName] using actual_return
  have call : ScopedIO.WorldSource.Eval SynergyC.Header.layout noPure
      (ScopedIO.WorldIO.external platform fault) platform writeExpr
      ⟨frame caller x 8,stream⟩ after (ScopedIO.WorldIO.unsigned64 8) :=
    .call (write_arguments platform fault caller x stream unshadowed) external
  apply Loops.StmtRun.branch
    (ScopedIO.WorldSource.Eval.binary
      (op:="!=") ⟨by decide,by decide,by decide,by decide⟩ call
      (ScopedIO.WorldSource.Eval.pure (fuel:=1) (s:=after.app) rfl) rfl)
  exact Loops.StmtRun.skip after

theorem source_of_checked_return (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (caller : State) (x : Int)
    (hx : SynergyC.Word512.Range x) (stream : ScopedIO.Stream)
    (after : ScopedIO.WorldIO.World)
    (unshadowed : Machine.getVar (frame caller x 8) "stdout"=none)
    (actual_return : ScopedIO.WorldIO.stdio platform fault "fwrite"
      [.pointer (wordsAddress caller) true,.integer ⟨⟨true,32⟩,8⟩,
        .integer ⟨⟨true,32⟩,8⟩,ScopedIO.WorldIO.stdoutValue platform]
      ⟨frame caller x 8,stream⟩=some (ScopedIO.WorldIO.unsigned64 8,after)) :
    ScopedIO.WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform fault 1
      "emitU" [SynergyC.Word512.value x] ⟨caller,stream⟩ .unit ⟨caller,after.stream⟩ ∧
    after.stream.accepted=stream.accepted++EmitUBuffer.bytes x := by
  have outputs := EmitUBuffer.accepted_output_of_full_return
    platform fault stream caller x after actual_return
  have body : ScopedIO.WorldSource.Run SynergyC.Header.layout noPure
      (ScopedIO.WorldIO.external platform fault) platform Generated.f_emitU.body
      ⟨EmitUFrames.parameter caller x,stream⟩
      (.continuing ⟨EmitUFrames.parameter caller x,after.stream⟩) := by
    rw [actual_body]
    apply Loops.StmtRun.sequence
    · have initialization := EmitUFrames.actual_world_initialization noPure
        (ScopedIO.WorldIO.external platform fault) platform stream caller x
      have loop := EmitULoop.actual_world_loop noPure
        (ScopedIO.WorldIO.external platform fault) platform stream caller x hx
      have write := checked_write_path platform fault caller x stream after unshadowed actual_return
      exact world_seq_append initialization
        (Loops.SeqRun.next loop (Loops.SeqRun.next write (Loops.SeqRun.nil _)))
    · change (⟨EmitUFrames.parameter caller x,after.stream⟩ : ScopedIO.WorldIO.World)=
        ⟨Machine.popScope (EmitUFrames.parameter caller x) after.app,after.stream⟩
      rw [outputs.1,pop_parameter]
  have installed : Generated.f_emitU∈Bundle.code := by
    rw [Bundle.code_exact]
    simp only [Generated.functions,List.mem_cons]
    tauto
  have source := ScopedIO.WorldSource.installed_body (f:=Generated.f_emitU)
    (rank:=0) installed (pure:=noPure)
    (by intro name actual start value final h; contradiction)
    (service:=ScopedIO.WorldIO.external platform fault)
    (fun _ _ _ _ _ h=>ScopedIO.WorldSource.external_call h)
    (EmitUFrames.actual_argument hx) body
    (show ScopedIO.WorldSource.Finish SynergyC.Header.layout Generated.f_emitU
      ⟨caller,stream⟩ (.continuing ⟨EmitUFrames.parameter caller x,after.stream⟩)
      .unit ⟨caller,after.stream⟩ from ⟨rfl,rfl,by
        change (⟨caller,after.stream⟩ : ScopedIO.WorldIO.World)=
          ⟨Machine.popScope caller (EmitUFrames.parameter caller x),after.stream⟩
        rw [pop_caller]⟩)
  exact ⟨source,outputs.2⟩

#print axioms checked_write_path
#print axioms source_of_checked_return
end SynergyHeightC.EmitUSource
