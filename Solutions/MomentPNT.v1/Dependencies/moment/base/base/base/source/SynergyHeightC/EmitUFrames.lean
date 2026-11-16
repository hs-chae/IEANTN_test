/- Actual emitU parameter and array initialization. The eight output words
remain indeterminate here until the actual source loop is proved. -/
import SynergyHeightC.Bundle
import SynergyC.Word512
import ScopedC.TypedFrameBasic
import ScopedIO.WorldLift
namespace SynergyHeightC.EmitUFrames
open ScopedC ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def statements : List Stmt := match Generated.f_emitU.body with
  | .sequence ss => ss
  | _ => []
def wordsDecl : Decl := {type:="uint64_t",name:="words",value:=none,arrayExtent:=some 8}
def indexDecl : Decl := {type:="unsigned int",name:="i",value:=some (.nat 0)}

def parameter (caller : State) (x : Int) : State :=
  allocate {caller with env:=[]} "U" "x" (some (SynergyC.Word512.value x))
def words (caller : State) (x : Int) : State :=
  ArrayDeclarations.allocateArray (parameter caller x) "uint64_t" "words" 8
def initial (caller : State) (x : Int) : State :=
  allocate (words caller x) "unsigned int" "i" (some (.integer ⟨⟨false,32⟩,0⟩))

theorem actual_initial_declarations : statements.take 2=
    [.declare [wordsDecl],.declare [indexDecl]] := by rfl

theorem actual_argument {caller : State} {x : Int} (hx : SynergyC.Word512.Range x) :
    bindArgs SynergyC.Header.layout Generated.f_emitU.parameters [SynergyC.Word512.value x] caller=
      some (parameter caller x) := by
  exact TypedFrames.bind_one SynergyC.Header.layout caller "U" "x" _ _
    (SynergyC.Word512.cast_word {caller with env:=[]} hx)

theorem declare_words (call : Machine.Call) (caller : State) (x : Int) :
    ArrayDeclarations.declarations SynergyC.Header.layout call [wordsDecl] (parameter caller x)=
      some (words caller x) := by rfl

theorem declare_index (call : Machine.Call) (caller : State) (x : Int) :
    ArrayDeclarations.declarations SynergyC.Header.layout call [indexDecl] (words caller x)=
      some (initial caller x) := by rfl

theorem actual_initial_execution (call : Machine.Call) (caller : State) (x : Int) :
    ArraySourceExecute.statements SynergyC.Header.layout call 128 2048 (statements.take 2)
      (parameter caller x)=some (.continuing (initial caller x)) := by rfl

/-- The actual array storage is allocated before any output write; no
initialized application buffer is postulated by the stdio platform contract. -/
theorem actual_world_initialization (pure : Machine.Call) (call : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (stream : ScopedIO.Stream) (caller : State) (x : Int) :
    Loops.SeqRun (ScopedIO.WorldSource.Eval SynergyC.Header.layout pure call platform)
      (ScopedIO.WorldSource.Declare SynergyC.Header.layout pure) truth ScopedIO.WorldSource.Scope
      (statements.take 2) ⟨parameter caller x,stream⟩ (.continuing ⟨initial caller x,stream⟩) :=
  (ScopedIO.WorldLift.pure_sound SynergyC.Header.layout pure call platform stream 128 2048).2.1
    (statements.take 2) (parameter caller x) (.continuing (initial caller x))
      (actual_initial_execution pure caller x)

#print axioms actual_argument
#print axioms actual_initial_declarations
#print axioms actual_world_initialization
end SynergyHeightC.EmitUFrames
