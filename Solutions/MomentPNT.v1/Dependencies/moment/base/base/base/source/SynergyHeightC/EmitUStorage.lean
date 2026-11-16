/- Concrete source-owned emitU local array and index frames. Only the
loop's proved stores may turn the initially indeterminate cells into parts. -/
import SynergyHeightC.EmitUWord64
namespace SynergyHeightC.EmitUStorage
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def partialCells (x : Int) (i : Nat) : List (Option Value) :=
  (List.range 8).map (fun j => if j < i then some (EmitUWord64.value (EmitUWord64.part x j)) else none)

def arrayObject (x : Int) (i : Nat) : Object :=
  {type:="uint64_t",cells:=partialCells x i,isArray:=true}

def array (caller : State) (x : Int) (i : Nat) : State :=
  {EmitUFrames.parameter caller x with
    heap:=(EmitUFrames.parameter caller x).heap++[arrayObject x i]
    env:=("words",⟨caller.heap.length+1,0,[]⟩)::(EmitUFrames.parameter caller x).env}

def frame (caller : State) (x : Int) (i : Nat) : State :=
  allocate (array caller x i) "unsigned int" "i" (some (.integer ⟨⟨false,32⟩,(i:Int)⟩))

def xAddress (caller : State) : Address := ⟨caller.heap.length,0,[]⟩
def wordsAddress (caller : State) : Address := ⟨caller.heap.length+1,0,[]⟩
def iAddress (caller : State) : Address := ⟨caller.heap.length+2,0,[]⟩

theorem partial_length (x : Int) (i : Nat) : (partialCells x i).length=8 := by
  simp [partialCells]

theorem first_frame (caller : State) (x : Int) : frame caller x 0=EmitUFrames.initial caller x := by
  simp [frame,array,arrayObject,EmitUFrames.initial,EmitUFrames.words,ArrayDeclarations.allocateArray,
    EmitUFrames.parameter,Machine.allocate,partialCells,List.append_assoc]

theorem full_cells (x : Int) : partialCells x 8=EmitUWord64.cells x := by rfl

theorem heap_shape (caller : State) (x : Int) (i : Nat) :
    (frame caller x i).heap=caller.heap++[
      {type:="U",cells:=[some (SynergyC.Word512.value x)]},arrayObject x i,
      {type:="unsigned int",cells:=[some (.integer ⟨⟨false,32⟩,(i:Int)⟩)]}] := by
  simp [frame,array,EmitUFrames.parameter,Machine.allocate,List.append_assoc]

theorem env_shape (caller : State) (x : Int) (i : Nat) :
    (frame caller x i).env=[("i",iAddress caller),("words",wordsAddress caller),("x",xAddress caller)] := by
  simp [frame,array,EmitUFrames.parameter,Machine.allocate,iAddress,wordsAddress,xAddress,List.length_append]

theorem get_x (caller : State) (x : Int) (i : Nat) :
    Machine.getVar (frame caller x i) "x"=some (xAddress caller) := by
  simp [Machine.getVar,env_shape,List.lookup]

theorem get_words (caller : State) (x : Int) (i : Nat) :
    Machine.getVar (frame caller x i) "words"=some (wordsAddress caller) := by
  simp [Machine.getVar,env_shape,List.lookup]

theorem get_i (caller : State) (x : Int) (i : Nat) :
    Machine.getVar (frame caller x i) "i"=some (iAddress caller) := by
  simp [Machine.getVar,env_shape,List.lookup]

theorem read_x (caller : State) (x : Int) (i : Nat) :
    Machine.read SynergyC.Header.layout (frame caller x i) (xAddress caller)=
      some (SynergyC.Word512.value x) := by
  simp [Machine.read,xAddress,heap_shape,Machine.nested,Machine.initialized,SynergyC.Word512.value]

theorem read_i (caller : State) (x : Int) (i : Nat) :
    Machine.read SynergyC.Header.layout (frame caller x i) (iAddress caller)=
      some (.integer ⟨⟨false,32⟩,(i:Int)⟩) := by
  simp [Machine.read,iAddress,heap_shape,Machine.nested,Machine.initialized]

#print axioms first_frame
#print axioms full_cells
#print axioms get_x
#print axioms read_x
#print axioms read_i
end SynergyHeightC.EmitUStorage
