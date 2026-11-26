import GoldbachDirect.Memory

namespace GoldbachDirect.Semantics
open GoldbachDirect

inductive External where
  | malloc | calloc | free | cudaSetDevice | cudaDeviceGetAttribute | cudaMalloc | cudaFree
  | cudaStreamCreateWithFlags | cudaStreamDestroy | cudaMemcpy | cudaDeviceSynchronize
  | cudaGetLastError | cudaStreamSynchronize | atomicOr
  | printf | fflush | fopen | fwrite | fclose | exitProcess
  deriving Repr, DecidableEq

def External.name : External → String
  | .malloc => "malloc" | .calloc => "calloc" | .free => "free"
  | .cudaSetDevice => "cudaSetDevice" | .cudaDeviceGetAttribute => "cudaDeviceGetAttribute"
  | .cudaMalloc => "cudaMalloc" | .cudaFree => "cudaFree"
  | .cudaStreamCreateWithFlags => "cudaStreamCreateWithFlags" | .cudaStreamDestroy => "cudaStreamDestroy"
  | .cudaMemcpy => "cudaMemcpy" | .cudaDeviceSynchronize => "cudaDeviceSynchronize"
  | .cudaGetLastError => "cudaGetLastError" | .cudaStreamSynchronize => "cudaStreamSynchronize"
  | .atomicOr => "atomicOr" | .printf => "printf" | .fflush => "fflush"
  | .fopen => "fopen" | .fwrite => "fwrite" | .fclose => "fclose" | .exitProcess => "_Exit"

inductive Primitive where
  | call (name : External)
  | launch (kernel : Function)

inductive CallResult where
  | value (value : Value)
  | terminated (status : Int)

abbrev Foreign (F : Type) := Primitive → List Value → State F → CallResult → State F → Prop

/-- Header constants and CUDA special registers are individual source/ABI data.
Own function bodies are never looked up in Foreign: calls resolve Program first. -/
structure Context (F : Type) where
  program : Program
  foreign : Foreign F
  headerConstant : String → Option Value
  builtin : String → String → Option Value

def findFunction (program : Program) (name : String) : Option Function :=
  program.findSome? (fun top => match top with
    | .function f => if f.name = name then some f else none | _ => none)

def constantName (name : String) : Prop := name ∈ ["NULL","cudaSuccess","cudaStreamNonBlocking",
  "cudaMemcpyHostToDevice","cudaMemcpyDeviceToHost","cudaDevAttrMaxThreadsPerBlock",
  "cudaDevAttrMaxGridDimX","stdout"]

def builtinName (name field : String) : Prop :=
  name ∈ ["blockIdx","blockDim","threadIdx","gridDim"] ∧ field ∈ ["x","y","z"]

def binary (state : State F) (op : Binary) (left right : Value) : Option Value :=
  match left,right with
  | .integer a,.integer b => (Integer.binary op a b).map Value.integer
  | .pointer a,.integer b =>
    match op with
    | .add => (state.pointerAdd a b.toInt).map Value.pointer
    | .sub => (state.pointerAdd a (-b.toInt)).map Value.pointer
    | .eq => if b.toInt = 0 then some (.integer (.boolean false)) else none
    | .ne => if b.toInt = 0 then some (.integer (.boolean true)) else none
    | _ => none
  | .integer a,.pointer b =>
    match op with
    | .add => (state.pointerAdd b a.toInt).map Value.pointer
    | .eq => if a.toInt = 0 then some (.integer (.boolean false)) else none
    | .ne => if a.toInt = 0 then some (.integer (.boolean true)) else none
    | _ => none
  | .pointer a,.pointer b =>
    match op with
    | .eq => some (.integer (.boolean (a.object = b.object && a.offset = b.offset)))
    | .ne => some (.integer (.boolean (!(a.object = b.object && a.offset = b.offset))))
    | _ => none
  | .null,.null => match op with
    | .eq => some (.integer (.boolean true)) | .ne => some (.integer (.boolean false)) | _ => none
  | .pointer _,.null | .null,.pointer _ => match op with
    | .eq => some (.integer (.boolean false)) | .ne => some (.integer (.boolean true)) | _ => none
  | _,_ => none

/-- Parameter declarations allocate addressable automatic cells and perform the
ordinary declared conversions; out parameters therefore refer to real caller cells. -/
def bindParameters : State F → List (CType × String) → List Value → Option (State F)
  | state,[],[] => some state
  | state,(type,name)::parameters,value::values => do
    let next ← state.declare type name (some value)
    bindParameters next parameters values
  | _,_,_ => none

inductive Flow where
  | normal | returned (value : Value) | broke | continued | jumped (label : String)
  | terminated (status : Int)

def labelTail (label : String) : List Stmt → Option (List Stmt)
  | [] => none
  | .label name::rest => if name = label then some rest else labelTail label rest
  | _::rest => labelTail label rest

mutual
  inductive Eval (context : Context F) : State F → Expr → Value → State F → Prop where
    | literal (value : Literal) (before : State F) (result : Value)
        (valid : value.value = some result) : Eval context before (.literal value) result before
    | paren (run : Eval context before expression value after) :
        Eval context before (.paren expression) value after
    | variable (present : before.environment.lookup name = some pointer)
        (read : before.load pointer = some value) :
        Eval context before (.variable name) value before
    | constant (absent : before.environment.lookup name = none) (allowed : constantName name)
        (read : context.headerConstant name = some value) :
        Eval context before (.variable name) value before
    | builtin (allowed : builtinName name field) (read : context.builtin name field = some value) :
        Eval context before (.member (.variable name) field false) value before
    | address (place : Place context before expression pointer after) :
        Eval context before (.unary .address expression) (.pointer pointer) after
    | load (place : Place context before expression pointer after)
        (read : after.load pointer = some value) :
        Eval context before expression value after
    | cast (run : Eval context before expression value after)
        (converted : value.convert type = some result) :
        Eval context before (.cast type expression) result after
    | unary (run : Eval context before expression (.integer value) after)
        (computed : Integer.unary op value = some result) :
        Eval context before (.unary op expression) (.integer result) after
    | binaryLR (leftRun : Eval context before left a middle)
        (rightRun : Eval context middle right b after) (computed : binary after op a b = some result) :
        Eval context before (.binary op left right) result after
    | binaryRL (rightRun : Eval context before right b middle)
        (leftRun : Eval context middle left a after) (computed : binary after op a b = some result) :
        Eval context before (.binary op left right) result after
    | andFalse (leftRun : Eval context before left a after) (test : a.truth = some false) :
        Eval context before (.binary .logicalAnd left right) (.integer (.boolean false)) after
    | andTrue (leftRun : Eval context before left a middle) (test : a.truth = some true)
        (rightRun : Eval context middle right b after) (result : b.truth = some value) :
        Eval context before (.binary .logicalAnd left right) (.integer (.boolean value)) after
    | orTrue (leftRun : Eval context before left a after) (test : a.truth = some true) :
        Eval context before (.binary .logicalOr left right) (.integer (.boolean true)) after
    | orFalse (leftRun : Eval context before left a middle) (test : a.truth = some false)
        (rightRun : Eval context middle right b after) (result : b.truth = some value) :
        Eval context before (.binary .logicalOr left right) (.integer (.boolean value)) after
    | conditionalTrue (condition : Eval context before test value middle) (truth : value.truth = some true)
        (yesRun : Eval context middle yes result after) :
        Eval context before (.conditional test yes no) result after
    | conditionalFalse (condition : Eval context before test value middle) (truth : value.truth = some false)
        (noRun : Eval context middle no result after) :
        Eval context before (.conditional test yes no) result after
    | call (arguments : Args context before expressions values middle)
        (called : Call context name values middle (.value result) after) :
        Eval context before (.call name expressions) result after

  inductive Place (context : Context F) : State F → Expr → Pointer → State F → Prop where
    | variable (present : before.environment.lookup name = some pointer) :
        Place context before (.variable name) pointer before
    | paren (place : Place context before expression pointer after) :
        Place context before (.paren expression) pointer after
    | dereference (run : Eval context before expression (.pointer pointer) after) :
        Place context before (.unary .dereference expression) pointer after
    | index (baseRun : Eval context before base (.pointer pointer) middle)
        (indexRun : Eval context middle index (.integer offset) after)
        (added : after.pointerAdd pointer offset.toInt = some result) :
        Place context before (.index base index) result after

  inductive ArgSequence (context : Context F) :
      State F → List (Nat × Expr) → List (Nat × Value) → State F → Prop where
    | nil : ArgSequence context state [] [] state
    | cons (run : Eval context before expression value middle)
        (rest : ArgSequence context middle expressions values after) :
        ArgSequence context before ((index,expression)::expressions) ((index,value)::values) after

  /-- Every C++-permitted argument order is represented, preserving source argument
  positions. An extraction cannot assume stateful arguments always run left-to-right. -/
  inductive Args (context : Context F) : State F → List Expr → List Value → State F → Prop where
    | ordered (permutation : order.Perm ((List.range expressions.length).zip expressions))
        (run : ArgSequence context before order evaluated after)
        (positions : List.Forall₂ (fun index value => evaluated.lookup index = some value)
          (List.range expressions.length) values) : Args context before expressions values after

  inductive Exec (context : Context F) : State F → Stmt → Flow → State F → Prop where
    | block (entered : start = before.enterScope)
        (bodyRun : ExecList context start body flow middle)
        (finished : after = {middle.leaveScope start.scope before.environment with scope := before.scope}) :
        Exec context before (.block body) flow after
    | declareNone (declared : before.declare type name none = some after) :
        Exec context before (.declare type name none) .normal after
    | declareSome (run : Eval context before expression value middle)
        (declared : middle.declare type name (some value) = some after) :
        Exec context before (.declare type name (some expression)) .normal after
    | assign (right : Eval context before expression value middle)
        (left : Place context middle destination pointer assigned)
        (stored : assigned.store pointer value = some after) :
        Exec context before (.assign destination expression) .normal after
    | assignOp (right : Eval context before expression b middle)
        (left : Place context middle destination pointer assigned) (old : assigned.load pointer = some a)
        (computed : binary assigned op a b = some value) (stored : assigned.store pointer value = some after) :
        Exec context before (.assignOp op destination expression) .normal after
    | expression (run : Eval context before expression value after) :
        Exec context before (.expression expression) .normal after
    | callTerminated (arguments : Args context before expressions values middle)
        (called : Call context name values middle (.terminated status) after) :
        Exec context before (.expression (.call name expressions)) (.terminated status) after
    | ifTrue (testRun : Eval context before condition value middle) (test : value.truth = some true)
        (bodyRun : Exec context middle yes flow after) :
        Exec context before (.ite condition yes no) flow after
    | ifFalse (testRun : Eval context before condition value after) (test : value.truth = some false) :
        Exec context before (.ite condition yes none) .normal after
    | ifElse (testRun : Eval context before condition value middle) (test : value.truth = some false)
        (bodyRun : Exec context middle no flow after) :
        Exec context before (.ite condition yes (some no)) flow after
    | whileFalse (testRun : Eval context before condition value after) (test : value.truth = some false) :
        Exec context before (.whileLoop condition body) .normal after
    | whileNext (testRun : Eval context before condition value tested) (test : value.truth = some true)
        (bodyRun : Exec context tested body .normal middle)
        (rest : Exec context middle (.whileLoop condition body) flow after) :
        Exec context before (.whileLoop condition body) flow after
    | whileContinue (testRun : Eval context before condition value tested) (test : value.truth = some true)
        (bodyRun : Exec context tested body .continued middle)
        (rest : Exec context middle (.whileLoop condition body) flow after) :
        Exec context before (.whileLoop condition body) flow after
    | whileBreak (testRun : Eval context before condition value tested) (test : value.truth = some true)
        (bodyRun : Exec context tested body .broke after) :
        Exec context before (.whileLoop condition body) .normal after
    | whileExit (testRun : Eval context before condition value tested) (test : value.truth = some true)
        (bodyRun : Exec context tested body flow after)
        (abrupt : flow ≠ .normal ∧ flow ≠ .broke ∧ flow ≠ .continued) :
        Exec context before (.whileLoop condition body) flow after
    | returnNone : Exec context state (.returnValue none) (.returned .unit) state
    | returnSome (run : Eval context before expression value after) :
        Exec context before (.returnValue (some expression)) (.returned value) after
    | breakLoop : Exec context state .breakLoop .broke state
    | continueLoop : Exec context state .continueLoop .continued state
    | label : Exec context state (.label name) .normal state
    | gotoLabel : Exec context state (.gotoLabel name) (.jumped name) state
    | launch (selected : findFunction context.program name = some kernel)
        (arguments : Args context before [grid,block,shared,stream] config configured)
        (operands : Args context configured expressions values middle)
        (called : context.foreign (.launch kernel) (config++values) middle (.value .unit) after) :
        Exec context before (.launch name grid block shared stream expressions) .normal after

  inductive ExecList (context : Context F) : State F → List Stmt → Flow → State F → Prop where
    | nil : ExecList context state [] .normal state
    | cons (first : Exec context before statement .normal middle)
        (rest : ExecList context middle statements flow after) :
        ExecList context before (statement::statements) flow after
    | abrupt (first : Exec context before statement flow after) (abrupt : flow ≠ .normal) :
        ExecList context before (statement::statements) flow after

  /-- Labels belong to the actual function body. A goto resumes its exact suffix
  without destroying the function's locals or assuming the cleanup postcondition. -/
  inductive Body (context : Context F) :
      List Stmt → State F → List Stmt → Flow → State F → Prop where
    | finish (run : ExecList context before statements flow after)
        (finished : ∀ label, flow ≠ .jumped label) : Body context whole before statements flow after
    | jump (run : ExecList context before statements (.jumped label) middle)
        (target : labelTail label whole = some suffix)
        (tail : Body context whole middle suffix flow after) :
        Body context whole before statements flow after

  inductive Call (context : Context F) :
      String → List Value → State F → CallResult → State F → Prop where
    | external (absent : findFunction context.program name = none)
        (named : external.name = name)
        (run : context.foreign (.call external) values before result after) :
        Call context name values before result after
    | internal (selected : findFunction context.program name = some function)
        (shape : function.body = .block statements)
        (parameters : bindParameters {before.enterScope with environment := []}
          function.parameters values = some entered)
        (run : Body context statements entered statements (.returned value) middle)
        (converted : Value.convert function.result value = some result)
        (finished : after = {middle.leaveScope entered.scope before.environment with scope := before.scope}) :
        Call context name values before (.value result) after
    | internalVoid (selected : findFunction context.program name = some function)
        (shape : function.body = .block statements) (void : function.result = .void)
        (parameters : bindParameters {before.enterScope with environment := []}
          function.parameters values = some entered)
        (run : Body context statements entered statements .normal middle)
        (finished : after = {middle.leaveScope entered.scope before.environment with scope := before.scope}) :
        Call context name values before (.value .unit) after
    | internalTerminated (selected : findFunction context.program name = some function)
        (shape : function.body = .block statements)
        (parameters : bindParameters {before.enterScope with environment := []}
          function.parameters values = some entered)
        (run : Body context statements entered statements (.terminated status) after) :
        Call context name values before (.terminated status) after
end

/-- Generic selected-source execution. No prime/bitmap/witness/Goldbach fact is a
constructor. Source identity and well-formedness are supplied by a checked file
certificate, and own helper calls resolve the very same program internally. -/
def SourceExec (context : Context F) (arguments : List Value) (before : State F)
    (status : Integer) (after : State F) : Prop :=
  Call context "main" arguments before (.value (.integer status)) after

end GoldbachDirect.Semantics
