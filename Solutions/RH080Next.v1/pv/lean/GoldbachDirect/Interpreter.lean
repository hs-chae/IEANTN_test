import GoldbachDirect.InterpreterArgs

/-! A fuel-bounded, certifying interpreter for the actual source AST. It chooses
one permitted operand order, interprets own functions internally, and rejects
unsupported/faulting/fuel-exhausted executions. Every returned result carries
an existing operational-semantics proof. Only individual external calls use a
callback, itself required to return a proof about the same call and state.
No callback or interpreter branch mentions application correctness. -/
namespace GoldbachDirect.Interpreter
open Semantics
open SourcePure

abbrev PrimitiveExecutor (context : Context F) :=
  (primitive : Primitive) → (arguments : List Value) → (before : State F) →
    Option {out : CallResult × State F // context.foreign primitive arguments before out.1 out.2}

abbrev Evaluated (context : Context F) (before : State F) (expression : Expr) :=
  {out : Value × State F // Eval context before expression out.1 out.2}
abbrev Located (context : Context F) (before : State F) (expression : Expr) :=
  {out : Pointer × State F // Place context before expression out.1 out.2}
abbrev Executed (context : Context F) (before : State F) (statement : Stmt) :=
  {out : Flow × State F // Exec context before statement out.1 out.2}
abbrev Listed (context : Context F) (before : State F) (statements : List Stmt) :=
  {out : Flow × State F // ExecList context before statements out.1 out.2}
abbrev Bodied (context : Context F) (whole : List Stmt) (before : State F) (statements : List Stmt) :=
  {out : Flow × State F // Body context whole before statements out.1 out.2}
abbrev Called (context : Context F) (name : String) (arguments : List Value) (before : State F) :=
  {out : CallResult × State F // Call context name arguments before out.1 out.2}

abbrev Sequenced (context : Context F) (start : Nat) (before : State F) (expressions : List Expr) :=
  {out : List Value × State F // out.1.length = expressions.length ∧
    ArgSequence context before (numbered start expressions) (numbered start out.1) out.2}

def externalNames : List External := [.malloc,.calloc,.free,.cudaSetDevice,
  .cudaDeviceGetAttribute,.cudaMalloc,.cudaFree,.cudaStreamCreateWithFlags,.cudaStreamDestroy,
  .cudaMemcpy,.cudaDeviceSynchronize,.cudaGetLastError,.cudaStreamSynchronize,.atomicOr,
  .printf,.fflush,.fopen,.fwrite,.fclose,.exitProcess]

def externalNamed (name : String) : Option {external : External // external.name = name} :=
  externalNames.attach.findSome? (fun external =>
    if same : external.val.name = name then some ⟨external.val,same⟩ else none)

mutual
  def evaluate (fuel : Nat) (context : Context F) (primitive : PrimitiveExecutor context)
      (before : State F) (expression : Expr) : Option (Evaluated context before expression) :=
    match fuel with
    | 0 => none
    | fuel+1 =>
      if closed : CallFree expression then
        match computed : PureEval.eval context before expression with
        | none => none
        | some value => some ⟨(value,before),PureEval.eval_complete closed computed⟩
      else match expression with
      | .paren expression => do
        let out ← evaluate fuel context primitive before expression
        return ⟨out.val,.paren out.property⟩
      | .cast type expression => do
        let out ← evaluate fuel context primitive before expression
        match converted : out.val.1.convert type with
        | none => none
        | some value => return ⟨(value,out.val.2),.cast out.property converted⟩
      | .unary .address expression => do
        let out ← locate fuel context primitive before expression
        return ⟨(.pointer out.val.1,out.val.2),.address out.property⟩
      | .unary .dereference expression => do
        let out ← locate fuel context primitive before (.unary .dereference expression)
        match read : out.val.2.load out.val.1 with
        | none => none
        | some value => return ⟨(value,out.val.2),.load out.property read⟩
      | .unary op expression => do
        let out ← evaluate fuel context primitive before expression
        match valueIs : out.val.1 with
        | .integer value =>
          match computed : Integer.unary op value with
          | none => none
          | some result =>
            return ⟨(.integer result,out.val.2),.unary (valueIs ▸ out.property) computed⟩
        | _ => none
      | .binary .logicalAnd left right => do
        let a ← evaluate fuel context primitive before left
        match tested : a.val.1.truth with
        | none => none
        | some false => return ⟨(.integer (.boolean false),a.val.2),.andFalse a.property tested⟩
        | some true => do
          let b ← evaluate fuel context primitive a.val.2 right
          match result : b.val.1.truth with
          | none => none
          | some truth => return ⟨(.integer (.boolean truth),b.val.2),.andTrue a.property tested b.property result⟩
      | .binary .logicalOr left right => do
        let a ← evaluate fuel context primitive before left
        match tested : a.val.1.truth with
        | none => none
        | some true => return ⟨(.integer (.boolean true),a.val.2),.orTrue a.property tested⟩
        | some false => do
          let b ← evaluate fuel context primitive a.val.2 right
          match result : b.val.1.truth with
          | none => none
          | some truth => return ⟨(.integer (.boolean truth),b.val.2),.orFalse a.property tested b.property result⟩
      | .binary op left right => do
        let a ← evaluate fuel context primitive before left
        let b ← evaluate fuel context primitive a.val.2 right
        match computed : binary b.val.2 op a.val.1 b.val.1 with
        | none => none
        | some result => return ⟨(result,b.val.2),.binaryLR a.property b.property computed⟩
      | .index base offset => do
        let out ← locate fuel context primitive before (.index base offset)
        match read : out.val.2.load out.val.1 with
        | none => none
        | some value => return ⟨(value,out.val.2),.load out.property read⟩
      | .conditional test yes no => do
        let tested ← evaluate fuel context primitive before test
        match truth : tested.val.1.truth with
        | none => none
        | some true => do
          let branch ← evaluate fuel context primitive tested.val.2 yes
          return ⟨branch.val,.conditionalTrue tested.property truth branch.property⟩
        | some false => do
          let branch ← evaluate fuel context primitive tested.val.2 no
          return ⟨branch.val,.conditionalFalse tested.property truth branch.property⟩
      | .call name expressions => do
        let values ← evaluateArguments fuel context primitive 0 before expressions
        let out ← invoke fuel context primitive name values.val.1 values.val.2
        match resultIs : out.val.1 with
        | .value value =>
          return ⟨(value,out.val.2),.call (numbered_arguments values.property.1 values.property.2) (resultIs ▸ out.property)⟩
        | .terminated _ => none
      | _ => none

  def evaluateArguments (fuel : Nat) (context : Context F) (primitive : PrimitiveExecutor context)
      (start : Nat) (before : State F) (expressions : List Expr) :
      Option (Sequenced context start before expressions) :=
    match fuel with
    | 0 => none
    | fuel+1 => match expressions with
      | [] => some ⟨([],before),rfl,.nil⟩
      | expression :: rest => do
        let first ← evaluate fuel context primitive before expression
        let tail ← evaluateArguments fuel context primitive (start+1) first.val.2 rest
        return ⟨(first.val.1 :: tail.val.1,tail.val.2),
          by simpa using congrArg Nat.succ tail.property.1,
          by simpa only [numbered] using ArgSequence.cons first.property tail.property.2⟩

  def locate (fuel : Nat) (context : Context F) (primitive : PrimitiveExecutor context)
      (before : State F) (expression : Expr) : Option (Located context before expression) :=
    match fuel with
    | 0 => none
    | fuel+1 => match expression with
      | .variable name =>
        match found : before.environment.lookup name with
        | none => none
        | some pointer => some ⟨(pointer,before),.variable found⟩
      | .paren expression => do
        let out ← locate fuel context primitive before expression
        return ⟨out.val,.paren out.property⟩
      | .unary .dereference expression => do
        let out ← evaluate fuel context primitive before expression
        match isPointer : out.val.1 with
        | .pointer pointer => return ⟨(pointer,out.val.2),.dereference (isPointer ▸ out.property)⟩
        | _ => none
      | .index base offset => do
        let baseOut ← evaluate fuel context primitive before base
        match baseIs : baseOut.val.1 with
        | .pointer pointer => do
          let offsetOut ← evaluate fuel context primitive baseOut.val.2 offset
          match offsetIs : offsetOut.val.1 with
          | .integer index =>
            match added : offsetOut.val.2.pointerAdd pointer index.toInt with
            | none => none
            | some result => return ⟨(result,offsetOut.val.2),
                .index (baseIs ▸ baseOut.property) (offsetIs ▸ offsetOut.property) added⟩
          | _ => none
        | _ => none
      | _ => none

  def execute (fuel : Nat) (context : Context F) (primitive : PrimitiveExecutor context)
      (before : State F) (statement : Stmt) : Option (Executed context before statement) :=
    match fuel with
    | 0 => none
    | fuel+1 => match statement with
      | .block statements => do
        let start := before.enterScope
        let out ← executeList fuel context primitive start statements
        let after := {out.val.2.leaveScope start.scope before.environment with scope := before.scope}
        return ⟨(out.val.1,after),.block rfl out.property rfl⟩
      | .declare type name none =>
        match declared : before.declare type name none with
        | none => none
        | some after => some ⟨(.normal,after),.declareNone declared⟩
      | .declare type name (some expression) => do
        let out ← evaluate fuel context primitive before expression
        match declared : out.val.2.declare type name (some out.val.1) with
        | none => none
        | some after => return ⟨(.normal,after),.declareSome out.property declared⟩
      | .assign destination expression => do
        let right ← evaluate fuel context primitive before expression
        let left ← locate fuel context primitive right.val.2 destination
        match stored : left.val.2.store left.val.1 right.val.1 with
        | none => none
        | some after => return ⟨(.normal,after),.assign right.property left.property stored⟩
      | .assignOp op destination expression => do
        let right ← evaluate fuel context primitive before expression
        let left ← locate fuel context primitive right.val.2 destination
        match old : left.val.2.load left.val.1 with
        | none => none
        | some oldValue =>
          match computed : binary left.val.2 op oldValue right.val.1 with
          | none => none
          | some value =>
            match stored : left.val.2.store left.val.1 value with
            | none => none
            | some after => return ⟨(.normal,after),.assignOp right.property left.property old computed stored⟩
      | .expression (.call name expressions) => do
        let values ← evaluateArguments fuel context primitive 0 before expressions
        let out ← invoke fuel context primitive name values.val.1 values.val.2
        match resultIs : out.val.1 with
        | .value value => return ⟨(.normal,out.val.2),
            .expression (.call (numbered_arguments values.property.1 values.property.2) (resultIs ▸ out.property))⟩
        | .terminated status => return ⟨(.terminated status,out.val.2),
            .callTerminated (numbered_arguments values.property.1 values.property.2) (resultIs ▸ out.property)⟩
      | .expression expression => do
        let out ← evaluate fuel context primitive before expression
        return ⟨(.normal,out.val.2),.expression out.property⟩
      | .ite test yes no => do
        let tested ← evaluate fuel context primitive before test
        match truth : tested.val.1.truth with
        | none => none
        | some true => do
          let out ← execute fuel context primitive tested.val.2 yes
          return ⟨out.val,.ifTrue tested.property truth out.property⟩
        | some false => match noIs : no with
          | none => return ⟨(.normal,tested.val.2),by rw [noIs]; exact .ifFalse tested.property truth⟩
          | some no => do
            let out ← execute fuel context primitive tested.val.2 no
            return ⟨out.val,by rw [noIs]; exact .ifElse tested.property truth out.property⟩
      | .whileLoop test body => do
        let tested ← evaluate fuel context primitive before test
        match truth : tested.val.1.truth with
        | none => none
        | some false => return ⟨(.normal,tested.val.2),.whileFalse tested.property truth⟩
        | some true => do
          let out ← execute fuel context primitive tested.val.2 body
          match flowIs : out.val.1 with
          | .normal => do
            let rest ← execute fuel context primitive out.val.2 (.whileLoop test body)
            return ⟨rest.val,.whileNext tested.property truth (flowIs ▸ out.property) rest.property⟩
          | .continued => do
            let rest ← execute fuel context primitive out.val.2 (.whileLoop test body)
            return ⟨rest.val,.whileContinue tested.property truth (flowIs ▸ out.property) rest.property⟩
          | .broke => return ⟨(.normal,out.val.2),.whileBreak tested.property truth (flowIs ▸ out.property)⟩
          | .returned value => return ⟨(.returned value,out.val.2),
              .whileExit tested.property truth (flowIs ▸ out.property) (by simp)⟩
          | .jumped label => return ⟨(.jumped label,out.val.2),
              .whileExit tested.property truth (flowIs ▸ out.property) (by simp)⟩
          | .terminated status => return ⟨(.terminated status,out.val.2),
              .whileExit tested.property truth (flowIs ▸ out.property) (by simp)⟩
      | .returnValue none => some ⟨(.returned .unit,before),.returnNone⟩
      | .returnValue (some expression) => do
        let out ← evaluate fuel context primitive before expression
        return ⟨(.returned out.val.1,out.val.2),.returnSome out.property⟩
      | .breakLoop => some ⟨(.broke,before),.breakLoop⟩
      | .continueLoop => some ⟨(.continued,before),.continueLoop⟩
      | .label name => some ⟨(.normal,before),.label⟩
      | .gotoLabel name => some ⟨(.jumped name,before),.gotoLabel⟩
      | .launch name grid block shared stream expressions =>
        match selected : findFunction context.program name with
        | none => none
        | some function => do
          let config ← evaluateArguments fuel context primitive 0 before [grid,block,shared,stream]
          let values ← evaluateArguments fuel context primitive 0 config.val.2 expressions
          let out ← primitive (.launch function) (config.val.1 ++ values.val.1) values.val.2
          match resultIs : out.val.1 with
          | .value .unit => return ⟨(.normal,out.val.2),.launch selected
              (numbered_arguments config.property.1 config.property.2) (numbered_arguments values.property.1 values.property.2) (resultIs ▸ out.property)⟩
          | _ => none
      | .forLoop .. => none

  def executeList (fuel : Nat) (context : Context F) (primitive : PrimitiveExecutor context)
      (before : State F) (statements : List Stmt) : Option (Listed context before statements) :=
    match fuel with
    | 0 => none
    | fuel+1 => match statements with
      | [] => some ⟨(.normal,before),.nil⟩
      | statement :: statements => do
        let first ← execute fuel context primitive before statement
        match flowIs : first.val.1 with
        | .normal => do
          let rest ← executeList fuel context primitive first.val.2 statements
          return ⟨rest.val,.cons (flowIs ▸ first.property) rest.property⟩
        | .returned value => return ⟨(.returned value,first.val.2),.abrupt (flowIs ▸ first.property) (by simp)⟩
        | .continued => return ⟨(.continued,first.val.2),.abrupt (flowIs ▸ first.property) (by simp)⟩
        | .broke => return ⟨(.broke,first.val.2),.abrupt (flowIs ▸ first.property) (by simp)⟩
        | .jumped label => return ⟨(.jumped label,first.val.2),.abrupt (flowIs ▸ first.property) (by simp)⟩
        | .terminated status => return ⟨(.terminated status,first.val.2),.abrupt (flowIs ▸ first.property) (by simp)⟩

  def executeBody (fuel : Nat) (context : Context F) (primitive : PrimitiveExecutor context)
      (whole : List Stmt) (before : State F) (statements : List Stmt) :
      Option (Bodied context whole before statements) :=
    match fuel with
    | 0 => none
    | fuel+1 => do
      let out ← executeList fuel context primitive before statements
      match flowIs : out.val.1 with
      | .jumped label =>
        match target : labelTail label whole with
        | none => none
        | some suffix => do
          let rest ← executeBody fuel context primitive whole out.val.2 suffix
          return ⟨rest.val,.jump (flowIs ▸ out.property) target rest.property⟩
      | .normal => return ⟨(.normal,out.val.2),.finish (flowIs ▸ out.property) (by intro label h; cases h)⟩
      | .returned value => return ⟨(.returned value,out.val.2),.finish (flowIs ▸ out.property) (by intro label h; cases h)⟩
      | .broke => return ⟨(.broke,out.val.2),.finish (flowIs ▸ out.property) (by intro label h; cases h)⟩
      | .continued => return ⟨(.continued,out.val.2),.finish (flowIs ▸ out.property) (by intro label h; cases h)⟩
      | .terminated status => return ⟨(.terminated status,out.val.2),.finish (flowIs ▸ out.property) (by intro label h; cases h)⟩

  def invoke (fuel : Nat) (context : Context F) (primitive : PrimitiveExecutor context)
      (name : String) (values : List Value) (before : State F) : Option (Called context name values before) :=
    match fuel with
    | 0 => none
    | fuel+1 =>
      match selected : findFunction context.program name with
      | none => do
        let external ← externalNamed name
        let out ← primitive (.call external.val) values before
        return ⟨out.val,.external selected external.property out.property⟩
      | some function =>
        match shape : function.body with
        | .block statements =>
          match parameters : bindParameters {before.enterScope with environment := []}
              function.parameters values with
          | none => none
          | some entered => do
            let out ← executeBody fuel context primitive statements entered statements
            match flowIs : out.val.1 with
            | .returned value =>
              match converted : value.convert function.result with
              | none => none
              | some result =>
                let after := {out.val.2.leaveScope entered.scope before.environment with scope := before.scope}
                return ⟨(.value result,after),.internal selected shape parameters
                  (flowIs ▸ out.property) converted rfl⟩
            | .normal =>
              if isVoid : function.result = .void then
                let after := {out.val.2.leaveScope entered.scope before.environment with scope := before.scope}
                return ⟨(.value .unit,after),.internalVoid selected shape isVoid parameters
                  (flowIs ▸ out.property) rfl⟩
              else none
            | .terminated status => return ⟨(.terminated status,out.val.2),
                .internalTerminated selected shape parameters (flowIs ▸ out.property)⟩
            | _ => none
        | _ => none
end

/-- A successful computed call is already an actual source operational proof;
fuel and the chosen permitted argument order add no semantic assumption. -/
theorem invoke_sound {context : Context F} {primitive : PrimitiveExecutor context}
    {fuel : Nat} {name : String} {values : List Value} {before : State F}
    {out : Called context name values before}
    (_computed : invoke fuel context primitive name values before = some out) :
    Call context name values before out.val.1 out.val.2 := out.property

end GoldbachDirect.Interpreter
