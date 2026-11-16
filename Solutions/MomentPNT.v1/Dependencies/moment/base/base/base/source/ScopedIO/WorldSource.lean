/- Additive source semantics for standard external stdout and I/O effects.
The application's original Machine/ArraySourceCalls are unchanged. A pure
macro-step always carries an existing complete actual-source execution tree;
application mathematical success or intended output can never be a leaf. -/
import ScopedIO.WorldRuntime
import ScopedC.ArraySourceCalls
namespace ScopedIO.WorldSource
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

mutual
  inductive Eval (cfg : Layout) (pure : Machine.Call) (call : WorldIO.Call) (p : WorldIO.Platform) :
      Expr → World → World → Value → Prop
    /-- Existing typed expression execution; the containing source call
    must prove every successful pure callback by an actual C source tree. -/
    | pure {e s t v stream fuel} (run : evalExpr cfg pure fuel s e=some (v,t)) :
        Eval cfg pure call p e ⟨s,stream⟩ ⟨t,stream⟩ v
    /-- Standard C platform identifier, used only when not shadowed by
    application memory. No heap FILE object or initialized app cache is assumed. -/
    | stdout {s stream} (unshadowed : Machine.getVar s "stdout"=none) :
        Eval cfg pure call p (.var "stdout") ⟨s,stream⟩ ⟨s,stream⟩ (stdoutValue p)
    | call {name es s middle t args v}
        (arguments : Arguments cfg pure call p es s middle args)
        (run : call name args middle=some (v,t)) :
        Eval cfg pure call p (.call (.var name) es) s t v
    | binary {op lhs rhs s middle t a b v}
        (ordinary : op≠"=" ∧ op≠"," ∧ op≠"&&" ∧ op≠"||")
        (left : Eval cfg pure call p lhs s middle a)
        (right : Eval cfg pure call p rhs middle t b)
        (arithmetic : Machine.binaryValue cfg t.app op a b=some v) :
        Eval cfg pure call p (.binary op lhs rhs) s t v
  inductive Arguments (cfg : Layout) (pure : Machine.Call) (call : WorldIO.Call) (p : WorldIO.Platform) :
      List Expr → World → World → List Value → Prop
    | nil (s : World) : Arguments cfg pure call p [] s s []
    | cons {e es s middle t v vs} (first : Eval cfg pure call p e s middle v)
        (rest : Arguments cfg pure call p es middle t vs) :
        Arguments cfg pure call p (e::es) s t (v::vs)
end

def Declare (cfg : Layout) (pure : Machine.Call) (ds : List Decl) (s t : World) : Prop :=
  ArrayDeclarations.declarations cfg pure ds s.app=some t.app ∧ t.stream=s.stream

def pop (before after : World) : World := {after with app:=Machine.popScope before.app after.app}

def Scope (before : World) : Loops.Flow World Value → Loops.Flow World Value → Prop
  | .continuing inner,.continuing outer => outer=pop before inner
  | .returned inner v,.returned outer w => w=v ∧ outer=pop before inner
  | _,_ => False

abbrev Run (cfg : Layout) (pure : Machine.Call) (call : WorldIO.Call) (p : WorldIO.Platform) :=
  Loops.StmtRun (Eval cfg pure call p) (Declare cfg pure) truth Scope

def Finish (cfg : Layout) (f : Function) (caller : World)
    (inner : Loops.Flow World Value) (v : Value) (after : World) : Prop :=
  match inner with
  | .returned final value => castValue cfg final.app 100 f.returnType value=some v ∧ after=pop caller final
  | .continuing final => normalizeType f.returnType="void" ∧ v=.unit ∧ after=pop caller final

/-- A finite actual-body tree. The pure alternative requires a complete
old C-source tree, whose runtime leaves contain no I/O. The installed-body
alternative executes the unchanged AST in the new explicit stdio world.
Only the fixed generic WorldIO.external contract is a platform leaf. -/
def SourceCall (cfg : Layout) (code : List Function) (p : WorldIO.Platform) (fault : WorldIO.FaultPolicy) :
    Nat → String → List Value → World → Value → World → Prop
  | 0,name,args,s,v,t => WorldIO.external p fault name args s=some (v,t)
  | rank+1,name,args,s,v,t =>
      WorldIO.external p fault name args s=some (v,t) ∨
      (∃ oldRank, ArraySourceCalls.SourceCall cfg code oldRank name args s.app v t.app ∧ t.stream=s.stream) ∨
      ∃ f, f∈code ∧ f.name=name ∧
        ∃ pure : Machine.Call, (∀ called actual start value final,
          pure called actual start=some (value,final) →
          ∃ oldRank, ArraySourceCalls.SourceCall cfg code oldRank called actual start value final) ∧
        ∃ service : WorldIO.Call, (∀ called actual start value final,
          service called actual start=some (value,final) →
          SourceCall cfg code p fault rank called actual start value final) ∧
        ∃ frame, bindArgs cfg f.parameters args s.app=some frame ∧
          ∃ outcome, Run cfg pure service p f.body ⟨frame,s.stream⟩ outcome ∧ Finish cfg f s outcome v t

theorem pure_call {cfg : Layout} {code : List Function} {p : WorldIO.Platform} {fault : WorldIO.FaultPolicy}
    {rank oldRank : Nat} {name : String} {args : List Value} {s t : State} {v : Value}
    (h : ArraySourceCalls.SourceCall cfg code oldRank name args s v t) (stream : Stream) :
    SourceCall cfg code p fault (rank+1) name args ⟨s,stream⟩ v ⟨t,stream⟩ :=
  Or.inr (Or.inl ⟨oldRank,h,rfl⟩)

theorem external_call {cfg : Layout} {code : List Function} {p : WorldIO.Platform} {fault : WorldIO.FaultPolicy}
    {rank : Nat} {name : String} {args : List Value} {s t : World} {v : Value}
    (h : WorldIO.external p fault name args s=some (v,t)) :
    SourceCall cfg code p fault rank name args s v t := by
  cases rank with
  | zero => exact h
  | succ rank => exact Or.inl h

#print axioms pure_call
#print axioms external_call
end ScopedIO.WorldSource
