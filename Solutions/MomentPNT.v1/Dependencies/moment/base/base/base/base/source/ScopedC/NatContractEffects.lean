/- Contract-accelerated actual-source execution preserves the separate Nat
arena when every successful installed function contract preserves it. -/
import ScopedC.NatStatementEffects
import ScopedC.ContractExecute
namespace ScopedC.NatEffects
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] Machine.castValue Machine.bindArgs
  ArraySourceExecute.statement ContractExecute.execute ContractExecute.once

theorem finish {cfg : Layout} {f : Function} {caller : State}
    {out : ArraySourceExecute.Outcome} {v : Value} {t : State}
    (h : ArraySourceCallExecute.finish cfg f caller out = some (v,t)) :
    t.nats = flowArena out := by
  cases out with
  | returned after value =>
      cases hc : castValue cfg after 100 f.returnType value with
      | none => simp [ArraySourceCallExecute.finish,hc] at h
      | some w =>
          simp only [ArraySourceCallExecute.finish,hc,Bind.bind,Option.bind,Pure.pure,
            Option.some.injEq,Prod.mk.injEq] at h
          exact (congrArg State.nats h.2).symm
  | continuing after =>
      by_cases hv : normalizeType f.returnType = "void"
      · simp only [ArraySourceCallExecute.finish,hv,ite_true,Option.some.injEq,Prod.mk.injEq] at h
        exact (congrArg State.nats h.2).symm
      · simp only [ArraySourceCallExecute.finish,hv,ite_false] at h
        contradiction

theorem contract_once {cfg : Layout} {code : List Function}
    {expressionFuel statementFuel : Nat} {service : Call} (keeps : Preserves service) :
    Preserves (ContractExecute.once cfg code expressionFuel statementFuel service) := by
  intro name args s v t h
  cases hf : ArraySourceCallExecute.find code name with
  | none => simp [ContractExecute.once,hf] at h
  | some f =>
      cases hb : bindArgs cfg f.parameters args s with
      | none => simp [ContractExecute.once,hf,hb] at h
      | some frame =>
          cases ho : ArraySourceExecute.statement cfg service expressionFuel statementFuel f.body frame with
          | none => simp [ContractExecute.once,hf,hb,ho] at h
          | some out =>
              simp only [ContractExecute.once,hf,hb,ho,Bind.bind,Option.bind] at h
              exact (finish h).trans ((statement keeps ho).trans (bind_arguments hb))

theorem contract_all (cfg : Layout) (code : List Function) (expressionFuel statementFuel : Nat)
    (contract : Call) (keeps : Preserves contract) (fuel : Nat) :
    Preserves (ContractExecute.execute cfg code expressionFuel statementFuel contract fuel) := by
  induction fuel with
  | zero => simpa only [ContractExecute.execute] using keeps
  | succ fuel ih =>
      intro name args s v t h
      cases hc : contract name args s with
      | some out =>
          simp only [ContractExecute.execute,hc,Option.some.injEq] at h
          subst out
          exact keeps name args s v t hc
      | none =>
          have actual : ContractExecute.once cfg code expressionFuel statementFuel
              (ContractExecute.execute cfg code expressionFuel statementFuel contract fuel)
              name args s = some (v,t) := by
            simpa only [ContractExecute.execute,hc] using h
          exact contract_once ih name args s v t actual

theorem contract_execute {cfg : Layout} {code : List Function}
    {expressionFuel statementFuel fuel : Nat} {contract : Call} (keeps : Preserves contract)
    {name : String} {args : List Value} {s t : State} {v : Value}
    (h : ContractExecute.execute cfg code expressionFuel statementFuel contract fuel
      name args s = some (v,t)) : t.nats = s.nats :=
  contract_all cfg code expressionFuel statementFuel contract keeps fuel name args s v t h

#print axioms finish
#print axioms contract_once
#print axioms contract_all
#print axioms contract_execute
end ScopedC.NatEffects
