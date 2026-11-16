/- The unchanged main's actual fflush return check and normal return statement.
A checked zero return proves accepted bytes delivered under the generic stdio contract. -/
import SynergyHeightC.MainWorldService
import SynergyHeightC.MainTotalOutput
import ScopedIO.WorldContracts
namespace SynergyHeightC.MainWorldFlush
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical ScopedIO
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

def expression : Expr := .call (.var "fflush") [.var "stdout"]
def checkedFlush : Stmt := .branch (.binary "!=" expression (.nat 0))
  (.eval (.call (.var "fail") [])) .skip

theorem stdout_unshadowed (total : ProofBox) (i : Nat) :
    Machine.getVar (FullMainEdges.loopState total i) "stdout"=none := by
  simp [Machine.getVar,FullMainEdges.loopState,Machine.allocate,FullMainPrefix.afterSpan,
    FullMainPrefix.afterHeight,FullMainPrefix.afterCells,FullMainPrefix.cache,
    InitCacheProposal.postState,InitCacheProposal.globals,List.lookup]

theorem source_partition : PointExecuteAPI.mainStatements.drop 7=[
    .eval (.call (.var "emitI") [.var "total"]),checkedFlush,.returnStmt (.nat 0)] := by rfl

theorem actual_flush (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    (total : ProofBox) (i : Nat) (before : WorldIO.World)
    (memory : before.app=FullMainEdges.loopState total i)
    {after : WorldIO.World}
    (accepted : WorldIO.stdio platform fault "fflush" [WorldIO.stdoutValue platform] before=
      some (WorldIO.signed32 0,after)) :
    WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (MainWorldService.call platform fault) platform checkedFlush before (.continuing after) ∧
    after.app=before.app ∧ after.stream.accepted=before.stream.accepted ∧
      after.stream.delivered=before.stream.accepted.length := by
  have unshadowed : Machine.getVar before.app "stdout"=none := by
    rw [memory]
    exact stdout_unshadowed total i
  have call : MainWorldService.call platform fault "fflush" [WorldIO.stdoutValue platform] before=
      some (WorldIO.signed32 0,after) := by
    simpa [MainWorldService.call,WorldIO.external,RuntimeCore.call,RuntimeCore.binaryName]
      using accepted
  have arguments : WorldSource.Arguments SynergyC.Header.layout FullMainPrefix.service
      (MainWorldService.call platform fault) platform [.var "stdout"] before before
      [WorldIO.stdoutValue platform] := by
    cases before
    exact .cons (.stdout unshadowed) (.nil _)
  have flushCall : WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service
      (MainWorldService.call platform fault) platform expression before after (WorldIO.signed32 0) :=
    .call arguments call
  have actual : WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (MainWorldService.call platform fault) platform checkedFlush before (.continuing after) := by
    apply Loops.StmtRun.branch
      (WorldSource.Eval.binary
        (op:="!=") ⟨by decide,by decide,by decide,by decide⟩ flushCall
        (WorldSource.Eval.pure (fuel:=1) (s:=after.app) rfl) rfl)
    exact Loops.StmtRun.skip after
  exact ⟨actual,WorldIO.fflush_zero platform fault _ (WorldIO.stdout_handle platform) accepted⟩

theorem actual_return (service : WorldIO.Call) (platform : WorldIO.Platform)
    (world : WorldIO.World) : WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      service platform (.returnStmt (.nat 0)) world (.returned world (WorldIO.signed32 0)) := by
  cases world
  exact Loops.StmtRun.returnValue (WorldSource.Eval.pure (fuel:=1) rfl)

#print axioms stdout_unshadowed
#print axioms source_partition
#print axioms actual_flush
#print axioms actual_return
end SynergyHeightC.MainWorldFlush
