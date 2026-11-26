import FFTMainCertificateCall
import FFTMainLocalsTransport
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainRecursiveStatement
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource MainRootBirth
open MainCertificate MainAllocation

def sourceArguments : List Expr := [.variable "output",RecursiveSource.literal 0,.variable "data",
  RecursiveSource.literal 0,RecursiveSource.literal 1,.variable "twiddle",.variable "n",.variable "n",.variable "work"]
def statement : Stmt := StatusCall.statement "fft_recursive" sourceArguments

theorem actual_w4_statement : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 22).take 1=[statement] := by rfl
theorem actual_fap_statement : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 22).take 1=[statement] := by rfl

/-- The actual nine source operands, read from the real main pointer and n
slots. Pure-argument uniqueness accounts for every permitted evaluation order. -/
theorem source_arguments {F : Type} (context : Context F) {state : State F}
    {n nId owner pointerBase status : Nat} {objects ids : Role→Nat}
    (full : FullMainLocals state n nId owner objects ids pointerBase status) :
    Args context state sourceArguments
      (arguments (objects .output) (objects .data) (objects .twiddle) (objects .work) 0 0 1 n n) state := by
  apply Args.ordered (List.Perm.refl _)
  · exact .cons (.variable (full.lookup (some (.inl (some .output)))) (full.read (some (.inl (some .output)))))
      (.cons (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
      (.cons (.variable (full.lookup (some (.inl (some .data)))) (full.read (some (.inl (some .data)))))
      (.cons (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
      (.cons (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
      (.cons (.variable (full.lookup (some (.inl (some .twiddle)))) (full.read (some (.inl (some .twiddle)))))
      (.cons (.variable (full.lookup (some (.inl none))) (full.read (some (.inl none))))
      (.cons (.variable (full.lookup (some (.inl none))) (full.read (some (.inl none))))
      (.cons (.variable (full.lookup (some (.inl (some .work)))) (full.read (some (.inl (some .work))))) .nil))))))))
  · exact .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl .nil))))))))

theorem source_arguments_pure : ∀e∈sourceArguments,SourcePure.CallFree e := by
  intro e member
  simp only [sourceArguments,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial

/-- Any real automatic main/loader slots survive the recursive Call because
its actual output/work writes are host arrays, distinct from automatic slots. -/
theorem locals_after_recursive {F I : Type} {before after : State F} {p : InputLoader.Profile}
    {nId owner pointerBase status jId : Nat} {objects ids : Role→Nat}
    {tableData oldWork outputData workData : Nat→Nat}
    (front : MainSuffix.FrontReady before p nId owner objects ids pointerBase status jId tableData oldWork)
    (post : CallPost (buffers p objects front.distinct) (exponent p) 0 0 1
      (MainSuffix.loadedData p) tableData (fun _=>0) oldWork before after outputData workData)
    {names : I→String} {types : I→CType} {localIds : I→Nat} {localValues : I→Value}
    (locals : Locals before names types localIds owner localValues) :
    Locals after names types localIds owner localValues := by
  apply MainTransport.locals_of_frame front.well locals post.frame.frame
  · intro v;rw [post.frame.environment]
  · intro v
    change localIds v∉[objects .output,objects .work]
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
    exact ⟨(array_ne_slot front.output (locals.slots v)).symm,
      (array_ne_slot front.work (locals.slots v)).symm⟩

#print axioms source_arguments
#print axioms locals_after_recursive
end RH080Next.FFTPV.MainRecursiveStatement
