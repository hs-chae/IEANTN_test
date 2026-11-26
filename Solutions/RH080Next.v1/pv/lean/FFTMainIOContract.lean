/- Precise generic LP64 stdio boundary. Allocation failure and negative
printf returns with partial output are retained. This contract contains no
norm-function, FFT, certificate, or analytic correctness assertion. -/
import FFTMainIOSemantics
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainIO
open GoldbachDirect GoldbachDirect.Semantics WordArrays MainAllocation SourceLocals

structure PrintEvent where
  argument : Nat
  written : String
  success : Bool
  deriving DecidableEq

structure IOState where
  stdout : String := ""
  events : List PrintEvent := []
  deriving DecidableEq

def decimalLF (n : Nat) : String := n.repr ++ "\n"

theorem decimalLF_length (n : Nat) (fit : n<2^64) : (decimalLF n).length≤21 := by
  have digits : n.repr.length≤20 := (Nat.length_repr_le_iff (by decide : 0<20)).2 (by omega)
  simp only [decimalLF,String.length_append]
  rw [show "\n".length=1 from by decide]
  omega

def emit (before : State IOState) (n : Nat) (written : String) (success : Bool) : State IOState :=
  {before with foreign := ⟨before.foreign.stdout++written,
    before.foreign.events++[⟨n,written,success⟩]⟩}

/-- The only supported formatting operation is the generic literal %llu LF
with an actual unsigned 64-bit operand. Failure may write any prefix and must
return a negative int. Successful return is the exact character count. -/
inductive PrintfCall : List Value → State IOState → CallResult → State IOState → Prop where
  | success (before : State IOState) (n : Nat) (fit : n<2^64) :
      PrintfCall [.string "%llu\n",.integer (integer64 n)] before
        (.value (.integer (Integer.cast .i32 (decimalLF n).length)))
        (emit before n (decimalLF n) true)
  | failure (before : State IOState) (n : Nat) (fit : n<2^64)
      (written tail : String) (isPrefix : written++tail=decimalLF n)
      (code : Int) (negative : -(2^31)≤code ∧ code<0) :
      PrintfCall [.string "%llu\n",.integer (integer64 n)] before
        (.value (.integer (Integer.cast .i32 code))) (emit before n written false)

def memoryOnlyContext (program : Program) : Context IOState :=
  {program:=program,foreign:=fun primitive args before result after=>match primitive with
    | .call operation=>∃value,result=.value value ∧ PlatformMemory.Call IOState operation args before value after
    | _=>False,
   headerConstant:=fun _=>none,builtin:=fun _ _=>none}

def ioForeign : Foreign IOState := fun primitive args before result after=>match primitive with
  | .call operation =>
      (∃value,result=.value value ∧ PlatformMemory.Call IOState operation args before value after) ∨
      (operation=.printf ∧ PrintfCall args before result after)
  | _=>False

def ioContext (program : Program) : Context IOState :=
  {memoryOnlyContext program with foreign:=ioForeign}

theorem memoryOnly_hasMemory (program : Program) : HasMemory (memoryOnlyContext program) := by
  intro operation args before value after actual
  exact ⟨value,rfl,actual⟩

theorem memoryOnly_sound (program : Program) : MemorySound (memoryOnlyContext program) := by
  intro operation args before result after _ actual
  exact actual

theorem io_hasMemory (program : Program) : HasMemory (ioContext program) := by
  intro operation args before value after actual
  exact Or.inl ⟨value,rfl,actual⟩

theorem io_sound (program : Program) : MemorySound (ioContext program) := by
  intro operation args before result after allowed actual
  rcases actual with actual | ⟨printf,_⟩
  · exact actual
  · rcases allowed with rfl | rfl <;> cases printf

theorem memoryOnly_foreign_frame (program : Program) :
    ∀primitive values before result after,
      (memoryOnlyContext program).foreign primitive values before result after →
      after.foreign=before.foreign := by
  intro primitive values before result after actual
  cases primitive with
  | launch => cases actual
  | call operation =>
    obtain ⟨value,rfl,api⟩:=actual
    cases api with
    | mallocFailure => rfl
    | mallocSuccess _ _ _ _ _ _ born => exact (PlatformMemory.allocation_identity born).2.2.2.2.2
    | callocFailure => rfl
    | callocSuccess _ _ _ _ _ _ _ _ _ _ born => exact (PlatformMemory.allocation_identity born).2.2.2.2.2
    | freeNull => rfl
    | freeObject _ _ pointer released =>
      unfold PlatformMemory.release at released
      split at released
      · cases released
      · split_ifs at released
        all_goals simp_all
        cases released
        rfl

theorem memoryOnly_call_in_io {program : Program} {name : String} {values : List Value}
    {before after : State IOState} {result : CallResult}
    (actual : Call (memoryOnlyContext program) name values before result after) :
    Call (ioContext program) name values before result after := by
  apply call_extend_foreign ioForeign ?_ actual
  intro primitive values before result after actual
  cases primitive with
  | launch => cases actual
  | call operation => exact Or.inl actual

theorem printf_cases {args : List Value} {before after : State IOState} {result : CallResult}
    (actual : ioForeign (.call .printf) args before result after) : PrintfCall args before result after := by
  rcases actual with ⟨value,_,api⟩ | ⟨_,api⟩
  · cases api
  · exact api

end RH080Next.FFTPV.MainIO
