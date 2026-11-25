import GoldbachDirect.Correspondence.StatementsProofs
import GoldbachDirect.Correspondence.Preprocessing

/-! Independent source-to-syntax correspondence for the declared C++20/CUDA
fragment. This relation does not mention the executable checker, tokenizer,
AST token renderer, or equality between rendered token lists. Header contents,
macro expansion, C++ typing and compiler execution remain separate contracts. -/
namespace GoldbachDirect.Correspondence

/-- Fixed generic header/runtime symbols and CUDA coordinates cannot be rebound
by the restricted application's declarations. Own bindings start with a letter;
this also excludes implementation-reserved/predefined macro binding names.
References such as the documented external _Exit remain legal expressions. -/
def protectedPlatformNames : List String :=
  ["NULL", "stdout", "cudaSuccess", "cudaStreamNonBlocking", "cudaMemcpyHostToDevice",
   "cudaMemcpyDeviceToHost", "cudaDevAttrMaxThreadsPerBlock", "cudaDevAttrMaxGridDimX",
   "blockIdx", "blockDim", "threadIdx", "gridDim", "malloc", "calloc", "free",
   "cudaSetDevice", "cudaDeviceGetAttribute", "cudaMalloc", "cudaFree",
   "cudaStreamCreateWithFlags", "cudaStreamDestroy", "cudaMemcpy", "cudaDeviceSynchronize",
   "cudaGetLastError", "cudaStreamSynchronize", "atomicOr", "printf", "fflush", "fopen",
   "fwrite", "fclose", "_Exit"]

def BindingName (name : String) : Prop :=
  syntaxIdentifier name = true ∧ name.startsWith "_" = false ∧
    name ∉ protectedPlatformNames

def bindingIdentifier (name : String) : Bool :=
  syntaxIdentifier name && !name.startsWith "_" && !(name ∈ protectedPlatformNames)

theorem bindingIdentifier_sound {name : String}
    (checked : bindingIdentifier name = true) : BindingName name := by
  simpa [bindingIdentifier, BindingName, and_assoc] using checked

def supportedProgramSyntax (program : Program) : Bool :=
  programGuard (exprSyntaxSafe 1024) bindingIdentifier program

theorem supportedProgramSyntax_sound {program : Program}
    (checked : supportedProgramSyntax program = true) :
    ProgramSyntax (ExpressionSyntax 13) BindingName program.tokens program := by
  exact programGuard_sound (ExpressionSyntax 13) BindingName
    (exprSyntaxSafe 1024) bindingIdentifier (fun _ h => exprSyntaxSafe_sound h)
    (fun _ h => bindingIdentifier_sound h) program checked

inductive SourceSyntaxCorresponds (source : String) (program : Program) : Prop where
  | derived {tokens : List String}
      (characters : Lexical.declarativeLex source tokens)
      (parsed : ProgramSyntax (ExpressionSyntax 13) BindingName tokens program)
      (directives : SourcePreprocessingSyntax source) : SourceSyntaxCorresponds source program

end GoldbachDirect.Correspondence
