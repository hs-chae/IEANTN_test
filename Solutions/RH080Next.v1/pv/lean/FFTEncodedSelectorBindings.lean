/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTEncodedSelectorSafe
import FFTRecursiveSource
import FapFFTRecursiveSource
import WindowData
import FapData
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.FFTPV.EncodedSelector
open GoldbachDirect

def guard (length fallback : Nat) : Stmt:=
  .ite (.binary .ge (.variable "j") (.literal (.integer length "ULL")))
    (.block [.returnValue (some (.literal (.integer fallback "ULL")))]) none

def function (length fallback : Nat) (tree : Tree) : Function:=
  {result:=.u64,name:="encoded_node",parameters:=[(.u64,"j")],emptyVoid:=false,
    body:=.block [guard length fallback,tree.statement]}

def w4Tree : Tree:=build 2520 0 RH080Next.WindowPV.Data.encoded
def fapTree : Tree:=build 400 0 RH080Next.FapPV.Data.encoded

theorem w4_actual_function : FFTRecursivePV.encoded_node_ast=function 2520 10000000000000000 w4Tree:=by
  rfl

theorem fap_actual_function : FapFFTRecursivePV.encoded_node_ast=function 400 10000000000000000 fapTree:=by
  rfl

theorem w4_covers : Covers w4Tree 0 RH080Next.WindowPV.Data.encoded:=
  build_covers _ _ _ (by decide +kernel) (by decide +kernel)

theorem fap_covers : Covers fapTree 0 RH080Next.FapPV.Data.encoded:=
  build_covers _ _ _ (by decide +kernel) (by decide +kernel)

#print axioms w4_actual_function
#print axioms fap_actual_function
#print axioms w4_covers
#print axioms fap_covers
end RH080Next.FFTPV.EncodedSelector
