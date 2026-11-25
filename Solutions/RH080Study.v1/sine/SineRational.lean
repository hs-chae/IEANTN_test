/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SineCells00
import SineCells01
import SineCells02
import SineCells03
import SineCells04
import SineCells05
import SineCells06
import SineCells07
import SineCells08
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.SineBridge
theorem rational_error (r : Fin 129) : |(sineFixed r.val : ℚ)/1000000000 - polyQ ((3141592654*r.val/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  fin_cases r
  · exact error000
  · exact error001
  · exact error002
  · exact error003
  · exact error004
  · exact error005
  · exact error006
  · exact error007
  · exact error008
  · exact error009
  · exact error010
  · exact error011
  · exact error012
  · exact error013
  · exact error014
  · exact error015
  · exact error016
  · exact error017
  · exact error018
  · exact error019
  · exact error020
  · exact error021
  · exact error022
  · exact error023
  · exact error024
  · exact error025
  · exact error026
  · exact error027
  · exact error028
  · exact error029
  · exact error030
  · exact error031
  · exact error032
  · exact error033
  · exact error034
  · exact error035
  · exact error036
  · exact error037
  · exact error038
  · exact error039
  · exact error040
  · exact error041
  · exact error042
  · exact error043
  · exact error044
  · exact error045
  · exact error046
  · exact error047
  · exact error048
  · exact error049
  · exact error050
  · exact error051
  · exact error052
  · exact error053
  · exact error054
  · exact error055
  · exact error056
  · exact error057
  · exact error058
  · exact error059
  · exact error060
  · exact error061
  · exact error062
  · exact error063
  · exact error064
  · exact error065
  · exact error066
  · exact error067
  · exact error068
  · exact error069
  · exact error070
  · exact error071
  · exact error072
  · exact error073
  · exact error074
  · exact error075
  · exact error076
  · exact error077
  · exact error078
  · exact error079
  · exact error080
  · exact error081
  · exact error082
  · exact error083
  · exact error084
  · exact error085
  · exact error086
  · exact error087
  · exact error088
  · exact error089
  · exact error090
  · exact error091
  · exact error092
  · exact error093
  · exact error094
  · exact error095
  · exact error096
  · exact error097
  · exact error098
  · exact error099
  · exact error100
  · exact error101
  · exact error102
  · exact error103
  · exact error104
  · exact error105
  · exact error106
  · exact error107
  · exact error108
  · exact error109
  · exact error110
  · exact error111
  · exact error112
  · exact error113
  · exact error114
  · exact error115
  · exact error116
  · exact error117
  · exact error118
  · exact error119
  · exact error120
  · exact error121
  · exact error122
  · exact error123
  · exact error124
  · exact error125
  · exact error126
  · exact error127
  · exact error128
end RH080.SineBridge
#print axioms RH080.SineBridge.rational_error
