import SynergyAnalytic.Height768GenericV4.Chunk00
import SynergyAnalytic.Height768GenericV4.Chunk01
import SynergyAnalytic.Height768GenericV4.Chunk02
import SynergyAnalytic.Height768GenericV4.Chunk03
import SynergyAnalytic.Height768GenericV4.Chunk04
import SynergyAnalytic.Height768GenericV4.Chunk05
import SynergyAnalytic.Height768GenericV4.Chunk06
import SynergyAnalytic.Height768GenericV4.Chunk07
import SynergyAnalytic.Height768GenericV4.Chunk08
import SynergyAnalytic.Height768GenericV4.Chunk09
import SynergyAnalytic.Height768GenericV4.Chunk10
import SynergyAnalytic.Height768GenericV4.Chunk11
import SynergyAnalytic.Height768GenericV4.Chunk12
import SynergyAnalytic.Height768GenericV4.Chunk13
import SynergyAnalytic.Height768GenericV4.Chunk14
import SynergyAnalytic.Height768GenericV4.Chunk15
import SynergyAnalytic.Height768GenericV4.Chunk16
import SynergyAnalytic.Height768GenericV4.Chunk17
import SynergyAnalytic.Height768GenericV4.Chunk18
import SynergyAnalytic.Height768GenericV4.Chunk19
import SynergyAnalytic.Height768GenericV4.Chunk20
import SynergyAnalytic.Height768GenericV4.Chunk21
import SynergyAnalytic.Height768GenericV4.Chunk22
import SynergyAnalytic.Height768GenericV4.Chunk23
import SynergyAnalytic.Height768GenericV4.Chunk24
import SynergyAnalytic.Height768GenericV4.Chunk25
import SynergyAnalytic.Height768GenericV4.Chunk26
import SynergyAnalytic.Height768GenericV4.Chunk27
import SynergyAnalytic.Height768GenericV4.Chunk28
import SynergyAnalytic.Height768GenericV4.Chunk29
import SynergyAnalytic.Height768GenericV4.Chunk30
import SynergyAnalytic.Height768GenericV4.Chunk31
import SynergyAnalytic.Height768GenericV4.Chunk32
import SynergyAnalytic.Height768GenericV4.Chunk33
import SynergyAnalytic.Height768GenericV4.Chunk34
import SynergyAnalytic.Height768GenericV4.Chunk35
import SynergyAnalytic.Height768GenericV4.Chunk36
import SynergyAnalytic.Height768GenericV4.Chunk37
import SynergyAnalytic.Height768GenericV4.Chunk38
import SynergyAnalytic.Height768GenericV4.Chunk39
import SynergyAnalytic.Height768GenericV4.Chunk40
import SynergyAnalytic.Height768GenericV4.Chunk41
import SynergyAnalytic.Height768GenericV4.Chunk42
import SynergyAnalytic.Height768GenericV4.Chunk43
import SynergyAnalytic.Height768GenericV4.Chunk44
import SynergyAnalytic.Height768GenericV4.Chunk45
import SynergyAnalytic.Height768GenericV4.Chunk46
import SynergyAnalytic.Height768GenericV4.Chunk47
import SynergyAnalytic.Height768GenericV4.Chunk48
import SynergyAnalytic.Height768GenericV4.Chunk49
import SynergyAnalytic.Height768GenericV4.Chunk50
import SynergyAnalytic.Height768GenericV4.Chunk51
import SynergyAnalytic.Height768GenericV4.Chunk52
import SynergyAnalytic.Height768GenericV4.Chunk53
import SynergyAnalytic.Height768GenericV4.Chunk54
import SynergyAnalytic.Height768GenericV4.Chunk55
import SynergyAnalytic.Height768GenericV4.Chunk56
import SynergyAnalytic.Height768GenericV4.Chunk57
import SynergyAnalytic.Height768GenericV4.Chunk58
import SynergyAnalytic.Height768GenericV4.Chunk59
import SynergyAnalytic.Height768GenericV4.Chunk60
import SynergyAnalytic.Height768GenericV4.Chunk61
import SynergyAnalytic.Height768GenericV4.Chunk62
import SynergyAnalytic.Height768GenericV4.Chunk63
import SynergyAnalytic.Height768GenericV4.Chunk64
import SynergyAnalytic.Height768GenericV4.Chunk65
import SynergyAnalytic.Height768GenericV4.Chunk66
import SynergyAnalytic.Height768GenericV4.Chunk67
import SynergyAnalytic.Height768GenericV4.Chunk68
import SynergyAnalytic.Height768GenericV4.Chunk69
import SynergyAnalytic.Height768GenericV4.Chunk70
import SynergyAnalytic.Height768GenericV4.Chunk71
import SynergyAnalytic.Height768GenericV4.Chunk72
import SynergyAnalytic.Height768GenericV4.Chunk73
import SynergyAnalytic.Height768GenericV4.Chunk74
import SynergyAnalytic.Height768GenericV4.Chunk75
import SynergyAnalytic.Height768GenericV4.Chunk76
import SynergyAnalytic.Height768GenericV4.Chunk77
import SynergyAnalytic.Height768GenericV4.Chunk78
import SynergyAnalytic.Height768GenericV4.Chunk79
import SynergyAnalytic.Height768GenericV4.Chunk80
import SynergyAnalytic.Height768GenericV4.Chunk81
import SynergyAnalytic.Height768GenericV4.Chunk82
import SynergyAnalytic.Height768GenericV4.Chunk83
import SynergyAnalytic.Height768GenericV4.Chunk84
import SynergyAnalytic.Height768GenericV4.Chunk85
import SynergyAnalytic.Height768GenericV4.Chunk86
import SynergyAnalytic.Height768GenericV4.Chunk87
import SynergyAnalytic.Height768GenericV4.Chunk88
import SynergyAnalytic.Height768GenericV4.Chunk89
import SynergyAnalytic.Height768GenericV4.Chunk90
import SynergyAnalytic.Height768GenericV4.Chunk91
import SynergyAnalytic.Height768GenericV4.Chunk92
import SynergyAnalytic.Height768GenericV4.Chunk93
import SynergyAnalytic.Height768GenericV4.Chunk94
import SynergyAnalytic.Height768GenericV4.Chunk95
import SynergyAnalytic.HeightPointResultBounds
namespace SynergyAnalytic.HeightPoint
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kernel_generic_height_all (i:Nat) (hi:i<logCellCount) :
    genericPointCheck (logCell (i+1)) (point constantValues) (cWords[i]?) (DWords[i]?) mainIndex slopeIndex=true := by
  have hchunks : ∀b<96,(List.range 8).all (fun j=>
      genericPointCheck (logCell (j+8*b+1)) (point constantValues) (cWords[j+8*b]?) (DWords[j+8*b]?) mainIndex slopeIndex)=true := by
    intro b hb
    interval_cases b
    · exact kernel_height_generic_v4_chunk00
    · exact kernel_height_generic_v4_chunk01
    · exact kernel_height_generic_v4_chunk02
    · exact kernel_height_generic_v4_chunk03
    · exact kernel_height_generic_v4_chunk04
    · exact kernel_height_generic_v4_chunk05
    · exact kernel_height_generic_v4_chunk06
    · exact kernel_height_generic_v4_chunk07
    · exact kernel_height_generic_v4_chunk08
    · exact kernel_height_generic_v4_chunk09
    · exact kernel_height_generic_v4_chunk10
    · exact kernel_height_generic_v4_chunk11
    · exact kernel_height_generic_v4_chunk12
    · exact kernel_height_generic_v4_chunk13
    · exact kernel_height_generic_v4_chunk14
    · exact kernel_height_generic_v4_chunk15
    · exact kernel_height_generic_v4_chunk16
    · exact kernel_height_generic_v4_chunk17
    · exact kernel_height_generic_v4_chunk18
    · exact kernel_height_generic_v4_chunk19
    · exact kernel_height_generic_v4_chunk20
    · exact kernel_height_generic_v4_chunk21
    · exact kernel_height_generic_v4_chunk22
    · exact kernel_height_generic_v4_chunk23
    · exact kernel_height_generic_v4_chunk24
    · exact kernel_height_generic_v4_chunk25
    · exact kernel_height_generic_v4_chunk26
    · exact kernel_height_generic_v4_chunk27
    · exact kernel_height_generic_v4_chunk28
    · exact kernel_height_generic_v4_chunk29
    · exact kernel_height_generic_v4_chunk30
    · exact kernel_height_generic_v4_chunk31
    · exact kernel_height_generic_v4_chunk32
    · exact kernel_height_generic_v4_chunk33
    · exact kernel_height_generic_v4_chunk34
    · exact kernel_height_generic_v4_chunk35
    · exact kernel_height_generic_v4_chunk36
    · exact kernel_height_generic_v4_chunk37
    · exact kernel_height_generic_v4_chunk38
    · exact kernel_height_generic_v4_chunk39
    · exact kernel_height_generic_v4_chunk40
    · exact kernel_height_generic_v4_chunk41
    · exact kernel_height_generic_v4_chunk42
    · exact kernel_height_generic_v4_chunk43
    · exact kernel_height_generic_v4_chunk44
    · exact kernel_height_generic_v4_chunk45
    · exact kernel_height_generic_v4_chunk46
    · exact kernel_height_generic_v4_chunk47
    · exact kernel_height_generic_v4_chunk48
    · exact kernel_height_generic_v4_chunk49
    · exact kernel_height_generic_v4_chunk50
    · exact kernel_height_generic_v4_chunk51
    · exact kernel_height_generic_v4_chunk52
    · exact kernel_height_generic_v4_chunk53
    · exact kernel_height_generic_v4_chunk54
    · exact kernel_height_generic_v4_chunk55
    · exact kernel_height_generic_v4_chunk56
    · exact kernel_height_generic_v4_chunk57
    · exact kernel_height_generic_v4_chunk58
    · exact kernel_height_generic_v4_chunk59
    · exact kernel_height_generic_v4_chunk60
    · exact kernel_height_generic_v4_chunk61
    · exact kernel_height_generic_v4_chunk62
    · exact kernel_height_generic_v4_chunk63
    · exact kernel_height_generic_v4_chunk64
    · exact kernel_height_generic_v4_chunk65
    · exact kernel_height_generic_v4_chunk66
    · exact kernel_height_generic_v4_chunk67
    · exact kernel_height_generic_v4_chunk68
    · exact kernel_height_generic_v4_chunk69
    · exact kernel_height_generic_v4_chunk70
    · exact kernel_height_generic_v4_chunk71
    · exact kernel_height_generic_v4_chunk72
    · exact kernel_height_generic_v4_chunk73
    · exact kernel_height_generic_v4_chunk74
    · exact kernel_height_generic_v4_chunk75
    · exact kernel_height_generic_v4_chunk76
    · exact kernel_height_generic_v4_chunk77
    · exact kernel_height_generic_v4_chunk78
    · exact kernel_height_generic_v4_chunk79
    · exact kernel_height_generic_v4_chunk80
    · exact kernel_height_generic_v4_chunk81
    · exact kernel_height_generic_v4_chunk82
    · exact kernel_height_generic_v4_chunk83
    · exact kernel_height_generic_v4_chunk84
    · exact kernel_height_generic_v4_chunk85
    · exact kernel_height_generic_v4_chunk86
    · exact kernel_height_generic_v4_chunk87
    · exact kernel_height_generic_v4_chunk88
    · exact kernel_height_generic_v4_chunk89
    · exact kernel_height_generic_v4_chunk90
    · exact kernel_height_generic_v4_chunk91
    · exact kernel_height_generic_v4_chunk92
    · exact kernel_height_generic_v4_chunk93
    · exact kernel_height_generic_v4_chunk94
    · exact kernel_height_generic_v4_chunk95
  have hb : i/8<96 := by norm_num [logCellCount] at hi;omega
  have hj : i%8∈List.range 8 := List.mem_range.mpr (Nat.mod_lt i (by decide))
  have hv:=(List.all_eq_true.mp (hchunks (i/8) hb)) (i%8) hj
  simpa only [Nat.mod_add_div] using hv

#print axioms kernel_generic_height_all
end SynergyAnalytic.HeightPoint
