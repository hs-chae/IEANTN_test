import PVCore.Source
import FKS2Table4.Program
import FKS2Pair.OldInputs
import ForwardRamanujan.Old
import ForwardRamanujanUpdate.Updated
import ForwardRamanujanUpdate.OldGrouped
import ForwardRamanujanUpdate.UpdatedGrouped

/-! Decisive test: does the one generic renderer reproduce every existing selected C file? -/
open PVCore

def ofTransport (p : FKS2Table4.TransportProgram) : Program :=
  ⟨"fks2_table4_transport", p.inputs, p.scale, [(.plus, p.anchor), (.plus, p.point), (.plus, p.tail)]⟩
def ofRamanujan (p : ForwardRamanujan.Program) : Program :=
  ⟨"ramanujan_epsilon_bound", p.inputs, p.scale, [(.minus, p.fixedOffset), (.minus, p.positiveOffset)]⟩

#eval [("Table4 QRH (v5)", sourceMatches FKS2Table4.selectedSource (ofTransport FKS2Table4.selected)),
       ("Table4 old (v6)", sourceMatches FKS2Pair.Old.oldSource (ofTransport FKS2Pair.Old.oldProgram)),
       ("Ramanujan old (v1)", sourceMatches ForwardRamanujan.Old.actualSource (ofRamanujan ForwardRamanujan.Old.program)),
       ("Ramanujan updated (v2)", sourceMatches ForwardRamanujan.Updated.actualSource (ofRamanujan ForwardRamanujan.Updated.program)),
       ("Ramanujan old grouped", sourceMatches ForwardRamanujan.OldGrouped.actualSource (ofRamanujan ForwardRamanujan.OldGrouped.program)),
       ("Ramanujan updated grouped", sourceMatches ForwardRamanujan.UpdatedGrouped.actualSource (ofRamanujan ForwardRamanujan.UpdatedGrouped.program)),
       -- negative: the Table 4 file against the Ramanujan wrapper, and a renamed function
       ("NEG Table4 file vs Ramanujan program", sourceMatches FKS2Table4.selectedSource (ofRamanujan ForwardRamanujan.Updated.program)),
       ("NEG renamed function", sourceMatches FKS2Table4.selectedSource { ofTransport FKS2Table4.selected with fnName := "g" })]
