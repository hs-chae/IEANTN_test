import RamanujanPV.FiniteScalarMillion.Log0000
import RamanujanPV.FiniteScalarMillion.Log0001
import RamanujanPV.FiniteScalarMillion.Log0002
import RamanujanPV.FiniteScalarMillion.Log0003
import RamanujanPV.FiniteScalarMillion.Log0004
import RamanujanPV.FiniteScalarMillion.Log0005
import RamanujanPV.FiniteScalarMillion.Log0006
import RamanujanPV.FiniteScalarMillion.Log0007
import RamanujanPV.FiniteScalarMillion.Log0008
import RamanujanPV.FiniteScalarMillion.LogFinal
import RamanujanPV.FiniteExpSource
namespace RamanujanPV.ScalarIndependentAudit
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
example : RamanujanPV.FiniteExpSource.actualSource=(include_str "/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1/c/verified_finite_exp.c") := by rfl
example : RamanujanPV.FiniteLogSource.actualSource=(include_str "/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1/c/verified_finite_log.c") := by rfl
example : (RamanujanPV.LocalCellsMillion.rows.get 0)=⟨38358837683,38358837739,14111427770,1644673232,632207037,26795374111319,4486419048288114⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 0).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 0).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0000
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 0).n (RamanujanPV.LocalCellsMillion.rows.get 0).Lu := RamanujanPV.FiniteScalarMillion.log_source_0000
example : (RamanujanPV.LocalCellsMillion.rows.get 1)=⟨38358837739,38358837887,14111427791,1644673234,632207038,26795374112925,4486419054568933⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 1).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 1).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0001
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 1).n (RamanujanPV.LocalCellsMillion.rows.get 1).Lu := RamanujanPV.FiniteScalarMillion.log_source_0001
example : (RamanujanPV.LocalCellsMillion.rows.get 2)=⟨38358837887,38358837919,14111427845,1644673237,632207038,26795374117167,4486419071168645⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 2).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 2).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0002
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 2).n (RamanujanPV.LocalCellsMillion.rows.get 2).Lu := RamanujanPV.FiniteScalarMillion.log_source_0002
example : (RamanujanPV.LocalCellsMillion.rows.get 3)=⟨38358837919,38358837997,14111427857,1644673240,632207040,26795374118084,4486419074757804⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 3).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 3).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0003
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 3).n (RamanujanPV.LocalCellsMillion.rows.get 3).Lu := RamanujanPV.FiniteScalarMillion.log_source_0003
example : (RamanujanPV.LocalCellsMillion.rows.get 4)=⟨38358837997,38358838163,14111427886,1644673244,632207042,26795374120320,4486419083506243⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 4).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 4).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0004
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 4).n (RamanujanPV.LocalCellsMillion.rows.get 4).Lu := RamanujanPV.FiniteScalarMillion.log_source_0004
example : (RamanujanPV.LocalCellsMillion.rows.get 5)=⟨38358838163,38358838391,14111427947,1644673252,632207045,26795374125078,4486419102124826⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 5).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 5).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0005
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 5).n (RamanujanPV.LocalCellsMillion.rows.get 5).Lu := RamanujanPV.FiniteScalarMillion.log_source_0005
example : (RamanujanPV.LocalCellsMillion.rows.get 6)=⟨38358838391,38358838619,14111428031,1644673260,632207048,26795374131613,4486419127697352⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 6).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 6).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0006
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 6).n (RamanujanPV.LocalCellsMillion.rows.get 6).Lu := RamanujanPV.FiniteScalarMillion.log_source_0006
example : (RamanujanPV.LocalCellsMillion.rows.get 7)=⟨38358838619,38358838909,14111428115,1644673273,632207054,26795374138149,4486419153269710⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 7).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 7).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0007
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 7).n (RamanujanPV.LocalCellsMillion.rows.get 7).Lu := RamanujanPV.FiniteScalarMillion.log_source_0007
example : (RamanujanPV.LocalCellsMillion.rows.get 8)=⟨38358838909,38358839293,14111428221,1644673285,632207059,26795374146461,4486419185796179⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 8).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 8).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0008
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 8).n (RamanujanPV.LocalCellsMillion.rows.get 8).Lu := RamanujanPV.FiniteScalarMillion.log_source_0008
example : (RamanujanPV.LocalCellsMillion.rows.get 9)=⟨38358839293,38358839759,14111428363,1644673302,632207066,26795374157468,4486419228865582⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 9).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 9).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0009
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 9).n (RamanujanPV.LocalCellsMillion.rows.get 9).Lu := RamanujanPV.FiniteScalarMillion.log_source_0009
example : (RamanujanPV.LocalCellsMillion.rows.get 10)=⟨38358839759,38358840101,14111428534,1644673318,632207071,26795374170825,4486419281132173⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 10).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 10).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0010
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 10).n (RamanujanPV.LocalCellsMillion.rows.get 10).Lu := RamanujanPV.FiniteScalarMillion.log_source_0010
example : (RamanujanPV.LocalCellsMillion.rows.get 11)=⟨38358840101,38358840413,14111428660,1644673335,632207078,26795374180629,4486419319490711⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 11).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 11).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0011
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 11).n (RamanujanPV.LocalCellsMillion.rows.get 11).Lu := RamanujanPV.FiniteScalarMillion.log_source_0011
example : (RamanujanPV.LocalCellsMillion.rows.get 12)=⟨38358840413,38358840713,14111428775,1644673345,632207081,26795374189572,4486419354484632⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 12).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 12).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0012
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 12).n (RamanujanPV.LocalCellsMillion.rows.get 12).Lu := RamanujanPV.FiniteScalarMillion.log_source_0012
example : (RamanujanPV.LocalCellsMillion.rows.get 13)=⟨38358840713,38358841007,14111428885,1644673356,632207085,26795374198171,4486419388132639⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 13).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 13).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0013
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 13).n (RamanujanPV.LocalCellsMillion.rows.get 13).Lu := RamanujanPV.FiniteScalarMillion.log_source_0013
example : (RamanujanPV.LocalCellsMillion.rows.get 14)=⟨38358841007,38358841447,14111428993,1644673370,632207091,26795374206598,4486419421107690⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 14).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 14).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0014
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 14).n (RamanujanPV.LocalCellsMillion.rows.get 14).Lu := RamanujanPV.FiniteScalarMillion.log_source_0014
example : (RamanujanPV.LocalCellsMillion.rows.get 15)=⟨38358841447,38358841979,14111429155,1644673391,632207100,26795374219210,4486419470458079⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 15).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 15).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0015
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 15).n (RamanujanPV.LocalCellsMillion.rows.get 15).Lu := RamanujanPV.FiniteScalarMillion.log_source_0015
example : (RamanujanPV.LocalCellsMillion.rows.get 16)=⟨38358841979,38358842513,14111429351,1644673412,632207108,26795374234459,4486419530127194⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 16).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 16).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0016
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 16).n (RamanujanPV.LocalCellsMillion.rows.get 16).Lu := RamanujanPV.FiniteScalarMillion.log_source_0016
example : (RamanujanPV.LocalCellsMillion.rows.get 17)=⟨38358842513,38358843191,14111429547,1644673434,632207116,26795374249766,4486419590020517⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 17).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 17).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0017
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 17).n (RamanujanPV.LocalCellsMillion.rows.get 17).Lu := RamanujanPV.FiniteScalarMillion.log_source_0017
example : (RamanujanPV.LocalCellsMillion.rows.get 18)=⟨38358843191,38358843739,14111429797,1644673462,632207127,26795374269200,4486419666064970⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 18).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 18).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0018
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 18).n (RamanujanPV.LocalCellsMillion.rows.get 18).Lu := RamanujanPV.FiniteScalarMillion.log_source_0018
example : (RamanujanPV.LocalCellsMillion.rows.get 19)=⟨38358843739,38358844361,14111429998,1644673490,632207140,26795374284908,4486419727528580⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 19).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 19).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0019
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 19).n (RamanujanPV.LocalCellsMillion.rows.get 19).Lu := RamanujanPV.FiniteScalarMillion.log_source_0019
example : (RamanujanPV.LocalCellsMillion.rows.get 20)=⟨38358844361,38358844723,14111430227,1644673516,632207150,26795374302736,4486419797292215⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 20).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 20).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0020
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 20).n (RamanujanPV.LocalCellsMillion.rows.get 20).Lu := RamanujanPV.FiniteScalarMillion.log_source_0020
example : (RamanujanPV.LocalCellsMillion.rows.get 21)=⟨38358844723,38358845333,14111430360,1644673535,632207159,26795374313113,4486419837893997⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 21).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 21).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0021
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 21).n (RamanujanPV.LocalCellsMillion.rows.get 21).Lu := RamanujanPV.FiniteScalarMillion.log_source_0021
example : (RamanujanPV.LocalCellsMillion.rows.get 22)=⟨38358845333,38358846173,14111430585,1644673564,632207172,26795374330598,4486419906311551⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 22).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 22).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0022
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 22).n (RamanujanPV.LocalCellsMillion.rows.get 22).Lu := RamanujanPV.FiniteScalarMillion.log_source_0022
example : (RamanujanPV.LocalCellsMillion.rows.get 23)=⟨38358846173,38358847139,14111430894,1644673600,632207186,26795374354675,4486420000526004⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 23).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 23).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0023
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 23).n (RamanujanPV.LocalCellsMillion.rows.get 23).Lu := RamanujanPV.FiniteScalarMillion.log_source_0023
example : (RamanujanPV.LocalCellsMillion.rows.get 24)=⟨38358847139,38358847951,14111431249,1644673638,632207200,26795374382365,4486420108872383⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 24).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 24).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0024
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 24).n (RamanujanPV.LocalCellsMillion.rows.get 24).Lu := RamanujanPV.FiniteScalarMillion.log_source_0024
example : (RamanujanPV.LocalCellsMillion.rows.get 25)=⟨38358847951,38358848597,14111431548,1644673672,632207213,26795374405640,4486420199946259⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 25).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 25).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0025
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 25).n (RamanujanPV.LocalCellsMillion.rows.get 25).Lu := RamanujanPV.FiniteScalarMillion.log_source_0025
example : (RamanujanPV.LocalCellsMillion.rows.get 26)=⟨38358848597,38358849253,14111431785,1644673698,632207223,26795374424156,4486420272401720⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 26).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 26).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0026
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 26).n (RamanujanPV.LocalCellsMillion.rows.get 26).Lu := RamanujanPV.FiniteScalarMillion.log_source_0026
example : (RamanujanPV.LocalCellsMillion.rows.get 27)=⟨38358849253,38358849989,14111432027,1644673724,632207233,26795374442960,4486420345978552⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 27).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 27).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0027
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 27).n (RamanujanPV.LocalCellsMillion.rows.get 27).Lu := RamanujanPV.FiniteScalarMillion.log_source_0027
example : (RamanujanPV.LocalCellsMillion.rows.get 28)=⟨38358849989,38358850883,14111432297,1644673755,632207245,26795374464057,4486420428528198⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 28).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 28).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0028
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 28).n (RamanujanPV.LocalCellsMillion.rows.get 28).Lu := RamanujanPV.FiniteScalarMillion.log_source_0028
example : (RamanujanPV.LocalCellsMillion.rows.get 29)=⟨38358850883,38358851681,14111432626,1644673788,632207256,26795374489682,4486420528799261⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 29).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 29).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0029
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 29).n (RamanujanPV.LocalCellsMillion.rows.get 29).Lu := RamanujanPV.FiniteScalarMillion.log_source_0029
example : (RamanujanPV.LocalCellsMillion.rows.get 30)=⟨38358851681,38358852619,14111432920,1644673825,632207272,26795374512556,4486420618302849⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 30).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 30).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0030
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 30).n (RamanujanPV.LocalCellsMillion.rows.get 30).Lu := RamanujanPV.FiniteScalarMillion.log_source_0030
example : (RamanujanPV.LocalCellsMillion.rows.get 31)=⟨38358852619,38358853591,14111433265,1644673864,632207287,26795374539442,4486420723508984⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 31).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 31).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0031
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 31).n (RamanujanPV.LocalCellsMillion.rows.get 31).Lu := RamanujanPV.FiniteScalarMillion.log_source_0031
example : (RamanujanPV.LocalCellsMillion.rows.get 32)=⟨38358853591,38358854453,14111433623,1644673894,632207295,26795374567304,4486420832528318⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 32).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 32).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0032
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 32).n (RamanujanPV.LocalCellsMillion.rows.get 32).Lu := RamanujanPV.FiniteScalarMillion.log_source_0032
example : (RamanujanPV.LocalCellsMillion.rows.get 33)=⟨38358854453,38358855239,14111433940,1644673924,632207304,26795374592012,4486420929210222⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 33).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 33).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0033
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 33).n (RamanujanPV.LocalCellsMillion.rows.get 33).Lu := RamanujanPV.FiniteScalarMillion.log_source_0033
example : (RamanujanPV.LocalCellsMillion.rows.get 34)=⟨38358855239,38358856171,14111434229,1644673959,632207319,26795374614542,4486421017367896⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 34).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 34).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0034
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 34).n (RamanujanPV.LocalCellsMillion.rows.get 34).Lu := RamanujanPV.FiniteScalarMillion.log_source_0034
example : (RamanujanPV.LocalCellsMillion.rows.get 35)=⟨38358856171,38358856969,14111434572,1644674001,632207336,26795374641256,4486421121901073⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 35).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 35).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0035
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 35).n (RamanujanPV.LocalCellsMillion.rows.get 35).Lu := RamanujanPV.FiniteScalarMillion.log_source_0035
example : (RamanujanPV.LocalCellsMillion.rows.get 36)=⟨38358856969,38358857701,14111434865,1644674034,632207349,26795374664130,4486421211404660⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 36).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 36).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0036
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 36).n (RamanujanPV.LocalCellsMillion.rows.get 36).Lu := RamanujanPV.FiniteScalarMillion.log_source_0036
example : (RamanujanPV.LocalCellsMillion.rows.get 37)=⟨38358857701,38358858283,14111435135,1644674061,632207358,26795374685112,4486421293505722⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 37).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 37).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0037
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 37).n (RamanujanPV.LocalCellsMillion.rows.get 37).Lu := RamanujanPV.FiniteScalarMillion.log_source_0037
example : (RamanujanPV.LocalCellsMillion.rows.get 38)=⟨38358858283,38358858823,14111435349,1644674087,632207369,26795374701794,4486421358782864⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 38).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 38).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0038
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 38).n (RamanujanPV.LocalCellsMillion.rows.get 38).Lu := RamanujanPV.FiniteScalarMillion.log_source_0038
example : (RamanujanPV.LocalCellsMillion.rows.get 39)=⟨38358858823,38358859379,14111435547,1644674114,632207381,26795374717273,4486421419349141⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 39).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 39).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0039
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 39).n (RamanujanPV.LocalCellsMillion.rows.get 39).Lu := RamanujanPV.FiniteScalarMillion.log_source_0039
example : (RamanujanPV.LocalCellsMillion.rows.get 40)=⟨38358859379,38358860093,14111435752,1644674145,632207396,26795374733210,4486421481710081⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 40).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 40).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0040
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 40).n (RamanujanPV.LocalCellsMillion.rows.get 40).Lu := RamanujanPV.FiniteScalarMillion.log_source_0040
example : (RamanujanPV.LocalCellsMillion.rows.get 41)=⟨38358860093,38358860789,14111436014,1644674172,632207406,26795374753676,4486421561792272⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 41).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 41).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0041
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 41).n (RamanujanPV.LocalCellsMillion.rows.get 41).Lu := RamanujanPV.FiniteScalarMillion.log_source_0041
example : (RamanujanPV.LocalCellsMillion.rows.get 42)=⟨38358860789,38358861613,14111436271,1644674203,632207419,26795374773626,4486421639855593⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 42).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 42).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0042
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 42).n (RamanujanPV.LocalCellsMillion.rows.get 42).Lu := RamanujanPV.FiniteScalarMillion.log_source_0042
example : (RamanujanPV.LocalCellsMillion.rows.get 43)=⟨38358861613,38358862727,14111436574,1644674242,632207436,26795374797245,4486421732275380⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 43).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 43).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0043
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 43).n (RamanujanPV.LocalCellsMillion.rows.get 43).Lu := RamanujanPV.FiniteScalarMillion.log_source_0043
example : (RamanujanPV.LocalCellsMillion.rows.get 44)=⟨38358862727,38358864007,14111436983,1644674291,632207456,26795374829176,4486421857221635⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 44).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 44).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0044
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 44).n (RamanujanPV.LocalCellsMillion.rows.get 44).Lu := RamanujanPV.FiniteScalarMillion.log_source_0044
example : (RamanujanPV.LocalCellsMillion.rows.get 45)=⟨38358864007,38358865147,14111437454,1644674339,632207472,26795374865866,4486422000786303⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 45).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 45).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0045
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 45).n (RamanujanPV.LocalCellsMillion.rows.get 45).Lu := RamanujanPV.FiniteScalarMillion.log_source_0045
example : (RamanujanPV.LocalCellsMillion.rows.get 46)=⟨38358865147,38358866311,14111437874,1644674383,632207488,26795374898543,4486422128648592⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 46).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 46).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0046
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 46).n (RamanujanPV.LocalCellsMillion.rows.get 46).Lu := RamanujanPV.FiniteScalarMillion.log_source_0046
example : (RamanujanPV.LocalCellsMillion.rows.get 47)=⟨38358866311,38358867257,14111438302,1644674431,632207507,26795374931907,4486422259202874⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 47).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 47).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0047
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 47).n (RamanujanPV.LocalCellsMillion.rows.get 47).Lu := RamanujanPV.FiniteScalarMillion.log_source_0047
example : (RamanujanPV.LocalCellsMillion.rows.get 48)=⟨38358867257,38358868039,14111438650,1644674465,632207518,26795374959023,4486422365306170⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 48).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 48).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0048
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 48).n (RamanujanPV.LocalCellsMillion.rows.get 48).Lu := RamanujanPV.FiniteScalarMillion.log_source_0048
example : (RamanujanPV.LocalCellsMillion.rows.get 49)=⟨38358868039,38358868997,14111438938,1644674503,632207535,26795374981439,4486422453015091⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 49).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 49).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0049
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 49).n (RamanujanPV.LocalCellsMillion.rows.get 49).Lu := RamanujanPV.FiniteScalarMillion.log_source_0049
example : (RamanujanPV.LocalCellsMillion.rows.get 50)=⟨38358868997,38358869963,14111439290,1644674540,632207548,26795375008898,4486422560464468⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 50).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 50).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0050
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 50).n (RamanujanPV.LocalCellsMillion.rows.get 50).Lu := RamanujanPV.FiniteScalarMillion.log_source_0050
example : (RamanujanPV.LocalCellsMillion.rows.get 51)=⟨38358869963,38358870817,14111439645,1644674581,632207564,26795375036588,4486422668810842⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 51).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 51).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0051
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 51).n (RamanujanPV.LocalCellsMillion.rows.get 51).Lu := RamanujanPV.FiniteScalarMillion.log_source_0051
example : (RamanujanPV.LocalCellsMillion.rows.get 52)=⟨38358870817,38358871591,14111439960,1644674620,632207581,26795375061067,4486422764595411⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 52).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 52).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0052
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 52).n (RamanujanPV.LocalCellsMillion.rows.get 52).Lu := RamanujanPV.FiniteScalarMillion.log_source_0052
example : (RamanujanPV.LocalCellsMillion.rows.get 53)=⟨38358871591,38358872423,14111440244,1644674656,632207596,26795375083252,4486422851407335⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 53).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 53).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0053
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 53).n (RamanujanPV.LocalCellsMillion.rows.get 53).Lu := RamanujanPV.FiniteScalarMillion.log_source_0053
example : (RamanujanPV.LocalCellsMillion.rows.get 54)=⟨38358872423,38358873269,14111440550,1644674688,632207608,26795375107101,4486422944724284⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 54).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 54).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0054
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 54).n (RamanujanPV.LocalCellsMillion.rows.get 54).Lu := RamanujanPV.FiniteScalarMillion.log_source_0054
example : (RamanujanPV.LocalCellsMillion.rows.get 55)=⟨38358873269,38358874297,14111440862,1644674721,632207620,26795375131350,4486423039611689⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 55).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 55).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0055
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 55).n (RamanujanPV.LocalCellsMillion.rows.get 55).Lu := RamanujanPV.FiniteScalarMillion.log_source_0055
example : (RamanujanPV.LocalCellsMillion.rows.get 56)=⟨38358874297,38358875329,14111441240,1644674763,632207636,26795375160817,4486423154912004⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 56).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 56).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0056
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 56).n (RamanujanPV.LocalCellsMillion.rows.get 56).Lu := RamanujanPV.FiniteScalarMillion.log_source_0056
example : (RamanujanPV.LocalCellsMillion.rows.get 57)=⟨38358875329,38358876263,14111441619,1644674805,632207652,26795375190398,4486423270661067⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 57).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 57).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0057
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 57).n (RamanujanPV.LocalCellsMillion.rows.get 57).Lu := RamanujanPV.FiniteScalarMillion.log_source_0057
example : (RamanujanPV.LocalCellsMillion.rows.get 58)=⟨38358876263,38358876971,14111441963,1644674842,632207665,26795375217170,4486423375418448⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 58).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 58).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0058
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 58).n (RamanujanPV.LocalCellsMillion.rows.get 58).Lu := RamanujanPV.FiniteScalarMillion.log_source_0058
example : (RamanujanPV.LocalCellsMillion.rows.get 59)=⟨38358876971,38358877957,14111442224,1644674878,632207682,26795375237464,4486423454827679⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 59).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 59).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0059
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 59).n (RamanujanPV.LocalCellsMillion.rows.get 59).Lu := RamanujanPV.FiniteScalarMillion.log_source_0059
example : (RamanujanPV.LocalCellsMillion.rows.get 60)=⟨38358877957,38358879121,14111442586,1644674923,632207701,26795375265726,4486423565417463⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 60).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 60).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0060
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 60).n (RamanujanPV.LocalCellsMillion.rows.get 60).Lu := RamanujanPV.FiniteScalarMillion.log_source_0060
example : (RamanujanPV.LocalCellsMillion.rows.get 61)=⟨38358879121,38358880141,14111443014,1644674972,632207720,26795375299091,4486423695971574⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 61).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 61).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0061
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 61).n (RamanujanPV.LocalCellsMillion.rows.get 61).Lu := RamanujanPV.FiniteScalarMillion.log_source_0061
example : (RamanujanPV.LocalCellsMillion.rows.get 62)=⟨38358880141,38358881287,14111443390,1644675018,632207739,26795375328328,4486423810374724⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 62).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 62).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0062
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 62).n (RamanujanPV.LocalCellsMillion.rows.get 62).Lu := RamanujanPV.FiniteScalarMillion.log_source_0062
example : (RamanujanPV.LocalCellsMillion.rows.get 63)=⟨38358881287,38358882643,14111443811,1644675071,632207762,26795375361177,4486423938909964⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 63).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 63).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0063
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 63).n (RamanujanPV.LocalCellsMillion.rows.get 63).Lu := RamanujanPV.FiniteScalarMillion.log_source_0063
example : (RamanujanPV.LocalCellsMillion.rows.get 64)=⟨38358882643,38358883961,14111444310,1644675126,632207783,26795375400045,4486424090998857⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 64).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 64).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0064
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 64).n (RamanujanPV.LocalCellsMillion.rows.get 64).Lu := RamanujanPV.FiniteScalarMillion.log_source_0064
example : (RamanujanPV.LocalCellsMillion.rows.get 65)=⟨38358883961,38358885449,14111444795,1644675182,632207805,26795375437824,4486424238825635⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 65).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 65).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0065
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 65).n (RamanujanPV.LocalCellsMillion.rows.get 65).Lu := RamanujanPV.FiniteScalarMillion.log_source_0065
example : (RamanujanPV.LocalCellsMillion.rows.get 66)=⟨38358885449,38358886963,14111445342,1644675249,632207833,26795375480476,4486424405719576⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 66).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 66).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0066
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 66).n (RamanujanPV.LocalCellsMillion.rows.get 66).Lu := RamanujanPV.FiniteScalarMillion.log_source_0066
example : (RamanujanPV.LocalCellsMillion.rows.get 67)=⟨38358886963,38358888721,14111445899,1644675311,632207857,26795375523873,4486424575529718⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 67).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 67).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0067
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 67).n (RamanujanPV.LocalCellsMillion.rows.get 67).Lu := RamanujanPV.FiniteScalarMillion.log_source_0067
example : (RamanujanPV.LocalCellsMillion.rows.get 68)=⟨38358888721,38358890723,14111446546,1644675381,632207883,26795375574263,4486424772707046⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 68).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 68).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0068
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 68).n (RamanujanPV.LocalCellsMillion.rows.get 68).Lu := RamanujanPV.FiniteScalarMillion.log_source_0068
example : (RamanujanPV.LocalCellsMillion.rows.get 69)=⟨38358890723,38358892757,14111447283,1644675469,632207919,26795375631648,4486424997251224⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 69).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 69).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0069
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 69).n (RamanujanPV.LocalCellsMillion.rows.get 69).Lu := RamanujanPV.FiniteScalarMillion.log_source_0069
example : (RamanujanPV.LocalCellsMillion.rows.get 70)=⟨38358892757,38358894527,14111448031,1644675549,632207948,26795375689951,4486425225384392⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 70).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 70).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0070
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 70).n (RamanujanPV.LocalCellsMillion.rows.get 70).Lu := RamanujanPV.FiniteScalarMillion.log_source_0070
example : (RamanujanPV.LocalCellsMillion.rows.get 71)=⟨38358894527,38358896423,14111448682,1644675618,632207973,26795375740686,4486425423907463⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 71).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 71).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0071
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 71).n (RamanujanPV.LocalCellsMillion.rows.get 71).Lu := RamanujanPV.FiniteScalarMillion.log_source_0071
example : (RamanujanPV.LocalCellsMillion.rows.get 72)=⟨38358896423,38358898199,14111449380,1644675690,632207999,26795375795032,4486425636562792⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 72).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 72).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0072
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 72).n (RamanujanPV.LocalCellsMillion.rows.get 72).Lu := RamanujanPV.FiniteScalarMillion.log_source_0072
example : (RamanujanPV.LocalCellsMillion.rows.get 73)=⟨38358898199,38358899921,14111450033,1644675770,632208032,26795375845939,4486425835758818⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 73).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 73).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0073
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 73).n (RamanujanPV.LocalCellsMillion.rows.get 73).Lu := RamanujanPV.FiniteScalarMillion.log_source_0073
example : (RamanujanPV.LocalCellsMillion.rows.get 74)=⟨38358899921,38358902147,14111450666,1644675849,632208066,26795375895298,4486426028898233⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 74).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 74).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0074
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 74).n (RamanujanPV.LocalCellsMillion.rows.get 74).Lu := RamanujanPV.FiniteScalarMillion.log_source_0074
example : (RamanujanPV.LocalCellsMillion.rows.get 75)=⟨38358902147,38358904391,14111451485,1644675942,632208102,26795375959104,4486426278566179⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 75).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 75).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0075
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 75).n (RamanujanPV.LocalCellsMillion.rows.get 75).Lu := RamanujanPV.FiniteScalarMillion.log_source_0075
example : (RamanujanPV.LocalCellsMillion.rows.get 76)=⟨38358904391,38358906653,14111452311,1644676034,632208137,26795376023425,4486426530253161⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 76).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 76).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0076
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 76).n (RamanujanPV.LocalCellsMillion.rows.get 76).Lu := RamanujanPV.FiniteScalarMillion.log_source_0076
example : (RamanujanPV.LocalCellsMillion.rows.get 77)=⟨38358906653,38358909263,14111453143,1644676134,632208178,26795376088263,4486426783958845⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 77).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 77).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0077
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 77).n (RamanujanPV.LocalCellsMillion.rows.get 77).Lu := RamanujanPV.FiniteScalarMillion.log_source_0077
example : (RamanujanPV.LocalCellsMillion.rows.get 78)=⟨38358909263,38358911567,14111454103,1644676250,632208226,26795376163075,4486427076696351⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 78).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 78).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0078
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 78).n (RamanujanPV.LocalCellsMillion.rows.get 78).Lu := RamanujanPV.FiniteScalarMillion.log_source_0078
example : (RamanujanPV.LocalCellsMillion.rows.get 79)=⟨38358911567,38358913699,14111454951,1644676344,632208262,26795376229117,4486427335112729⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 79).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 79).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0079
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 79).n (RamanujanPV.LocalCellsMillion.rows.get 79).Lu := RamanujanPV.FiniteScalarMillion.log_source_0079
example : (RamanujanPV.LocalCellsMillion.rows.get 80)=⟨38358913699,38358916111,14111455735,1644676436,632208299,26795376290228,4486427574237736⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 80).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 80).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0080
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 80).n (RamanujanPV.LocalCellsMillion.rows.get 80).Lu := RamanujanPV.FiniteScalarMillion.log_source_0080
example : (RamanujanPV.LocalCellsMillion.rows.get 81)=⟨38358916111,38358918751,14111456622,1644676535,632208337,26795376359365,4486427844767499⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 81).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 81).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0081
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 81).n (RamanujanPV.LocalCellsMillion.rows.get 81).Lu := RamanujanPV.FiniteScalarMillion.log_source_0081
example : (RamanujanPV.LocalCellsMillion.rows.get 82)=⟨38358918751,38358921481,14111457594,1644676640,632208376,26795376435037,4486428140869783⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 82).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 82).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0082
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 82).n (RamanujanPV.LocalCellsMillion.rows.get 82).Lu := RamanujanPV.FiniteScalarMillion.log_source_0082
example : (RamanujanPV.LocalCellsMillion.rows.get 83)=⟨38358921481,38358924629,14111458598,1644676765,632208429,26795376513289,4486428447066415⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 83).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 83).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0083
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 83).n (RamanujanPV.LocalCellsMillion.rows.get 83).Lu := RamanujanPV.FiniteScalarMillion.log_source_0083
example : (RamanujanPV.LocalCellsMillion.rows.get 84)=⟨38358924629,38358928217,14111459756,1644676908,632208489,26795376603523,4486428800145806⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 84).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 84).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0084
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 84).n (RamanujanPV.LocalCellsMillion.rows.get 84).Lu := RamanujanPV.FiniteScalarMillion.log_source_0084
example : (RamanujanPV.LocalCellsMillion.rows.get 85)=⟨38358928217,38358931519,14111461076,1644677050,632208542,26795376706368,4486429202575741⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 85).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 85).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0085
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 85).n (RamanujanPV.LocalCellsMillion.rows.get 85).Lu := RamanujanPV.FiniteScalarMillion.log_source_0085
example : (RamanujanPV.LocalCellsMillion.rows.get 86)=⟨38358931519,38358934459,14111462291,1644677174,632208585,26795376801016,4486429572927793⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 86).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 86).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0086
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 86).n (RamanujanPV.LocalCellsMillion.rows.get 86).Lu := RamanujanPV.FiniteScalarMillion.log_source_0086
example : (RamanujanPV.LocalCellsMillion.rows.get 87)=⟨38358934459,38358936793,14111463372,1644677291,632208628,26795376885288,4486429902677900⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 87).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 87).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0087
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 87).n (RamanujanPV.LocalCellsMillion.rows.get 87).Lu := RamanujanPV.FiniteScalarMillion.log_source_0087
example : (RamanujanPV.LocalCellsMillion.rows.get 88)=⟨38358936793,38358939193,14111464231,1644677378,632208658,26795376952189,4486430164459215⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 88).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 88).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0088
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 88).n (RamanujanPV.LocalCellsMillion.rows.get 88).Lu := RamanujanPV.FiniteScalarMillion.log_source_0088
example : (RamanujanPV.LocalCellsMillion.rows.get 89)=⟨38358939193,38358941519,14111465114,1644677471,632208692,26795377020982,4486430433643052⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 89).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 89).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0089
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 89).n (RamanujanPV.LocalCellsMillion.rows.get 89).Lu := RamanujanPV.FiniteScalarMillion.log_source_0089
example : (RamanujanPV.LocalCellsMillion.rows.get 90)=⟨38358941519,38358943691,14111465969,1644677559,632208723,26795377087654,4486430694527032⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 90).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 90).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0090
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 90).n (RamanujanPV.LocalCellsMillion.rows.get 90).Lu := RamanujanPV.FiniteScalarMillion.log_source_0090
example : (RamanujanPV.LocalCellsMillion.rows.get 91)=⟨38358943691,38358946289,14111466768,1644677656,632208763,26795377149912,4486430938138346⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 91).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 91).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0091
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 91).n (RamanujanPV.LocalCellsMillion.rows.get 91).Lu := RamanujanPV.FiniteScalarMillion.log_source_0091
example : (RamanujanPV.LocalCellsMillion.rows.get 92)=⟨38358946289,38358948989,14111467724,1644677770,632208810,26795377224380,4486431229529916⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 92).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 92).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0092
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 92).n (RamanujanPV.LocalCellsMillion.rows.get 92).Lu := RamanujanPV.FiniteScalarMillion.log_source_0092
example : (RamanujanPV.LocalCellsMillion.rows.get 93)=⟨38358948989,38358952153,14111468717,1644677888,632208858,26795377301772,4486431532361746⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 93).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 93).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0093
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 93).n (RamanujanPV.LocalCellsMillion.rows.get 93).Lu := RamanujanPV.FiniteScalarMillion.log_source_0093
example : (RamanujanPV.LocalCellsMillion.rows.get 94)=⟨38358952153,38358955189,14111469881,1644678016,632208906,26795377392464,4486431887235779⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 94).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 94).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0094
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 94).n (RamanujanPV.LocalCellsMillion.rows.get 94).Lu := RamanujanPV.FiniteScalarMillion.log_source_0094
example : (RamanujanPV.LocalCellsMillion.rows.get 95)=⟨38358955189,38358958273,14111470998,1644678146,632208958,26795377479487,4486432227753345⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 95).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 95).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0095
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 95).n (RamanujanPV.LocalCellsMillion.rows.get 95).Lu := RamanujanPV.FiniteScalarMillion.log_source_0095
example : (RamanujanPV.LocalCellsMillion.rows.get 96)=⟨38358958273,38358961831,14111472133,1644678277,632209010,26795377567887,4486432573654395⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 96).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 96).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0096
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 96).n (RamanujanPV.LocalCellsMillion.rows.get 96).Lu := RamanujanPV.FiniteScalarMillion.log_source_0096
example : (RamanujanPV.LocalCellsMillion.rows.get 97)=⟨38358961831,38358965149,14111473442,1644678426,632209068,26795377669872,4486432972719518⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 97).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 97).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0097
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 97).n (RamanujanPV.LocalCellsMillion.rows.get 97).Lu := RamanujanPV.FiniteScalarMillion.log_source_0097
example : (RamanujanPV.LocalCellsMillion.rows.get 98)=⟨38358965149,38358968251,14111474662,1644678548,632209110,26795377764978,4486433344866206⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 98).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 98).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0098
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 98).n (RamanujanPV.LocalCellsMillion.rows.get 98).Lu := RamanujanPV.FiniteScalarMillion.log_source_0098
example : (RamanujanPV.LocalCellsMillion.rows.get 99)=⟨38358968251,38358971317,14111475804,1644678676,632209159,26795377853893,4486433692786286⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 99).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 99).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0099
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 99).n (RamanujanPV.LocalCellsMillion.rows.get 99).Lu := RamanujanPV.FiniteScalarMillion.log_source_0099
example : (RamanujanPV.LocalCellsMillion.rows.get 100)=⟨38358971317,38358974519,14111476932,1644678795,632209202,26795377941776,4486434036668623⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 100).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 100).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0100
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 100).n (RamanujanPV.LocalCellsMillion.rows.get 100).Lu := RamanujanPV.FiniteScalarMillion.log_source_0100
example : (RamanujanPV.LocalCellsMillion.rows.get 101)=⟨38358974519,38358977623,14111478109,1644678921,632209248,26795378033558,4486434395804586⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 101).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 101).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0101
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 101).n (RamanujanPV.LocalCellsMillion.rows.get 101).Lu := RamanujanPV.FiniteScalarMillion.log_source_0101
example : (RamanujanPV.LocalCellsMillion.rows.get 102)=⟨38358977623,38358980563,14111479251,1644679036,632209288,26795378122530,4486434743949033⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 102).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 102).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0102
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 102).n (RamanujanPV.LocalCellsMillion.rows.get 102).Lu := RamanujanPV.FiniteScalarMillion.log_source_0102
example : (RamanujanPV.LocalCellsMillion.rows.get 103)=⟨38358980563,38358983317,14111480333,1644679146,632209326,26795378206801,4486435073699275⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 103).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 103).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0103
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 103).n (RamanujanPV.LocalCellsMillion.rows.get 103).Lu := RamanujanPV.FiniteScalarMillion.log_source_0103
example : (RamanujanPV.LocalCellsMillion.rows.get 104)=⟨38358983317,38358986051,14111481346,1644679261,632209371,26795378285741,4486435382587693⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 104).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 104).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0104
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 104).n (RamanujanPV.LocalCellsMillion.rows.get 104).Lu := RamanujanPV.FiniteScalarMillion.log_source_0104
example : (RamanujanPV.LocalCellsMillion.rows.get 105)=⟨38358986051,38358988867,14111482352,1644679372,632209413,26795378364108,4486435689232865⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 105).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 105).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0105
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 105).n (RamanujanPV.LocalCellsMillion.rows.get 105).Lu := RamanujanPV.FiniteScalarMillion.log_source_0105
example : (RamanujanPV.LocalCellsMillion.rows.get 106)=⟨38358988867,38358991813,14111483388,1644679487,632209457,26795378444825,4486436005075220⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 106).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 106).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0106
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 106).n (RamanujanPV.LocalCellsMillion.rows.get 106).Lu := RamanujanPV.FiniteScalarMillion.log_source_0106
example : (RamanujanPV.LocalCellsMillion.rows.get 107)=⟨38358991813,38358995123,14111484472,1644679613,632209507,26795378529268,4486436335498411⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 107).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 107).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0107
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 107).n (RamanujanPV.LocalCellsMillion.rows.get 107).Lu := RamanujanPV.FiniteScalarMillion.log_source_0107
example : (RamanujanPV.LocalCellsMillion.rows.get 108)=⟨38358995123,38358998731,14111485689,1644679763,632209570,26795378624145,4486436706747744⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 108).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 108).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0108
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 108).n (RamanujanPV.LocalCellsMillion.rows.get 108).Lu := RamanujanPV.FiniteScalarMillion.log_source_0108
example : (RamanujanPV.LocalCellsMillion.rows.get 109)=⟨38358998731,38359002049,14111487017,1644679913,632209628,26795378727564,4486437111420695⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 109).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 109).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0109
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 109).n (RamanujanPV.LocalCellsMillion.rows.get 109).Lu := RamanujanPV.FiniteScalarMillion.log_source_0109
example : (RamanujanPV.LocalCellsMillion.rows.get 110)=⟨38359002049,38359005511,14111488237,1644680059,632209688,26795378822670,4486437483567354⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 110).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 110).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0110
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 110).n (RamanujanPV.LocalCellsMillion.rows.get 110).Lu := RamanujanPV.FiniteScalarMillion.log_source_0110
example : (RamanujanPV.LocalCellsMillion.rows.get 111)=⟨38359005511,38359008841,14111489511,1644680203,632209744,26795378921904,4486437871864967⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 111).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 111).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0111
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 111).n (RamanujanPV.LocalCellsMillion.rows.get 111).Lu := RamanujanPV.FiniteScalarMillion.log_source_0111
example : (RamanujanPV.LocalCellsMillion.rows.get 112)=⟨38359008841,38359012141,14111490736,1644680334,632209792,26795379017354,4486438245357533⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 112).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 112).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0112
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 112).n (RamanujanPV.LocalCellsMillion.rows.get 112).Lu := RamanujanPV.FiniteScalarMillion.log_source_0112
example : (RamanujanPV.LocalCellsMillion.rows.get 113)=⟨38359012141,38359015813,14111491950,1644680476,632209849,26795379111944,4486438615485314⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 113).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 113).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0113
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 113).n (RamanujanPV.LocalCellsMillion.rows.get 113).Lu := RamanujanPV.FiniteScalarMillion.log_source_0113
example : (RamanujanPV.LocalCellsMillion.rows.get 114)=⟨38359015813,38359019441,14111493301,1644680621,632209903,26795379217197,4486439027336566⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 114).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 114).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0114
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 114).n (RamanujanPV.LocalCellsMillion.rows.get 114).Lu := RamanujanPV.FiniteScalarMillion.log_source_0114
example : (RamanujanPV.LocalCellsMillion.rows.get 115)=⟨38359019441,38359022963,14111494635,1644680757,632209950,26795379321189,4486439434252744⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 115).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 115).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0115
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 115).n (RamanujanPV.LocalCellsMillion.rows.get 115).Lu := RamanujanPV.FiniteScalarMillion.log_source_0115
example : (RamanujanPV.LocalCellsMillion.rows.get 116)=⟨38359022963,38359026583,14111495931,1644680905,632210008,26795379422143,4486439829279908⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 116).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 116).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0116
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 116).n (RamanujanPV.LocalCellsMillion.rows.get 116).Lu := RamanujanPV.FiniteScalarMillion.log_source_0116
example : (RamanujanPV.LocalCellsMillion.rows.get 117)=⟨38359026583,38359029911,14111497263,1644681056,632210067,26795379525906,4486440235298749⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 117).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 117).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0117
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 117).n (RamanujanPV.LocalCellsMillion.rows.get 117).Lu := RamanujanPV.FiniteScalarMillion.log_source_0117
example : (RamanujanPV.LocalCellsMillion.rows.get 118)=⟨38359029911,38359033249,14111498487,1644681203,632210127,26795379621298,4486440608567091⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 118).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 118).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0118
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 118).n (RamanujanPV.LocalCellsMillion.rows.get 118).Lu := RamanujanPV.FiniteScalarMillion.log_source_0118
example : (RamanujanPV.LocalCellsMillion.rows.get 119)=⟨38359033249,38359036433,14111499715,1644681339,632210179,26795379716978,4486440982956801⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 119).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 119).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0119
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 119).n (RamanujanPV.LocalCellsMillion.rows.get 119).Lu := RamanujanPV.FiniteScalarMillion.log_source_0119
example : (RamanujanPV.LocalCellsMillion.rows.get 120)=⟨38359036433,38359039349,14111500886,1644681458,632210220,26795379808243,4486441340074014⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 120).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 120).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0120
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 120).n (RamanujanPV.LocalCellsMillion.rows.get 120).Lu := RamanujanPV.FiniteScalarMillion.log_source_0120
example : (RamanujanPV.LocalCellsMillion.rows.get 121)=⟨38359039349,38359042261,14111501959,1644681587,632210273,26795379891826,4486441667132389⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 121).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 121).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0121
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 121).n (RamanujanPV.LocalCellsMillion.rows.get 121).Lu := RamanujanPV.FiniteScalarMillion.log_source_0121
example : (RamanujanPV.LocalCellsMillion.rows.get 122)=⟨38359042261,38359045289,14111503030,1644681710,632210322,26795379975295,4486441993742012⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 122).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 122).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0122
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 122).n (RamanujanPV.LocalCellsMillion.rows.get 122).Lu := RamanujanPV.FiniteScalarMillion.log_source_0122
example : (RamanujanPV.LocalCellsMillion.rows.get 123)=⟨38359045289,38359048381,14111504144,1644681832,632210368,26795380062089,4486442333362181⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 123).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 123).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0123
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 123).n (RamanujanPV.LocalCellsMillion.rows.get 123).Lu := RamanujanPV.FiniteScalarMillion.log_source_0123
example : (RamanujanPV.LocalCellsMillion.rows.get 124)=⟨38359048381,38359050931,14111505282,1644681952,632210411,26795380150717,4486442680160663⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 124).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 124).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0124
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 124).n (RamanujanPV.LocalCellsMillion.rows.get 124).Lu := RamanujanPV.FiniteScalarMillion.log_source_0124
example : (RamanujanPV.LocalCellsMillion.rows.get 125)=⟨38359050931,38359053547,14111506220,1644682048,632210445,26795380223809,4486442966168515⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 125).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 125).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0125
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 125).n (RamanujanPV.LocalCellsMillion.rows.get 125).Lu := RamanujanPV.FiniteScalarMillion.log_source_0125
example : (RamanujanPV.LocalCellsMillion.rows.get 126)=⟨38359053547,38359056121,14111507182,1644682159,632210489,26795380298793,4486443259578887⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 126).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 126).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0126
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 126).n (RamanujanPV.LocalCellsMillion.rows.get 126).Lu := RamanujanPV.FiniteScalarMillion.log_source_0126
example : (RamanujanPV.LocalCellsMillion.rows.get 127)=⟨38359056121,38359058377,14111508129,1644682258,632210524,26795380372574,4486443548278395⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 127).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 127).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0127
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 127).n (RamanujanPV.LocalCellsMillion.rows.get 127).Lu := RamanujanPV.FiniteScalarMillion.log_source_0127
example : (RamanujanPV.LocalCellsMillion.rows.get 128)=⟨38359058377,38359060847,14111508959,1644682359,632210566,26795380437239,4486443801311207⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 128).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 128).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0128
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 128).n (RamanujanPV.LocalCellsMillion.rows.get 128).Lu := RamanujanPV.FiniteScalarMillion.log_source_0128
example : (RamanujanPV.LocalCellsMillion.rows.get 129)=⟨38359060847,38359063063,14111509868,1644682451,632210598,26795380508038,4486444078346245⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 129).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 129).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0129
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 129).n (RamanujanPV.LocalCellsMillion.rows.get 129).Lu := RamanujanPV.FiniteScalarMillion.log_source_0129
example : (RamanujanPV.LocalCellsMillion.rows.get 130)=⟨38359063063,38359065487,14111510683,1644682541,632210632,26795380571557,4486444326892566⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 130).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 130).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0130
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 130).n (RamanujanPV.LocalCellsMillion.rows.get 130).Lu := RamanujanPV.FiniteScalarMillion.log_source_0130
example : (RamanujanPV.LocalCellsMillion.rows.get 131)=⟨38359065487,38359068157,14111511575,1644682633,632210664,26795380641038,4486444598768156⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 131).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 131).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0131
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 131).n (RamanujanPV.LocalCellsMillion.rows.get 131).Lu := RamanujanPV.FiniteScalarMillion.log_source_0131
example : (RamanujanPV.LocalCellsMillion.rows.get 132)=⟨38359068157,38359070699,14111512557,1644682746,632210709,26795380717570,4486444898235127⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 132).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 132).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0132
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 132).n (RamanujanPV.LocalCellsMillion.rows.get 132).Lu := RamanujanPV.FiniteScalarMillion.log_source_0132
example : (RamanujanPV.LocalCellsMillion.rows.get 133)=⟨38359070699,38359073219,14111513492,1644682852,632210750,26795380790433,4486445183345636⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 133).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 133).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0133
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 133).n (RamanujanPV.LocalCellsMillion.rows.get 133).Lu := RamanujanPV.FiniteScalarMillion.log_source_0133
example : (RamanujanPV.LocalCellsMillion.rows.get 134)=⟨38359073219,38359075441,14111514419,1644682959,632210793,26795380862665,4486445465988693⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 134).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 134).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0134
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 134).n (RamanujanPV.LocalCellsMillion.rows.get 134).Lu := RamanujanPV.FiniteScalarMillion.log_source_0134
example : (RamanujanPV.LocalCellsMillion.rows.get 135)=⟨38359075441,38359077703,14111515237,1644683049,632210827,26795380926356,4486445715207964⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 135).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 135).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0135
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 135).n (RamanujanPV.LocalCellsMillion.rows.get 135).Lu := RamanujanPV.FiniteScalarMillion.log_source_0135
example : (RamanujanPV.LocalCellsMillion.rows.get 136)=⟨38359077703,38359079593,14111516069,1644683132,632210855,26795380991193,4486445968913722⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 136).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 136).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0136
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 136).n (RamanujanPV.LocalCellsMillion.rows.get 136).Lu := RamanujanPV.FiniteScalarMillion.log_source_0136
example : (RamanujanPV.LocalCellsMillion.rows.get 137)=⟨38359079593,38359081837,14111516764,1644683215,632210889,26795381045367,4486446180896011⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 137).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 137).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0137
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 137).n (RamanujanPV.LocalCellsMillion.rows.get 137).Lu := RamanujanPV.FiniteScalarMillion.log_source_0137
example : (RamanujanPV.LocalCellsMillion.rows.get 138)=⟨38359081837,38359083701,14111517590,1644683299,632210918,26795381109689,4486446432582731⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 138).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 138).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0138
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 138).n (RamanujanPV.LocalCellsMillion.rows.get 138).Lu := RamanujanPV.FiniteScalarMillion.log_source_0138
example : (RamanujanPV.LocalCellsMillion.rows.get 139)=⟨38359083701,38359085641,14111518275,1644683375,632210947,26795381163118,4486446641648817⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 139).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 139).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0139
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 139).n (RamanujanPV.LocalCellsMillion.rows.get 139).Lu := RamanujanPV.FiniteScalarMillion.log_source_0139
example : (RamanujanPV.LocalCellsMillion.rows.get 140)=⟨38359085641,38359087579,14111518989,1644683450,632210974,26795381218725,4486446859239130⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 140).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 140).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0140
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 140).n (RamanujanPV.LocalCellsMillion.rows.get 140).Lu := RamanujanPV.FiniteScalarMillion.log_source_0140
example : (RamanujanPV.LocalCellsMillion.rows.get 141)=⟨38359087579,38359089443,14111519702,1644683526,632211002,26795381274275,4486447076605067⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 141).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 141).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0141
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 141).n (RamanujanPV.LocalCellsMillion.rows.get 141).Lu := RamanujanPV.FiniteScalarMillion.log_source_0141
example : (RamanujanPV.LocalCellsMillion.rows.get 142)=⟨38359089443,38359091753,14111520388,1644683601,632211030,26795381327704,4486447285671152⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 142).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 142).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0142
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 142).n (RamanujanPV.LocalCellsMillion.rows.get 142).Lu := RamanujanPV.FiniteScalarMillion.log_source_0142
example : (RamanujanPV.LocalCellsMillion.rows.get 143)=⟨38359091753,38359094369,14111521237,1644683697,632211067,26795381393917,4486447544760554⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 143).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 143).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0143
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 143).n (RamanujanPV.LocalCellsMillion.rows.get 143).Lu := RamanujanPV.FiniteScalarMillion.log_source_0143
example : (RamanujanPV.LocalCellsMillion.rows.get 144)=⟨38359094369,38359097003,14111522200,1644683808,632211111,26795381468901,4486447838170900⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 144).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 144).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0144
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 144).n (RamanujanPV.LocalCellsMillion.rows.get 144).Lu := RamanujanPV.FiniteScalarMillion.log_source_0144
example : (RamanujanPV.LocalCellsMillion.rows.get 145)=⟨38359097003,38359099763,14111523169,1644683920,632211156,26795381544401,4486448133600115⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 145).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 145).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0145
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 145).n (RamanujanPV.LocalCellsMillion.rows.get 145).Lu := RamanujanPV.FiniteScalarMillion.log_source_0145
example : (RamanujanPV.LocalCellsMillion.rows.get 146)=⟨38359099763,38359103171,14111524184,1644684041,632211205,26795381623513,4486448443161412⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 146).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 146).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0146
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 146).n (RamanujanPV.LocalCellsMillion.rows.get 146).Lu := RamanujanPV.FiniteScalarMillion.log_source_0146
example : (RamanujanPV.LocalCellsMillion.rows.get 147)=⟨38359103171,38359107047,14111525438,1644684192,632211267,26795381721199,4486448825402337⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 147).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 147).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0147
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 147).n (RamanujanPV.LocalCellsMillion.rows.get 147).Lu := RamanujanPV.FiniteScalarMillion.log_source_0147
example : (RamanujanPV.LocalCellsMillion.rows.get 148)=⟨38359107047,38359110799,14111526864,1644684355,632211331,26795381832299,4486449260134194⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 148).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 148).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0148
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 148).n (RamanujanPV.LocalCellsMillion.rows.get 148).Lu := RamanujanPV.FiniteScalarMillion.log_source_0148
example : (RamanujanPV.LocalCellsMillion.rows.get 149)=⟨38359110799,38359114609,14111528244,1644684508,632211390,26795381939845,4486449680958170⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 149).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 149).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0149
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 149).n (RamanujanPV.LocalCellsMillion.rows.get 149).Lu := RamanujanPV.FiniteScalarMillion.log_source_0149
example : (RamanujanPV.LocalCellsMillion.rows.get 150)=⟨38359114609,38359118311,14111529646,1644684665,632211450,26795382049054,4486450108287332⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 150).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 150).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0150
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 150).n (RamanujanPV.LocalCellsMillion.rows.get 150).Lu := RamanujanPV.FiniteScalarMillion.log_source_0150
example : (RamanujanPV.LocalCellsMillion.rows.get 151)=⟨38359118311,38359121729,14111531008,1644684818,632211509,26795382155166,4486450523503443⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 151).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 151).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0151
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 151).n (RamanujanPV.LocalCellsMillion.rows.get 151).Lu := RamanujanPV.FiniteScalarMillion.log_source_0151
example : (RamanujanPV.LocalCellsMillion.rows.get 152)=⟨38359121729,38359124971,14111532265,1644684961,632211565,26795382253139,4486450906865890⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 152).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 152).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0152
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 152).n (RamanujanPV.LocalCellsMillion.rows.get 152).Lu := RamanujanPV.FiniteScalarMillion.log_source_0152
example : (RamanujanPV.LocalCellsMillion.rows.get 153)=⟨38359124971,38359128331,14111533458,1644685103,632211623,26795382346066,4486451270488392⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 153).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 153).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0153
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 153).n (RamanujanPV.LocalCellsMillion.rows.get 153).Lu := RamanujanPV.FiniteScalarMillion.log_source_0153
example : (RamanujanPV.LocalCellsMillion.rows.get 154)=⟨38359128331,38359132291,14111534694,1644685254,632211686,26795382442376,4486451647345645⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 154).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 154).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0154
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 154).n (RamanujanPV.LocalCellsMillion.rows.get 154).Lu := RamanujanPV.FiniteScalarMillion.log_source_0154
example : (RamanujanPV.LocalCellsMillion.rows.get 155)=⟨38359132291,38359136191,14111536151,1644685403,632211738,26795382555884,4486452091498868⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 155).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 155).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0155
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 155).n (RamanujanPV.LocalCellsMillion.rows.get 155).Lu := RamanujanPV.FiniteScalarMillion.log_source_0155
example : (RamanujanPV.LocalCellsMillion.rows.get 156)=⟨38359136191,38359140367,14111537585,1644685572,632211806,26795382667672,4486452528922524⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 156).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 156).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0156
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 156).n (RamanujanPV.LocalCellsMillion.rows.get 156).Lu := RamanujanPV.FiniteScalarMillion.log_source_0156
example : (RamanujanPV.LocalCellsMillion.rows.get 157)=⟨38359140367,38359144211,14111539122,1644685732,632211863,26795382787371,4486452997302336⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 157).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 157).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0157
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 157).n (RamanujanPV.LocalCellsMillion.rows.get 157).Lu := RamanujanPV.FiniteScalarMillion.log_source_0157
example : (RamanujanPV.LocalCellsMillion.rows.get 158)=⟨38359144211,38359147681,14111540536,1644685877,632211914,26795382897554,4486453428445002⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 158).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 158).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0158
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 158).n (RamanujanPV.LocalCellsMillion.rows.get 158).Lu := RamanujanPV.FiniteScalarMillion.log_source_0158
example : (RamanujanPV.LocalCellsMillion.rows.get 159)=⟨38359147681,38359150457,14111541812,1644686011,632211962,26795382997017,4486453817639828⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 159).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 159).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0159
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 159).n (RamanujanPV.LocalCellsMillion.rows.get 159).Lu := RamanujanPV.FiniteScalarMillion.log_source_0159
example : (RamanujanPV.LocalCellsMillion.rows.get 160)=⟨38359150457,38359153361,14111542833,1644686125,632212006,26795383076587,4486454128995754⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 160).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 160).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0160
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 160).n (RamanujanPV.LocalCellsMillion.rows.get 160).Lu := RamanujanPV.FiniteScalarMillion.log_source_0160
example : (RamanujanPV.LocalCellsMillion.rows.get 161)=⟨38359153361,38359155677,14111543902,1644686232,632212042,26795383159826,4486454454708136⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 161).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 161).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0161
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 161).n (RamanujanPV.LocalCellsMillion.rows.get 161).Lu := RamanujanPV.FiniteScalarMillion.log_source_0161
example : (RamanujanPV.LocalCellsMillion.rows.get 162)=⟨38359155677,38359157987,14111544754,1644686334,632212084,26795383226211,4486454714470459⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 162).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 162).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0162
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 162).n (RamanujanPV.LocalCellsMillion.rows.get 162).Lu := RamanujanPV.FiniteScalarMillion.log_source_0162
example : (RamanujanPV.LocalCellsMillion.rows.get 163)=⟨38359157987,38359160207,14111545604,1644686425,632212118,26795383292424,4486454973559825⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 163).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 163).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0163
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 163).n (RamanujanPV.LocalCellsMillion.rows.get 163).Lu := RamanujanPV.FiniteScalarMillion.log_source_0163
example : (RamanujanPV.LocalCellsMillion.rows.get 164)=⟨38359160207,38359162327,14111546420,1644686518,632212154,26795383356057,4486455222554844⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 164).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 164).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0164
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 164).n (RamanujanPV.LocalCellsMillion.rows.get 164).Lu := RamanujanPV.FiniteScalarMillion.log_source_0164
example : (RamanujanPV.LocalCellsMillion.rows.get 165)=⟨38359162327,38359164251,14111547200,1644686593,632212178,26795383416824,4486455460333811⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 165).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 165).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0165
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 165).n (RamanujanPV.LocalCellsMillion.rows.get 165).Lu := RamanujanPV.FiniteScalarMillion.log_source_0165
example : (RamanujanPV.LocalCellsMillion.rows.get 166)=⟨38359164251,38359166453,14111547908,1644686684,632212218,26795383471973,4486455676129425⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 166).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 166).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0166
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 166).n (RamanujanPV.LocalCellsMillion.rows.get 166).Lu := RamanujanPV.FiniteScalarMillion.log_source_0166
example : (RamanujanPV.LocalCellsMillion.rows.get 167)=⟨38359166453,38359168759,14111548718,1644686776,632212254,26795383535090,4486455923105572⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 167).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 167).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0167
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 167).n (RamanujanPV.LocalCellsMillion.rows.get 167).Lu := RamanujanPV.FiniteScalarMillion.log_source_0167
example : (RamanujanPV.LocalCellsMillion.rows.get 168)=⟨38359168759,38359170769,14111549566,1644686865,632212286,26795383601188,4486456181746350⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 168).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 168).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0168
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 168).n (RamanujanPV.LocalCellsMillion.rows.get 168).Lu := RamanujanPV.FiniteScalarMillion.log_source_0168
example : (RamanujanPV.LocalCellsMillion.rows.get 169)=⟨38359170769,38359172611,14111550306,1644686946,632212316,26795383658802,4486456407187724⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 169).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 169).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0169
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 169).n (RamanujanPV.LocalCellsMillion.rows.get 169).Lu := RamanujanPV.FiniteScalarMillion.log_source_0169
example : (RamanujanPV.LocalCellsMillion.rows.get 170)=⟨38359172611,38359174831,14111550983,1644687031,632212352,26795383711600,4486456613786320⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 170).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 170).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0170
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 170).n (RamanujanPV.LocalCellsMillion.rows.get 170).Lu := RamanujanPV.FiniteScalarMillion.log_source_0170
example : (RamanujanPV.LocalCellsMillion.rows.get 171)=⟨38359174831,38359176643,14111551800,1644687118,632212384,26795383775234,4486456862781164⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 171).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 171).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0171
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 171).n (RamanujanPV.LocalCellsMillion.rows.get 171).Lu := RamanujanPV.FiniteScalarMillion.log_source_0171
example : (RamanujanPV.LocalCellsMillion.rows.get 172)=⟨38359176643,38359179029,14111552467,1644687199,632212418,26795383827172,4486457066014977⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 172).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 172).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0172
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 172).n (RamanujanPV.LocalCellsMillion.rows.get 172).Lu := RamanujanPV.FiniteScalarMillion.log_source_0172
example : (RamanujanPV.LocalCellsMillion.rows.get 173)=⟨38359179029,38359181387,14111553344,1644687295,632212454,26795383895563,4486457333628556⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 173).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 173).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0173
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 173).n (RamanujanPV.LocalCellsMillion.rows.get 173).Lu := RamanujanPV.FiniteScalarMillion.log_source_0173
example : (RamanujanPV.LocalCellsMillion.rows.get 174)=⟨38359181387,38359183853,14111554212,1644687392,632212491,26795383963152,4486457598101559⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 174).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 174).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0174
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 174).n (RamanujanPV.LocalCellsMillion.rows.get 174).Lu := RamanujanPV.FiniteScalarMillion.log_source_0174
example : (RamanujanPV.LocalCellsMillion.rows.get 175)=⟨38359183853,38359186057,14111555119,1644687483,632212522,26795384033836,4486457874687942⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 175).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 175).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0175
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 175).n (RamanujanPV.LocalCellsMillion.rows.get 175).Lu := RamanujanPV.FiniteScalarMillion.log_source_0175
example : (RamanujanPV.LocalCellsMillion.rows.get 176)=⟨38359186057,38359188383,14111555930,1644687570,632212554,26795384097011,4486458121888285⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 176).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 176).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0176
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 176).n (RamanujanPV.LocalCellsMillion.rows.get 176).Lu := RamanujanPV.FiniteScalarMillion.log_source_0176
example : (RamanujanPV.LocalCellsMillion.rows.get 177)=⟨38359188383,38359190957,14111556786,1644687670,632212594,26795384163682,4486458382772295⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 177).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 177).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0177
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 177).n (RamanujanPV.LocalCellsMillion.rows.get 177).Lu := RamanujanPV.FiniteScalarMillion.log_source_0177
example : (RamanujanPV.LocalCellsMillion.rows.get 178)=⟨38359190957,38359193507,14111557733,1644687780,632212638,26795384237463,4486458671471720⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 178).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 178).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0178
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 178).n (RamanujanPV.LocalCellsMillion.rows.get 178).Lu := RamanujanPV.FiniteScalarMillion.log_source_0178
example : (RamanujanPV.LocalCellsMillion.rows.get 179)=⟨38359193507,38359195579,14111558671,1644687875,632212671,26795384310555,4486458957479485⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 179).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 179).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0179
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 179).n (RamanujanPV.LocalCellsMillion.rows.get 179).Lu := RamanujanPV.FiniteScalarMillion.log_source_0179
example : (RamanujanPV.LocalCellsMillion.rows.get 180)=⟨38359195579,38359197719,14111559433,1644687964,632212707,26795384369946,4486459189874785⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 180).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 180).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0180
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 180).n (RamanujanPV.LocalCellsMillion.rows.get 180).Lu := RamanujanPV.FiniteScalarMillion.log_source_0180
example : (RamanujanPV.LocalCellsMillion.rows.get 181)=⟨38359197719,38359200239,14111560220,1644688057,632212744,26795384431286,4486459429896978⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 181).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 181).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0181
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 181).n (RamanujanPV.LocalCellsMillion.rows.get 181).Lu := RamanujanPV.FiniteScalarMillion.log_source_0181
example : (RamanujanPV.LocalCellsMillion.rows.get 182)=⟨38359200239,38359202573,14111561147,1644688155,632212780,26795384503518,4486459712539957⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 182).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 182).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0182
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 182).n (RamanujanPV.LocalCellsMillion.rows.get 182).Lu := RamanujanPV.FiniteScalarMillion.log_source_0182
example : (RamanujanPV.LocalCellsMillion.rows.get 183)=⟨38359202573,38359204847,14111562006,1644688254,632212819,26795384570419,4486459974321123⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 183).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 183).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0183
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 183).n (RamanujanPV.LocalCellsMillion.rows.get 183).Lu := RamanujanPV.FiniteScalarMillion.log_source_0183
example : (RamanujanPV.LocalCellsMillion.rows.get 184)=⟨38359204847,38359207063,14111562842,1644688346,632212854,26795384635600,4486460229372725⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 184).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 184).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0184
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 184).n (RamanujanPV.LocalCellsMillion.rows.get 184).Lu := RamanujanPV.FiniteScalarMillion.log_source_0184
example : (RamanujanPV.LocalCellsMillion.rows.get 185)=⟨38359207063,38359208963,14111563658,1644688431,632212884,26795384699118,4486460477919137⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 185).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 185).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0185
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 185).n (RamanujanPV.LocalCellsMillion.rows.get 185).Lu := RamanujanPV.FiniteScalarMillion.log_source_0185
example : (RamanujanPV.LocalCellsMillion.rows.get 186)=⟨38359208963,38359211039,14111564357,1644688514,632212918,26795384753579,4486460691022906⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 186).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 186).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0186
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 186).n (RamanujanPV.LocalCellsMillion.rows.get 186).Lu := RamanujanPV.FiniteScalarMillion.log_source_0186
example : (RamanujanPV.LocalCellsMillion.rows.get 187)=⟨38359211039,38359213051,14111565120,1644688598,632212950,26795384813084,4486460923866947⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 187).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 187).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0187
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 187).n (RamanujanPV.LocalCellsMillion.rows.get 187).Lu := RamanujanPV.FiniteScalarMillion.log_source_0187
example : (RamanujanPV.LocalCellsMillion.rows.get 188)=⟨38359213051,38359215491,14111565860,1644688683,632212983,26795384870755,4486461149532676⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 188).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 188).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0188
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 188).n (RamanujanPV.LocalCellsMillion.rows.get 188).Lu := RamanujanPV.FiniteScalarMillion.log_source_0188
example : (RamanujanPV.LocalCellsMillion.rows.get 189)=⟨38359215491,38359218241,14111566758,1644688795,632213031,26795384940694,4486461423202840⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 189).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 189).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0189
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 189).n (RamanujanPV.LocalCellsMillion.rows.get 189).Lu := RamanujanPV.FiniteScalarMillion.log_source_0189
example : (RamanujanPV.LocalCellsMillion.rows.get 190)=⟨38359218241,38359221203,14111567770,1644688912,632213077,26795385019519,4486461731642521⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 190).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 190).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0190
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 190).n (RamanujanPV.LocalCellsMillion.rows.get 190).Lu := RamanujanPV.FiniteScalarMillion.log_source_0190
example : (RamanujanPV.LocalCellsMillion.rows.get 191)=⟨38359221203,38359224187,14111568859,1644689041,632213130,26795385104421,4486462063860044⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 191).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 191).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0191
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 191).n (RamanujanPV.LocalCellsMillion.rows.get 191).Lu := RamanujanPV.FiniteScalarMillion.log_source_0191
example : (RamanujanPV.LocalCellsMillion.rows.get 192)=⟨38359224187,38359227407,14111569957,1644689170,632213182,26795385189953,4486462398545182⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 192).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 192).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0192
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 192).n (RamanujanPV.LocalCellsMillion.rows.get 192).Lu := RamanujanPV.FiniteScalarMillion.log_source_0192
example : (RamanujanPV.LocalCellsMillion.rows.get 193)=⟨38359227407,38359230367,14111571142,1644689298,632213229,26795385282249,4486462759700154⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 193).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 193).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0193
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 193).n (RamanujanPV.LocalCellsMillion.rows.get 193).Lu := RamanujanPV.FiniteScalarMillion.log_source_0193
example : (RamanujanPV.LocalCellsMillion.rows.get 194)=⟨38359230367,38359233709,14111572231,1644689424,632213279,26795385367093,4486463091693463⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 194).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 194).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0194
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 194).n (RamanujanPV.LocalCellsMillion.rows.get 194).Lu := RamanujanPV.FiniteScalarMillion.log_source_0194
example : (RamanujanPV.LocalCellsMillion.rows.get 195)=⟨38359233709,38359237627,14111573460,1644689572,632213340,26795385462887,4486463466531762⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 195).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 195).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0195
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 195).n (RamanujanPV.LocalCellsMillion.rows.get 195).Lu := RamanujanPV.FiniteScalarMillion.log_source_0195
example : (RamanujanPV.LocalCellsMillion.rows.get 196)=⟨38359237627,38359241399,14111574901,1644689725,632213396,26795385575191,4486463905974192⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 196).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 196).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0196
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 196).n (RamanujanPV.LocalCellsMillion.rows.get 196).Lu := RamanujanPV.FiniteScalarMillion.log_source_0196
example : (RamanujanPV.LocalCellsMillion.rows.get 197)=⟨38359241399,38359245083,14111576289,1644689881,632213456,26795385683310,4486464329041293⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 197).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 197).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0197
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 197).n (RamanujanPV.LocalCellsMillion.rows.get 197).Lu := RamanujanPV.FiniteScalarMillion.log_source_0197
example : (RamanujanPV.LocalCellsMillion.rows.get 198)=⟨38359245083,38359249069,14111577644,1644690028,632213511,26795385788906,4486464742238423⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 198).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 198).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0198
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 198).n (RamanujanPV.LocalCellsMillion.rows.get 198).Lu := RamanujanPV.FiniteScalarMillion.log_source_0198
example : (RamanujanPV.LocalCellsMillion.rows.get 199)=⟨38359249069,38359253291,14111579111,1644690197,632213578,26795385903159,4486465189307735⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 199).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 199).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0199
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 199).n (RamanujanPV.LocalCellsMillion.rows.get 199).Lu := RamanujanPV.FiniteScalarMillion.log_source_0199
example : (RamanujanPV.LocalCellsMillion.rows.get 200)=⟨38359253291,38359257743,14111580664,1644690366,632213641,26795386024176,4486465662846876⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 200).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 200).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0200
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 200).n (RamanujanPV.LocalCellsMillion.rows.get 200).Lu := RamanujanPV.FiniteScalarMillion.log_source_0200
example : (RamanujanPV.LocalCellsMillion.rows.get 201)=⟨38359257743,38359262443,14111582302,1644690556,632213717,26795386151787,4486466162182557⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 201).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 201).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0201
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 201).n (RamanujanPV.LocalCellsMillion.rows.get 201).Lu := RamanujanPV.FiniteScalarMillion.log_source_0201
example : (RamanujanPV.LocalCellsMillion.rows.get 202)=⟨38359262443,38359267127,14111584031,1644690750,632213792,26795386286505,4486466689334146⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 202).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 202).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0202
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 202).n (RamanujanPV.LocalCellsMillion.rows.get 202).Lu := RamanujanPV.FiniteScalarMillion.log_source_0202
example : (RamanujanPV.LocalCellsMillion.rows.get 203)=⟨38359267127,38359272037,14111585754,1644690935,632213860,26795386420765,4486467214691068⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 203).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 203).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0203
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 203).n (RamanujanPV.LocalCellsMillion.rows.get 203).Lu := RamanujanPV.FiniteScalarMillion.log_source_0203
example : (RamanujanPV.LocalCellsMillion.rows.get 204)=⟨38359272037,38359276937,14111587560,1644691145,632213944,26795386561503,4486467765396112⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 204).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 204).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0204
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 204).n (RamanujanPV.LocalCellsMillion.rows.get 204).Lu := RamanujanPV.FiniteScalarMillion.log_source_0204
example : (RamanujanPV.LocalCellsMillion.rows.get 205)=⟨38359276937,38359282051,14111589363,1644691340,632214016,26795386701954,4486468314979613⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 205).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 205).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0205
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 205).n (RamanujanPV.LocalCellsMillion.rows.get 205).Lu := RamanujanPV.FiniteScalarMillion.log_source_0205
example : (RamanujanPV.LocalCellsMillion.rows.get 206)=⟨38359282051,38359286767,14111591244,1644691551,632214098,26795386848539,4486468888565324⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 206).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 206).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0206
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 206).n (RamanujanPV.LocalCellsMillion.rows.get 206).Lu := RamanujanPV.FiniteScalarMillion.log_source_0206
example : (RamanujanPV.LocalCellsMillion.rows.get 207)=⟨38359286767,38359291741,14111592979,1644691741,632214169,26795386983716,4486469417511379⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 207).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 207).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0207
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 207).n (RamanujanPV.LocalCellsMillion.rows.get 207).Lu := RamanujanPV.FiniteScalarMillion.log_source_0207
example : (RamanujanPV.LocalCellsMillion.rows.get 208)=⟨38359291741,38359296329,14111594809,1644691941,632214244,26795387126289,4486469975394544⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 208).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 208).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0208
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 208).n (RamanujanPV.LocalCellsMillion.rows.get 208).Lu := RamanujanPV.FiniteScalarMillion.log_source_0208
example : (RamanujanPV.LocalCellsMillion.rows.get 209)=⟨38359296329,38359300543,14111596497,1644692123,632214312,26795387257797,4486470489984135⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 209).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 209).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0209
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 209).n (RamanujanPV.LocalCellsMillion.rows.get 209).Lu := RamanujanPV.FiniteScalarMillion.log_source_0209
example : (RamanujanPV.LocalCellsMillion.rows.get 210)=⟨38359300543,38359305349,14111598047,1644692310,632214389,26795387378585,4486470962625898⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 210).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 210).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0210
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 210).n (RamanujanPV.LocalCellsMillion.rows.get 210).Lu := RamanujanPV.FiniteScalarMillion.log_source_0210
example : (RamanujanPV.LocalCellsMillion.rows.get 211)=⟨38359305349,38359310609,14111599815,1644692509,632214466,26795387516342,4486471501666275⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 211).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 211).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0211
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 211).n (RamanujanPV.LocalCellsMillion.rows.get 211).Lu := RamanujanPV.FiniteScalarMillion.log_source_0211
example : (RamanujanPV.LocalCellsMillion.rows.get 212)=⟨38359310609,38359315531,14111601750,1644692723,632214547,26795387667111,4486472091627439⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 212).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 212).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0212
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 212).n (RamanujanPV.LocalCellsMillion.rows.get 212).Lu := RamanujanPV.FiniteScalarMillion.log_source_0212
example : (RamanujanPV.LocalCellsMillion.rows.get 213)=⟨38359315531,38359320563,14111603561,1644692934,632214632,26795387808193,4486472643678345⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 213).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 213).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0213
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 213).n (RamanujanPV.LocalCellsMillion.rows.get 213).Lu := RamanujanPV.FiniteScalarMillion.log_source_0213
example : (RamanujanPV.LocalCellsMillion.rows.get 214)=⟨38359320563,38359325429,14111605412,1644693134,632214706,26795387952428,4486473208066829⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 214).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 214).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0214
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 214).n (RamanujanPV.LocalCellsMillion.rows.get 214).Lu := RamanujanPV.FiniteScalarMillion.log_source_0214
example : (RamanujanPV.LocalCellsMillion.rows.get 215)=⟨38359325429,38359330409,14111607202,1644693337,632214785,26795388091904,4486473753836911⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 215).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 215).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0215
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 215).n (RamanujanPV.LocalCellsMillion.rows.get 215).Lu := RamanujanPV.FiniteScalarMillion.log_source_0215
example : (RamanujanPV.LocalCellsMillion.rows.get 216)=⟨38359330409,38359335457,14111609034,1644693529,632214854,26795388234648,4486474312393153⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 216).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 216).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0216
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 216).n (RamanujanPV.LocalCellsMillion.rows.get 216).Lu := RamanujanPV.FiniteScalarMillion.log_source_0216
example : (RamanujanPV.LocalCellsMillion.rows.get 217)=⟨38359335457,38359340639,14111610891,1644693742,632214938,26795388379342,4486474878576113⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 217).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 217).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0217
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 217).n (RamanujanPV.LocalCellsMillion.rows.get 217).Lu := RamanujanPV.FiniteScalarMillion.log_source_0217
example : (RamanujanPV.LocalCellsMillion.rows.get 218)=⟨38359340639,38359345361,14111612797,1644693954,632215019,26795388527876,4486475459788643⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 218).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 218).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0218
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 218).n (RamanujanPV.LocalCellsMillion.rows.get 218).Lu := RamanujanPV.FiniteScalarMillion.log_source_0218
example : (RamanujanPV.LocalCellsMillion.rows.get 219)=⟨38359345361,38359350479,14111614535,1644694146,632215092,26795388663225,4486475989407588⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 219).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 219).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0219
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 219).n (RamanujanPV.LocalCellsMillion.rows.get 219).Lu := RamanujanPV.FiniteScalarMillion.log_source_0219
example : (RamanujanPV.LocalCellsMillion.rows.get 220)=⟨38359350479,38359355813,14111616417,1644694372,632215185,26795388809924,4486476563441963⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 220).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 220).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0220
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 220).n (RamanujanPV.LocalCellsMillion.rows.get 220).Lu := RamanujanPV.FiniteScalarMillion.log_source_0220
example : (RamanujanPV.LocalCellsMillion.rows.get 221)=⟨38359355813,38359361393,14111618380,1644694595,632215272,26795388962815,4486477161702750⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 221).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 221).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0221
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 221).n (RamanujanPV.LocalCellsMillion.rows.get 221).Lu := RamanujanPV.FiniteScalarMillion.log_source_0221
example : (RamanujanPV.LocalCellsMillion.rows.get 222)=⟨38359361393,38359366807,14111620432,1644694831,632215365,26795389122757,4486477787554896⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 222).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 222).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0222
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 222).n (RamanujanPV.LocalCellsMillion.rows.get 222).Lu := RamanujanPV.FiniteScalarMillion.log_source_0222
example : (RamanujanPV.LocalCellsMillion.rows.get 223)=⟨38359366807,38359372343,14111622424,1644695063,632215458,26795389277941,4486478394788473⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 223).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 223).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0223
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 223).n (RamanujanPV.LocalCellsMillion.rows.get 223).Lu := RamanujanPV.FiniteScalarMillion.log_source_0223
example : (RamanujanPV.LocalCellsMillion.rows.get 224)=⟨38359372343,38359378843,14111624461,1644695304,632215556,26795389436622,4486479015705537⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 224).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 224).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0224
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 224).n (RamanujanPV.LocalCellsMillion.rows.get 224).Lu := RamanujanPV.FiniteScalarMillion.log_source_0224
example : (RamanujanPV.LocalCellsMillion.rows.get 225)=⟨38359378843,38359385593,14111626852,1644695568,632215656,26795389622934,4486479744744810⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 225).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 225).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0225
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 225).n (RamanujanPV.LocalCellsMillion.rows.get 225).Lu := RamanujanPV.FiniteScalarMillion.log_source_0225
example : (RamanujanPV.LocalCellsMillion.rows.get 226)=⟨38359385593,38359392109,14111629335,1644695834,632215754,26795389816412,4486480501824018⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 226).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 226).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0226
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 226).n (RamanujanPV.LocalCellsMillion.rows.get 226).Lu := RamanujanPV.FiniteScalarMillion.log_source_0226
example : (RamanujanPV.LocalCellsMillion.rows.get 227)=⟨38359392109,38359398313,14111631732,1644696101,632215856,26795390003183,4486481232657764⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 227).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 227).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0227
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 227).n (RamanujanPV.LocalCellsMillion.rows.get 227).Lu := RamanujanPV.FiniteScalarMillion.log_source_0227
example : (RamanujanPV.LocalCellsMillion.rows.get 228)=⟨38359398313,38359404491,14111634015,1644696355,632215953,26795390181011,4486481928497620⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 228).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 228).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0228
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 228).n (RamanujanPV.LocalCellsMillion.rows.get 228).Lu := RamanujanPV.FiniteScalarMillion.log_source_0228
example : (RamanujanPV.LocalCellsMillion.rows.get 229)=⟨38359404491,38359409707,14111636287,1644696588,632216035,26795390358094,4486482621421268⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 229).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 229).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0229
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 229).n (RamanujanPV.LocalCellsMillion.rows.get 229).Lu := RamanujanPV.FiniteScalarMillion.log_source_0229
example : (RamanujanPV.LocalCellsMillion.rows.get 230)=⟨38359409707,38359414867,14111638206,1644696810,632216123,26795390507602,4486483206447241⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 230).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 230).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0230
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 230).n (RamanujanPV.LocalCellsMillion.rows.get 230).Lu := RamanujanPV.FiniteScalarMillion.log_source_0230
example : (RamanujanPV.LocalCellsMillion.rows.get 231)=⟨38359414867,38359420037,14111640104,1644697030,632216211,26795390655505,4486483785192229⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 231).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 231).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0231
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 231).n (RamanujanPV.LocalCellsMillion.rows.get 231).Lu := RamanujanPV.FiniteScalarMillion.log_source_0231
example : (RamanujanPV.LocalCellsMillion.rows.get 232)=⟨38359420037,38359424951,14111642006,1644697250,632216298,26795390803695,4486484365058748⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 232).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 232).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0232
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 232).n (RamanujanPV.LocalCellsMillion.rows.get 232).Lu := RamanujanPV.FiniteScalarMillion.log_source_0232
example : (RamanujanPV.LocalCellsMillion.rows.get 233)=⟨38359424951,38359429643,14111643814,1644697450,632216374,26795390944547,4486484916212361⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 233).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 233).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0233
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 233).n (RamanujanPV.LocalCellsMillion.rows.get 233).Lu := RamanujanPV.FiniteScalarMillion.log_source_0233
example : (RamanujanPV.LocalCellsMillion.rows.get 234)=⟨38359429643,38359434371,14111645540,1644697642,632216448,26795391079036,4486485442466431⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 234).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 234).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0234
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 234).n (RamanujanPV.LocalCellsMillion.rows.get 234).Lu := RamanujanPV.FiniteScalarMillion.log_source_0234
example : (RamanujanPV.LocalCellsMillion.rows.get 235)=⟨38359434371,38359439641,14111647280,1644697846,632216530,26795391214556,4486485972758399⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 235).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 235).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0235
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 235).n (RamanujanPV.LocalCellsMillion.rows.get 235).Lu := RamanujanPV.FiniteScalarMillion.log_source_0235
example : (RamanujanPV.LocalCellsMillion.rows.get 236)=⟨38359439641,38359444549,14111649218,1644698056,632216608,26795391365612,4486486563840938⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 236).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 236).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0236
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 236).n (RamanujanPV.LocalCellsMillion.rows.get 236).Lu := RamanujanPV.FiniteScalarMillion.log_source_0236
example : (RamanujanPV.LocalCellsMillion.rows.get 237)=⟨38359444549,38359449773,14111651024,1644698269,632216694,26795391506292,4486487114321572⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 237).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 237).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0237
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 237).n (RamanujanPV.LocalCellsMillion.rows.get 237).Lu := RamanujanPV.FiniteScalarMillion.log_source_0237
example : (RamanujanPV.LocalCellsMillion.rows.get 238)=⟨38359449773,38359454933,14111652946,1644698471,632216767,26795391656030,4486487700244658⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 238).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 238).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0238
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 238).n (RamanujanPV.LocalCellsMillion.rows.get 238).Lu := RamanujanPV.FiniteScalarMillion.log_source_0238
example : (RamanujanPV.LocalCellsMillion.rows.get 239)=⟨38359454933,38359460779,14111654844,1644698676,632216843,26795391803933,4486488278989596⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 239).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 239).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0239
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 239).n (RamanujanPV.LocalCellsMillion.rows.get 239).Lu := RamanujanPV.FiniteScalarMillion.log_source_0239
example : (RamanujanPV.LocalCellsMillion.rows.get 240)=⟨38359460779,38359466489,14111656995,1644698917,632216936,26795391971499,4486488934676211⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 240).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 240).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0240
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 240).n (RamanujanPV.LocalCellsMillion.rows.get 240).Lu := RamanujanPV.FiniteScalarMillion.log_source_0240
example : (RamanujanPV.LocalCellsMillion.rows.get 241)=⟨38359466489,38359471973,14111659095,1644699152,632217026,26795392135167,4486489575109040⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 241).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 241).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0241
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 241).n (RamanujanPV.LocalCellsMillion.rows.get 241).Lu := RamanujanPV.FiniteScalarMillion.log_source_0241
example : (RamanujanPV.LocalCellsMillion.rows.get 242)=⟨38359471973,38359477543,14111661113,1644699379,632217114,26795392292357,4486490190193743⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 242).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 242).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0242
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 242).n (RamanujanPV.LocalCellsMillion.rows.get 242).Lu := RamanujanPV.FiniteScalarMillion.log_source_0242
example : (RamanujanPV.LocalCellsMillion.rows.get 243)=⟨38359477543,38359483081,14111663162,1644699609,632217203,26795392452012,4486490814924196⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 243).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 243).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0243
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 243).n (RamanujanPV.LocalCellsMillion.rows.get 243).Lu := RamanujanPV.FiniteScalarMillion.log_source_0243
example : (RamanujanPV.LocalCellsMillion.rows.get 244)=⟨38359483081,38359488707,14111665199,1644699841,632217294,26795392610749,4486491436065655⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 244).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 244).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0244
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 244).n (RamanujanPV.LocalCellsMillion.rows.get 244).Lu := RamanujanPV.FiniteScalarMillion.log_source_0244
example : (RamanujanPV.LocalCellsMillion.rows.get 245)=⟨38359488707,38359494487,14111667269,1644700072,632217382,26795392772009,4486492067077071⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 245).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 245).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0245
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 245).n (RamanujanPV.LocalCellsMillion.rows.get 245).Lu := RamanujanPV.FiniteScalarMillion.log_source_0245
example : (RamanujanPV.LocalCellsMillion.rows.get 246)=⟨38359494487,38359500979,14111669395,1644700321,632217482,26795392937684,4486492715360956⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 246).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 246).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0246
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 246).n (RamanujanPV.LocalCellsMillion.rows.get 246).Lu := RamanujanPV.FiniteScalarMillion.log_source_0246
example : (RamanujanPV.LocalCellsMillion.rows.get 247)=⟨38359500979,38359507957,14111671783,1644700605,632217598,26795393123766,4486493443502876⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 247).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 247).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0247
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 247).n (RamanujanPV.LocalCellsMillion.rows.get 247).Lu := RamanujanPV.FiniteScalarMillion.log_source_0247
example : (RamanujanPV.LocalCellsMillion.rows.get 248)=⟨38359507957,38359515409,14111674350,1644700911,632217723,26795393323779,4486494226154375⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 248).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 248).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0248
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 248).n (RamanujanPV.LocalCellsMillion.rows.get 248).Lu := RamanujanPV.FiniteScalarMillion.log_source_0248
example : (RamanujanPV.LocalCellsMillion.rows.get 249)=⟨38359515409,38359523077,14111677092,1644701228,632217849,26795393537378,4486495061969709⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 249).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 249).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0249
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 249).n (RamanujanPV.LocalCellsMillion.rows.get 249).Lu := RamanujanPV.FiniteScalarMillion.log_source_0249
example : (RamanujanPV.LocalCellsMillion.rows.get 250)=⟨38359523077,38359531073,14111679913,1644701543,632217970,26795393757169,4486495922011439⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 250).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 250).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0250
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 250).n (RamanujanPV.LocalCellsMillion.rows.get 250).Lu := RamanujanPV.FiniteScalarMillion.log_source_0250
example : (RamanujanPV.LocalCellsMillion.rows.get 251)=⟨38359531073,38359538813,14111682854,1644701883,632218105,26795393986360,4486496818841852⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 251).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 251).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0251
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 251).n (RamanujanPV.LocalCellsMillion.rows.get 251).Lu := RamanujanPV.FiniteScalarMillion.log_source_0251
example : (RamanujanPV.LocalCellsMillion.rows.get 252)=⟨38359538813,38359547417,14111685702,1644702218,632218240,26795394208215,4486497686959022⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 252).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 252).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0252
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 252).n (RamanujanPV.LocalCellsMillion.rows.get 252).Lu := RamanujanPV.FiniteScalarMillion.log_source_0252
example : (RamanujanPV.LocalCellsMillion.rows.get 253)=⟨38359547417,38359555303,14111688867,1644702549,632218359,26795394454834,4486498651982481⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 253).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 253).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0253
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 253).n (RamanujanPV.LocalCellsMillion.rows.get 253).Lu := RamanujanPV.FiniteScalarMillion.log_source_0253
example : (RamanujanPV.LocalCellsMillion.rows.get 254)=⟨38359555303,38359563301,14111691768,1644702870,632218481,26795394680873,4486499536475102⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 254).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 254).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0254
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 254).n (RamanujanPV.LocalCellsMillion.rows.get 254).Lu := RamanujanPV.FiniteScalarMillion.log_source_0254
example : (RamanujanPV.LocalCellsMillion.rows.get 255)=⟨38359563301,38359571581,14111694710,1644703217,632218621,26795394910122,4486500433529660⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 255).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 255).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0255
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 255).n (RamanujanPV.LocalCellsMillion.rows.get 255).Lu := RamanujanPV.FiniteScalarMillion.log_source_0255
example : (RamanujanPV.LocalCellsMillion.rows.get 256)=⟨38359571581,38359579597,14111697756,1644703559,632218753,26795395147454,4486501362213291⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 256).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 256).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0256
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 256).n (RamanujanPV.LocalCellsMillion.rows.get 256).Lu := RamanujanPV.FiniteScalarMillion.log_source_0256
example : (RamanujanPV.LocalCellsMillion.rows.get 257)=⟨38359579597,38359588297,14111700705,1644703903,632218891,26795395377219,4486502261286685⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 257).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 257).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0257
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 257).n (RamanujanPV.LocalCellsMillion.rows.get 257).Lu := RamanujanPV.FiniteScalarMillion.log_source_0257
example : (RamanujanPV.LocalCellsMillion.rows.get 258)=⟨38359588297,38359597583,14111703906,1644704268,632219034,26795395626589,4486503237077518⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 258).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 258).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0258
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 258).n (RamanujanPV.LocalCellsMillion.rows.get 258).Lu := RamanujanPV.FiniteScalarMillion.log_source_0258
example : (RamanujanPV.LocalCellsMillion.rows.get 259)=⟨38359597583,38359606697,14111707322,1644704650,632219181,26795395892756,4486504278593954⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 259).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 259).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0259
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 259).n (RamanujanPV.LocalCellsMillion.rows.get 259).Lu := RamanujanPV.FiniteScalarMillion.log_source_0259
example : (RamanujanPV.LocalCellsMillion.rows.get 260)=⟨38359606697,38359615871,14111710675,1644705018,632219320,26795396153993,4486505300818861⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 260).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 260).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0260
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 260).n (RamanujanPV.LocalCellsMillion.rows.get 260).Lu := RamanujanPV.FiniteScalarMillion.log_source_0260
example : (RamanujanPV.LocalCellsMillion.rows.get 261)=⟨38359615871,38359624879,14111714050,1644705377,632219451,26795396416950,4486506329773305⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 261).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 261).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0261
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 261).n (RamanujanPV.LocalCellsMillion.rows.get 261).Lu := RamanujanPV.FiniteScalarMillion.log_source_0261
example : (RamanujanPV.LocalCellsMillion.rows.get 262)=⟨38359624879,38359634011,14111717364,1644705755,632219599,26795396675149,4486507340109177⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 262).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 262).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0262
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 262).n (RamanujanPV.LocalCellsMillion.rows.get 262).Lu := RamanujanPV.FiniteScalarMillion.log_source_0262
example : (RamanujanPV.LocalCellsMillion.rows.get 263)=⟨38359634011,38359642291,14111720723,1644706118,632219734,26795396936902,4486508364352891⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 263).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 263).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0263
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 263).n (RamanujanPV.LocalCellsMillion.rows.get 263).Lu := RamanujanPV.FiniteScalarMillion.log_source_0263
example : (RamanujanPV.LocalCellsMillion.rows.get 264)=⟨38359642291,38359650319,14111723769,1644706447,632219856,26795397174233,4486509293036548⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 264).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 264).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0264
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 264).n (RamanujanPV.LocalCellsMillion.rows.get 264).Lu := RamanujanPV.FiniteScalarMillion.log_source_0264
example : (RamanujanPV.LocalCellsMillion.rows.get 265)=⟨38359650319,38359658549,14111726722,1644706770,632219977,26795397404342,4486510193455718⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 265).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 265).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0265
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 265).n (RamanujanPV.LocalCellsMillion.rows.get 265).Lu := RamanujanPV.FiniteScalarMillion.log_source_0265
example : (RamanujanPV.LocalCellsMillion.rows.get 266)=⟨38359658549,38359666703,14111729750,1644707116,632220113,26795397640240,4486511116531323⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 266).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 266).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0266
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 266).n (RamanujanPV.LocalCellsMillion.rows.get 266).Lu := RamanujanPV.FiniteScalarMillion.log_source_0266
example : (RamanujanPV.LocalCellsMillion.rows.get 267)=⟨38359666703,38359675261,14111732750,1644707460,632220249,26795397873960,4486512031082697⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 267).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 267).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0267
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 267).n (RamanujanPV.LocalCellsMillion.rows.get 267).Lu := RamanujanPV.FiniteScalarMillion.log_source_0267
example : (RamanujanPV.LocalCellsMillion.rows.get 268)=⟨38359675261,38359684787,14111735898,1644707831,632220399,26795398119260,4486512990946621⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 268).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 268).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0268
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 268).n (RamanujanPV.LocalCellsMillion.rows.get 268).Lu := RamanujanPV.FiniteScalarMillion.log_source_0268
example : (RamanujanPV.LocalCellsMillion.rows.get 269)=⟨38359684787,38359693727,14111739402,1644708220,632220547,26795398392306,4486514059381254⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 269).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 269).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0269
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 269).n (RamanujanPV.LocalCellsMillion.rows.get 269).Lu := RamanujanPV.FiniteScalarMillion.log_source_0269
example : (RamanujanPV.LocalCellsMillion.rows.get 270)=⟨38359693727,38359702247,14111742691,1644708583,632220685,26795398648555,4486515062090259⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 270).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 270).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0270
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 270).n (RamanujanPV.LocalCellsMillion.rows.get 270).Lu := RamanujanPV.FiniteScalarMillion.log_source_0270
example : (RamanujanPV.LocalCellsMillion.rows.get 271)=⟨38359702247,38359710511,14111745826,1644708923,632220812,26795398892765,4486516017692187⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 271).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 271).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0271
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 271).n (RamanujanPV.LocalCellsMillion.rows.get 271).Lu := RamanujanPV.FiniteScalarMillion.log_source_0271
example : (RamanujanPV.LocalCellsMillion.rows.get 272)=⟨38359710511,38359719883,14111748866,1644709292,632220965,26795399129638,4486516944581049⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 272).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 272).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0272
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 272).n (RamanujanPV.LocalCellsMillion.rows.get 272).Lu := RamanujanPV.FiniteScalarMillion.log_source_0272
example : (RamanujanPV.LocalCellsMillion.rows.get 273)=⟨38359719883,38359729249,14111752314,1644709686,632221120,26795399398269,4486517995743132⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 273).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 273).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0273
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 273).n (RamanujanPV.LocalCellsMillion.rows.get 273).Lu := RamanujanPV.FiniteScalarMillion.log_source_0273
example : (RamanujanPV.LocalCellsMillion.rows.get 274)=⟨38359729249,38359739389,14111755759,1644710086,632221279,26795399666728,4486519046232238⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 274).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 274).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0274
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 274).n (RamanujanPV.LocalCellsMillion.rows.get 274).Lu := RamanujanPV.FiniteScalarMillion.log_source_0274
example : (RamanujanPV.LocalCellsMillion.rows.get 275)=⟨38359739389,38359749713,14111759489,1644710511,632221446,26795399957373,4486520183532919⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 275).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 275).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0275
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 275).n (RamanujanPV.LocalCellsMillion.rows.get 275).Lu := RamanujanPV.FiniteScalarMillion.log_source_0275
example : (RamanujanPV.LocalCellsMillion.rows.get 276)=⟨38359749713,38359760407,14111763287,1644710960,632221628,26795400253292,4486521341470988⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 276).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 276).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0276
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 276).n (RamanujanPV.LocalCellsMillion.rows.get 276).Lu := RamanujanPV.FiniteScalarMillion.log_source_0276
example : (RamanujanPV.LocalCellsMillion.rows.get 277)=⟨38359760407,38359770941,14111767221,1644711409,632221804,26795400559815,4486522540908400⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 277).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 277).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0277
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 277).n (RamanujanPV.LocalCellsMillion.rows.get 277).Lu := RamanujanPV.FiniteScalarMillion.log_source_0277
example : (RamanujanPV.LocalCellsMillion.rows.get 278)=⟨38359770941,38359781483,14111771097,1644711842,632221970,26795400861753,4486523722400025⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 278).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 278).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0278
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 278).n (RamanujanPV.LocalCellsMillion.rows.get 278).Lu := RamanujanPV.FiniteScalarMillion.log_source_0278
example : (RamanujanPV.LocalCellsMillion.rows.get 279)=⟨38359781483,38359791521,14111774975,1644712267,632222130,26795401163920,4486524904788954⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 279).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 279).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0279
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 279).n (RamanujanPV.LocalCellsMillion.rows.get 279).Lu := RamanujanPV.FiniteScalarMillion.log_source_0279
example : (RamanujanPV.LocalCellsMillion.rows.get 280)=⟨38359791521,38359801813,14111778668,1644712680,632222289,26795401451640,4486526030649433⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 280).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 280).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0280
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 280).n (RamanujanPV.LocalCellsMillion.rows.get 280).Lu := RamanujanPV.FiniteScalarMillion.log_source_0280
example : (RamanujanPV.LocalCellsMillion.rows.get 281)=⟨38359801813,38359812311,14111782454,1644713095,632222446,26795401746641,4486527184998389⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 281).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 281).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0281
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 281).n (RamanujanPV.LocalCellsMillion.rows.get 281).Lu := RamanujanPV.FiniteScalarMillion.log_source_0281
example : (RamanujanPV.LocalCellsMillion.rows.get 282)=⟨38359812311,38359822469,14111786316,1644713516,632222603,26795402047547,4486528362452178⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 282).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 282).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0282
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 282).n (RamanujanPV.LocalCellsMillion.rows.get 282).Lu := RamanujanPV.FiniteScalarMillion.log_source_0282
example : (RamanujanPV.LocalCellsMillion.rows.get 283)=⟨38359822469,38359832683,14111790053,1644713932,632222763,26795402338706,4486529501771858⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 283).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 283).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0283
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 283).n (RamanujanPV.LocalCellsMillion.rows.get 283).Lu := RamanujanPV.FiniteScalarMillion.log_source_0283
example : (RamanujanPV.LocalCellsMillion.rows.get 284)=⟨38359832683,38359837684,14111793810,1644714148,632222921,26795402631471,4486530647372318⟩ := by rfl
example : RamanujanPV.FiniteLogExecution.check (RamanujanPV.LocalCellsMillion.rows.get 284).n (2^35) 35 (RamanujanPV.LocalCellsMillion.rows.get 284).Lu=true := RamanujanPV.FiniteScalarMillion.log_checked_0284
example : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get 284).n (RamanujanPV.LocalCellsMillion.rows.get 284).Lu := RamanujanPV.FiniteScalarMillion.log_source_0284
example (i : Nat) (hi : i<285) : RamanujanPV.FiniteLogExecution.SourceExecution (RamanujanPV.LocalCellsMillion.rows.get i).n (RamanujanPV.LocalCellsMillion.rows.get i).Lu := RamanujanPV.FiniteScalarMillion.all_log_source i hi
example (i : Nat) (hi : i<285) : Real.log ((RamanujanPV.LocalCellsMillion.rows.get i).n:ℝ)≤((RamanujanPV.LocalCellsMillion.rows.get i).Lu:ℝ)/(2:ℝ)^40 := RamanujanPV.FiniteScalarMillion.all_log_real_upper i hi
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0000
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0000
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0001
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0001
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0002
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0002
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0003
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0003
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0004
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0004
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0005
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0005
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0006
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0006
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0007
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0007
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0008
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0008
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0009
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0009
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0010
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0010
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0011
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0011
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0012
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0012
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0013
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0013
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0014
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0014
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0015
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0015
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0016
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0016
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0017
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0017
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0018
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0018
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0019
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0019
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0020
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0020
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0021
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0021
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0022
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0022
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0023
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0023
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0024
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0024
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0025
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0025
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0026
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0026
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0027
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0027
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0028
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0028
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0029
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0029
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0030
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0030
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0031
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0031
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0032
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0032
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0033
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0033
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0034
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0034
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0035
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0035
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0036
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0036
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0037
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0037
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0038
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0038
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0039
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0039
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0040
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0040
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0041
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0041
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0042
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0042
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0043
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0043
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0044
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0044
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0045
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0045
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0046
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0046
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0047
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0047
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0048
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0048
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0049
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0049
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0050
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0050
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0051
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0051
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0052
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0052
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0053
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0053
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0054
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0054
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0055
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0055
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0056
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0056
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0057
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0057
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0058
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0058
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0059
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0059
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0060
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0060
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0061
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0061
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0062
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0062
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0063
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0063
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0064
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0064
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0065
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0065
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0066
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0066
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0067
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0067
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0068
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0068
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0069
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0069
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0070
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0070
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0071
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0071
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0072
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0072
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0073
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0073
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0074
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0074
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0075
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0075
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0076
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0076
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0077
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0077
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0078
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0078
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0079
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0079
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0080
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0080
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0081
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0081
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0082
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0082
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0083
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0083
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0084
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0084
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0085
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0085
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0086
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0086
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0087
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0087
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0088
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0088
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0089
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0089
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0090
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0090
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0091
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0091
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0092
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0092
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0093
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0093
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0094
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0094
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0095
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0095
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0096
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0096
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0097
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0097
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0098
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0098
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0099
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0099
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0100
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0100
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0101
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0101
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0102
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0102
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0103
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0103
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0104
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0104
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0105
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0105
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0106
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0106
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0107
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0107
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0108
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0108
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0109
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0109
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0110
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0110
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0111
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0111
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0112
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0112
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0113
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0113
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0114
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0114
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0115
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0115
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0116
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0116
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0117
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0117
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0118
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0118
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0119
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0119
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0120
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0120
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0121
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0121
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0122
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0122
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0123
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0123
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0124
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0124
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0125
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0125
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0126
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0126
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0127
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0127
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0128
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0128
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0129
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0129
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0130
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0130
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0131
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0131
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0132
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0132
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0133
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0133
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0134
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0134
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0135
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0135
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0136
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0136
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0137
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0137
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0138
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0138
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0139
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0139
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0140
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0140
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0141
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0141
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0142
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0142
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0143
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0143
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0144
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0144
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0145
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0145
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0146
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0146
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0147
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0147
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0148
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0148
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0149
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0149
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0150
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0150
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0151
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0151
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0152
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0152
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0153
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0153
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0154
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0154
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0155
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0155
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0156
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0156
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0157
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0157
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0158
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0158
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0159
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0159
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0160
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0160
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0161
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0161
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0162
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0162
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0163
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0163
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0164
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0164
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0165
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0165
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0166
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0166
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0167
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0167
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0168
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0168
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0169
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0169
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0170
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0170
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0171
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0171
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0172
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0172
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0173
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0173
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0174
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0174
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0175
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0175
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0176
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0176
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0177
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0177
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0178
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0178
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0179
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0179
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0180
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0180
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0181
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0181
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0182
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0182
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0183
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0183
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0184
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0184
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0185
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0185
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0186
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0186
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0187
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0187
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0188
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0188
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0189
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0189
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0190
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0190
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0191
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0191
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0192
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0192
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0193
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0193
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0194
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0194
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0195
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0195
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0196
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0196
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0197
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0197
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0198
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0198
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0199
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0199
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0200
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0200
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0201
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0201
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0202
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0202
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0203
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0203
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0204
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0204
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0205
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0205
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0206
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0206
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0207
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0207
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0208
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0208
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0209
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0209
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0210
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0210
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0211
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0211
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0212
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0212
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0213
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0213
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0214
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0214
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0215
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0215
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0216
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0216
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0217
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0217
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0218
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0218
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0219
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0219
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0220
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0220
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0221
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0221
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0222
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0222
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0223
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0223
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0224
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0224
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0225
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0225
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0226
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0226
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0227
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0227
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0228
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0228
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0229
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0229
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0230
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0230
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0231
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0231
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0232
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0232
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0233
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0233
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0234
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0234
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0235
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0235
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0236
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0236
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0237
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0237
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0238
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0238
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0239
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0239
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0240
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0240
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0241
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0241
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0242
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0242
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0243
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0243
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0244
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0244
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0245
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0245
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0246
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0246
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0247
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0247
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0248
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0248
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0249
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0249
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0250
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0250
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0251
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0251
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0252
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0252
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0253
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0253
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0254
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0254
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0255
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0255
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0256
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0256
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0257
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0257
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0258
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0258
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0259
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0259
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0260
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0260
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0261
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0261
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0262
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0262
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0263
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0263
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0264
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0264
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0265
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0265
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0266
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0266
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0267
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0267
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0268
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0268
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0269
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0269
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0270
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0270
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0271
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0271
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0272
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0272
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0273
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0273
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0274
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0274
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0275
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0275
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0276
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0276
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0277
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0277
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0278
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0278
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0279
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0279
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0280
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0280
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0281
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0281
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0282
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0282
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0283
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0283
#print axioms RamanujanPV.FiniteScalarMillion.log_checked_0284
#print axioms RamanujanPV.FiniteScalarMillion.log_source_0284
#print axioms RamanujanPV.FiniteScalarMillion.all_log_runs
#print axioms RamanujanPV.FiniteScalarMillion.all_log_source
#print axioms RamanujanPV.FiniteScalarMillion.all_log_real_upper
end RamanujanPV.ScalarIndependentAudit
