from pathlib import Path
import subprocess,sys,json
R=Path(__file__).resolve().parents[2];bank=R/'research/main-final-total-bank-v3/objects';steps=[]
for module,roots,attempt in [
 ('SynergyAnalytic.CountBoundary100',['SynergyAnalytic.count_boundary_affine_at100_narrow','SynergyAnalytic.count_boundary_affine_at100'],'count-boundary100-root-v1'),
 ('SynergyAnalytic.CountCellOrdinate100',['SynergyAnalytic.source_ordinate_from_count_cells_at100'],'count-cell-ordinate100-root-v1'),
 ('SynergyAnalytic.BackwardHeightContraction',['SynergyAnalytic.fraction_ratio_backward','SynergyAnalytic.pairedFactor_relative_backward','SynergyAnalytic.pairedFactor_backward_300_330','SynergyAnalytic.finiteCoefficient_backward'],'backward-height-contraction-root-v1'),
 ('SynergyAnalytic.SpectralBase300',['SynergyAnalytic.spectralBase_300_tiny'],'spectral-base300-root-v1'),
 ('SynergyAnalytic.HeightBudget300',['SynergyAnalytic.height_spectral_budget_300'],'height-budget300-root-v1'),
 ('SynergyAnalytic.HeightRawSpectral300',['SynergyAnalytic.height_raw_spectral_300'],'height-raw-spectral300-root-v1'),
 ('SynergyAnalytic.DirectPsiSource',['SynergyAnalytic.paired_zero_sum_norm','SynergyAnalytic.CHJ_remainder_normalized_tiny','SynergyAnalytic.direct_psi_normalized_of_raw'],'direct-psi-source-root-v1'),
 ('SynergyAnalytic.HeightPiPsi300',['SynergyAnalytic.pi_300_of_height_caps','SynergyAnalytic.psi_300_of_height_caps'],'height-pi-psi300-root-v1'),
 ('SynergyHeightC.MainPiPsi300Read',['SynergyHeightC.MainPiPsi300Read.pi_psi_300_from_actual_total_read'],'main-pi-psi300-read-v1'),
 ('SynergyHeightC.MainPiPsi300Program',['SynergyHeightC.MainPiPsi300Program.main_observed_pi_psi_300'],'main-pi-psi300-program-v1')]:
 out=R/'research/analytic/work'/attempt
 command=[sys.executable,str(R/'research/main-weight-v1/compile_consumer.py'),'--module',module,'--bank',str(bank),'--out',str(out),'--publish-object']
 for root in roots:command+=['--root',root]
 q=subprocess.run(command,cwd=R)
 if q.returncode:raise SystemExit(q.returncode)
 d=json.loads((out/'RECEIPT.json').read_text());steps.append(dict(module=module,receipt=str(out/'RECEIPT.json'),seconds=d['seconds'],roots=roots))
(B:=R/'research/earlier-onset-v1/SOURCE_RECEIPT.json').write_text(json.dumps(dict(status='PASS_ACTUAL_SOURCE_MAIN_READ_OBSERVED_OUTPUT_PI_AND_DIRECT_PSI_FROM300',steps=steps,
 qualification='Unchanged Csource/model/algorithm/330numericworkload and same14currentanalyticinputs. Earlier300validity derived by new actualcount-at100 proof and backwardpairedtransfer, not substitutedparameter orψfromπ. This is not the originaldifferent-input/all12-row legacyfrontier contract.'),indent=2)+'\n')
print('PASS_ACTUAL_SOURCE_MAIN_READ_OBSERVED_OUTPUT_PI_AND_DIRECT_PSI_FROM300')
