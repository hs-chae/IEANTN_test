# Correction: the PNT numerical closure is not yet entirely source-first

The six conditional Lean conclusions in this package remain valid, with the
recorded exact types and standard-three-axiom closures. The actual C mass and
first-moment programs, their source/execution proofs and observed-output links
also remain valid. The completed source/formula audit is unchanged.

The stronger claim that the entire PNT numerical proof chain has already been
converted to source-first verification is incomplete. A subsequent independent
audit found numerical scalar proofs embedded inline in the earlier kernel-only
overlay. Removing named RowFacts dependencies and all native execution axioms did
not establish source-first coverage of those additional proof sites.

In the research PNT path, [the actual-height-cap proof](../MomentPNT.v1/Dependencies/moment/source/SynergyMomentMath/PointCaps.lean)
reaches [the continuous-count proof](../MomentPNT.v1/Dependencies/moment/base/base/base/base/base/source/SynergyAnalytic/ContinuousProfile.lean), which uses the numerical boundary
providers `source_cseven_upper`, `source_ceight_upper` and `source_log_ge28`.
Their proofs reach `WinnerOriginalScalars.cSeven_upper` and
`WinnerOriginalScalars.height_log_lower` in [OriginalScalars](../MomentPNT.v1/Dependencies/moment/base/base/base/base/base/source/OriginalScalars.lean),
and `WinnerOriginalScalars.eta_bsix_upper`, `WinnerOriginalScalars.ceight_simple_upper`
and `WinnerOriginalScalars.mu_bsix_upper` in [OriginalBoundaryScalars](../MomentPNT.v1/Dependencies/moment/base/base/base/base/base/source/OriginalBoundaryScalars.lean). These were still
discharged by ordinary Lean kernel computation. They were not replaced merely
by verifying the C programs that compute the height profile and moments.

Accordingly, this snapshot combines source-first verified numerical programs
with kernel-only numerical boundary support. It is not a completed source-first
migration of the whole PNT numerical closure. Kernel-only checks are not called
PV. The separately labelled direct-vector controls remain kernel-only.

The old Scoped Winner inventory contains40 such inline scalar proof sites in16
owner declarations, in addition to the named numerical leaves. The actual C
computations for their scalar counterparts have already been proved. Work now
connects those source-derived predicates to the original theorem interfaces and
then checks complete original-site coverage in both PNT paths. No additional
numerical premise or new axiom is authorized by this correction.

The source archive and its hashes are preserved as the exact historical
snapshot. This correction takes precedence over language in that snapshot that
could be read as claiming a fully source-first numerical closure. No official
Comparator receipt or verified-network status was claimed or is introduced.
