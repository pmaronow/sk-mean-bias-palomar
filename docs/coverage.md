# Numbered claim coverage

This inventory maps the current paper's 50 numbered results, three definitions and five remarks to actual Lean declarations. The [machine-readable ledger](numbered-claims.json) records the exact quoted target, declaration kind and source location, and a source-level qualification for every entry. These are automated Codex comparisons; authorship and responsibility do not establish human mathematical review.

The [checker](../scripts/check_numbered_claims.py) verifies source quotations and declaration kinds, generates exact compiled-type queries, and audits transitive axioms. It does not prove TeX-to-Lean equivalence, replace a full build, or run an independent kernel. See [verification](verification.md) for the current source revision and completed checks, and [mathematical scope](mathematical-scope.md) for proof routes and limitations.

The theorem names below are primary anchors. Entries with several anchors are conjunctions or supporting bridge families; every listed anchor is included in the checker. The four unanchored explanatory remarks have no separately certified target. Remark 13.2 has arithmetic and closure anchors, with partial explanatory coverage.

| Claim | Primary Lean anchor | Coverage kind |
| --- | --- | --- |
| Theorem 1.1 | [`HexagonPaper.main_mean_bias_upper`](../HexagonPaper/MainUpperOnly.lean) | proved statement |
| Proposition 3.1 | [`QuantitativeFollowup.foundation_martingale_contact`](../QuantitativeFollowup/FoundationMartingaleContact.lean) | proved statement |
| Remark 3.2 | None (explanatory prose) | explanatory unanchored |
| Proposition 3.3 | [`QuantitativeFollowup.foundation_integrated_variance`](../QuantitativeFollowup/FoundationIntegratedVariance.lean) | proved statement |
| Remark 3.4 | None (explanatory prose) | explanatory unanchored |
| Lemma 3.5 | [`QuantitativeFollowup.foundation_overlap_decomposition`](../QuantitativeFollowup/FoundationDecomposition.lean) | proved statement |
| Proposition 3.6 | [`QuantitativePaper.interpolation_envelope`](../QuantitativePaper/InterpolationEnvelope.lean) | proved statement |
| Corollary 3.7 | [`QuantitativeFollowup.smallIntervalDefect_printed_derivative`](../QuantitativeFollowup/SupportingPrintedOptimizedEnvelope.lean) (+4 anchors) | proved bundle |
| Lemma 3.8 | [`QuantitativeFollowup.foundation_trial_budget_complete`](../QuantitativeFollowup/FoundationTrialBudget.lean) | proved statement |
| Proposition 3.9 | [`QuantitativeFollowup.foundation_mean_bias`](../QuantitativeFollowup/FoundationMeanBias.lean) | proved statement |
| Definition 4.1 | [`QuantitativeFollowup.AnisotropicSpinModel`](../QuantitativeFollowup/AnisotropicSpinModel.lean) (+10 anchors) | definition |
| Lemma 4.2 | [`HexagonPaper.posterior_self_overlap_both_models`](../HexagonPaper/Posterior.lean) (+1 anchor) | proved bundle |
| Lemma 4.3 | [`HexagonPaper.lem_fnd_path_heat`](../HexagonPaper/PathHeatSourceLemma.lean) (+12 anchors) | analytic heat infrastructure |
| Remark 4.4 | None (explanatory prose) | explanatory unanchored |
| Lemma 5.1 | [`QuantitativeFollowup.vectorCenteredKernelScore_future_comparison`](../QuantitativeFollowup/VectorCenteredKernelComparison.lean) (+9 anchors) | proved bundle |
| Proposition 5.2 | [`HexagonPaper.vector_quantile_interval_variance_128`](../HexagonPaper/MomentsVariance.lean) | proved statement |
| Corollary 5.3 | [`HexagonPaper.vector_cubic_self_overlap_moment_free_425_from_full_layercake`](../HexagonPaper/MomentsCubicFree.lean) (+2 anchors) | proved bundle |
| Lemma 6.1 | [`QuantitativeFollowup.directional_covariance_decay`](../QuantitativeFollowup/DirectionalCovarianceDecay.lean) | proved statement |
| Lemma 6.2 | [`QuantitativeFollowup.vector_mean_increment_towards_support_full`](../QuantitativeFollowup/VectorMeanIncrementEndpoints.lean) (+3 anchors) | proved bundle |
| Lemma 6.3 | [`QuantitativeFollowup.covariance_of_mean_increment`](../QuantitativeFollowup/MeanCovarianceResidual.lean) | proved statement |
| Proposition 6.4 | [`HexagonPaper.mean_direction_covariance_341`](../HexagonPaper/MeanCovariance.lean) | proved statement |
| Proposition 7.1 | [`QuantitativeFollowup.localization_profile_of_energy_free`](../QuantitativeFollowup/FollowupVariationalSourceFacts.lean) (+8 anchors) | proved bundle |
| Remark 7.2 | None (explanatory prose) | explanatory unanchored |
| Lemma 7.3 | [`QuantitativeFollowup.partial_reflected_regularization_full`](../QuantitativeFollowup/PartialFunctionalRegularization.lean) (+5 anchors) | proved bundle |
| Lemma 7.4 | [`HexagonPaper.weighted_one_sign_coercivity`](../HexagonPaper/Coercivity.lean) (+2 anchors) | proved bundle |
| Lemma 7.5 | [`QuantitativeFollowup.scalar_density_bound_uniform_minimizers`](../QuantitativeFollowup/ScalarDensity.lean) (+6 anchors) | proved bundle |
| Proposition 7.6 | [`QuantitativeFollowup.scalar_trial_isolation`](../QuantitativeFollowup/TrialIsolation.lean) | proved statement |
| Lemma 8.1 | [`HexagonPaper.local_deficit_certificate`](../HexagonPaper/LocalDeficitCertificate.lean) (+1 anchor) | proved bundle |
| Lemma 8.2 | [`QuantitativeFollowup.scalar_root_density_measure_lower_of_linear_growth`](../QuantitativeFollowup/ScalarRootDensityMeasure.lean) (+1 anchor) | proved bundle |
| Proposition 8.3 | [`QuantitativeFollowup.root_quantile_localization`](../QuantitativeFollowup/RootQuantileLocalization.lean) | proved statement |
| Corollary 8.4 | [`QuantitativeFollowup.probability_root_quantile_localization`](../QuantitativeFollowup/RootProbabilityQuantile.lean) | proved statement |
| Lemma 9.1 | [`QuantitativeFollowup.supporting_printed_scalar_spatial_bounds`](../QuantitativeFollowup/SupportingPrintedScalarStabilityChains.lean) (+11 anchors) | proved bundle |
| Lemma 9.2 | [`HexagonPaper.scalarStoppedPath_printed_likelihood`](../HexagonPaper/PrefixLikelihoodPrinted.lean) (+7 anchors) | representative likelihood bundle |
| Lemma 9.3 | [`QuantitativeFollowup.scalar_multiplier_continuity`](../QuantitativeFollowup/ScalarMultiplierContinuity.lean) | proved statement |
| Lemma 9.4 | [`QuantitativeFollowup.scalar_kernel_bounds`](../QuantitativeFollowup/ScalarKernelBounds.lean) (+1 anchor) | proved bundle |
| Definition 9.5 | [`QuantitativeFollowup.scalarResponseOperator`](../QuantitativeFollowup/ScalarResponseOperator.lean) (+7 anchors) | definition |
| Lemma 9.6 | [`HexagonPaper.scalar_response_identity`](../HexagonPaper/ScalarChapterSix.lean) | proved statement |
| Lemma 9.7 | [`QuantitativeFollowup.scalar_multiplier_domination`](../QuantitativeFollowup/ScalarMultiplierDomination.lean) (+1 anchor) | proved bundle |
| Lemma 9.8 | [`QuantitativeFollowup.scalar_reference_multiplier`](../QuantitativeFollowup/ScalarReferenceMultiplier.lean) | proved statement |
| Proposition 9.9 | [`QuantitativeFollowup.scalar_minimizer_stability`](../QuantitativeFollowup/ScalarMinimizerStability.lean) (+6 anchors) | exact error bundle |
| Definition 10.1 | [`FourPapersCommon.FiniteTerminalGenealogy`](../FourPapersCommon/FiniteCascadeTreeRecords.lean) (+7 anchors) | definition |
| Lemma 10.2 | [`HexagonPaper.cavityTree_native_tail_smooth_and_jets`](../HexagonPaper/CavityTreeNativeAllJets.lean) (+8 anchors) | proved bundle |
| Lemma 10.3 | [`HexagonPaper.tree_likelihood_arbitrary_profile`](../HexagonPaper/TreeLikelihood.lean) (+5 anchors) | proved bundle |
| Lemma 10.4 | [`QuantitativeFollowup.anisotropic_cavity_row_parameter_nodeTheta`](../QuantitativeFollowup/AnisotropicNodeTheta.lean) (+8 anchors) | proved bundle |
| Lemma 10.5 | [`HexagonPaper.cavity_streaming_arbitrary_profile`](../HexagonPaper/CavityStreaming.lean) | proved statement |
| Corollary 10.6 | [`QuantitativeFollowup.cavityNative_positive_spin_comparison`](../QuantitativeFollowup/FollowupCavityNativeComparison.lean) | proved statement |
| Lemma 10.7 | [`QuantitativeFollowup.cavityGeneratedActualObservedRawStreamingTerm_three_defects`](../QuantitativeFollowup/FollowupCavityGeneratedObservedRawTermThreeDefects.lean) (+5 anchors) | proved bundle |
| Lemma 10.8 | [`QuantitativeFollowup.followup_cavity_taylor_remainder`](../QuantitativeFollowup/FollowupCavityTaylorRemainderLemma.lean) | proved statement |
| Lemma 11.1 | [`HexagonPaper.cavityOriginalCpp_zero_response_three_group`](../HexagonPaper/CavityFixedRowExpansionOriginalResponse.lean) (+4 anchors) | proved bundle |
| Lemma 11.2 | [`QuantitativeFollowup.followupCavityCpp_zero_response_integral`](../QuantitativeFollowup/FollowupCavityCppZeroResponseIntegratedResults.lean) (+7 anchors) | proved bundle |
| Lemma 11.3 | [`QuantitativeFollowup.followup_signed_response_estimate`](../QuantitativeFollowup/FollowupCavitySignedResponseLemma.lean) | proved statement |
| Lemma 12.1 | [`QuantitativeFollowup.followup_cavity_four_rest_variance_comparison`](../QuantitativeFollowup/FollowupCavityFourRestVarianceComparison.lean) | proved statement |
| Lemma 12.2 | [`QuantitativeFollowup.followup_actual_full_variance_trace`](../QuantitativeFollowup/FollowupCavityFullVarianceTraceActualSource.lean) | proved statement |
| Lemma 12.3 | [`QuantitativeFollowup.followup_cavity_third_rest_moment_thermal`](../QuantitativeFollowup/FollowupCavityThirdRestMomentThermalIntegral.lean) | proved statement |
| Proposition 12.4 | [`QuantitativeFollowup.followup_cavity_contraction_actual_printed_stability`](../QuantitativeFollowup/FollowupCavityStableDefectActualSource.lean) | conditional stability infrastructure |
| Corollary 12.5 | [`QuantitativeFollowup.followup_cavity_stable_defect_actual_printed_stability`](../QuantitativeFollowup/FollowupCavityStableDefectActualSource.lean) (+3 anchors) | conditional stability infrastructure |
| Proposition 13.1 | [`QuantitativeFollowup.small_interval_near_zero`](../QuantitativeFollowup/SmallIntervalProposition.lean) (+1 anchor) | proved bundle |
| Remark 13.2 | [`HexagonPaper.critical_exponent_balance`](../HexagonPaper/RateArithmetic.lean) (+7 anchors) | partial remark |

Proof bundles use concrete model statements. In particular, the proposition-valued `SmallIntervalTarget` is discharged by `small_interval_near_zero`; its definition alone is not counted as a proof. The scalar likelihood uses positive-representative bridges for coefficients positive almost everywhere, and exact scalar stability uses a proved supremum-error comparison bundle. The completed response operator agrees with its printed formula on dense endpoint-fixed Lipschitz tests; no separate all-L2 representative identity is asserted by the ledger.

Tree results use a finite shared-grid binary genealogy. Encoding a general marked tree is a mathematical representation bridge. The heat identity retains explicit analytic and Gaussian-representation hypotheses. The contraction and stable-interval results retain the paper's stability premise, which the actual main proof discharges internally.

A standalone audit requires a fresh build first so the existing compiled artifacts correspond to current sources. The complete [verification command](../scripts/verify.sh) performs that build. The numbered audit freezes hashes of local exported/server/private artifacts and the transitive external import closure before and after inspection, including the sources used to traverse imports. An imported module without available source blocks this audit because its further compiled imports cannot be established by this method. Preparation mode makes no artifact claim.

After the build, run the audit from the repository root:

```sh
python3 scripts/check_numbered_claims.py --output ../verification-work/numbered-claims
```

The generated audit deliberately has no `module` header. In Lean 4.35 this loads full transitive private data; each theorem or lemma anchor must have its actual theorem body and a proposition type. An ordinary import inside a module may instead expose a theorem as an abstract declaration with precomputed axiom metadata. The final receipt records `proof_bodies_loaded: true` only after the body and axiom checks pass.

Use `--prepare-only` to inspect the generated audit without running Lean. A preparation pass is source-structure evidence only and explicitly reports `kernel_axioms_passed: false`. Generated audit source, raw compiler output and machine reports belong in the separate verification workspace, not the public source tree.
