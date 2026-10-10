# Mathematical scope and source fidelity

The selected interface concerns the actual zero-field Sherrington–Kirkpatrick model, with independent standard Gaussian couplings indexed once by `i < j`. For each fixed real inverse temperature `β > 1`, it states a nonnegative mean pressure bias bounded by `Cβ N^(-7/10)` for every natural-number size `N ≥ 2`, where `Cβ > 0` depends on the temperature. The manuscript's one-sided Theorem 1.1 follows immediately. Positive constants and nonnegativity strengthen its displayed conclusion without adding a premise.

This is an automated mathematical-source comparison. Authorship and maintenance responsibility do not establish human mathematical review. Compiler, axiom and independent-kernel outcomes are recorded separately in [verification.md](verification.md).

## Definitions, domains and normalizations

[Challenge.lean](../Challenge.lean) defines configurations as `Fin N → Bool`, maps the two Boolean values to spins `±1`, and equips the real edge-indexed coupling vector with a product of standard Gaussian laws. Its Hamiltonian includes `β/√N`; the paper instead places `β` outside its Hamiltonian in the Boltzmann exponential. The partition functions coincide. The spin sum uses counting measure over all `2^N` configurations and includes the entropy term once. The expected log-partition function divided by `N` is pressure, and the gap is limiting pressure minus expected finite pressure.

The compact interface defines limiting pressure by `Filter.limUnder atTop` of this concrete pressure sequence. [Solution.lean](../Solution.lean) supplies convergence for every `β > 0` and the equality `SKMeanBias.parisiLimit_eq_variational` to `Paper.parisiPDEValue β 0`. This is an explicitly disclosed equivalent definition. It does not assume convergence, use an arbitrary pressure function, or assume the desired bias bound. The totalized limit definition has no asserted variational interpretation for `β ≤ 0`; totalized real division at size zero is outside the finite-volume theorem's `N ≥ 2` domain.

The substantive [Parisi functional](../Paper/RSFunctional.lean) ranges over all probability measures on `[0,1]`, including atoms, and uses the CDF `μ([0,q])`. The native potential has terminal value `log(cosh x)` and the functional adds `log 2`. This equals the manuscript's terminal `log(2 cosh x)` convention; a spatially constant shift does not alter the PDE derivatives. [The PDE formula](../Paper/ParisiPDEFormula.lean) and the proved weak-solution construction/uniqueness connect the all-measure variational value to the finite-step value and the physical thermodynamic pressure.

The completed Gaussian model appearing in auxiliary estimates adds an independent common Gaussian energy variable of variance `1/2`, hence adds `βD` to `log Z`. Its mean is zero, so it preserves expected pressure; its log-partition variance changes by `β²/2`. It is a proof device, and the headline model remains uncompleted.

| Selected result | Exact scope |
| --- | --- |
| `SKMeanBias.thermodynamic_limit` | Concrete expected pressure converges for `β > 0`. |
| `SKMeanBias.main_mean_bias` | Fixed `β > 1`; positive constant; every `N ≥ 2`; `0 ≤ bias ≤ Cβ N^(-7/10)`. |
| `SKMeanBias.free_energy_density_correction` | Bias divided by `β`, with the same exponent. Since physical free energy is `−log Z/β`, this is expected physical free energy density minus its limiting value. |
| `SKMeanBias.log_partition_mean_correction` | Nonnegative `N Pβ − E log Z`, at most `Cβ N^(3/10)`. |
| `SKMeanBias.strictly_better_than_two_thirds` | Existential positive exponent saving; the proof chooses `1/30`. |
| `SKMeanBias.mean_bias_little_o_two_thirds` | Full natural-number sequence: `N^(2/3) bias → 0`. |

## Formal proof route and dependencies

[HexagonPaper.Main](../HexagonPaper/Main.lean) reuses `QuantitativeFollowup.improved_native_bias` from [FollowupNativeMainResults](../QuantitativeFollowup/FollowupNativeMainResults.lean). That result obtains the internally proved `followup_actual_four_term_budget` from [FollowupCavityActualStableProfile](../QuantitativeFollowup/FollowupCavityActualStableProfile.lean), then applies the optimized tilt and finite-size comparison. The stability, endpoint, atom, response and remainder inputs are supplied by substantive imported proofs. The headline theorem has no variance-asymptotic, moment-limit or `PositiveLaplaceWindow` premise.

This organization is an alternative to the manuscript's current six-step presentation. Additional correspondence declarations support that presentation, but the small Main wrapper does not prove every displayed line by following the paper in order. The exponent saving uses the project's own `7/10` theorem; it does not formalize the cited external proof route.

Substantive dependencies include the physical Parisi formula and finite-volume bound, arbitrary-measure PDE construction and uniqueness, minimizing-profile support and density properties, interpolation envelopes, Gaussian and Brascamp–Lieb estimates, scalar floor costs, quantile localization, scalar response bounds, and cavity endpoint/remainder estimates. The transitive axiom audit identifies the actual formal dependencies. A bibliographic citation alone is not a formal proof certificate.

The distributed Lean sources retain the local import closure of the six-result interface and every declaration supporting the 58 numbered coverage entries, with a single import-only build entry point. Additional modules outside that closure are excluded. The build targets are `HexagonUpperBound`, `Challenge` and `Solution`; the verification script checks that their live import graph covers every retained local Lean source. This packaging choice does not broaden the selected mathematical scope or remove the qualifications below.

## Numbered correspondence and remaining representation bridges

[coverage.md](coverage.md) and [numbered-claims.json](numbered-claims.json) inventory the manuscript's 50 results, three definitions and five remarks. They identify actual declarations and source quotations, and separate theorem proofs, bundles, definitions, explicit hypotheses and explanatory prose. The reproducible checker records compiled target types and transitive axioms. It does not mechanically establish semantic equivalence between TeX and Lean.

Material qualifications include:

- The Gaussian heat statement retains explicit analytic, interchange and Gaussian-representation hypotheses. The general marked-tree description is represented by a finite shared-grid binary genealogy; an unrestricted tree-to-genealogy representation theorem is not supplied merely by that encoding.
- Lemma 9.2's coefficient positive almost everywhere is handled through a proved everywhere-positive representative and clock/drift/noise bridges, composed with the existing likelihood theorem. A separate standalone likelihood declaration for every original representative is not claimed.
- Definition 9.5's response operator is extended from a bounded dense family. The printed integral formula is proved on endpoint-fixed Lipschitz tests; a separate pointwise formula for arbitrary `L²` representatives is not claimed.
- Proposition 9.9's exact supremum-defined error is connected to the native error through an additional proved comparison bundle. The bundle supplies correspondence; the native theorem alone should not be read as having the edited exact-error target.
- Proposition 12.4 and Corollary 12.5 retain an explicit stability premise. The actual main proof discharges its needed stability input internally.
- `SmallIntervalTarget` is a proposition-valued specification; `small_interval_near_zero` proves it. The specification alone is not counted as a theorem. Four remarks are explanatory unanchored prose; Remark 13.2 has only arithmetic/supporting bindings and is not certified in its entirety.

## Conditional comparisons and limits of the headline

The earlier development included optional transfers from explicitly assumed positive ordinary variance limits, completed second-moment limits or eventual variance prefactors to an eventual `N^(-5/6)` bias lower bound. Their separate external-comparison entry point is excluded from this distribution. Those conditional implications do not establish their inputs and are not additional selected results. The completed-model second-moment identity is an exact normalization result, separate from an asymptotic hypothesis. Neither the interface nor the coverage ledger claims an unconditional external variance asymptotic, limiting distribution or `PositiveLaplaceWindow`.

The selected results give no uniform temperature constant as `β` approaches one or infinity, nonzero-field or non-Gaussian extension, ground-state limit, matching `7/10` lower bound, exact bias exponent, variance prefactor, or fluctuation limiting law. Historical verification records for earlier manuscripts cannot validate this source revision. See the separate verification report before treating any of these proof declarations as mechanically checked.
