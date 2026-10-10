# Finite-size mean bias in the Sherrington–Kirkpatrick model

This repository contains the paper *An N^(-7/10) Bound for the Finite-Size Bias of the Sherrington–Kirkpatrick Free Energy* by P. M. Aronow and Patrick Lopatto, its Lean development, and a small theorem interface for independent comparison.

The [release repository](https://github.com/pmaronow/sk-mean-bias-palomar) begins with one source commit. Earlier verification revisions are retained as external provenance in [the verification report](docs/verification.md), outside this repository's history.

The model has zero external field, spins in `{−1, 1}^N`, and independent standard Gaussian couplings on pairs `i < j`. The Hamiltonian is

```text
H_N(σ) = N^(-1/2) ∑_{i<j} g_ij σ_i σ_j,
p_{N,β} = N^(-1) E[log ∑_σ exp(β H_N(σ))].
```

For each fixed real `β > 1`, the headline result is

```text
∃ C_β > 0, ∀ N ≥ 2, 0 ≤ P_β − p_{N,β} ≤ C_β N^(-7/10),
```

where `P_β` is the Parisi variational value. The source proof has no variance-limit or fluctuation-law hypothesis. Its validation status is reported in [the verification report](docs/verification.md), which distinguishes checks of named earlier revisions from the release source comparison.

## Results and theorem interface

[Challenge.lean](Challenge.lean) states the selected results using concrete model definitions and permitted library imports. [Solution.lean](Solution.lean) supplies the corresponding declarations. The Challenge theorem bodies contain intentional `sorry` placeholders; the Solution and its transitive proof dependencies must pass the proof-hole and axiom checks described below.

| Declaration in `SKMeanBias` | Mathematical statement |
| --- | --- |
| `thermodynamic_limit` | For `β > 0`, the expected pressure converges to the interface's limiting value. |
| `main_mean_bias` | The nonnegative mean pressure bias has the `N^(-7/10)` upper bound for fixed `β > 1`. |
| `free_energy_density_correction` | The physical mean free energy density correction, `(P_β − p_{N,β})/β`, has the same rate. |
| `log_partition_mean_correction` | `N P_β − E log Z_{N,β}` is nonnegative and at most `C_β N^(3/10)`. |
| `strictly_better_than_two_thirds` | There is a positive saving over exponent `2/3`; the proof uses `δ = 1/30`. |
| `mean_bias_little_o_two_thirds` | `N^(2/3) (P_β − p_{N,β})` tends to zero. |

For a compact readable interface, `SKMeanBias.parisiLimit` is defined as the limit of the expected finite-volume pressure using `Filter.limUnder`. `SKMeanBias.parisiLimit_eq_variational` identifies it with `Paper.parisiPDEValue β 0` for `β > 0`. The latter is the infimum over all probability measures on `[0,1]` of the weak-PDE Parisi functional. Its potential uses terminal value `log(cosh x)` and adds `log 2` in the functional, which equals the paper's `log(2 cosh x)` convention. The sum over spins uses counting measure and includes the entropy term once.

The headline source development begins at [HexagonPaper/Main.lean](HexagonPaper/Main.lean). It draws on the earlier quantitative interpolation and cavity development. This is an alternative formal proof organization; the small wrapper does not reproduce every displayed step of the manuscript's current exposition. The [mathematical scope report](docs/mathematical-scope.md), [coverage report](docs/coverage.md), and [numbered-claim ledger](docs/numbered-claims.json) describe this distinction and the substantive dependencies.

## Installation and build

Install [elan](https://github.com/leanprover/elan) and ensure `lean` and `lake` are on `PATH`. The repository pins Lean in [lean-toolchain](lean-toolchain), Mathlib in [lakefile.toml](lakefile.toml), and all resolved Lake dependencies in [lake-manifest.json](lake-manifest.json).

The verification scripts require Git and Python 3.11 or later. Comparator's isolated checks additionally require Linux with `bwrap` (bubblewrap) and the independent checker binaries bundled in the pinned Lean toolchain.

The full private-import proof audits require Linux `vm.max_map_count` of at least `262144`. Have the administrator configure this kernel setting on the verification host or container environment before running verification. The scripts check this runtime prerequisite before loading the large proof development.

The pinned versions are Lean `4.35.0-rc2` and canonical Mathlib revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Compatibility work preserves the mathematical statements; the provenance and verification reports record its limits.

From the repository root:

```sh
lake exe cache get
lake build
```

The first command fetches the pinned dependencies' compiled library cache. Local mathematical sources are built from this repository. A full source build and audit can require substantial time and memory because the retained dependency development is large.

The manuscript source is [paper/main.tex](paper/main.tex). With a TeX distribution providing `pdflatex` and `bibtex`, build it from the repository root:

```sh
./scripts/build-paper.sh
```

The script writes the PDF and TeX intermediates to a separate directory.

## Verification

Install the pinned Python verification dependencies first. The reproducible entry point is:

```sh
python3 -m pip install -r requirements-verification.txt
./scripts/verify.sh
```

It checks the public source structure and pins, builds the submitted Lean sources, scans for proof holes and forbidden declarations, audits the selected proofs' transitive axioms, checks the numbered-claim ledger's bindings and prints its exact compiled targets, and invokes Comparator with its required independent kernel checks. Individual checks and tool pins are documented in [docs/verification.md](docs/verification.md) and in the scripts. Comparator's configuration is [comparator.json](comparator.json).

Read the report's source identifier and individual outcomes before relying on a verification claim. Compilation establishes that declarations type-check; a target comparison also needs agreement on definitions, hypotheses, quantifiers, and conclusions. A dependency audit does not establish that a theorem proves a different manuscript statement.

## Scope

The constant depends on the fixed temperature. There is no uniform control as `β` approaches one or infinity, and no ground-state conclusion. The selected statements concern the zero-field Gaussian SK model. They do not establish a matching `N^(-7/10)` lower bound, an exact bias exponent, a variance prefactor, or a fluctuation limiting law.

The distributed Lean sources retain the local import closure of the six-result interface and the declarations supporting all 58 numbered coverage entries. Supplementary modules outside that closure are excluded. Conditional comparisons discussed in the manuscript require positive variance or second-moment asymptotic premises; the selected proofs do not establish those premises. Proposition-valued target definitions are specifications until proved by a corresponding declaration. Literature citations identify background; their presence alone is not a proof certificate. See [docs/mathematical-scope.md](docs/mathematical-scope.md) for the precise restrictions and coverage gaps.

## Attribution and provenance

The paper authors, formalization authors, and responsible maintainers are P. M. Aronow and Patrick Lopatto. **Sol 6.1** autoformalized the original development. **Codex** subsequently prepared the public repository and theorem interface. Codex's compiler compatibility work adapted the development to the pinned toolchain while preserving mathematical statements. Codex's automated source review and verification are reported separately in the scope and verification documents. Named authorship and maintenance responsibility do not imply human mathematical review.

[docs/provenance.md](docs/provenance.md) describes the source lineage and the difference between inherited records and checks of this revision. The [source-origin manifest](provenance/source-origins.json) preserves the original locations of flattened local Lean modules.

## Licensing

Original code and documentation are available under the [MIT license](LICENSE). Vendored material retains its own licenses and notices, including Apache-2.0 source headers and per-file modification notices. The MIT license does not replace those grants. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), [LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt), and the [retained RSAT notice](LICENSES/RSAT-NOTICE.txt). Lake downloads external dependencies under their respective pinned upstream licenses.
