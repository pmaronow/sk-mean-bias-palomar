module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.Real.Lemmas

public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-!
# Mean bias of the zero-field Sherrington–Kirkpatrick model

The disorder contains one independent standard Gaussian for each pair `i < j`.
The partition function is the **unnormalized** sum over all `2^n` spin
configurations. The results concern a fixed inverse temperature `β > 1`;
constants may depend on `β`, and the bounds hold for every integer `n ≥ 2`.

For a short, independently readable interface, `parisiLimit` is defined as the
thermodynamic limit of the expected pressure. `Solution.lean` proves that for
every `β > 0` this definition equals `Paper.parisiPDEValue β 0`, the variational
infimum over all probability measures on `[0,1]` in the proof development. The
first theorem establishes convergence, so the limit definition does not assume
existence. At nonpositive temperatures the totalized limit definition has no
asserted variational interpretation.

Only the six theorem declarations below intentionally contain `sorry`.
-/

namespace SKMeanBias

/-- `true` is spin `+1`, and `false` is spin `-1`. -/
abbrev Configuration (n : ℕ) := Fin n → Bool

/-- Unordered pairs of distinct sites, represented once by `i < j`. -/
abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

/-- One real disorder coordinate for every edge. -/
abbrev Couplings (n : ℕ) := Edge n → ℝ

/-- Convert the Boolean spin encoding to its value in `{−1,+1}`. -/
@[expose] def spinSign (s : Bool) : ℝ := if s then 1 else -1

/-- Independent centered Gaussian couplings, each with variance one. -/
@[expose] def couplingLaw (n : ℕ) : Measure (Couplings n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 1)

/-- Zero-field SK Hamiltonian with the paper's `β / √n` normalization. -/
@[expose] def hamiltonian {n : ℕ} (β : ℝ) (g : Couplings n)
    (σ : Configuration n) : ℝ :=
  β / Real.sqrt (n : ℝ) *
    ∑ ij : Edge n, g ij * spinSign (σ ij.val.1) * spinSign (σ ij.val.2)

/-- Sum over all configurations, without a `2⁻ⁿ` factor. -/
@[expose] def partitionFunction {n : ℕ} (β : ℝ) (g : Couplings n) : ℝ :=
  ∑ σ : Configuration n, Real.exp (hamiltonian β g σ)

/-- Natural logarithm of the unnormalized partition function at fixed disorder. -/
@[expose] def logPartition (n : ℕ) (β : ℝ) (g : Couplings n) : ℝ :=
  Real.log (partitionFunction β g)

/-- Gaussian-disorder expectation of the natural logarithm of `Zₙ(β)`. -/
@[expose] def expectedLogPartition (n : ℕ) (β : ℝ) : ℝ :=
  ∫ g : Couplings n, logPartition n β g ∂couplingLaw n

/-- Expected log-partition function per spin. -/
@[expose] def pressure (n : ℕ) (β : ℝ) : ℝ :=
  expectedLogPartition n β / (n : ℝ)

/-- Thermodynamic pressure; its variational interpretation is proved in Solution. -/
@[expose] def parisiLimit (β : ℝ) : ℝ :=
  limUnder atTop (fun n : ℕ => pressure n β)

/-- `p∞(β) − E[log Zₙ(β)] / n`. -/
@[expose] def finiteBias (n : ℕ) (β : ℝ) : ℝ :=
  parisiLimit β - pressure n β

/-- The concrete pressure sequence converges to the defined thermodynamic value. -/
theorem thermodynamic_limit (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => pressure n β) atTop (𝓝 (parisiLimit β)) := by
  sorry

/-- Paper Theorem 1.1, with the additionally proved nonnegativity of the bias. -/
theorem main_mean_bias (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ finiteBias n β ∧
        finiteBias n β ≤ C * (n : ℝ) ^ (-(7 / 10 : ℝ)) := by
  sorry

/-- The free-energy-density correction is the pressure gap divided by `β`. -/
theorem free_energy_density_correction (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ finiteBias n β / β ∧
        finiteBias n β / β ≤ C * (n : ℝ) ^ (-(7 / 10 : ℝ)) := by
  sorry

/-- The gap `n p∞(β) − E[log Zₙ(β)]` has order at most `n^(3/10)`. -/
theorem log_partition_mean_correction (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ (n : ℝ) * finiteBias n β ∧
        (n : ℝ) * finiteBias n β ≤ C * (n : ℝ) ^ (3 / 10 : ℝ) := by
  sorry

/-- A positive fixed-temperature saving over exponent `2/3`; Solution uses `1/30`. -/
theorem strictly_better_than_two_thirds (β : ℝ) (hβ : 1 < β) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ finiteBias n β ∧
        finiteBias n β ≤ C * (n : ℝ) ^ (-(2 / 3 : ℝ) - δ) := by
  sorry

/-- The bias is `o(n^(-2/3))` as `n → ∞` for every fixed `β > 1`. -/
theorem mean_bias_little_o_two_thirds (β : ℝ) (hβ : 1 < β) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (2 / 3 : ℝ) * finiteBias n β)
      atTop (𝓝 0) := by
  sorry

end SKMeanBias
