module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.Real.Lemmas
public import HexagonPaper.Main
public import HexagonPaper.MainAsymptotics
public import Paper.ParisiPDEFormula

public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-!
# Proved submission interface

The concrete definitions and the six advertised statement types reproduce
`Challenge.lean` independently. This module does not import Challenge. Its
proofs bridge the physical finite SK model to the substantive development and
explicitly identify the thermodynamic limit with the all-measure Parisi PDE
variational value. No theorem in this module has a proof placeholder.
-/

namespace SKMeanBias

abbrev Configuration (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
abbrev Couplings (n : ℕ) := Edge n → ℝ

@[expose] def spinSign (s : Bool) : ℝ := if s then 1 else -1

@[expose] def couplingLaw (n : ℕ) : Measure (Couplings n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 1)

@[expose] def hamiltonian {n : ℕ} (β : ℝ) (g : Couplings n)
    (σ : Configuration n) : ℝ :=
  β / Real.sqrt (n : ℝ) *
    ∑ ij : Edge n, g ij * spinSign (σ ij.val.1) * spinSign (σ ij.val.2)

@[expose] def partitionFunction {n : ℕ} (β : ℝ) (g : Couplings n) : ℝ :=
  ∑ σ : Configuration n, Real.exp (hamiltonian β g σ)

@[expose] def logPartition (n : ℕ) (β : ℝ) (g : Couplings n) : ℝ :=
  Real.log (partitionFunction β g)

@[expose] def expectedLogPartition (n : ℕ) (β : ℝ) : ℝ :=
  ∫ g : Couplings n, logPartition n β g ∂couplingLaw n

@[expose] def pressure (n : ℕ) (β : ℝ) : ℝ :=
  expectedLogPartition n β / (n : ℝ)

@[expose] def parisiLimit (β : ℝ) : ℝ :=
  limUnder atTop (fun n : ℕ => pressure n β)

@[expose] def finiteBias (n : ℕ) (β : ℝ) : ℝ :=
  parisiLimit β - pressure n β

/-- The standalone pressure definition uses the exact physical model. -/
theorem pressure_eq_original (n : ℕ) (β : ℝ) :
    pressure n β = QuantitativePaper.pressure n β := by
  simp only [pressure, expectedLogPartition, logPartition, partitionFunction,
    hamiltonian, couplingLaw, spinSign, QuantitativePaper.pressure,
    QuantitativePaper.logPartition, QuantitativePaper.couplingLaw,
    Paper.skPartitionFunction, Paper.skHamiltonian, Paper.skCouplingLaw,
    Paper.spinSign, zero_mul, add_zero]

/-- The alternative interface limit equals the all-profile variational value. -/
theorem parisiLimit_eq_variational (β : ℝ) (hβ : 0 < β) :
    parisiLimit β = Paper.parisiPDEValue β 0 := by
  have hlim : Tendsto (fun n : ℕ => pressure n β) atTop
      (𝓝 (Paper.parisiPDEValue β 0)) := by
    simpa only [pressure_eq_original, QuantitativePaper.pressure_eq_finiteSKFreeEnergy]
      using Paper.physicalParisiFormula β 0 hβ
  exact hlim.limUnder_eq

theorem finiteBias_eq_original (n : ℕ) (β : ℝ) (hβ : 0 < β) :
    finiteBias n β = QuantitativeFollowup.finiteBias n β := by
  rw [finiteBias, parisiLimit_eq_variational β hβ, pressure_eq_original]
  rfl

theorem thermodynamic_limit (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => pressure n β) atTop (𝓝 (parisiLimit β)) := by
  rw [parisiLimit_eq_variational β hβ]
  simpa only [pressure_eq_original, QuantitativePaper.pressure_eq_finiteSKFreeEnergy]
    using Paper.physicalParisiFormula β 0 hβ

theorem main_mean_bias (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ finiteBias n β ∧
        finiteBias n β ≤ C * (n : ℝ) ^ (-(7 / 10 : ℝ)) := by
  simpa only [finiteBias_eq_original _ β (lt_trans zero_lt_one hβ)]
    using HexagonPaper.main_mean_bias β hβ

theorem free_energy_density_correction (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ finiteBias n β / β ∧
        finiteBias n β / β ≤ C * (n : ℝ) ^ (-(7 / 10 : ℝ)) := by
  simpa only [finiteBias_eq_original _ β (lt_trans zero_lt_one hβ)]
    using HexagonPaper.free_energy_density_correction β hβ

theorem log_partition_mean_correction (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ (n : ℝ) * finiteBias n β ∧
        (n : ℝ) * finiteBias n β ≤ C * (n : ℝ) ^ (3 / 10 : ℝ) := by
  simpa only [finiteBias_eq_original _ β (lt_trans zero_lt_one hβ)]
    using HexagonPaper.log_partition_mean_correction β hβ

theorem strictly_better_than_two_thirds (β : ℝ) (hβ : 1 < β) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ finiteBias n β ∧
        finiteBias n β ≤ C * (n : ℝ) ^ (-(2 / 3 : ℝ) - δ) := by
  simpa only [finiteBias_eq_original _ β (lt_trans zero_lt_one hβ)]
    using HexagonPaper.strictly_better_than_two_thirds β hβ

theorem mean_bias_little_o_two_thirds (β : ℝ) (hβ : 1 < β) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (2 / 3 : ℝ) * finiteBias n β)
      atTop (𝓝 0) := by
  simpa only [finiteBias_eq_original _ β (lt_trans zero_lt_one hβ)]
    using HexagonPaper.mean_bias_little_o_two_thirds β hβ

end SKMeanBias
