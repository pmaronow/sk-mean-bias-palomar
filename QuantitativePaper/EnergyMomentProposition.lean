module
public import QuantitativePaper.ZeroTemperatureControlScalarLimit
public import QuantitativePaper.SoftMaxLogMomentLimit

@[expose] public section

/-! Full actual main Lemma 5.6. The centering ground value is the genuine
infimum over integrable monotone |x|-terminal profiles, and its scalar
temperature limit is proved rather than supplied as a hypothesis. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper

def scalarCenteredGroundLogMoment (n : ℕ) (lam : ℝ) : ℝ :=
  cgf (fun g=>groundState n g-(n:ℝ)*groundScalarValue) (couplingLaw n) lam

theorem integrable_exp_scalarCenteredGround (n : ℕ) (lam : ℝ) :
    Integrable (fun g=>Real.exp (lam*(groundState n g-(n:ℝ)*groundScalarValue))) (couplingLaw n) := by
  simp_rw [mul_sub,Real.exp_sub,div_eq_mul_inv]
  exact (integrable_exp_groundState n lam).mul_const _

theorem scalarCenteredGround_mgf_pos (n : ℕ) (lam : ℝ) :
    0 < mgf (fun g=>groundState n g-(n:ℝ)*groundScalarValue) (couplingLaw n) lam :=
  mgf_pos (integrable_exp_scalarCenteredGround n lam)

theorem scalarCenteredGroundLogMoment_eq (n : ℕ) (lam : ℝ) :
    scalarCenteredGroundLogMoment n lam=cgf (groundState n) (couplingLaw n) lam-
      lam*(n:ℝ)*groundScalarValue := by
  unfold scalarCenteredGroundLogMoment
  have hh:=FourPapersCommon.cgf_add_constant (couplingLaw n) (groundState n)
    lam (-((n:ℝ)*groundScalarValue)) (integrable_exp_groundState n lam)
  convert! hh using 1 <;> ring

theorem scalarCenteredEnergyLogMoment_ground_limit (n : ℕ) (lam : ℝ) :
    Tendsto (fun β:ℝ=>scalarCenteredEnergyLogMoment n β lam) atTop
      (𝓝 (scalarCenteredGroundLogMoment n lam)) := by
  simp_rw [scalarCenteredEnergyLogMoment_eq,scalarCenteredGroundLogMoment_eq]
  have ht:=scalar_zero_temperature_limit_at_zero.const_mul (lam*(n:ℝ))
  exact (tendsto_cgf_energyFreeEnergy_groundState_real n lam).sub ht

/-- Exact finite and zero-temperature clauses of the source lemma. The
stronger beta>0 finite scope contains every source beta≥beta0>1. -/
def EnergyMomentIdentityTarget : Prop :=
  EnergyMomentFiniteTarget ∧ ∀n:ℕ,0<n→∀lam:ℝ,
    Integrable (fun g=>Real.exp (lam*(groundState n g-(n:ℝ)*groundScalarValue))) (couplingLaw n) ∧
    0 < mgf (fun g=>groundState n g-(n:ℝ)*groundScalarValue) (couplingLaw n) lam ∧
    Tendsto (fun β:ℝ=>scalarCenteredEnergyLogMoment n β lam) atTop
      (𝓝 (scalarCenteredGroundLogMoment n lam))

theorem energy_moment_identity : EnergyMomentIdentityTarget :=
  ⟨energy_moment_finite,fun n _ lam=>⟨integrable_exp_scalarCenteredGround n lam,
    scalarCenteredGround_mgf_pos n lam,scalarCenteredEnergyLogMoment_ground_limit n lam⟩⟩

end QuantitativePaper
