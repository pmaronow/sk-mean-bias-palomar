module
public import QuantitativePaper.ScalarVariational
public import QuantitativeFollowup.ChenSK
public import FourPapersCommon.LogMGFUniformComparison

@[expose] public section

/-! The actual finite-SK clauses of Lemma 5.6, with its energy normalization.
The separate unbounded-profile zero-temperature functional is not assumed or
identified with a limit in this file. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 500000

def scalarEnergyValue (β lam : ℝ) : ℝ := constrainedParisiValue β (lam/β)/β

def completedEnergyFreeEnergy (n : ℕ) (β : ℝ) (p : Couplings n×ℝ) : ℝ :=
  energyFreeEnergy n β p.1+p.2

def completedEnergyLaplace (n : ℕ) (β lam : ℝ) : ℝ :=
  if lam=0 then (∫g,energyFreeEnergy n β g ∂couplingLaw n)/(n:ℝ)
  else cgf (completedEnergyFreeEnergy n β) (completionLaw n) lam/((n:ℝ)*lam)

def energyComparisonError (n : ℕ) (β lam : ℝ) : ℝ :=
  scalarEnergyValue β lam-completedEnergyLaplace n β lam

def energyMeanDeficit (n : ℕ) (β : ℝ) : ℝ :=
  scalarEnergyValue β 0-(∫g,energyFreeEnergy n β g ∂couplingLaw n)/(n:ℝ)

def scalarCenteredEnergyLogMoment (n : ℕ) (β lam : ℝ) : ℝ :=
  cgf (fun g=>energyFreeEnergy n β g-(n:ℝ)*scalarEnergyValue β 0) (couplingLaw n) lam

/-- Genuine removable extension of the paper's quotient to zero. -/
def scalarCenteredEnergyMoment (n : ℕ) (β lam : ℝ) : ℝ :=
  normalizedEnergyMoment n β lam/(n:ℝ)-scalarEnergyValue β 0

theorem integrable_exp_scalarCenteredEnergy (n : ℕ) (β lam : ℝ) :
    Integrable (fun g=>Real.exp (lam*(energyFreeEnergy n β g-(n:ℝ)*scalarEnergyValue β 0)))
      (couplingLaw n) := by
  simp_rw [mul_sub,Real.exp_sub,div_eq_mul_inv]
  exact (integrable_exp_energyFreeEnergy n β lam).mul_const _

theorem scalarCenteredEnergy_mgf_pos (n : ℕ) (β lam : ℝ) :
    0 < mgf (fun g=>energyFreeEnergy n β g-(n:ℝ)*scalarEnergyValue β 0) (couplingLaw n) lam :=
  mgf_pos (integrable_exp_scalarCenteredEnergy n β lam)

theorem scalarCenteredEnergyLogMoment_eq (n : ℕ) (β lam : ℝ) :
    scalarCenteredEnergyLogMoment n β lam=
      cgf (energyFreeEnergy n β) (couplingLaw n) lam-lam*(n:ℝ)*scalarEnergyValue β 0 := by
  unfold scalarCenteredEnergyLogMoment
  have hh:=FourPapersCommon.cgf_add_constant (couplingLaw n) (energyFreeEnergy n β)
    lam (-((n:ℝ)*scalarEnergyValue β 0)) (integrable_exp_energyFreeEnergy n β lam)
  convert! hh using 1 <;> ring

theorem scalarCenteredEnergyMoment_of_ne (n : ℕ) (hn : 0<n) (β : ℝ)
    {lam : ℝ} (hlam : lam≠0) :
    scalarCenteredEnergyMoment n β lam=scalarCenteredEnergyLogMoment n β lam/((n:ℝ)*lam) := by
  have hn' : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  rw [scalarCenteredEnergyMoment,normalizedEnergyMoment_of_ne n β hlam,
    scalarCenteredEnergyLogMoment_eq]
  unfold cgf mgf
  field_simp
  <;> ring

theorem scalarCenteredEnergyMoment_zero (n : ℕ) (β : ℝ) :
    scalarCenteredEnergyMoment n β 0=-energyMeanDeficit n β := by
  rw [scalarCenteredEnergyMoment,normalizedEnergyMoment_zero]
  unfold energyMeanDeficit
  ring

theorem convexOn_scalarCenteredEnergyMoment (n : ℕ) (β : ℝ) (hβ : 0<β) :
    ConvexOn ℝ univ (scalarCenteredEnergyMoment n β) := by
  have hh:=((QuantitativeFollowup.convexOn_normalizedEnergyMoment n β hβ).smul
    (show 0≤(n:ℝ)⁻¹ by positivity)).add_const (-scalarEnergyValue β 0)
  convert! hh using 1
  funext lam
  simp only [scalarCenteredEnergyMoment,smul_eq_mul,Pi.add_apply]
  ring

theorem hasDerivAt_scalarCenteredEnergyMoment_zero (n : ℕ) (β : ℝ) :
    HasDerivAt (scalarCenteredEnergyMoment n β)
      (variance (energyFreeEnergy n β) (couplingLaw n)/(2*(n:ℝ))) 0 := by
  convert! ((hasDerivAt_normalizedEnergyMoment_zero n β).div_const (n:ℝ)).sub_const
    (scalarEnergyValue β 0) using 1 <;> (try dsimp [scalarCenteredEnergyMoment]) <;> ring

theorem integrable_exp_completedEnergyFreeEnergy (n : ℕ) (β lam : ℝ) :
    Integrable (fun p=>Real.exp (lam*completedEnergyFreeEnergy n β p)) (completionLaw n) := by
  have hi:=(integrable_exp_energyFreeEnergy n β lam).mul_prod
    (integrable_exp_mul_gaussianReal (μ:=0) (v:=1/2) lam)
  convert! hi using 1
  funext p
  rw [completedEnergyFreeEnergy,mul_add,Real.exp_add]

theorem cgf_completedEnergyFreeEnergy (n : ℕ) (β lam : ℝ) :
    cgf (completedEnergyFreeEnergy n β) (completionLaw n) lam=
      cgf (energyFreeEnergy n β) (couplingLaw n) lam+lam^2/4 := by
  have hm : mgf (completedEnergyFreeEnergy n β) (completionLaw n) lam=
      mgf (energyFreeEnergy n β) (couplingLaw n) lam*Real.exp (lam^2/4) := by
    unfold mgf completedEnergyFreeEnergy completionLaw
    simp_rw [mul_add,Real.exp_add]
    rw [integral_prod_mul (fun g=>Real.exp (lam*energyFreeEnergy n β g))
      (fun d:ℝ=>Real.exp (lam*d))]
    have hg:=congrFun (mgf_fun_id_gaussianReal (μ:=0) (v:=1/2)) lam
    simp only [mgf,zero_mul,zero_add] at hg
    rw [hg]
    congr 2
    norm_num
    ring
  unfold cgf
  rw [hm,Real.log_mul (mgf_pos (integrable_exp_energyFreeEnergy n β lam)).ne'
    (Real.exp_ne_zero _),Real.log_exp]

theorem completedEnergyLaplace_eq (n : ℕ) (hn : 0<n) (β : ℝ)
    {lam : ℝ} (hlam : lam≠0) :
    completedEnergyLaplace n β lam=normalizedEnergyMoment n β lam/(n:ℝ)+lam/(4*(n:ℝ)) := by
  have hn' : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  rw [completedEnergyLaplace,if_neg hlam,cgf_completedEnergyFreeEnergy,
    normalizedEnergyMoment_of_ne n β hlam]
  unfold cgf mgf
  field_simp
  <;> ring

theorem completedEnergyLaplace_eq_original (n : ℕ) (β lam : ℝ) (hβ : β≠0) :
    completedEnergyLaplace n β lam=completedFractionalPressure n β (lam/β)/β := by
  by_cases hl : lam=0
  · subst lam
    simp only [completedEnergyLaplace,completedFractionalPressure,zero_div,ite_true,pressure]
    rw [show energyFreeEnergy n β=(fun g=>logPartition n β g/β) by rfl,
      integral_div]
    ring
  · have hlβ : lam/β≠0:=div_ne_zero hl hβ
    rw [completedEnergyLaplace,if_neg hl,completedFractionalPressure,if_neg hlβ]
    have he : completedEnergyFreeEnergy n β=(fun p=>β⁻¹*completedLogPartition n β p) := by
      funext p
      unfold completedEnergyFreeEnergy completedLogPartition energyFreeEnergy
      field_simp
    rw [he,cgf,mgf_const_mul]
    change cgf (completedLogPartition n β) (completionLaw n) (β⁻¹*lam)/((n:ℝ)*lam)=_
    rw [show β⁻¹*lam=lam/β by ring]
    field_simp

theorem energy_tail_moment_exact (n : ℕ) (hn : 0<n) (β : ℝ)
    {lam : ℝ} (hlam : lam≠0) :
    scalarCenteredEnergyMoment n β lam=scalarEnergyValue β lam-scalarEnergyValue β 0-
      energyComparisonError n β lam-lam/(4*(n:ℝ)) := by
  rw [energyComparisonError,completedEnergyLaplace_eq n hn β hlam,scalarCenteredEnergyMoment]
  ring

/-- All finite-temperature clauses; the scalar zero-temperature clause is
deliberately a separate target, whose profile construction is not assumed. -/
def EnergyMomentFiniteTarget : Prop :=
  ∀n:ℕ,0<n→∀β:ℝ,0<β→
    (∀lam:ℝ, Integrable (fun g=>Real.exp (lam*(energyFreeEnergy n β g-
      (n:ℝ)*scalarEnergyValue β 0))) (couplingLaw n) ∧
      0 < mgf (fun g=>energyFreeEnergy n β g-(n:ℝ)*scalarEnergyValue β 0) (couplingLaw n) lam) ∧
    (∀lam:ℝ,lam≠0→scalarCenteredEnergyMoment n β lam=
      scalarCenteredEnergyLogMoment n β lam/((n:ℝ)*lam)) ∧
    ConvexOn ℝ univ (scalarCenteredEnergyMoment n β) ∧
    scalarCenteredEnergyMoment n β 0=-energyMeanDeficit n β ∧
    HasDerivAt (scalarCenteredEnergyMoment n β)
      (variance (energyFreeEnergy n β) (couplingLaw n)/(2*(n:ℝ))) 0 ∧
    ∀lam∈Ioc (0:ℝ) β,scalarCenteredEnergyMoment n β lam=
      scalarEnergyValue β lam-scalarEnergyValue β 0-energyComparisonError n β lam-lam/(4*(n:ℝ))

theorem energy_moment_finite : EnergyMomentFiniteTarget := by
  intro n hn β hβ
  refine ⟨fun lam=>⟨integrable_exp_scalarCenteredEnergy n β lam,
    scalarCenteredEnergy_mgf_pos n β lam⟩,
    fun lam hlam=>scalarCenteredEnergyMoment_of_ne n hn β hlam,
    convexOn_scalarCenteredEnergyMoment n β hβ,scalarCenteredEnergyMoment_zero n β,
    hasDerivAt_scalarCenteredEnergyMoment_zero n β,?_⟩
  intro lam hlam
  exact energy_tail_moment_exact n hn β hlam.1.ne'

end QuantitativePaper
