module
public import QuantitativeFollowup.AnisotropicFiniteCascade
public import QuantitativePaper.VectorTerminalSmooth
public import QuantitativePaper.SmoothGaussianStep
public import QuantitativePaper.VectorSharpMassBounds

@[expose] public section

/-! Genuine joint C∞ and bounded positive-order spatial jets of the
anisotropic finite-profile potential. Constants are constructed from
bounded affine spin features and the actual Gaussian recursion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem anisotropicFinitePotential_terminal_softmax (D : AnisotropicSpinModel n)
    (s : RSBScheme k) : anisotropicFinitePotential D s 0=finiteLinearSoftmax (anisotropicTerminalLinear D) := by
  funext P
  simp only [anisotropicFinitePotential,finiteStateGaussianTerminalCascade,
    finiteStateGaussianCascade,gtStateLogPartition,gtStatePartition,finiteLinearSoftmax,
    finiteLinearPartition,anisotropicEnergyMap_apply,add_zero]

theorem anisotropicFinitePotential_gaussianShiftColeHopf (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) :
    anisotropicFinitePotential D s (j+1)=gaussianShiftColeHopf (anisotropicSchemeInput D s j)
      (anisotropicSchemeMass s j) (anisotropicFinitePotential D s j) := by
  funext P
  rw [anisotropicFinitePotential_coleHopf]
  unfold OverlapPaper.sourceLogAverage gaussianShiftColeHopf gaussianShiftAverage gaussianShiftPartition
  rw [fieldGaussian_eq_stdGaussian]

theorem anisotropicFinitePotential_smooth_bounded_jets (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (N j : ℕ) :
    ContDiff ℝ N (anisotropicFinitePotential D s j) ∧
    ∃ K : ℝ,1 ≤ K ∧ ∀i,1 ≤ i→i ≤ N→∀P : AnisotropicParameter n,
      ‖iteratedFDeriv ℝ i (anisotropicFinitePotential D s j) P‖ ≤ K^i := by
  induction j with
  | zero =>
    rw [anisotropicFinitePotential_terminal_softmax]
    let l:=anisotropicTerminalLinear D
    let B:=fun i=>(i.factorial:ℝ)*logJetCoefficient i*(finitePartitionPowerBound l N)^i
    refine ⟨contDiff_finiteLinearSoftmax _ N,finiteJetPowerBound B N,
      finiteJetPowerBound_ge_one B N,?_⟩
    intro i hi0 hi P
    exact (norm_iteratedFDeriv_finiteLinearSoftmax_le l N i hi0 hi P).trans
      (finite_jet_bound_le_power B N i hi0 hi)
  | succ j ih =>
    obtain ⟨hf,K,hK,hJets⟩:=ih
    rw [anisotropicFinitePotential_gaussianShiftColeHopf]
    exact gaussianShiftColeHopf_smooth_bounded_jets N _ hf ‖anisotropicEnergyMap D‖₊
      (anisotropicFinitePotential_lipschitz D s j) K hK hJets
      (anisotropicSchemeInput D s j) (anisotropicSchemeMass s j)

theorem contDiff_anisotropicFinitePotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) : ContDiff ℝ ∞ (anisotropicFinitePotential D s j) :=
  contDiff_infty.mpr (fun N=>(anisotropicFinitePotential_smooth_bounded_jets D s N j).1)

end QuantitativeFollowup
