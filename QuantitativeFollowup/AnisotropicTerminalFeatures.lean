module
public import QuantitativeFollowup.AnisotropicFiniteFeatureKernels

@[expose] public section

/-! The terminal spin is sampled from the literal anisotropic Hamiltonian
Gibbs kernel. Pair responses at time one equal its actual moments. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def anisotropicTerminalSpinKernel (D : AnisotropicSpinModel n) :
    Kernel (AnisotropicParameter n) (Configuration n) :=
  (finiteStateGibbsKernel (fun _ : Configuration n=>0)).comap (anisotropicEnergyMap D)
    (anisotropicEnergyMap D).continuous.measurable

instance anisotropicTerminalSpinKernel_markov (D : AnisotropicSpinModel n) :
    IsMarkovKernel (anisotropicTerminalSpinKernel D) := by
  haveI := isMarkovKernel_finiteStateGibbsKernel (fun _ : Configuration n=>0)
  unfold anisotropicTerminalSpinKernel
  infer_instance

theorem anisotropicFiniteSpinKernel_zero_eq_terminalKernel (D : AnisotropicSpinModel n) (s : RSBScheme k) :
    anisotropicFiniteSpinKernel D s 0=anisotropicTerminalSpinKernel D := by
  simp only [anisotropicFiniteSpinKernel,anisotropicTerminalSpinKernel,
    finiteStateCascadeGibbsKernel,finiteStateCascadeFieldKernel,
    OverlapPaper.sourceKernelLaw,Kernel.comp_id]

def anisotropicTerminalFeatureMean (D : AnisotropicSpinModel n) (f : Configuration n→ℝ)
    (P : AnisotropicParameter n) : ℝ := ∫σ,f σ ∂anisotropicTerminalSpinKernel D P

theorem anisotropicFiniteFeatureMean_zero (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (f : Configuration n→ℝ) :
    anisotropicFiniteFeatureMean D s 0 f=anisotropicTerminalFeatureMean D f := by
  funext P
  rw [anisotropicFiniteFeatureMean,anisotropicTerminalFeatureMean,anisotropicFiniteSpinKernel_zero_eq_terminalKernel]

theorem anisotropicTerminalFeatureMean_bound (D : AnisotropicSpinModel n)
    (f : Configuration n→ℝ) (B : ℝ) (hb : ∀σ,‖f σ‖≤B) (P : AnisotropicParameter n) :
    ‖anisotropicTerminalFeatureMean D f P‖≤B := by
  simpa only [anisotropicTerminalFeatureMean,probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ:=anisotropicTerminalSpinKernel D P) (.of_forall hb))

theorem measurable_anisotropicTerminalFeatureMean (D : AnisotropicSpinModel n)
    (f : Configuration n→ℝ) : Measurable (anisotropicTerminalFeatureMean D f) :=
  (measurable_of_finite f).stronglyMeasurable.integral_kernel.measurable

theorem anisotropicFiniteTailPairResponse_one (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    anisotropicFiniteTailPairResponse D s 1 P e=
      anisotropicTerminalFeatureMean D (fun σ=>Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)) P := by
  have hnode : anisotropicSchemeNode s (k+2) le_rfl=(1 : Paper.Overlap) := by
    apply Subtype.ext
    exact s.q_top
  rw [←hnode,anisotropicFiniteTailPairResponse_node,Nat.sub_self,anisotropicFiniteSpinKernel_zero_eq_terminalKernel]
  rfl

theorem anisotropicTailPairResponse_one (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    anisotropicTailPairResponse D μ 1 P e=
      anisotropicTerminalFeatureMean D (fun σ=>Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)) P := by
  have h := tendsto_anisotropicFiniteTailPairResponse_moving D μ e
    (tendsto_const_nhds (x:=(1 : Paper.Overlap))) (tendsto_const_nhds (x:=P))
  simp_rw [anisotropicFiniteTailPairResponse_one] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem continuous_anisotropicTerminalPairMean (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (e : AnisotropicCouplingIndex n) : Continuous (anisotropicTerminalFeatureMean D
      (fun σ=>Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2))) := by
  have h := (continuous_anisotropicTailPairResponse_joint D μ e).comp
    ((continuous_const (y:=(1 : Paper.Overlap))).prodMk continuous_id)
  simp only [Function.comp_def,anisotropicTailPairResponse_one] at h
  exact h

end QuantitativeFollowup
