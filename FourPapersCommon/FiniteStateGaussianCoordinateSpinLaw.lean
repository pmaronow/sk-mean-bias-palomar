module
public import FourPapersCommon.FiniteStateGaussianInputCoordinateLaw
public import FourPapersCommon.FiniteStateCascadeResponses

@[expose] public section

/-! An actual Gaussian input and a terminal spin sampled from its genuine
remaining cascade. The coordinate-spin expectation is a literal normalized
Gaussian response, with integrability and the spin mean proved internally. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
open SpinGlass.AT OverlapPaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

def finiteStateGaussianCoordinateSpinKernel (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ)
    (H : FiniteStateField S) : Kernel (FiniteStateGaussianInput I) S :=
  (finiteStateCascadeGibbsKernel V a L j).comap (fun z=>H+L j z) (by fun_prop)

theorem finiteStateGaussianCoordinateSpinKernel_markov (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) :
    IsMarkovKernel (finiteStateGaussianCoordinateSpinKernel V a L j H) := by
  haveI:=isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
  unfold finiteStateGaussianCoordinateSpinKernel
  infer_instance

def finiteStateGaussianCoordinateSpinLaw (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) : Measure (FiniteStateGaussianInput I×S) :=
  ((stdGaussian (FiniteStateGaussianInput I)).tilted
    (fun z=>a j*finiteStateGaussianTerminalCascade V a L j (H+L j z))) ⊗ₘ
      finiteStateGaussianCoordinateSpinKernel V a L j H

theorem finiteStateGaussianCoordinateSpinLaw_probability (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) :
    IsProbabilityMeasure (finiteStateGaussianCoordinateSpinLaw V a L j H) := by
  haveI:=finiteStateGaussianCoordinateSpinKernel_markov V a ha L j H
  haveI:=isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz
    (finiteStateGaussianTerminalCascade V a L j) (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)
    (L j) H (a j))
  unfold finiteStateGaussianCoordinateSpinLaw
  infer_instance

theorem integrable_finiteStateGaussianCoordinateSpinLaw_feature (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) (i : Fin (Fintype.card I)) :
    Integrable (fun z : FiniteStateGaussianInput I×S=>(finiteStateGaussianBasis I).repr z.1 i*K z.2)
      (finiteStateGaussianCoordinateSpinLaw V a L j H) := by
  let P:=(stdGaussian (FiniteStateGaussianInput I)).tilted
    (fun z=>a j*finiteStateGaussianTerminalCascade V a L j (H+L j z))
  let κ:=finiteStateGaussianCoordinateSpinKernel V a L j H
  haveI : IsMarkovKernel κ:=finiteStateGaussianCoordinateSpinKernel_markov V a ha L j H
  haveI : IsProbabilityMeasure P:=isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz
    _ (finiteStateGaussianTerminalCascade_lipschitz V a ha L j) (L j) H (a j))
  have hi : Integrable (fun z=>(finiteStateGaussianBasis I).repr z i) P:=
    integrable_finiteStateGaussianInput_coordinate_tilt (a j) (L j) _
      (finiteStateGaussianTerminalCascade_lipschitz V a ha L j) H i
  have hpres : MeasurePreserving Prod.fst (P ⊗ₘ κ) P:=⟨measurable_fst,by
    change (P ⊗ₘ κ).fst=P
    exact Measure.fst_compProd P κ⟩
  have hb:=((hpres.integrable_comp_of_integrable hi).norm).mul_const ‖K‖
  apply hb.mono'
  · exact ((continuous_finiteStateGaussianInput_coordinate i).measurable.comp measurable_fst |>.mul
      ((measurable_of_finite (fun σ:S=>K σ)).comp measurable_snd)).aestronglyMeasurable
  · exact .of_forall fun z=>by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K z.2)
        (abs_nonneg _)

theorem finiteStateGaussianCoordinateSpinLaw_coordinate_ibp (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) (i : Fin (Fintype.card I)) :
    (∫z,(finiteStateGaussianBasis I).repr z.1 i*K z.2
      ∂finiteStateGaussianCoordinateSpinLaw V a L j H)=
    ∫y,fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y
        (L j (finiteStateGaussianBasis I i)) K+
      a j*fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K*
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y (L j (finiteStateGaussianBasis I i))
      ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H := by
  haveI:=finiteStateGaussianCoordinateSpinKernel_markov V a ha L j H
  haveI:=isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz
    _ (finiteStateGaussianTerminalCascade_lipschitz V a ha L j) (L j) H (a j))
  have hi:=integrable_finiteStateGaussianCoordinateSpinLaw_feature V a ha L j H K i
  rw [finiteStateGaussianCoordinateSpinLaw,Measure.integral_compProd hi]
  simp_rw [finiteStateGaussianCoordinateSpinKernel,Kernel.comap_apply,integral_const_mul,
    ←fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L j]
  have hc:=finiteStateGaussianTerminalCascade_C2_bounds V a ha L j
  have hfirst : ∀y,‖fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y‖≤(1:ℝ≥0):=
    fun y=>norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)
  have hh:=finiteStateGaussianInput_coordinate_ibp_law (a j) (L j) _ hc.1 1
    (finiteStateCascadeHessianBound a j) hfirst hc.2 H K i
  have hk : finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H=
      finiteStateGaussianStepLaw (a j) (L j) (finiteStateGaussianTerminalCascade V a L j) H:=
    finiteStateGaussianStepKernel_apply (a j) (L j) (finiteStateGaussianTerminalCascade V a L j)
      hc.1.continuous.measurable H
  rw [hk]
  exact hh

end FourPapersCommon
