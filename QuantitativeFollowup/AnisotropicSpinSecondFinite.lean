module
public import QuantitativeFollowup.AnisotropicFiniteFeatureKernels
public import QuantitativeFollowup.AnisotropicNativeSpinConditionals
public import QuantitativeFollowup.FollowupCavityBinaryNodeStieltjes
public import FourPapersCommon.FiniteStateCascadeExpectationTransport

@[expose] public section

/-! The actual single-spin field-parameter Hessian and its finite strict-future
normalized moment decomposition. All future laws are the constructed
anisotropic Gaussian transition kernels. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open OverlapPaper (sourceKernelExpectation)
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def anisotropicSpinFeature (e : Fin n) : FiniteStateField (Configuration n) :=
  WithLp.toLp 2 (fun σ=>Paper.spinSign (σ e))

theorem anisotropicSpinFeature_binary (e : Fin n) (σ : Configuration n) :
    anisotropicSpinFeature e σ*anisotropicSpinFeature e σ=1 := by
  change Paper.spinSign (σ e)*Paper.spinSign (σ e)=1
  rw [←pow_two,Paper.spinSign_sq]

def anisotropicFiniteSpinSecond (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicFinitePotential D s j))
    P (anisotropicCoordinateDirection n e) (anisotropicCoordinateDirection n e)

theorem anisotropicFiniteSpinSecond_eq_energy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : Fin n) :
    anisotropicFiniteSpinSecond D s j P e=
      fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j)) (anisotropicEnergyMap D P)
        (anisotropicSpinFeature e) (anisotropicSpinFeature e) := by
  change directionalHessian (anisotropicFinitePotential D s j)
    P (anisotropicCoordinateDirection n e)=_
  rw [anisotropicFinitePotential_hessian_eq_cascade]
  have hfeature : anisotropicEnergyMap D (anisotropicCoordinateDirection n e)=anisotropicSpinFeature e := by
    ext σ
    exact anisotropicTerminalLinear_coordinate D σ e
  rw [hfeature]
  rfl

theorem continuous_anisotropicSpinResponse_joint (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (e : Fin n) :
    Continuous (fun z : Paper.Overlap×AnisotropicParameter n=>anisotropicMeasureTailMagnetization D μ z.1 z.2 e) := by
  have h:=((EuclideanSpace.proj e : Field n→L[ℝ]ℝ).continuous).comp
    (continuous_anisotropicMeasureTailMagnetization_joint D μ)
  simpa only [Function.comp_def,ContinuousLinearMap.id_apply,EuclideanSpace.coe_proj] using h

theorem anisotropicFiniteSpin_energy_first (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : Fin n) :
    fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j)
      (anisotropicEnergyMap D P) (anisotropicSpinFeature e)=
      anisotropicFiniteFeatureMean D s j (anisotropicSpinFeature e) P := by
  rw [fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean _ _ (anisotropicSchemeMass_nonneg s)]
  rfl

theorem anisotropicFiniteSpin_energy_future_square (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (p j : ℕ) (P : AnisotropicParameter n) (e : Fin n) :
    finiteStateCascadePairMoment (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) p j (anisotropicEnergyMap D P)
      (anisotropicSpinFeature e) (anisotropicSpinFeature e)=
      sourceKernelExpectation (fun r=>anisotropicDepthKernel D s (p+r)) j
        (fun y=>(anisotropicFiniteFeatureMean D s p (anisotropicSpinFeature e) y)^2) P := by
  let F:=finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) p
  let G:=fun y : FiniteStateField (Configuration n)=>
    fderiv ℝ F y (anisotropicSpinFeature e)*fderiv ℝ F y (anisotropicSpinFeature e)
  have hF:=contDiff_one_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) p
  have hGm : Measurable G:=
    (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)).measurable
  have ht:=sourceKernelExpectation_finiteStateCascade_comp_linear
    (anisotropicEnergyMap D) (anisotropicSchemeInput D s) (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (gtStateLogPartition (fun _ : Configuration n=>0))
    (finiteStateGaussianTerminal_lipschitz _) p j G hGm P
  rw [←anisotropicDepthKernel_eq_parameterCascadeKernel] at ht
  change sourceKernelExpectation _ j G (anisotropicEnergyMap D P)=_ at ht
  rw [finiteStateCascadePairMoment]
  change sourceKernelExpectation (fun r=>finiteStateGaussianCascadeKernel
    (anisotropicSchemeMass s) (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l))
    (gtStateLogPartition (fun _ : Configuration n=>0)) (p+r)) j G (anisotropicEnergyMap D P)=_
  rw [ht]
  congr 1
  funext y
  dsimp only [G,F]
  rw [anisotropicFiniteSpin_energy_first]
  ring

theorem anisotropicFiniteSpinSecond_future_decomposition (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) (e : Fin n) :
    anisotropicFiniteSpinSecond D s j P e+
      anisotropicSchemeMass s j*(anisotropicFiniteFeatureMean D s j (anisotropicSpinFeature e) P)^2+
      (∑p∈Finset.range j,(anisotropicSchemeMass s p-anisotropicSchemeMass s (p+1))*
        sourceKernelExpectation (fun r=>anisotropicDepthKernel D s (p+1+r)) (j-(p+1))
          (fun y=>(anisotropicFiniteFeatureMean D s (p+1) (anisotropicSpinFeature e) y)^2) P)=1 := by
  have he:=finiteStateCascadeBinaryFeature_second (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) j
    (anisotropicEnergyMap D P) (anisotropicSpinFeature e) (anisotropicSpinFeature_binary e)
  have ha0 : anisotropicSchemeMass s 0=1 := by simp [anisotropicSchemeMass,s.m_top]
  rw [ha0,sub_self,zero_mul,sub_zero,←anisotropicFiniteSpinSecond_eq_energy,
    anisotropicFiniteSpin_energy_first] at he
  simp_rw [←finiteStateCascadePairMoment_eq_splitLaw _ _ (anisotropicSchemeMass_nonneg s),
    anisotropicFiniteSpin_energy_future_square] at he
  linarith

end QuantitativeFollowup
