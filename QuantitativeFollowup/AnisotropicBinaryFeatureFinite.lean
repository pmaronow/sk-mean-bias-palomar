module
public import QuantitativeFollowup.AnisotropicFiniteFeatureKernels
public import QuantitativeFollowup.FollowupCavityBinaryNodeStieltjes
public import FourPapersCommon.FiniteStateCascadeExpectationTransport

@[expose] public section

/-! The actual pair-spin parameter Hessian and its finite strict-future
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

def anisotropicPairFeature (e : AnisotropicCouplingIndex n) : FiniteStateField (Configuration n) :=
  cavityPairFeature e.1.1 e.1.2

theorem anisotropicPairFeature_binary (e : AnisotropicCouplingIndex n) (σ : Configuration n) :
    anisotropicPairFeature e σ*anisotropicPairFeature e σ=1 := cavityPairFeature_binary _ _ σ

def anisotropicFinitePairSecond (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicFinitePotential (anisotropicUnitCouplings D) s j))
    (anisotropicCouplingRescaling D P) (anisotropicCouplingDirection e) (anisotropicCouplingDirection e)

theorem anisotropicFinitePairSecond_eq_energy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    anisotropicFinitePairSecond D s j P e=
      fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j)) (anisotropicEnergyMap D P)
        (anisotropicPairFeature e) (anisotropicPairFeature e) := by
  change directionalHessian (anisotropicFinitePotential (anisotropicUnitCouplings D) s j)
    (anisotropicCouplingRescaling D P) (anisotropicCouplingDirection e)=_
  rw [anisotropicFinitePotential_hessian_eq_cascade]
  have hinput : (fun l=>(anisotropicEnergyMap (anisotropicUnitCouplings D)).comp
      (anisotropicSchemeInput (anisotropicUnitCouplings D) s l))=cavityFiniteEnergyInput D s :=
    funext (anisotropicEnergyInputs_unitCouplings D s)
  have hfeature : anisotropicEnergyMap (anisotropicUnitCouplings D) (anisotropicCouplingDirection e)=
      anisotropicPairFeature e := by
    ext σ
    exact anisotropicTerminalLinear_unitCoupling D e σ
  rw [hinput,anisotropicEnergyMap_unitCouplings,hfeature]

theorem anisotropicFinitePair_energy_first (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j)
      (anisotropicEnergyMap D P) (anisotropicPairFeature e)=
      anisotropicFiniteFeatureMean D s j (anisotropicPairFeature e) P := by
  rw [fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean _ _ (anisotropicSchemeMass_nonneg s)]
  rfl

theorem anisotropicFinitePair_energy_future_square (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (p j : ℕ) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    finiteStateCascadePairMoment (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) p j (anisotropicEnergyMap D P)
      (anisotropicPairFeature e) (anisotropicPairFeature e)=
      sourceKernelExpectation (fun r=>anisotropicDepthKernel D s (p+r)) j
        (fun y=>(anisotropicFiniteFeatureMean D s p (anisotropicPairFeature e) y)^2) P := by
  let F:=finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) p
  let G:=fun y : FiniteStateField (Configuration n)=>
    fderiv ℝ F y (anisotropicPairFeature e)*fderiv ℝ F y (anisotropicPairFeature e)
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
  rw [anisotropicFinitePair_energy_first]
  ring

theorem anisotropicFinitePairSecond_future_decomposition (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    anisotropicFinitePairSecond D s j P e+
      anisotropicSchemeMass s j*(anisotropicFiniteFeatureMean D s j (anisotropicPairFeature e) P)^2+
      (∑p∈Finset.range j,(anisotropicSchemeMass s p-anisotropicSchemeMass s (p+1))*
        sourceKernelExpectation (fun r=>anisotropicDepthKernel D s (p+1+r)) (j-(p+1))
          (fun y=>(anisotropicFiniteFeatureMean D s (p+1) (anisotropicPairFeature e) y)^2) P)=1 := by
  have he:=finiteStateCascadeBinaryFeature_second (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) j
    (anisotropicEnergyMap D P) (anisotropicPairFeature e) (anisotropicPairFeature_binary e)
  have ha0 : anisotropicSchemeMass s 0=1 := by simp [anisotropicSchemeMass,s.m_top]
  rw [ha0,sub_self,zero_mul,sub_zero,←anisotropicFinitePairSecond_eq_energy,
    anisotropicFinitePair_energy_first] at he
  simp_rw [←finiteStateCascadePairMoment_eq_splitLaw _ _ (anisotropicSchemeMass_nonneg s),
    anisotropicFinitePair_energy_future_square] at he
  linarith

end QuantitativeFollowup
