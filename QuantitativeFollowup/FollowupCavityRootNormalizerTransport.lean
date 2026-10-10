module
public import QuantitativeFollowup.FollowupCavityRootScaling
public import QuantitativeFollowup.FollowupCavityNormalizerVarianceJets
public import QuantitativeFollowup.AnisotropicBinaryFeatureStieltjes
public import FourPapersCommon.SecondDerivativeComposition

@[expose] public section

/-! Actual arbitrary-profile coupling-coordinate transport. Each identity is
obtained from the honest finite Gaussian cascade and its proved limit. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem anisotropicFinitePotential_rootCouplingScale (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (s : RSBScheme k) (j : ℕ)
    (g : AnisotropicDisorder n) :
    anisotropicFinitePotential (anisotropicScaleRootCouplings D p u) s j
        (anisotropicDisorderInjection n g)=
      anisotropicFinitePotential D s j
        (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) := by
  unfold anisotropicFinitePotential
  rw [show (fun l=>(anisotropicEnergyMap (anisotropicScaleRootCouplings D p u)).comp
      (anisotropicSchemeInput (anisotropicScaleRootCouplings D p u) s l))=
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) from
        funext (cavityFiniteEnergyInput_scaleRootCouplings D p u s)]
  have he:=congrArg (fun L : AnisotropicDisorder n→L[ℝ]FiniteStateField (Configuration n)=>L g)
    (anisotropicRootEnergyMap_scaleRootCouplings D p u)
  exact congrArg (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j) he

theorem anisotropicMeasurePotential_rootCouplingScale (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : AnisotropicCouplingIndex n→Bool) (u : ℝ)
    (g : AnisotropicDisorder n) :
    anisotropicMeasurePotential (anisotropicScaleRootCouplings D p u) μ
        (anisotropicDisorderInjection n g)=
      anisotropicMeasurePotential D μ
        (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) := by
  apply tendsto_nhds_unique (tendsto_anisotropicDyadicPotential _ μ _)
  convert tendsto_anisotropicDyadicPotential D μ
    (anisotropicDisorderInjection n (gaussianSelectedScale p u g)) using 1
  funext j
  exact anisotropicFinitePotential_rootCouplingScale D p u _ _ g

theorem anisotropicMeasurePotential_unitCouplings (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) :
    anisotropicMeasurePotential (anisotropicUnitCouplings D) μ (anisotropicCouplingRescaling D P)=
      anisotropicMeasurePotential D μ P := by
  apply tendsto_nhds_unique (tendsto_anisotropicDyadicPotential _ μ _)
  convert tendsto_anisotropicDyadicPotential D μ P using 1
  funext j
  exact anisotropicFinitePotential_unitCouplings D _ _ P

theorem anisotropicCouplingRescaling_direction (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) :
    anisotropicCouplingRescaling D (anisotropicCouplingDirection e)=
      D.coupling e • anisotropicCouplingDirection e := by
  classical
  ext i
  cases i with
  | inl f =>
    by_cases hf:f=e
    · subst f;simp [anisotropicCouplingRescaling,anisotropicCouplingDirection,PiLp.single_apply,smul_eq_mul]
    · simp [anisotropicCouplingRescaling,anisotropicCouplingDirection,PiLp.single_apply,smul_eq_mul,hf]
  | inr i => simp [anisotropicCouplingRescaling,anisotropicCouplingDirection,PiLp.single_apply]

theorem anisotropicMeasurePotential_pair_first (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    fderiv ℝ (anisotropicMeasurePotential D μ) P (anisotropicCouplingDirection e)=
      D.coupling e*anisotropicTailPairResponse D μ ⟨0,by norm_num⟩ P e := by
  letI : IsBoundedSMul ℝ (AnisotropicParameter n) := .of_norm_smul_le norm_smul_le
  letI : ContinuousSMul ℝ (AnisotropicParameter n) := IsBoundedSMul.continuousSMul
  have he : anisotropicMeasurePotential D μ=
      (anisotropicMeasurePotential (anisotropicUnitCouplings D) μ)∘anisotropicCouplingRescaling D :=
    funext fun P=>(anisotropicMeasurePotential_unitCouplings D μ P).symm
  rw [he,fderiv_comp P
    ((contDiff_one_anisotropicMeasurePotential _ μ).differentiable (by norm_num) _)
    (anisotropicCouplingRescaling D).differentiableAt]
  simp only [ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,
    anisotropicCouplingRescaling_direction,map_smul,smul_eq_mul]
  unfold anisotropicTailPairResponse
  have hz : anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ ⟨0,by norm_num⟩=
      anisotropicMeasurePotential (anisotropicUnitCouplings D) μ :=
    funext (anisotropicMeasureTailPotential_zero _ μ)
  rw [hz]

theorem anisotropicMeasurePotential_pair_second (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) :
    fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential D μ)) P
      (anisotropicCouplingDirection e) (anisotropicCouplingDirection e)=
        (D.coupling e)^2*anisotropicTailPairSecond D μ ⟨0,by norm_num⟩ P e := by
  letI : IsBoundedSMul ℝ (AnisotropicParameter n) := .of_norm_smul_le norm_smul_le
  letI : ContinuousSMul ℝ (AnisotropicParameter n) := IsBoundedSMul.continuousSMul
  have he : anisotropicMeasurePotential D μ=
      (anisotropicMeasurePotential (anisotropicUnitCouplings D) μ)∘anisotropicCouplingRescaling D :=
    funext fun P=>(anisotropicMeasurePotential_unitCouplings D μ P).symm
  rw [he,second_fderiv_comp_apply _ _ P (anisotropicCouplingDirection e)
    (contDiff_two_anisotropicMeasurePotential _ μ).contDiffAt
    (anisotropicCouplingRescaling D).contDiff.contDiffAt]
  have hR : fderiv ℝ (⇑(anisotropicCouplingRescaling D))=fun _=>anisotropicCouplingRescaling D :=
    funext fun P=>(anisotropicCouplingRescaling D).fderiv
  simp only [ContinuousLinearMap.fderiv,anisotropicCouplingRescaling_direction,hR,
    fderiv_const_apply,map_smul,smul_eq_mul,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply,map_zero,add_zero]
  unfold anisotropicTailPairSecond
  have hz : anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ ⟨0,by norm_num⟩=
      anisotropicMeasurePotential (anisotropicUnitCouplings D) μ :=
    funext (anisotropicMeasureTailPotential_zero _ μ)
  rw [hz]
  ring

end QuantitativeFollowup
