module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeNodeMean
public import QuantitativeFollowup.FollowupCavitySignedResponseFutureScoreLimit
public import FRSB.FiniteForwardAction

@[expose] public section

/-! The retained finite posterior score equals the literal strict-future
profile integral along the genuine restarted Wiener state. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

theorem cavityRestartSpinVector_scheme_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (v : ℕ) (hv : v≤k+2) (sample : VectorDisorderBrownianSample n) :
    cavityRestartSpinVector D (Paper.parisiSchemeMeasure s) g q x sample
      (max q (anisotropicSchemeNode s v hv))=
      anisotropicFiniteTailMagnetization D s (max q (anisotropicSchemeNode s v hv))
        (anisotropicFiniteRestartPhysicalParameter D s g q (anisotropicInverseNoiseMap D x)
          (anisotropicRestartElapsed s q v) sample) := by
  unfold cavityRestartSpinVector anisotropicRestartPhysicalParameter
  rw [anisotropicMeasureTailMagnetization_scheme_eq_finite,anisotropicRestartState_scheme_eq_finite]
  rfl

theorem cascadePosteriorRecordedScore_anisotropic_integral (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (z : VectorDisorderBrownianSample n×Configuration n) :
    cascadePosteriorRecordedScore (fun _ : Configuration n=>0)
      (anisotropicSchemeMass (vectorClampedScheme s q q.property))
      (fun l=>(anisotropicEnergyMap D).comp
        (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
      (k+1) (anisotropicEnergyMap D (anisotropicFieldInjection n w))
      (anisotropicFiniteRestartEnergyHistory D s g q (anisotropicInverseNoiseMap D x) z.1,z.2)=
      fieldDot w z.2-
        ∫r,inner ℝ w (cavityRestartSpinVector D (Paper.parisiSchemeMeasure s) g q x z.1 (max q r))
          ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap) := by
  unfold cascadePosteriorRecordedScore
  rw [anisotropicEnergyMap_field,Fintype.sum_option,Fintype.sum_option]
  let cs:=vectorClampedScheme s q q.property
  let a:=anisotropicSchemeMass cs
  have ha0 : anisotropicSchemeMass (vectorClampedScheme s q q.property) 0=1 := by
    change cs.m ((k+1)+1)=1
    rw [vectorClampedScheme_mass_succ]
    exact s.m_top
  have haN : anisotropicSchemeMass (vectorClampedScheme s q q.property) (k+1)=0 := by
    change cs.m (k+1+1-(k+1))=0
    rw [show k+1+1-(k+1)=0+1 by omega,vectorClampedScheme_mass_succ]
    exact s.m_zero
  have hw (i : Fin (k+1)) : cascadePosteriorStieltjesWeight a (k+1) (some (some i))=
      s.m (i+1)-s.m i := by
    have hi:=i.isLt
    simp only [cascadePosteriorStieltjesWeight,a,anisotropicSchemeMass,
      show k+1+1-(k+1-(i+1))=(i+1)+1 by omega,
      show k+1+1-(k+1-i)=i+1 by omega,
      cs,vectorClampedScheme_mass_succ]
  simp only [cascadePosteriorStieltjesWeight,ha0,haN,sub_self,zero_mul,add_zero,zero_add]
  rw [FRSB.integral_parisiSchemeMeasure]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : (i:ℕ)+1≤k+2 := by have:=i.isLt;omega
  rw [show (anisotropicSchemeMass cs) (k+1-(i+1))-
      (anisotropicSchemeMass cs) (k+1-i)=s.m (i+1)-s.m i from hw i]
  congr 1
  change cascadePosteriorRecordedMean _ _ _ _ (i+1) _ _=_
  rw [cascadePosteriorRecordedMean_anisotropic_restart_node D s g q
    (anisotropicInverseNoiseMap D x) w (i+1) hi z.1,
    ←cavityRestartSpinVector_scheme_node D s g q x (i+1) hi z.1]
  exact real_inner_comm _ _

theorem cavityRestart_field_mean_integral_residual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x w : Field n) (sample : VectorDisorderBrownianSample n) :
    (∫r,inner ℝ w (cavityRestartSpinVector D μ g q x sample (max q r))
      ∂(μ:Measure Paper.Overlap))=
      inner ℝ w (cavityRestartSpinVector D μ g q x sample q)+
      ∫r,cavityRestartStrictFutureResidual D μ g q x w sample r ∂(μ:Measure Paper.Overlap) := by
  let F : C(Paper.Overlap,ℝ):=⟨cavityRestartStrictFutureResidual D μ g q x w sample,
    continuous_cavityRestartStrictFutureResidual D μ g q x w sample⟩
  have he : (fun r=>inner ℝ w (cavityRestartSpinVector D μ g q x sample (max q r)))=
      fun r=>inner ℝ w (cavityRestartSpinVector D μ g q x sample q)+F r := by
    funext r
    dsimp only [F,ContinuousMap.coe_mk,cavityRestartStrictFutureResidual]
    rw [inner_sub_right]
    ring
  rw [he,integral_add (integrable_const _) (continuousMap_integrable_probability F μ),integral_const]
  simp only [probReal_univ,one_smul,F,ContinuousMap.coe_mk]

theorem cascadePosteriorRecordedScore_anisotropic_residual (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (z : VectorDisorderBrownianSample n×Configuration n) :
    cascadePosteriorRecordedScore (fun _ : Configuration n=>0)
      (anisotropicSchemeMass (vectorClampedScheme s q q.property))
      (fun l=>(anisotropicEnergyMap D).comp
        (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
      (k+1) (anisotropicEnergyMap D (anisotropicFieldInjection n w))
      (anisotropicFiniteRestartEnergyHistory D s g q (anisotropicInverseNoiseMap D x) z.1,z.2)=
      fieldDot w z.2-inner ℝ w (cavityRestartSpinVector D (Paper.parisiSchemeMeasure s) g q x z.1 q)-
        ∫r,cavityRestartStrictFutureResidual D (Paper.parisiSchemeMeasure s) g q x w z.1 r
          ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap) := by
  rw [cascadePosteriorRecordedScore_anisotropic_integral,cavityRestart_field_mean_integral_residual]
  ring

end QuantitativeFollowup
