module
public import QuantitativeFollowup.FollowupCavityNormalizerVarianceDerivative
public import QuantitativeFollowup.AnisotropicTailHessian
public import FourPapersCommon.DerivativeInterpolation
public import Mathlib.Analysis.Calculus.FDeriv.Partial

@[expose] public section

/-! Genuine continuity of the spatial differential as the auxiliary variance
moves. Uniform value stability and the profile-independent spatial Hessian
bound yield this continuity, without assuming joint covariance smoothness. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem contDiff_two_anisotropicMeasurePotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) : ContDiff ℝ 2 (anisotropicMeasurePotential D μ) := by
  have hh:=(anisotropicMeasureTailPotential_hessian_limit D μ ⟨0,by norm_num⟩).2
  have he : anisotropicMeasureTailPotential D μ ⟨0,by norm_num⟩=anisotropicMeasurePotential D μ :=
    funext fun P=>anisotropicMeasureTailPotential_zero D μ P
  rw [he] at hh
  exact hh

theorem norm_anisotropicMeasurePotential_variance_fderiv_sub_le
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (b c : ℝ) (hb : 0<b) (hc : 0<c) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ) P-
      fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i c) μ) P‖≤
      2*((1/2:ℝ)+‖anisotropicEnergyMap D‖^2)*Real.sqrt |b-c| := by
  have hval (Q : AnisotropicParameter n) :
      ‖anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ Q-
        anisotropicMeasurePotential (anisotropicReplaceVariance D i c) μ Q‖≤(1/2:ℝ)*|b-c| := by
    simpa only [anisotropicMeasureTailPotential_zero,Subtype.coe_mk,sub_zero,
      Real.norm_eq_abs] using anisotropicMeasureTailPotential_variance_abs_sub_le
        D μ ⟨0,by norm_num⟩ Q i b c hb hc
  have hLb : LipschitzWith (‖anisotropicEnergyMap D‖₊^2)
      (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ)) := by
    simpa only [anisotropicReplaceVariance_energyMap] using
      anisotropicMeasurePotential_fderiv_lipschitz (anisotropicReplaceVariance D i b) μ
  have hLc : LipschitzWith (‖anisotropicEnergyMap D‖₊^2)
      (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i c) μ)) := by
    simpa only [anisotropicReplaceVariance_energyMap] using
      anisotropicMeasurePotential_fderiv_lipschitz (anisotropicReplaceVariance D i c) μ
  simpa only [NNReal.coe_pow,coe_nnnorm] using norm_fderiv_sub_le_sqrt_Banach
    (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ)
    (anisotropicMeasurePotential (anisotropicReplaceVariance D i c) μ)
    ((contDiff_one_anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ).differentiable (by norm_num))
    ((contDiff_one_anisotropicMeasurePotential (anisotropicReplaceVariance D i c) μ).differentiable (by norm_num))
    (‖anisotropicEnergyMap D‖₊^2) hLb hLc (1/2) |b-c| (by norm_num) (abs_nonneg _) hval P

theorem continuousAt_anisotropicMeasurePotential_variance_spatialDifferential
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (b : ℝ) (hb : 0<b) (P : AnisotropicParameter n) :
    ContinuousAt (fun z : ℝ×AnisotropicParameter n=>
      fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ) z.2) (b,P) := by
  let L : ℝ:=‖anisotropicEnergyMap D‖^2
  have he : ∀ᶠ z : ℝ×AnisotropicParameter n in 𝓝 (b,P),
      ‖fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ) z.2-
        fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ) P‖≤
        2*(1/2+L)*Real.sqrt |z.1-b|+L*‖z.2-P‖ := by
    have hp : ∀ᶠz : ℝ×AnisotropicParameter n in 𝓝 (b,P),0<z.1 :=
      (continuous_fst : Continuous (fun z : ℝ×AnisotropicParameter n=>z.1)).continuousAt.eventually (Ioi_mem_nhds hb)
    filter_upwards [hp] with z hz
    have hv:=norm_anisotropicMeasurePotential_variance_fderiv_sub_le D μ i z.1 b hz hb z.2
    have hL:=anisotropicMeasurePotential_fderiv_lipschitz (anisotropicReplaceVariance D i b) μ
    rw [anisotropicReplaceVariance_energyMap] at hL
    have htri : ‖fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ) z.2-
        fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ) P‖≤
        ‖fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ) z.2-
          fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ) z.2‖+
        ‖fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ) z.2-
          fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ) P‖ :=
      norm_sub_le_norm_sub_add_norm_sub
        (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ) z.2)
        (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ) z.2)
        (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ) P)
    exact htri.trans (add_le_add hv
      (by simpa only [L,NNReal.coe_pow,coe_nnnorm] using hL.norm_sub_le z.2 P))
  have hu : Tendsto (fun z : ℝ×AnisotropicParameter n=>
      2*(1/2+L)*Real.sqrt |z.1-b|+L*‖z.2-P‖) (𝓝 (b,P)) (𝓝 0) := by
    have hc : Continuous (fun z : ℝ×AnisotropicParameter n=>
      2*(1/2+L)*Real.sqrt |z.1-b|+L*‖z.2-P‖) := by fun_prop
    simpa only [sub_self,abs_zero,Real.sqrt_zero,norm_zero,mul_zero,add_zero] using hc.tendsto (b,P)
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm' he hu)

end QuantitativeFollowup
