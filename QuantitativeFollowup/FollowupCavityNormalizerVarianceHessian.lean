module
public import QuantitativeFollowup.FollowupCavityNormalizerVarianceJets

@[expose] public section

/-! Actual joint spatial Hessian continuity as one positive auxiliary
variance varies. Depth-uniform third spatial jets give a common Hessian
Lipschitz bound; two successive derivative interpolation estimates yield
covariance continuity without any joint covariance smoothness premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem anisotropicMeasurePotential_secondDifferential_lipschitz
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) :
    LipschitzWith (8*‖anisotropicEnergyMap D‖₊^3)
      (fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential D μ))) := by
  have hu:=(anisotropicMeasureTailPotential_hessian_limit D μ ⟨0,by norm_num⟩).1
  have he:anisotropicMeasureTailPotential D μ ⟨0,by norm_num⟩=anisotropicMeasurePotential D μ:=
    funext fun P=>anisotropicMeasureTailPotential_zero D μ P
  rw [he] at hu
  apply LipschitzWith.of_dist_le_mul
  intro P Q
  apply le_of_tendsto ((hu.tendsto_at P).dist (hu.tendsto_at Q))
  apply Eventually.of_forall
  intro j
  have hL:LipschitzWith (8*‖anisotropicEnergyMap D‖₊^3)
      (fderiv ℝ (fderiv ℝ (anisotropicDyadicTailPotential D μ ⟨0,by norm_num⟩ j))) := by
    unfold anisotropicDyadicTailPotential
    rw [anisotropicTailRecursion_eq_clamped D _ _ (by norm_num) le_rfl]
    exact anisotropicFinitePotential_secondDifferential_lipschitz D _ _
  exact hL.dist_le_mul P Q

theorem norm_anisotropicMeasurePotential_variance_secondDifferential_sub_le
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (b c : ℝ) (hb : 0<b) (hc : 0<c) (P : AnisotropicParameter n) :
    ‖fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ)) P-
      fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i c) μ)) P‖≤
      2*(2*((1/2:ℝ)+‖anisotropicEnergyMap D‖^2)+8*‖anisotropicEnergyMap D‖^3)*
        Real.sqrt (Real.sqrt |b-c|) := by
  let F:=fun v=>fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i v) μ)
  have hd (v:ℝ):Differentiable ℝ (F v):=
    ((contDiff_two_anisotropicMeasurePotential _ μ).fderiv_right (m:=1) (by norm_num)).differentiable_one
  have hL (v:ℝ):LipschitzWith (8*‖anisotropicEnergyMap D‖₊^3) (fderiv ℝ (F v)):=by
    simpa only [F,anisotropicReplaceVariance_energyMap] using
      anisotropicMeasurePotential_secondDifferential_lipschitz (anisotropicReplaceVariance D i v) μ
  simpa only [F,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,coe_nnnorm] using
    norm_fderiv_sub_le_sqrt_Banach (F b) (F c) (hd b) (hd c)
      (8*‖anisotropicEnergyMap D‖₊^3) (hL b) (hL c)
      (2*((1/2:ℝ)+‖anisotropicEnergyMap D‖^2)) (Real.sqrt |b-c|)
      (by positivity) (Real.sqrt_nonneg _) (fun Q=>
        norm_anisotropicMeasurePotential_variance_fderiv_sub_le D μ i b c hb hc Q) P

theorem continuousAt_anisotropicMeasurePotential_variance_spatialSecondDifferential
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (b : ℝ) (hb : 0<b) (P : AnisotropicParameter n) :
    ContinuousAt (fun z : ℝ×AnisotropicParameter n=>
      fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ)) z.2) (b,P) := by
  let L:ℝ:=8*‖anisotropicEnergyMap D‖^3
  let A:ℝ:=2*(2*((1/2:ℝ)+‖anisotropicEnergyMap D‖^2)+L)
  have he:∀ᶠz:ℝ×AnisotropicParameter n in 𝓝 (b,P),
      ‖fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ)) z.2-
        fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ)) P‖≤
        A*Real.sqrt (Real.sqrt |z.1-b|)+L*‖z.2-P‖ := by
    have hp:∀ᶠz:ℝ×AnisotropicParameter n in 𝓝 (b,P),0<z.1:=
      (continuous_fst:Continuous (fun z:ℝ×AnisotropicParameter n=>z.1)).continuousAt.eventually (Ioi_mem_nhds hb)
    filter_upwards [hp] with z hz
    have hv:=norm_anisotropicMeasurePotential_variance_secondDifferential_sub_le D μ i z.1 b hz hb z.2
    have hL:=anisotropicMeasurePotential_secondDifferential_lipschitz (anisotropicReplaceVariance D i b) μ
    rw [anisotropicReplaceVariance_energyMap] at hL
    apply (norm_sub_le_norm_sub_add_norm_sub _
      (fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ)) z.2) _).trans
    exact (add_le_add hv (by simpa only [L,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,coe_nnnorm] using hL.norm_sub_le z.2 P))
  have hu:Tendsto (fun z:ℝ×AnisotropicParameter n=>
      A*Real.sqrt (Real.sqrt |z.1-b|)+L*‖z.2-P‖) (𝓝 (b,P)) (𝓝 0):=by
    have hc:Continuous (fun z:ℝ×AnisotropicParameter n=>
      A*Real.sqrt (Real.sqrt |z.1-b|)+L*‖z.2-P‖):=by fun_prop
    simpa only [sub_self,abs_zero,Real.sqrt_zero,norm_zero,mul_zero,add_zero] using hc.tendsto (b,P)
  apply tendsto_sub_nhds_zero_iff.mp
  exact squeeze_zero_norm' (f:=fun z:ℝ×AnisotropicParameter n=>
    fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ)) z.2-
    fderiv ℝ (fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ)) P) he hu

end QuantitativeFollowup
