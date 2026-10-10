module
public import QuantitativeFollowup.FollowupCavityNormalizerVarianceJets
public import QuantitativeFollowup.FollowupCavityNormalizerMovingInput
public import FourPapersCommon.GaussianSelectedCoordinateScale

@[expose] public section

/-! The simultaneous incident-row and auxiliary-variance response of the
actual arbitrary-profile root potential on its genuine fixed Gaussian
coordinates. No joint covariance smoothness is supplied as a premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def anisotropicMovingRootPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : AnisotropicCouplingIndex n→Bool)
    (i : Fin n) (d alpha : ℝ) (u : ℝ) (g : AnisotropicDisorder n) : ℝ :=
  anisotropicMeasurePotential (anisotropicReplaceVariance D i (d-alpha*u)) μ
    (anisotropicDisorderInjection n (gaussianSelectedScale p u g))

theorem hasDerivAt_anisotropicMovingRootPotential
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (p : AnisotropicCouplingIndex n→Bool) (i : Fin n) (d alpha u : ℝ)
    (hu : 0<u) (hb : 0<d-alpha*u) (g : AnisotropicDisorder n) :
    HasDerivAt (fun v=>anisotropicMovingRootPotential D μ p i d alpha v g)
      (-alpha*anisotropicRootVarianceResponse (anisotropicReplaceVariance D i (d-alpha*u)) μ i
        (gaussianSelectedScale p u g)+
        fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i (d-alpha*u)) μ)
          (anisotropicDisorderInjection n (gaussianSelectedScale p u g))
          (anisotropicDisorderInjection n (gaussianSelectedScaleDerivative p u g))) u := by
  classical
  letI : IsBoundedSMul ℝ (AnisotropicParameter n) :=
    .of_norm_smul_le norm_smul_le
  letI : ContinuousSMul ℝ (AnisotropicParameter n) :=
    IsBoundedSMul.continuousSMul
  let F:=fun v=>anisotropicMeasurePotential (anisotropicReplaceVariance D i (d-alpha*v)) μ
  let G:=fun v=>anisotropicDisorderInjection n (gaussianSelectedScale p v g)
  have hF (v : ℝ) : Differentiable ℝ (F v):=
    (contDiff_one_anisotropicMeasurePotential _ μ).differentiable (by norm_num)
  have hm : ContinuousAt (fun z : ℝ×AnisotropicParameter n=>(d-alpha*z.1,z.2)) (u,G u) := by
    fun_prop
  have hc : ContinuousAt (fun z : ℝ×AnisotropicParameter n=>fderiv ℝ (F z.1) z.2) (u,G u) := by
    exact ContinuousAt.comp
      (f:=fun z : ℝ×AnisotropicParameter n=>(d-alpha*z.1,z.2))
      (g:=fun z : ℝ×AnisotropicParameter n=>
        fderiv ℝ (anisotropicMeasurePotential (anisotropicReplaceVariance D i z.1) μ) z.2)
      (continuousAt_anisotropicMeasurePotential_variance_spatialDifferential D μ i
        (d-alpha*u) hb (G u)) hm
  have hg : HasDerivAt G (anisotropicDisorderInjection n (gaussianSelectedScaleDerivative p u g)) u :=
    (anisotropicDisorderInjection n).hasFDerivAt.comp_hasDerivAt u
      (hasDerivAt_gaussianSelectedScale p u hu g)
  have hparam:=hasDerivAt_anisotropicMeasureTailPotential_variance_restart D μ i
    (gaussianSelectedScale p u g) ⟨0,by norm_num⟩ 0 (d-alpha*u) hb
  simp only [anisotropicMeasureTailPotential_zero,map_zero,add_zero] at hparam
  have ha : HasDerivAt (fun v : ℝ=>d-alpha*v) (-alpha) u := by
    convert (hasDerivAt_const u d).sub ((hasDerivAt_id u).const_mul alpha) using 1
    · funext v; rfl
    · simp
  have hd : HasDerivAt (fun v=>F v (G u))
      (-alpha*anisotropicRootVarianceResponse (anisotropicReplaceVariance D i (d-alpha*u)) μ i
        (gaussianSelectedScale p u g)) u := by
    simpa only [Function.comp_def,mul_comm,anisotropicRootVarianceResponse,F,G] using hparam.comp u ha
  exact hasDerivAt_moving_input_of_spatial_differential F G u _ _ hF hc hd hg

end QuantitativeFollowup
