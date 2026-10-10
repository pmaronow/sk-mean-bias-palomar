module
public import QuantitativeFollowup.AnisotropicVarianceJetContinuity
public import QuantitativeFollowup.AnisotropicWhitening
public import QuantitativeFollowup.AnisotropicWhitenedIto

@[expose] public section

/-! Actual diagonal covariance maps vary continuously with a positive
coordinate variance. The identities retain all other coordinates. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace QuantitativeFollowup
open QuantitativePaper
set_option maxHeartbeats 1000000
variable {n : ℕ}

def anisotropicCoordinateProjection (i : Fin n) : Field n→L[ℝ]Field n :=
  (EuclideanSpace.proj i).smulRight (EuclideanSpace.single i 1)

@[simp] theorem anisotropicCoordinateProjection_apply (i : Fin n) (z : Field n) (l : Fin n) :
    anisotropicCoordinateProjection i z l=if l=i then z i else 0 := by
  classical
  by_cases hli : l=i
  · subst l
    simp [anisotropicCoordinateProjection]
  · simp [anisotropicCoordinateProjection,EuclideanSpace.single_apply,Ne.symm hli,hli]

theorem anisotropicReplaceVariance_noiseMap (D : AnisotropicSpinModel n) (i : Fin n)
    (b : ℝ) (hb : 0<b) :
    anisotropicNoiseMap (anisotropicReplaceVariance D i b)=
      anisotropicNoiseMap D+(Real.sqrt b-Real.sqrt (D.variance i)) • anisotropicCoordinateProjection i := by
  classical
  ext z l
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,PiLp.add_apply,
    PiLp.smul_apply,smul_eq_mul,anisotropicNoiseMap_apply,
    anisotropicReplaceVariance_variance D i l b hb,anisotropicCoordinateProjection_apply]
  split_ifs with hli
  · subst l;ring
  · ring

theorem anisotropicReplaceVariance_inverseNoiseMap (D : AnisotropicSpinModel n) (i : Fin n)
    (b : ℝ) (hb : 0<b) :
    anisotropicInverseNoiseMap (anisotropicReplaceVariance D i b)=
      anisotropicInverseNoiseMap D+((Real.sqrt b)⁻¹-(Real.sqrt (D.variance i))⁻¹) •
        anisotropicCoordinateProjection i := by
  classical
  ext z l
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,PiLp.add_apply,
    PiLp.smul_apply,smul_eq_mul,anisotropicInverseNoiseMap_apply,
    anisotropicReplaceVariance_variance D i l b hb,anisotropicCoordinateProjection_apply]
  split_ifs with hli
  · subst l;ring
  · ring

theorem continuousAt_anisotropicReplaceVariance_noiseMap (D : AnisotropicSpinModel n)
    (i : Fin n) (b : ℝ) (hb : 0<b) :
    ContinuousAt (fun c=>anisotropicNoiseMap (anisotropicReplaceVariance D i c)) b := by
  have hc : Continuous (fun c=>anisotropicNoiseMap D+
      (Real.sqrt c-Real.sqrt (D.variance i)) • anisotropicCoordinateProjection i) := by fun_prop
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hb] with c hc
  exact anisotropicReplaceVariance_noiseMap D i c hc

theorem continuousAt_anisotropicReplaceVariance_inverseNoiseMap (D : AnisotropicSpinModel n)
    (i : Fin n) (b : ℝ) (hb : 0<b) :
    ContinuousAt (fun c=>anisotropicInverseNoiseMap (anisotropicReplaceVariance D i c)) b := by
  have hscalar : ContinuousAt (fun c=>(Real.sqrt c)⁻¹-(Real.sqrt (D.variance i))⁻¹) b :=
    ((Real.continuous_sqrt.continuousAt).inv₀ (Real.sqrt_pos.mpr hb).ne').sub continuousAt_const
  have hc : ContinuousAt (fun c=>anisotropicInverseNoiseMap D+
      ((Real.sqrt c)⁻¹-(Real.sqrt (D.variance i))⁻¹) • anisotropicCoordinateProjection i) b :=
    continuousAt_const.add (hscalar.smul continuousAt_const)
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hb] with c hc
  exact anisotropicReplaceVariance_inverseNoiseMap D i c hc

theorem continuousAt_anisotropicReplaceVariance_unitInput (D : AnisotropicSpinModel n)
    (i : Fin n) (b : ℝ) (hb : 0<b) :
    ContinuousAt (fun c=>anisotropicUnitInput (anisotropicReplaceVariance D i c)) b := by
  exact continuousAt_const.clm_comp (continuousAt_anisotropicReplaceVariance_noiseMap D i b hb)

theorem continuousAt_anisotropicReplaceVariance_whitenedDriftLip (D : AnisotropicSpinModel n)
    (i : Fin n) (b : ℝ) (hb : 0<b) :
    ContinuousAt (fun c=>(anisotropicWhitenedDriftLip (anisotropicReplaceVariance D i c):ℝ)) b := by
  simp only [anisotropicWhitenedDriftLip,anisotropicReplaceVariance_energyMap,
    NNReal.coe_mul,coe_nnnorm,NNReal.coe_pow]
  have hn:=(continuousAt_anisotropicReplaceVariance_noiseMap D i b hb).norm
  exact (hn.mul continuousAt_const).mul (continuousAt_const.mul hn)

end QuantitativeFollowup
