module
public import FourPapersCommon.GaussianSelectedMovingZeroHeat
public import QuantitativePaper.FiniteSpin

@[expose] public section

/-! Actual simultaneous Gaussian row heat at zero variance. The one-sided
derivative is derived from spatial C2 and exponential jet bounds. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon OverlapPaper
open scoped Topology BigOperators ContDiff
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityRowHeat (F : QuantitativePaper.Field n→ℝ) (v : ℝ) : ℝ :=
  ∫z,F (Real.sqrt v • z) ∂stdGaussian (QuantitativePaper.Field n)

def cavityRowHessianTrace (F : QuantitativePaper.Field n→ℝ) : ℝ :=
  ∑i : Fin n,fderiv ℝ (fderiv ℝ F) 0
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i)

structure CavityRowHeatData (F : QuantitativePaper.Field n→ℝ) where
  smooth : ContDiff ℝ 2 F
  bound : ℝ
  rate : ℝ
  bound_nonneg : 0≤bound
  rate_nonneg : 0≤rate
  value : ∀y,‖F y‖≤bound*Real.exp (rate*‖y‖)
  first : ∀y,‖fderiv ℝ F y‖≤bound*Real.exp (rate*‖y‖)
  second : ∀y,‖fderiv ℝ (fderiv ℝ F) y‖≤bound*Real.exp (rate*‖y‖)

theorem cavityGaussianSelectedScale_all (v : ℝ) (z : QuantitativePaper.Field n) :
    gaussianSelectedScale (fun _ : Fin n=>true) v z=Real.sqrt v • z := by
  rw [gaussianSelectedScale_apply]
  ext i
  simp only [Bool.true_eq,ite_true,WithLp.ofLp_sum,Finset.sum_apply,
    PiLp.smul_apply,smul_eq_mul,EuclideanSpace.basisFun_apply,PiLp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

@[simp] theorem cavityRowHeat_zero (F : QuantitativePaper.Field n→ℝ) :
    cavityRowHeat F 0=F 0 := by simp [cavityRowHeat]

theorem integrable_cavityRowHeat (F : QuantitativePaper.Field n→ℝ)
    (hF : CavityRowHeatData F) (v : ℝ) :
    Integrable (fun z=>F (Real.sqrt v • z)) (stdGaussian (QuantitativePaper.Field n)) := by
  apply integrable_gaussian_exponential_bound _ _
    (hF.smooth.continuous.measurable.comp
      ((Real.sqrt v • ContinuousLinearMap.id ℝ (QuantitativePaper.Field n)).continuous.measurable)) hF.bound
    (hF.rate*Real.sqrt v) hF.bound_nonneg
  intro z
  simpa only [Function.comp_def,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_assoc] using
    hF.value (Real.sqrt v • z)

theorem hasDerivWithinAt_cavityRowHeat_zero (F : QuantitativePaper.Field n→ℝ)
    (hF : CavityRowHeatData F) :
    HasDerivWithinAt (cavityRowHeat F) ((1/2:ℝ)*cavityRowHessianTrace F) (Ici (0:ℝ)) 0 := by
  let P:=fun _ : Fin n=>true
  let G:=fun z : ℝ×QuantitativePaper.Field n=>F z.2
  have hH (i : Fin n) (_ : P i=true) : ContinuousOn (fun z : ℝ×QuantitativePaper.Field n=>
      fderiv ℝ (fderiv ℝ (fun y=>G (z.1,y))) z.2
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((Ioo (-1:ℝ) 1)×ˢ(univ : Set (QuantitativePaper.Field n))) := by
    exact (((hF.smooth.fderiv_right (m:=1) (by norm_num)).continuous_fderiv (by norm_num)).comp
      continuous_snd |>.clm_apply continuous_const |>.clm_apply continuous_const).continuousOn
  have hd:=hasDerivWithinAt_gaussianSelected_moving_heat_zero P G (-1) 1 0 0
    hF.bound hF.rate (by constructor <;> norm_num) hF.bound_nonneg hF.rate_nonneg
    (fun _ _=>hF.smooth) hH (fun _ _=>hF.value) (fun _ _=>hF.first) (fun _ _=>hF.second)
  have hd':=hd.add_const (F 0)
  have he (v : ℝ) :
      (∫z : QuantitativePaper.Field n,
        (G (0-0*v,gaussianSelectedScale P v z)-G (0-0*v,gaussianSelectedScale P 0 z))
          ∂stdGaussian (QuantitativePaper.Field n))+F 0=cavityRowHeat F v := by
    simp only [G,P,cavityGaussianSelectedScale_all,Real.sqrt_zero,zero_smul,zero_mul,sub_zero]
    rw [integral_sub (integrable_cavityRowHeat F hF v) (integrable_const (F 0))]
    simp [cavityRowHeat]
  convert hd'.congr_of_mem (fun v _=>(he v).symm) (show (0:ℝ)∈Ici (0:ℝ) from by simp) using 1
  simp only [P,G,cavityGaussianSelectedScale_all,Real.sqrt_zero,zero_smul,
    gaussianSelectedSpatialTrace,Bool.true_eq,ite_true,integral_const,probReal_univ,one_smul,
    cavityRowHessianTrace]

theorem hasDerivWithinAt_cavityRowHeat_scaled_zero (F : QuantitativePaper.Field n→ℝ)
    (hF : CavityRowHeatData F) (scale : ℝ) (hscale : 0 ≤ scale) :
    HasDerivWithinAt (fun u=>cavityRowHeat F (scale*u))
      (scale/2*cavityRowHessianTrace F) (Ici (0:ℝ)) 0 := by
  have hd:=hasDerivWithinAt_cavityRowHeat_zero F hF
  have hi : HasDerivWithinAt (fun u : ℝ=>scale*u) scale (Ici (0:ℝ)) 0 := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id (0:ℝ)).const_mul scale).hasDerivWithinAt
  have hc:=hd.comp_of_eq 0 hi (fun u hu=>mul_nonneg hscale hu) (by simp)
  simpa only [Function.comp_def,mul_zero,mul_assoc,div_eq_mul_inv,mul_comm,mul_left_comm,one_mul] using hc

end QuantitativeFollowup
