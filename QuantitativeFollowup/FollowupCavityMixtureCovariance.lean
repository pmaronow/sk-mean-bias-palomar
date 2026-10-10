module
public import QuantitativeFollowup.FollowupCavityMixtureHeatZero

@[expose] public section

/-! The quotient and covariance calculation for the genuine Z-weighted
Gaussian mixture. Zero first row jets are used only after heat differentiation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityRowWeightedAverage (Z f : QuantitativePaper.Field n→ℝ) (v : ℝ) : ℝ :=
  cavityRowHeat (fun x=>Z x*f x) v/cavityRowHeat Z v

theorem cavityRow_second_product (f g : QuantitativePaper.Field n→ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x w : QuantitativePaper.Field n) :
    fderiv ℝ (fderiv ℝ (fun y=>f y*g y)) x w w=
      f x*fderiv ℝ (fderiv ℝ g) x w w+
      g x*fderiv ℝ (fderiv ℝ f) x w w+
      2*(fderiv ℝ f x w)*(fderiv ℝ g x w) := by
  let Df:=fun y=>fderiv ℝ f y w
  let Dg:=fun y=>fderiv ℝ g y w
  have hDf : ContDiff ℝ 1 Df := (hf.fderiv_right (m:=1) (by norm_num)).clm_apply contDiff_const
  have hDg : ContDiff ℝ 1 Dg := (hg.fderiv_right (m:=1) (by norm_num)).clm_apply contDiff_const
  have he : (fun y=>fderiv ℝ (fun z=>f z*g z) y w)=fun y=>f y*Dg y+g y*Df y := by
    funext y
    change (fderiv ℝ (f*g) y) w = _
    rw [((hf.differentiable (by norm_num) y).hasFDerivAt.mul
      (hg.differentiable (by norm_num) y).hasFDerivAt).fderiv]
    simp [Df,Dg,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  have hdf:=((hf.fderiv_right (m:=1) (by norm_num)).differentiable_one x).hasFDerivAt.clm_apply
    (hasFDerivAt_const w x)
  have hdg:=((hg.fderiv_right (m:=1) (by norm_num)).differentiable_one x).hasFDerivAt.clm_apply
    (hasFDerivAt_const w x)
  have hleft:=(((hf.mul hg).fderiv_right (m:=1) (by norm_num)).differentiable_one x).hasFDerivAt.clm_apply
    (hasFDerivAt_const w x)
  have hright:=((hf.differentiable (by norm_num) x).hasFDerivAt.mul hdg).add
    ((hg.differentiable (by norm_num) x).hasFDerivAt.mul hdf)
  have hl:=congrArg (fun A : QuantitativePaper.Field n→L[ℝ]ℝ=>A w) hleft.fderiv
  have hr:=congrArg (fun A : QuantitativePaper.Field n→L[ℝ]ℝ=>A w) hright.fderiv
  rw [he] at hl
  change fderiv ℝ (fun y=>f y*Dg y+g y*Df y) x w = _ at hr
  rw [hr] at hl
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    map_zero,mul_zero,add_zero] at hl
  nlinarith [hl]

theorem cavityRowHessianTrace_product_of_first_zero (Z f : QuantitativePaper.Field n→ℝ)
    (hZ : ContDiff ℝ 2 Z) (hf : ContDiff ℝ 2 f) (hzero : fderiv ℝ Z 0=0) :
    cavityRowHessianTrace (fun x=>Z x*f x)=
      Z 0*cavityRowHessianTrace f+f 0*cavityRowHessianTrace Z := by
  unfold cavityRowHessianTrace
  simp_rw [cavityRow_second_product Z f hZ hf 0,hzero,ContinuousLinearMap.zero_apply,
    mul_zero,zero_mul,add_zero]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]

theorem hasDerivWithinAt_cavityRowWeightedAverage_zero (Z f : QuantitativePaper.Field n→ℝ)
    (hZ : CavityRowHeatData Z) (hf : ContDiff ℝ 2 f)
    (hZf : CavityRowHeatData (fun x=>Z x*f x)) (hpos : 0<Z 0)
    (hzero : fderiv ℝ Z 0=0) :
    HasDerivWithinAt (cavityRowWeightedAverage Z f)
      ((1/2:ℝ)*cavityRowHessianTrace f) (Ici (0:ℝ)) 0 := by
  have hd:=(hasDerivWithinAt_cavityRowHeat_zero _ hZf).div
    (hasDerivWithinAt_cavityRowHeat_zero Z hZ) (by simpa using hpos.ne')
  change HasDerivWithinAt (cavityRowWeightedAverage Z f) _ _ _ at hd
  apply hd.congr_deriv
  rw [cavityRowHeat_zero,cavityRowHeat_zero,
    cavityRowHessianTrace_product_of_first_zero Z f hZ.smooth hf hzero]
  field_simp [hpos.ne']
  <;> ring

theorem cavityRowHessianTrace_covariance (f g h : QuantitativePaper.Field n→ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (hzero : fderiv ℝ f 0=0) :
    cavityRowHessianTrace (fun x=>h x-f x*g x)=
      cavityRowHessianTrace h-g 0*cavityRowHessianTrace f-f 0*cavityRowHessianTrace g := by
  have hdf:=hf.mul hg
  have he : fderiv ℝ (fun x=>h x-f x*g x)=fun x=>fderiv ℝ h x-fderiv ℝ (fun y=>f y*g y) x := by
    funext x
    exact fderiv_sub (hh.differentiable (by norm_num) x) (hdf.differentiable (by norm_num) x)
  have hes (x) : fderiv ℝ (fderiv ℝ (fun y=>h y-f y*g y)) x=
      fderiv ℝ (fderiv ℝ h) x-fderiv ℝ (fderiv ℝ (fun y=>f y*g y)) x := by
    rw [he]
    exact fderiv_sub ((hh.fderiv_right (m:=1) (by norm_num)).differentiable_one x)
      ((hdf.fderiv_right (m:=1) (by norm_num)).differentiable_one x)
  unfold cavityRowHessianTrace
  simp_rw [hes,ContinuousLinearMap.sub_apply]
  rw [Finset.sum_sub_distrib]
  change cavityRowHessianTrace h-cavityRowHessianTrace (fun x=>f x*g x)=_
  rw [cavityRowHessianTrace_product_of_first_zero f g hf hg hzero]
  unfold cavityRowHessianTrace
  ring

theorem hasDerivWithinAt_cavityRowWeightedCovariance_zero
    (Z f g h : QuantitativePaper.Field n→ℝ)
    (hZ : CavityRowHeatData Z) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) (hZf : CavityRowHeatData (fun x=>Z x*f x))
    (hZg : CavityRowHeatData (fun x=>Z x*g x))
    (hZh : CavityRowHeatData (fun x=>Z x*h x))
    (hpos : 0<Z 0) (hZzero : fderiv ℝ Z 0=0) (hfzero : fderiv ℝ f 0=0) :
    HasDerivWithinAt (fun v=>cavityRowWeightedAverage Z h v-
      cavityRowWeightedAverage Z f v*cavityRowWeightedAverage Z g v)
      ((1/2:ℝ)*cavityRowHessianTrace (fun x=>h x-f x*g x)) (Ici (0:ℝ)) 0 := by
  have hd:=(hasDerivWithinAt_cavityRowWeightedAverage_zero Z h hZ hh hZh hpos hZzero).sub
    ((hasDerivWithinAt_cavityRowWeightedAverage_zero Z f hZ hf hZf hpos hZzero).mul
      (hasDerivWithinAt_cavityRowWeightedAverage_zero Z g hZ hg hZg hpos hZzero))
  apply hd.congr_deriv
  have hv (a : QuantitativePaper.Field n→ℝ) : cavityRowWeightedAverage Z a 0=a 0 := by
    simp only [cavityRowWeightedAverage,cavityRowHeat_zero]
    exact mul_div_cancel_left₀ _ hpos.ne'
  rw [hv,hv,cavityRowHessianTrace_covariance f g h hf hg hh hfzero]
  ring

end QuantitativeFollowup
