module
public import QuantitativeFollowup.FollowupCavityMixtureHeatZero

@[expose] public section

/-! Simultaneous row heat with a genuinely moving positive last-field
parameter. Only joint value/Hessian continuity and actual local exponential
bounds are needed; no derivative in that last-field parameter is assumed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon OverlapPaper
open scoped Topology ContDiff
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

structure CavityMovingRowHeatData (F : ℝ×QuantitativePaper.Field n→ℝ) (l r : ℝ) where
  smooth : ∀b∈Ioo l r,ContDiff ℝ 2 (fun y=>F (b,y))
  continuous : ContinuousOn F ((Ioo l r)×ˢ(univ : Set (QuantitativePaper.Field n)))
  hessian_continuous : ContinuousOn (fun z : ℝ×QuantitativePaper.Field n=>
    fderiv ℝ (fderiv ℝ (fun y=>F (z.1,y))) z.2)
    ((Ioo l r)×ˢ(univ : Set (QuantitativePaper.Field n)))
  bound : ℝ
  rate : ℝ
  bound_nonneg : 0≤bound
  rate_nonneg : 0≤rate
  value : ∀b∈Ioo l r,∀y,‖F (b,y)‖≤bound*Real.exp (rate*‖y‖)
  first : ∀b∈Ioo l r,∀y,‖fderiv ℝ (fun x=>F (b,x)) y‖≤bound*Real.exp (rate*‖y‖)
  second : ∀b∈Ioo l r,∀y,‖fderiv ℝ (fderiv ℝ (fun x=>F (b,x))) y‖≤bound*Real.exp (rate*‖y‖)

def cavityMovingRowHeatData_slice (F : ℝ×QuantitativePaper.Field n→ℝ)
    (l r : ℝ) (hF : CavityMovingRowHeatData F l r) (b : ℝ) (hb : b∈Ioo l r) :
    CavityRowHeatData (fun y=>F (b,y)) :=
  ⟨hF.smooth b hb,hF.bound,hF.rate,hF.bound_nonneg,hF.rate_nonneg,
    hF.value b hb,hF.first b hb,hF.second b hb⟩

theorem hasDerivWithinAt_cavityRowHeat_moving_increment_zero
    (F : ℝ×QuantitativePaper.Field n→ℝ) (l r d alpha : ℝ)
    (hF : CavityMovingRowHeatData F l r) (hd : d∈Ioo l r) :
    HasDerivWithinAt (fun v=>cavityRowHeat (fun y=>F (d-alpha*v,y)) v-
      cavityRowHeat (fun y=>F (d-alpha*v,y)) 0)
      ((1/2:ℝ)*cavityRowHessianTrace (fun y=>F (d,y))) (Ici (0:ℝ)) 0 := by
  let P:=fun _ : Fin n=>true
  have hH (i : Fin n) (_ : P i=true) : ContinuousOn (fun z : ℝ×QuantitativePaper.Field n=>
      fderiv ℝ (fderiv ℝ (fun y=>F (z.1,y))) z.2
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((Ioo l r)×ˢ(univ : Set (QuantitativePaper.Field n))) :=
    (hF.hessian_continuous.clm_apply continuousOn_const).clm_apply continuousOn_const
  have ht:=hasDerivWithinAt_gaussianSelected_moving_heat_zero P F l r d alpha
    hF.bound hF.rate hd hF.bound_nonneg hF.rate_nonneg hF.smooth hH hF.value hF.first hF.second
  have hcont : ContinuousAt (fun v : ℝ=>d-alpha*v) 0 := by fun_prop
  have hnb : ∀ᶠ y : ℝ in 𝓝 (d-alpha*0),y∈Ioo l r := by
    rw [mul_zero,sub_zero]
    exact Ioo_mem_nhds hd.1 hd.2
  have hb : ∀ᶠ v : ℝ in 𝓝[Ici (0:ℝ)] 0,d-alpha*v∈Ioo l r :=
    (hcont.eventually hnb).filter_mono nhdsWithin_le_nhds
  have he : (fun v=>cavityRowHeat (fun y=>F (d-alpha*v,y)) v-
      cavityRowHeat (fun y=>F (d-alpha*v,y)) 0)=ᶠ[𝓝[Ici (0:ℝ)] 0]
      (fun v=>∫z : QuantitativePaper.Field n,
        F (d-alpha*v,gaussianSelectedScale P v z)-F (d-alpha*v,gaussianSelectedScale P 0 z)
          ∂stdGaussian (QuantitativePaper.Field n)) := by
    filter_upwards [hb] with v hv
    simp only [P,cavityGaussianSelectedScale_all]
    rw [integral_sub
      (integrable_cavityRowHeat _ (cavityMovingRowHeatData_slice F l r hF _ hv) v)
      (integrable_cavityRowHeat _ (cavityMovingRowHeatData_slice F l r hF _ hv) 0)]
    rfl
  have he0 : cavityRowHeat (fun y=>F (d-alpha*0,y)) 0-
      cavityRowHeat (fun y=>F (d-alpha*0,y)) 0=
      ∫z : QuantitativePaper.Field n,
        F (d-alpha*0,gaussianSelectedScale P 0 z)-F (d-alpha*0,gaussianSelectedScale P 0 z)
          ∂stdGaussian (QuantitativePaper.Field n) := by simp
  convert ht.congr_of_eventuallyEq he he0 using 1
  simp only [P,cavityGaussianSelectedScale_all,Real.sqrt_zero,zero_smul,
    gaussianSelectedSpatialTrace,ite_true,integral_const,probReal_univ,one_smul,cavityRowHessianTrace]

theorem continuousAt_cavityRowHeat_joint_zero
    (F : ℝ×QuantitativePaper.Field n→ℝ) (l r d : ℝ)
    (hF : CavityMovingRowHeatData F l r) (hd : d∈Ioo l r) :
    ContinuousAt (fun z : ℝ×ℝ=>cavityRowHeat (fun y=>F (z.1,y)) z.2) (d,0) := by
  have hb : ∀ᶠ z : ℝ×ℝ in 𝓝 (d,0),z.1∈Ioo l r :=
    continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds hd)
  have hv : ∀ᶠ z : ℝ×ℝ in 𝓝 (d,0),z.2<1 :=
    continuous_snd.continuousAt.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  apply continuousAt_of_dominated (bound:=fun w : QuantitativePaper.Field n=>
    hF.bound*Real.exp (hF.rate*‖w‖))
  · filter_upwards [hb] with z hz
    exact ((hF.smooth z.1 hz).continuous.comp
      ((continuous_const : Continuous (fun _ : QuantitativePaper.Field n=>Real.sqrt z.2)).smul continuous_id)).aestronglyMeasurable
  · filter_upwards [hb,hv] with z hz hzv
    exact .of_forall fun w=>by
      apply (hF.value z.1 hz (Real.sqrt z.2 • w)).trans
      have hs : Real.sqrt z.2≤1 := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hzv.le
      have hn : ‖Real.sqrt z.2 • w‖≤‖w‖ := by
        rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact (mul_le_mul_of_nonneg_right hs (norm_nonneg _)).trans_eq (one_mul _)
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hF.rate_nonneg)) hF.bound_nonneg
  · exact (integrable_exp_mul_norm_gaussian (stdGaussian (QuantitativePaper.Field n)) hF.rate).const_mul hF.bound
  · exact .of_forall fun w=>by
      have hc : ContinuousAt (fun z : ℝ×ℝ=>(z.1,Real.sqrt z.2 • w)) (d,0) := by fun_prop
      have hpoint : (d,(Real.sqrt (0:ℝ)) • w)∈((Ioo l r)×ˢ(univ : Set (QuantitativePaper.Field n))) :=
        ⟨hd,mem_univ _⟩
      have hh : ContinuousAt F (d,Real.sqrt (0:ℝ) • w) :=
        hF.continuous.continuousAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpoint)
      change ContinuousAt (fun z : ℝ×ℝ=>F (z.1,Real.sqrt z.2 • w)) (d,0)
      exact ContinuousAt.comp (f:=fun z : ℝ×ℝ=>(z.1,Real.sqrt z.2 • w)) (g:=F) hh hc

end QuantitativeFollowup
