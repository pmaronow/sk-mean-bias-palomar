module
public import QuantitativeFollowup.FollowupCavityMixtureMovingHeat
public import QuantitativeFollowup.FollowupCavityMixtureMovingIncrement
public import QuantitativeFollowup.FollowupCavityMixtureCovariance

@[expose] public section

/-! The correctly weighted moving-parameter covariance. Zero-row product
structure cancels the moving baseline exactly. No derivative with respect
to the last variance is required or supplied. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityMovingRowWeightedCovariance (Z f g h : ℝ×Field n→ℝ) (d gamma v : ℝ) : ℝ :=
  cavityRowWeightedAverage (fun x=>Z (d-gamma*v,x)) (fun x=>h (d-gamma*v,x)) v-
    cavityRowWeightedAverage (fun x=>Z (d-gamma*v,x)) (fun x=>f (d-gamma*v,x)) v*
    cavityRowWeightedAverage (fun x=>Z (d-gamma*v,x)) (fun x=>g (d-gamma*v,x)) v

theorem hasDerivWithinAt_cavityMovingRowWeightedCovariance_zero
    (Z f g h : ℝ×Field n→ℝ) (l r d gamma : ℝ)
    (hZ : CavityMovingRowHeatData Z l r)
    (hZf : CavityMovingRowHeatData (fun z=>Z z*f z) l r)
    (hZg : CavityMovingRowHeatData (fun z=>Z z*g z) l r)
    (hZh : CavityMovingRowHeatData (fun z=>Z z*h z) l r)
    (hd : d∈Ioo l r) (hpos : 0<Z (d,0))
    (hf : ContDiff ℝ 2 (fun x=>f (d,x))) (hg : ContDiff ℝ 2 (fun x=>g (d,x)))
    (hh : ContDiff ℝ 2 (fun x=>h (d,x)))
    (hZzero : fderiv ℝ (fun x=>Z (d,x)) 0=0)
    (hfzero : fderiv ℝ (fun x=>f (d,x)) 0=0)
    (hbase : ∀b∈Ioo l r,h (b,0)=f (b,0)*g (b,0)) :
    HasDerivWithinAt (cavityMovingRowWeightedCovariance Z f g h d gamma)
      ((1/2:ℝ)*cavityRowHessianTrace (fun x=>h (d,x)-f (d,x)*g (d,x))) (Ici (0:ℝ)) 0 := by
  let ZZ:=fun v=>cavityRowHeat (fun x=>Z (d-gamma*v,x)) v
  let FF:=fun v=>cavityRowHeat (fun x=>Z (d-gamma*v,x)*f (d-gamma*v,x)) v
  let GG:=fun v=>cavityRowHeat (fun x=>Z (d-gamma*v,x)*g (d-gamma*v,x)) v
  let HH:=fun v=>cavityRowHeat (fun x=>Z (d-gamma*v,x)*h (d-gamma*v,x)) v
  let Z0:=fun v=>cavityRowHeat (fun x=>Z (d-gamma*v,x)) 0
  let F0:=fun v=>cavityRowHeat (fun x=>Z (d-gamma*v,x)*f (d-gamma*v,x)) 0
  let G0:=fun v=>cavityRowHeat (fun x=>Z (d-gamma*v,x)*g (d-gamma*v,x)) 0
  let H0:=fun v=>cavityRowHeat (fun x=>Z (d-gamma*v,x)*h (d-gamma*v,x)) 0
  have hc (A : ℝ×Field n→ℝ) (hA : CavityMovingRowHeatData A l r) :
      ContinuousAt (fun v : ℝ=>cavityRowHeat (fun x=>A (d-gamma*v,x)) v) 0 := by
    have hm : ContinuousAt (fun v : ℝ=>(d-gamma*v,v)) 0 := by fun_prop
    exact (continuousAt_cavityRowHeat_joint_zero A l r d hA hd).comp_of_eq hm (by simp)
  have hc0 (A : ℝ×Field n→ℝ) (hA : CavityMovingRowHeatData A l r) :
      ContinuousAt (fun v : ℝ=>cavityRowHeat (fun x=>A (d-gamma*v,x)) 0) 0 := by
    have hm : ContinuousAt (fun v : ℝ=>(d-gamma*v,(0:ℝ))) 0 := by fun_prop
    exact (continuousAt_cavityRowHeat_joint_zero A l r d hA hd).comp_of_eq hm (by simp)
  have hb : ∀ᶠ v : ℝ in 𝓝[Ici (0:ℝ)] 0,d-gamma*v∈Ioo l r := by
    have hc : ContinuousAt (fun v : ℝ=>d-gamma*v) 0 := by fun_prop
    have hm : ∀ᶠ b : ℝ in 𝓝 (d-gamma*0),b∈Ioo l r := by
      rw [mul_zero,sub_zero]
      exact Ioo_mem_nhds hd.1 hd.2
    exact (hc.eventually hm).filter_mono nhdsWithin_le_nhds
  have hbase' : ∀ᶠ v : ℝ in 𝓝[Ici (0:ℝ)] 0,H0 v*Z0 v=F0 v*G0 v := by
    filter_upwards [hb] with v hv
    dsimp only [H0,Z0,F0,G0]
    rw [cavityRowHeat_zero,cavityRowHeat_zero,cavityRowHeat_zero,cavityRowHeat_zero,hbase _ hv]
    ring
  have hbase0 : H0 0*Z0 0=F0 0*G0 0 := by
    dsimp only [H0,Z0,F0,G0]
    simp only [mul_zero,sub_zero,cavityRowHeat_zero]
    rw [hbase d hd]
    ring
  have ht:=cavity_moving_covariance_from_heat_increments ZZ FF GG HH Z0 F0 G0 H0
    ((1/2:ℝ)*cavityRowHessianTrace (fun x=>Z (d,x)))
    ((1/2:ℝ)*cavityRowHessianTrace (fun x=>Z (d,x)*f (d,x)))
    ((1/2:ℝ)*cavityRowHessianTrace (fun x=>Z (d,x)*g (d,x)))
    ((1/2:ℝ)*cavityRowHessianTrace (fun x=>Z (d,x)*h (d,x)))
    (hc Z hZ).continuousWithinAt (hc0 _ hZf).continuousWithinAt
    (hc _ hZg).continuousWithinAt (hc0 _ hZh).continuousWithinAt
    (by rfl) (by rfl)
    (by rfl) (by rfl)
    (by dsimp only [ZZ];simpa only [mul_zero,sub_zero,cavityRowHeat_zero] using hpos.ne')
    hbase' hbase0
    (hasDerivWithinAt_cavityRowHeat_moving_increment_zero Z l r d gamma hZ hd)
    (hasDerivWithinAt_cavityRowHeat_moving_increment_zero _ l r d gamma hZf hd)
    (hasDerivWithinAt_cavityRowHeat_moving_increment_zero _ l r d gamma hZg hd)
    (hasDerivWithinAt_cavityRowHeat_moving_increment_zero _ l r d gamma hZh hd)
  change HasDerivWithinAt (cavityMovingRowWeightedCovariance Z f g h d gamma) _ _ _ at ht
  apply ht.congr_deriv
  dsimp only [ZZ,FF,GG,HH,Z0,F0,G0,H0]
  simp only [mul_zero,sub_zero,cavityRowHeat_zero]
  rw [cavityRowHessianTrace_product_of_first_zero _ _ (hZ.smooth d hd) hf hZzero,
    cavityRowHessianTrace_product_of_first_zero _ _ (hZ.smooth d hd) hg hZzero,
    cavityRowHessianTrace_product_of_first_zero _ _ (hZ.smooth d hd) hh hZzero,
    cavityRowHessianTrace_covariance _ _ _ hf hg hh hfzero,hbase d hd]
  field_simp [hpos.ne']
  <;> ring

end QuantitativeFollowup
