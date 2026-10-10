module
public import QuantitativeFollowup.ScalarHessianDynkin
public import FourPapersCommon.ParisiGradientL1

@[expose] public section

/-! A linear CDF-L¹ estimate for the actual Parisi Hessian.  Its comparison
uses the genuine Dynkin formula on one restarted diffusion, then an
exponentially weighted supremum contraction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem norm_parisiSpatialJet_three_le_fourteen (beta : ℝ) (hb : beta≠0)
    (ν : Paper.ParisiMeasure) (r x : ℝ) :
    ‖parisiSpatialJet beta ν 3 r x‖≤14 := by
  have hd := hasDerivAt_parisiSpatialJet_succ beta ν 1 r x
  have he : (fun y=>parisiSpatialJet beta ν (1+1) r y)=
      (fun y=>parisiHessian beta ν (r,y)) := by
    funext y
    exact parisiSpatialJet_two beta ν r y
  rw [he] at hd
  rw [←hd.deriv]
  exact norm_deriv_le_of_lipschitz (lipschitzWith_parisiHessian beta hb ν r)

private theorem unit_product_gap (a b u v : ℝ)
    (ha : ‖a‖≤1) (hv : ‖v‖≤1) :
    ‖a*u-b*v‖≤‖u-v‖+‖a-b‖ := by
  rw [show a*u-b*v=a*(u-v)+(a-b)*v by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  exact add_le_add
    ((mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans_eq (one_mul _))
    ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans_eq (mul_one _))

private theorem unit_square_gap (u v : ℝ) (hu : ‖u‖≤1) (hv : ‖v‖≤1) :
    ‖u^2-v^2‖≤2*‖u-v‖ := by
  rw [show u^2-v^2=(u-v)*(u+v) by ring,norm_mul]
  have hs : ‖u+v‖≤2 := (norm_add_le _ _).trans (by linarith)
  exact (mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem restartedHessianDifferenceSource_norm_le (beta : ℝ) (hb : beta≠0)
    (μ ν : Paper.ParisiMeasure) (a x : ℝ) (ha : 0≤a) (r : ℝ)
    (hr : a+r∈Icc (0 : ℝ) 1) (ω : Paper.BrownianSample) :
    ‖restartedHessianDifferenceSource beta μ ν a x ha r ω‖≤
      beta^2*(2*‖parisiHessian beta μ (a+r,canonicalParisiRestartState beta x μ a ha r.toNNReal ω)-
        parisiHessian beta ν (a+r,canonicalParisiRestartState beta x μ a ha r.toNNReal ω)‖+
        14*FourPapersCommon.parisiGradientL1Constant beta*FourPapersCommon.parisiCDFDistance μ ν+
        15*‖parisiCDF μ (a+r)-parisiCDF ν (a+r)‖) := by
  let y := canonicalParisiRestartState beta x μ a ha r.toNNReal ω
  have hc : ‖parisiCDF μ (a+r)‖≤1 := by
    rw [Real.norm_of_nonneg (parisiCDF_nonneg μ _)]
    exact parisiCDF_le_one μ _
  have hμ := norm_parisiHessian_le_one_all beta μ (a+r,y)
  have hν := norm_parisiHessian_le_one_all beta ν (a+r,y)
  have hνsq : ‖parisiHessian beta ν (a+r,y)^2‖≤1 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hν 2).trans_eq (by norm_num)
  have hH := (unit_product_gap (parisiCDF μ (a+r)) (parisiCDF ν (a+r))
    (parisiHessian beta μ (a+r,y)^2) (parisiHessian beta ν (a+r,y)^2) hc hνsq).trans
      (add_le_add (unit_square_gap _ _ hμ hν) le_rfl)
  have hG := (unit_product_gap (parisiCDF μ (a+r)) (parisiCDF ν (a+r))
    (parisiGradient beta μ (a+r,y)) (parisiGradient beta ν (a+r,y)) hc
    (norm_parisiGradient_le_one beta ν _)).trans
      (add_le_add (FourPapersCommon.parisiGradient_CDF_L1_bound beta hb μ ν (a+r) hr y) le_rfl)
  have hJ := norm_parisiSpatialJet_three_le_fourteen beta hb ν (a+r) y
  have hG0 := (norm_nonneg _).trans hG
  have hJprod := mul_le_mul hG hJ (norm_nonneg _) hG0
  unfold restartedHessianDifferenceSource
  change ‖beta^2*(_+_)‖≤_
  rw [norm_mul,Real.norm_of_nonneg (sq_nonneg beta)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg beta)
  apply ((norm_add_le _ _).trans (add_le_add hH (by simpa only [norm_mul] using hJprod))).trans_eq
  dsimp only [y]
  ring

def weightedHessianGap (beta : ℝ) (μ ν : Paper.ParisiMeasure) (K : ℝ) : ℝ :=
  sSup (Set.range (fun p : Paper.Overlap×ℝ=>Real.exp (-K*(1-(p.1:ℝ)))*
    ‖parisiHessian beta μ ((p.1:ℝ),p.2)-parisiHessian beta ν ((p.1:ℝ),p.2)‖))

theorem weightedHessianGap_bddAbove (beta : ℝ) (μ ν : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤K) :
    BddAbove (Set.range (fun p : Paper.Overlap×ℝ=>Real.exp (-K*(1-(p.1:ℝ)))*
      ‖parisiHessian beta μ ((p.1:ℝ),p.2)-parisiHessian beta ν ((p.1:ℝ),p.2)‖)) := by
  refine ⟨2,?_⟩
  rintro _ ⟨p,rfl⟩
  have he : Real.exp (-K*(1-(p.1:ℝ)))≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [p.1.property.2])
  have hd : ‖parisiHessian beta μ ((p.1:ℝ),p.2)-parisiHessian beta ν ((p.1:ℝ),p.2)‖≤2 :=
    (norm_sub_le _ _).trans (by linarith [norm_parisiHessian_le_one_all beta μ ((p.1:ℝ),p.2),
      norm_parisiHessian_le_one_all beta ν ((p.1:ℝ),p.2)])
  simpa only [one_mul] using mul_le_mul he hd (norm_nonneg _) zero_le_one

theorem weightedHessianGap_nonneg (beta : ℝ) (μ ν : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤K) : 0≤weightedHessianGap beta μ ν K := by
  let p : Paper.Overlap×ℝ := (⟨0,by norm_num,by norm_num⟩,0)
  exact (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)).trans
    (le_csSup (weightedHessianGap_bddAbove beta μ ν K hK) (Set.mem_range_self p))

theorem hessian_le_weightedHessianGap (beta : ℝ) (μ ν : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤K) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (x : ℝ) :
    ‖parisiHessian beta μ (a,x)-parisiHessian beta ν (a,x)‖≤
      weightedHessianGap beta μ ν K*Real.exp (K*(1-a)) := by
  have hm := le_csSup (weightedHessianGap_bddAbove beta μ ν K hK)
    (Set.mem_range_self ((⟨a,ha⟩:Paper.Overlap),x))
  have hh := mul_le_mul_of_nonneg_right hm (Real.exp_pos (K*(1-a))).le
  convert hh using 1
  · rw [mul_right_comm,←Real.exp_add];simp
  · rfl

theorem parisiHessian_difference_weighted_bound (beta : ℝ) (hb : beta≠0)
    (μ ν : Paper.ParisiMeasure) (K : ℝ) (hK : 0<K) (a x : ℝ)
    (ha : a∈Icc (0 : ℝ) 1) :
    ‖parisiHessian beta μ (a,x)-parisiHessian beta ν (a,x)‖≤
      beta^2*(15+14*FourPapersCommon.parisiGradientL1Constant beta)*
        FourPapersCommon.parisiCDFDistance μ ν+
      (2*beta^2/K)*weightedHessianGap beta μ ν K*Real.exp (K*(1-a)) := by
  let S := weightedHessianGap beta μ ν K
  let δ := FourPapersCommon.parisiCDFDistance μ ν
  let C := FourPapersCommon.parisiGradientL1Constant beta
  let T := 1-a
  let E := fun r : ℝ=>beta^2*(2*S*Real.exp (K*(T-r))+14*C*δ+
    15*‖parisiCDF μ (a+r)-parisiCDF ν (a+r)‖)
  have hS : 0≤S := weightedHessianGap_nonneg beta μ ν K hK.le
  have hδ : 0≤δ := FourPapersCommon.parisiCDFDistance_nonneg μ ν
  have hC : 0≤C := by dsimp only [C,FourPapersCommon.parisiGradientL1Constant];positivity
  have hT : 0≤T := sub_nonneg.mpr ha.2
  have hT1 : T≤1 := by dsimp only [T];linarith [ha.1]
  have hmono (τ : Paper.ParisiMeasure) : Monotone (fun r : ℝ=>parisiCDF τ (a+r)) :=
    fun _ _ h=>parisiCDF_monotone τ (by linarith only [h])
  have hCDFi : IntervalIntegrable (fun r : ℝ=>‖parisiCDF μ (a+r)-parisiCDF ν (a+r)‖) volume 0 T :=
    ((hmono μ).intervalIntegrable.sub (hmono ν).intervalIntegrable).norm
  have hecont : Continuous (fun r : ℝ=>Real.exp (K*(T-r))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hEi : IntervalIntegrable E volume 0 T :=
    (((hecont.intervalIntegrable 0 T).const_mul (2*S)).add intervalIntegrable_const |>.add
      (hCDFi.const_mul 15)).const_mul (beta^2)
  have hs (r : ℝ) (hr : r∈Ioc (0 : ℝ) T) :
      ‖∫ω,restartedHessianDifferenceSource beta μ ν a x ha.1 r ω ∂canonicalBrownianMeasure‖≤E r := by
    have hat : a+r∈Icc (0 : ℝ) 1 := ⟨by linarith [ha.1,hr.1],by dsimp only [T] at hr;linarith [hr.2]⟩
    have hpoint (ω : Paper.BrownianSample) :
        ‖restartedHessianDifferenceSource beta μ ν a x ha.1 r ω‖≤E r := by
      apply (restartedHessianDifferenceSource_norm_le beta hb μ ν a x ha.1 r hat ω).trans
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg beta)
      have hh := hessian_le_weightedHessianGap beta μ ν K hK.le (a+r) hat
        (canonicalParisiRestartState beta x μ a ha.1 r.toNNReal ω)
      have he : 1-(a+r)=T-r := by dsimp only [T];ring
      rw [he] at hh
      dsimp only [S,C,δ] at *
      nlinarith only [hh]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall hpoint)
  rw [parisiHessian_difference_restart_integral beta hb μ ν a x ha]
  apply (intervalIntegral.norm_integral_le_of_norm_le hT (.of_forall hs) hEi).trans
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
    ((hecont.intervalIntegrable 0 T).const_mul (2*S) |>.add intervalIntegrable_const)
    (hCDFi.const_mul 15),intervalIntegral.integral_add
    ((hecont.intervalIntegrable 0 T).const_mul (2*S)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  have he := FourPapersCommon.integral_exp_backward_weight_le K T T hK
  have hCDF := FourPapersCommon.integral_restart_CDF_difference_le μ ν a T ha ⟨hT,le_rfl⟩
  have hCT : 14*C*δ*T≤14*C*δ := mul_le_of_le_one_right (by positivity) hT1
  have heS := mul_le_mul_of_nonneg_left he (show 0≤2*S by positivity)
  have hC15 := mul_le_mul_of_nonneg_left hCDF (by norm_num : (0 : ℝ)≤15)
  have hh := mul_le_mul_of_nonneg_left (add_le_add (add_le_add heS hCT) hC15) (sq_nonneg beta)
  rw [intervalIntegral.integral_const_mul]
  have hfinal := hh.trans_eq (show beta^2*(2*S*(Real.exp (K*T)/K)+14*C*δ+
      15*FourPapersCommon.parisiCDFDistance μ ν)=
      beta^2*(15+14*FourPapersCommon.parisiGradientL1Constant beta)*
        FourPapersCommon.parisiCDFDistance μ ν+
      (2*beta^2/K)*weightedHessianGap beta μ ν K*Real.exp (K*(1-a)) by
    dsimp only [S,C,δ,T];ring)
  convert hfinal using 1; ring

end QuantitativeFollowup
