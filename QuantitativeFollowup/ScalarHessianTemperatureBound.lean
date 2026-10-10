module
public import QuantitativeFollowup.ScalarHessianTemperature

@[expose] public section

/-! Closed temperature-square continuity of the actual Parisi Hessian. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def weightedHessianTemperatureGap (beta gamma : ℝ) (μ : Paper.ParisiMeasure) (K : ℝ) : ℝ :=
  sSup (Set.range (fun p : Paper.Overlap×ℝ=> Real.exp (-K*(1-(p.1:ℝ)))*
    ‖parisiHessian beta μ ((p.1:ℝ),p.2)-parisiHessian gamma μ ((p.1:ℝ),p.2)‖))

theorem weightedHessianTemperatureGap_bddAbove (beta gamma : ℝ) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤ K) :
    BddAbove (Set.range (fun p : Paper.Overlap×ℝ=> Real.exp (-K*(1-(p.1:ℝ)))*
      ‖parisiHessian beta μ ((p.1:ℝ),p.2)-parisiHessian gamma μ ((p.1:ℝ),p.2)‖)) := by
  refine ⟨2,?_⟩
  rintro _ ⟨p,rfl⟩
  have he : Real.exp (-K*(1-(p.1:ℝ)))≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [p.1.property.2])
  have hd : ‖parisiHessian beta μ ((p.1:ℝ),p.2)-parisiHessian gamma μ ((p.1:ℝ),p.2)‖≤2 :=
    (norm_sub_le _ _).trans (by linarith [norm_parisiHessian_le_one_all beta μ ((p.1:ℝ),p.2),
      norm_parisiHessian_le_one_all gamma μ ((p.1:ℝ),p.2)])
  simpa only [one_mul] using mul_le_mul he hd (norm_nonneg _) zero_le_one

theorem weightedHessianTemperatureGap_nonneg (beta gamma : ℝ) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤ K) : 0≤ weightedHessianTemperatureGap beta gamma μ K := by
  let p : Paper.Overlap×ℝ := (⟨0,by norm_num,by norm_num⟩,0)
  exact (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)).trans
    (le_csSup (weightedHessianTemperatureGap_bddAbove beta gamma μ K hK) (Set.mem_range_self p))

theorem hessian_le_weightedTemperatureGap (beta gamma : ℝ) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤ K) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (x : ℝ) :
    ‖parisiHessian beta μ (a,x)-parisiHessian gamma μ (a,x)‖≤
      weightedHessianTemperatureGap beta gamma μ K*Real.exp (K*(1-a)) := by
  have hm := le_csSup (weightedHessianTemperatureGap_bddAbove beta gamma μ K hK)
    (Set.mem_range_self ((⟨a,ha⟩:Paper.Overlap),x))
  have hh := mul_le_mul_of_nonneg_right hm (Real.exp_pos (K*(1-a))).le
  convert hh using 1
  · rw [mul_right_comm,←Real.exp_add];simp
  · rfl

theorem hessian_temperature_weighted_restart_bound (beta gamma : ℝ)
    (hb : beta≠0) (hg : gamma≠0) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0< K) (a x : ℝ) (ha : a∈Icc (0 : ℝ) 1) :
    ‖parisiHessian beta μ (a,x)-parisiHessian gamma μ (a,x)‖≤
      scalarHessianTemperatureSourceConstant beta gamma*|beta^2-gamma^2|+
      (2*beta^2/K)*weightedHessianTemperatureGap beta gamma μ K*Real.exp (K*(1-a)) := by
  let X := canonicalParisiRestartState beta x μ a ha.1
  let d := canonicalParisiRestartDrift beta x μ a ha.1
  let hc := boundedDriftItoCharacteristics_canonicalParisiRestartState beta x μ a ha.1
  let S := weightedHessianTemperatureGap beta gamma μ K
  let T := 1-a
  let C := scalarHessianTemperatureSourceConstant beta gamma
  let E := fun r : ℝ=>2*beta^2*S*Real.exp (K*(T-r))+C*|beta^2-gamma^2|
  have hS : 0≤ S := weightedHessianTemperatureGap_nonneg beta gamma μ K hK.le
  have hC : 0≤ C := (scalarHessianTemperatureSourceConstant_pos beta gamma).le
  have hT : 0≤ T := sub_nonneg.mpr ha.2
  have hT1 : T≤1 := by dsimp only [T];linarith [ha.1]
  have hecont : Continuous (fun r : ℝ=> Real.exp (K*(T-r))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hEi : IntervalIntegrable E volume 0 T :=
    ((hecont.intervalIntegrable 0 T).const_mul (2*beta^2*S)).add intervalIntegrable_const
  have hraw := parisiJet_difference_restart_integral beta gamma hb hg μ μ 1 a x ha
  simp only [Nat.reduceAdd,parisiSpatialJet_two] at hraw
  rw [hraw]
  have hs (r : ℝ) (hr : r∈Ioc (0 : ℝ) T) :
      ‖(∫ω,scalarDynkinSource X d gamma beta μ (MvPolynomial.X 1) a r ω ∂canonicalBrownianMeasure)-
        (∫ω,scalarDynkinSource X d beta beta μ (MvPolynomial.X 1) a r ω ∂canonicalBrownianMeasure)‖≤ E r := by
    have hint (b : ℝ) : Integrable (scalarDynkinSource X d b beta μ (MvPolynomial.X 1) a r) canonicalBrownianMeasure := by
      obtain ⟨D,hD⟩ := hc.bounded_drift
      exact (integrable_const (scalarDynkinSourceBound b beta D (MvPolynomial.X 1))).mono'
        ((measurable_scalarDynkinSource hc b μ (MvPolynomial.X 1) a).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (.of_forall (norm_scalarDynkinSource_le X d b beta D D.coe_nonneg hD μ (MvPolynomial.X 1) a r))
    rw [←integral_sub (hint gamma) (hint beta)]
    have hat : a+r∈Icc (0 : ℝ) 1 := ⟨by linarith [ha.1,hr.1],by dsimp only [T] at hr;linarith [hr.2]⟩
    have hpoint (ω : Paper.BrownianSample) : ‖scalarDynkinSource X d gamma beta μ (MvPolynomial.X 1) a r ω-
        scalarDynkinSource X d beta beta μ (MvPolynomial.X 1) a r ω‖≤ E r := by
      have hp := scalarHessianTemperatureSource_norm_le beta gamma hb hg μ a x ha r ⟨hr.1.le,hr.2⟩ ω
      have hj := hessian_le_weightedTemperatureGap beta gamma μ K hK.le (a+r) hat (X r.toNNReal ω)
      have hex : 1-(a+r)=T-r := by dsimp only [T];ring
      rw [hex] at hj
      apply hp.trans
      dsimp only [E,S,C,X,d] at *
      nlinarith only [mul_le_mul_of_nonneg_left hj (show 0≤2*beta^2 by positivity)]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall hpoint)
  apply (intervalIntegral.norm_integral_le_of_norm_le hT (.of_forall hs) hEi).trans
  rw [intervalIntegral.integral_add ((hecont.intervalIntegrable 0 T).const_mul (2*beta^2*S))
    intervalIntegrable_const,intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  have he := mul_le_mul_of_nonneg_left (FourPapersCommon.integral_exp_backward_weight_le K T T hK)
    (show 0≤2*beta^2*S by positivity)
  have ht := mul_le_mul_of_nonneg_left hT1 (show 0≤ C*|beta^2-gamma^2| by positivity)
  have hh := add_le_add he ht
  convert hh using 1 <;> dsimp only [S,C,T] <;> ring

theorem weightedHessianTemperatureGap_contraction (beta gamma : ℝ)
    (hb : beta≠0) (hg : gamma≠0) (μ : Paper.ParisiMeasure) :
    weightedHessianTemperatureGap beta gamma μ (4*beta^2)≤
      scalarHessianTemperatureSourceConstant beta gamma*|beta^2-gamma^2|+
      weightedHessianTemperatureGap beta gamma μ (4*beta^2)/2 := by
  let K := 4*beta^2
  let S := weightedHessianTemperatureGap beta gamma μ K
  let C := scalarHessianTemperatureSourceConstant beta gamma
  have hb2 : 0< beta^2 := sq_pos_of_ne_zero hb
  have hK : 0< K := by dsimp only [K];positivity
  have hC : 0≤ C := (scalarHessianTemperatureSourceConstant_pos beta gamma).le
  change S≤ C*|beta^2-gamma^2|+S/2
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨p,rfl⟩
  let a : ℝ := p.1
  have ha : a∈Icc (0 : ℝ) 1 := p.1.property
  have hh := hessian_temperature_weighted_restart_bound beta gamma hb hg μ K hK a p.2 ha
  have hw := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-K*(1-a))).le
  have he : Real.exp (-K*(1-a))*Real.exp (K*(1-a))=1 := by rw [←Real.exp_add];simp
  have hratio : 2*beta^2/K=(1/2:ℝ) := by dsimp only [K];field_simp;norm_num
  have hident : Real.exp (-K*(1-a))*(C*|beta^2-gamma^2|+(2*beta^2/K)*S*Real.exp (K*(1-a)))=
      C*|beta^2-gamma^2| *Real.exp (-K*(1-a))+S/2 := by
    rw [hratio]
    calc
      _=C*|beta^2-gamma^2| *Real.exp (-K*(1-a))+S/2*
        (Real.exp (-K*(1-a))*Real.exp (K*(1-a))) := by ring
      _=_ := by rw [he,mul_one]
  have he1 : Real.exp (-K*(1-a))≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hK.le,ha.2])
  change Real.exp (-K*(1-a))*‖parisiHessian beta μ (a,p.2)-parisiHessian gamma μ (a,p.2)‖≤_
  exact hw.trans (hident.le.trans (add_le_add
    (mul_le_of_le_one_right (mul_nonneg hC (abs_nonneg _)) he1) le_rfl))

def scalarHessianTemperatureConstant (beta gamma : ℝ) : ℝ :=
  2*scalarHessianTemperatureSourceConstant beta gamma*Real.exp (4*beta^2)

theorem parisiHessian_temperature_square_bound (beta gamma : ℝ)
    (hb : beta≠0) (hg : gamma≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (x : ℝ) :
    ‖parisiHessian beta μ (a,x)-parisiHessian gamma μ (a,x)‖≤
      scalarHessianTemperatureConstant beta gamma*|beta^2-gamma^2| := by
  let K := 4*beta^2
  let C := scalarHessianTemperatureSourceConstant beta gamma
  have hK : 0≤ K := by dsimp only [K];positivity
  have hC : 0≤ C := (scalarHessianTemperatureSourceConstant_pos beta gamma).le
  have hs := weightedHessianTemperatureGap_contraction beta gamma hb hg μ
  have hS : weightedHessianTemperatureGap beta gamma μ K≤2*C*|beta^2-gamma^2| := by
    change weightedHessianTemperatureGap beta gamma μ K≤ C*|beta^2-gamma^2|+
      weightedHessianTemperatureGap beta gamma μ K/2 at hs
    linarith
  have he : Real.exp (K*(1-a))≤ Real.exp K := Real.exp_le_exp.mpr (by nlinarith [ha.1])
  exact (hessian_le_weightedTemperatureGap beta gamma μ K hK a ha x).trans
    (by
      convert mul_le_mul hS he (Real.exp_pos _).le (by positivity) using 1
      dsimp only [scalarHessianTemperatureConstant,C,K]
      ring)

end QuantitativeFollowup
