module
public import QuantitativeFollowup.ScalarJetComparison

@[expose] public section

/-! Linear inverse-temperature-square continuity of the actual scalar
Parisi gradient, proved from its genuine drift/variance-mismatch source. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def weightedGradientTemperatureGap (beta gamma : ℝ) (μ : Paper.ParisiMeasure) (K : ℝ) : ℝ :=
  sSup (Set.range (fun p : Paper.Overlap×ℝ=>Real.exp (-K*(1-(p.1:ℝ)))*
    ‖parisiGradient beta μ ((p.1:ℝ),p.2)-parisiGradient gamma μ ((p.1:ℝ),p.2)‖))

theorem weightedGradientTemperatureGap_bddAbove (beta gamma : ℝ) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤K) :
    BddAbove (Set.range (fun p : Paper.Overlap×ℝ=>Real.exp (-K*(1-(p.1:ℝ)))*
      ‖parisiGradient beta μ ((p.1:ℝ),p.2)-parisiGradient gamma μ ((p.1:ℝ),p.2)‖)) := by
  refine ⟨2,?_⟩
  rintro _ ⟨p,rfl⟩
  have he : Real.exp (-K*(1-(p.1:ℝ)))≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [p.1.property.2])
  have hd : ‖parisiGradient beta μ ((p.1:ℝ),p.2)-parisiGradient gamma μ ((p.1:ℝ),p.2)‖≤2 :=
    (norm_sub_le _ _).trans (by linarith [norm_parisiGradient_le_one beta μ ((p.1:ℝ),p.2),
      norm_parisiGradient_le_one gamma μ ((p.1:ℝ),p.2)])
  simpa only [one_mul] using mul_le_mul he hd (norm_nonneg _) zero_le_one

theorem weightedGradientTemperatureGap_nonneg (beta gamma : ℝ) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤K) : 0≤weightedGradientTemperatureGap beta gamma μ K := by
  let p : Paper.Overlap×ℝ := (⟨0,by norm_num,by norm_num⟩,0)
  exact (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)).trans
    (le_csSup (weightedGradientTemperatureGap_bddAbove beta gamma μ K hK) (Set.mem_range_self p))

theorem gradient_le_weightedTemperatureGap (beta gamma : ℝ) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤K) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (x : ℝ) :
    ‖parisiGradient beta μ (a,x)-parisiGradient gamma μ (a,x)‖≤
      weightedGradientTemperatureGap beta gamma μ K*Real.exp (K*(1-a)) := by
  have hm := le_csSup (weightedGradientTemperatureGap_bddAbove beta gamma μ K hK)
    (Set.mem_range_self ((⟨a,ha⟩:Paper.Overlap),x))
  have hh := mul_le_mul_of_nonneg_right hm (Real.exp_pos (K*(1-a))).le
  convert hh using 1
  · rw [mul_right_comm,←Real.exp_add];simp
  · rfl

theorem scalarGradientTemperatureSource_norm_le (beta gamma : ℝ) (hg : gamma≠0)
    (μ : Paper.ParisiMeasure) (a x : ℝ) (ha : a∈Icc (0 : ℝ) 1)
    (r : ℝ) (hr : r∈Icc (0 : ℝ) (1-a)) (ω : Paper.BrownianSample) :
    ‖scalarDynkinSource (canonicalParisiRestartState beta x μ a ha.1)
      (canonicalParisiRestartDrift beta x μ a ha.1) gamma beta μ (MvPolynomial.X 0) a r ω‖≤
      beta^2*‖parisiGradient beta μ (a+r,canonicalParisiRestartState beta x μ a ha.1 r.toNNReal ω)-
        parisiGradient gamma μ (a+r,canonicalParisiRestartState beta x μ a ha.1 r.toNNReal ω)‖+
      8*|beta^2-gamma^2| := by
  let y := canonicalParisiRestartState beta x μ a ha.1 r.toNNReal ω
  have hdr := canonicalParisiRestartDrift_eq beta x μ a ha.1 r.toNNReal
    (by rw [Real.coe_toNNReal _ hr.1];linarith [hr.2,ha.1]) ω
  rw [Real.coe_toNNReal _ hr.1] at hdr
  rw [scalarDynkinSource_spatialJet,hdr]
  simp only [nonlinearJetPolynomial,Finset.Icc_eq_empty_of_lt (by norm_num : 0<1),
    Finset.sum_empty,polynomialJetField,map_zero,mul_zero,zero_add,
    parisiSpatialJet_one,parisiSpatialJet_two]
  let A := parisiCDF μ (a+r)
  let B := parisiGradient beta μ (a+r,y)
  let G := parisiGradient gamma μ (a+r,y)
  have hA : ‖A‖≤1 := by rw [Real.norm_of_nonneg (parisiCDF_nonneg μ _)];exact parisiCDF_le_one μ _
  have hG : ‖G‖≤1 := norm_parisiGradient_le_one gamma μ _
  have hAG : ‖A*G‖≤1 := by rw [norm_mul];exact (mul_le_mul hA hG (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hR : ‖beta^2*A*B-gamma^2*A*G‖≤beta^2*‖B-G‖+|beta^2-gamma^2| := by
    rw [show beta^2*A*B-gamma^2*A*G=beta^2*A*(B-G)+(beta^2-gamma^2)*(A*G) by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,norm_mul,Real.norm_of_nonneg (sq_nonneg beta),Real.norm_eq_abs]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hA (sq_nonneg beta)).trans_eq (mul_one _)) (norm_nonneg _)
    · exact (mul_le_mul_of_nonneg_left hAG (abs_nonneg _)).trans_eq (mul_one _)
  have hH := norm_parisiHessian_le_one_all gamma μ (a+r,y)
  have hJ := norm_parisiSpatialJet_three_le_fourteen gamma hg μ (a+r) y
  have hR0 := (norm_nonneg _).trans hR
  have hRH := mul_le_mul hR hH (norm_nonneg _) hR0
  have hV := mul_le_mul_of_nonneg_left hJ (abs_nonneg ((beta^2-gamma^2)/2))
  change ‖(beta^2*A*B-gamma^2*A*G)*parisiHessian gamma μ (a+r,y)+
      ((beta^2-gamma^2)/2)*parisiSpatialJet gamma μ 3 (a+r) y‖≤_
  apply ((norm_add_le _ _).trans (add_le_add (by simpa only [norm_mul,mul_one] using hRH)
    (by simpa only [norm_mul,Real.norm_eq_abs] using hV))).trans_eq
  rw [abs_div]
  norm_num
  dsimp only [A,B,G,y]
  ring

theorem gradient_temperature_weighted_restart_bound (beta gamma : ℝ)
    (hb : beta≠0) (hg : gamma≠0) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0<K) (a x : ℝ) (ha : a∈Icc (0 : ℝ) 1) :
    ‖parisiGradient beta μ (a,x)-parisiGradient gamma μ (a,x)‖≤
      8*|beta^2-gamma^2|+(beta^2/K)*weightedGradientTemperatureGap beta gamma μ K*Real.exp (K*(1-a)) := by
  let S := weightedGradientTemperatureGap beta gamma μ K
  let T := 1-a
  let E := fun r : ℝ=>beta^2*S*Real.exp (K*(T-r))+8*|beta^2-gamma^2|
  have hS : 0≤S := weightedGradientTemperatureGap_nonneg beta gamma μ K hK.le
  have hT : 0≤T := sub_nonneg.mpr ha.2
  have hT1 : T≤1 := by dsimp only [T];linarith [ha.1]
  have hecont : Continuous (fun r : ℝ=>Real.exp (K*(T-r))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hEi : IntervalIntegrable E volume 0 T :=
    ((hecont.intervalIntegrable 0 T).const_mul (beta^2*S)).add intervalIntegrable_const
  rw [←parisiSpatialJet_one beta μ a x,←parisiSpatialJet_one gamma μ a x,
    parisiJet_difference_restart_integral beta gamma hb hg μ μ 0 a x ha]
  have hs (r : ℝ) (hr : r∈Ioc (0 : ℝ) T) :
      ‖(∫ω,scalarDynkinSource (canonicalParisiRestartState beta x μ a ha.1)
        (canonicalParisiRestartDrift beta x μ a ha.1) gamma beta μ (MvPolynomial.X 0) a r ω ∂canonicalBrownianMeasure)-
      (∫ω,scalarDynkinSource (canonicalParisiRestartState beta x μ a ha.1)
        (canonicalParisiRestartDrift beta x μ a ha.1) beta beta μ (MvPolynomial.X 0) a r ω ∂canonicalBrownianMeasure)‖≤E r := by
    rw [integral_scalarDynkinSource_restart_self_gradient beta μ a x ha r ⟨hr.1.le,hr.2⟩,sub_zero]
    have hat : a+r∈Icc (0 : ℝ) 1 := ⟨by linarith [ha.1,hr.1],by dsimp only [T] at hr;linarith [hr.2]⟩
    have hpoint (ω : Paper.BrownianSample) : ‖scalarDynkinSource
        (canonicalParisiRestartState beta x μ a ha.1) (canonicalParisiRestartDrift beta x μ a ha.1)
        gamma beta μ (MvPolynomial.X 0) a r ω‖≤E r := by
      have hp := scalarGradientTemperatureSource_norm_le beta gamma hg μ a x ha r ⟨hr.1.le,hr.2⟩ ω
      have hj := gradient_le_weightedTemperatureGap beta gamma μ K hK.le (a+r) hat
        (canonicalParisiRestartState beta x μ a ha.1 r.toNNReal ω)
      have hex : 1-(a+r)=T-r := by dsimp only [T];ring
      rw [hex] at hj
      apply hp.trans
      dsimp only [E,S]
      nlinarith only [mul_le_mul_of_nonneg_left hj (sq_nonneg beta)]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall hpoint)
  apply (intervalIntegral.norm_integral_le_of_norm_le hT (.of_forall hs) hEi).trans
  rw [intervalIntegral.integral_add ((hecont.intervalIntegrable 0 T).const_mul (beta^2*S))
    intervalIntegrable_const,intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  have he := mul_le_mul_of_nonneg_left (FourPapersCommon.integral_exp_backward_weight_le K T T hK)
    (show 0≤beta^2*S by positivity)
  have ht := mul_le_mul_of_nonneg_left hT1 (show 0≤8*|beta^2-gamma^2| by positivity)
  have hh := add_le_add he ht
  convert hh using 1 <;> dsimp only [S,T] <;> ring

end QuantitativeFollowup
