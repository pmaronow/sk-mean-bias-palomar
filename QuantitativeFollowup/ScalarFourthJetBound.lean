module
public import QuantitativeFollowup.ScalarJetDynkin

@[expose] public section

/-! An explicit fourth spatial jet bound, uniform over all Parisi measures.
The linear fourth-jet reaction and the bounded third jet are derived from
the genuine polynomial Dynkin formula. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def weightedFourthJet (beta : ℝ) (μ : Paper.ParisiMeasure) (K : ℝ) : ℝ :=
  sSup (Set.range (fun p : Paper.Overlap×ℝ=>Real.exp (-K*(1-(p.1:ℝ)))*
    ‖parisiSpatialJet beta μ 4 (p.1:ℝ) p.2‖))

theorem weightedFourthJet_bddAbove (beta : ℝ) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤K) :
    BddAbove (Set.range (fun p : Paper.Overlap×ℝ=>Real.exp (-K*(1-(p.1:ℝ)))*
      ‖parisiSpatialJet beta μ 4 (p.1:ℝ) p.2‖)) := by
  refine ⟨uniformSpatialConstant beta 3,?_⟩
  rintro _ ⟨p,rfl⟩
  have he : Real.exp (-K*(1-(p.1:ℝ)))≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [p.1.property.2])
  have hj := (norm_parisiSpatialJet_succ_le beta μ 3 (p.1:ℝ) p.2).trans
    (norm_spatialDerivativeBCF_le_uniform beta μ 3)
  exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
    (by simpa only [one_mul] using hj)

theorem weightedFourthJet_nonneg (beta : ℝ) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤K) : 0≤weightedFourthJet beta μ K := by
  let p : Paper.Overlap×ℝ := (⟨0,by norm_num,by norm_num⟩,0)
  exact (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)).trans
    (le_csSup (weightedFourthJet_bddAbove beta μ K hK) (Set.mem_range_self p))

theorem fourthJet_le_weightedFourthJet (beta : ℝ) (μ : Paper.ParisiMeasure)
    (K : ℝ) (hK : 0≤K) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (x : ℝ) :
    ‖parisiSpatialJet beta μ 4 a x‖≤weightedFourthJet beta μ K*Real.exp (K*(1-a)) := by
  have hm := le_csSup (weightedFourthJet_bddAbove beta μ K hK)
    (Set.mem_range_self ((⟨a,ha⟩:Paper.Overlap),x))
  have hh := mul_le_mul_of_nonneg_right hm (Real.exp_pos (K*(1-a))).le
  convert hh using 1
  · rw [mul_right_comm,←Real.exp_add];simp
  · rfl

theorem fourthJet_weighted_restart_bound (beta : ℝ) (hb : beta≠0)
    (μ : Paper.ParisiMeasure) (K : ℝ) (hK : 0<K) (a x : ℝ)
    (ha : a∈Icc (0 : ℝ) 1) :
    ‖parisiSpatialJet beta μ 4 a x‖≤10+588*beta^2+
      (4*beta^2/K)*weightedFourthJet beta μ K*Real.exp (K*(1-a)) := by
  let X := canonicalParisiRestartState beta x μ a ha.1
  let d := canonicalParisiRestartDrift beta x μ a ha.1
  let hc := boundedDriftItoCharacteristics_canonicalParisiRestartState beta x μ a ha.1
  let S := weightedFourthJet beta μ K
  let T := 1-a
  let E := fun r : ℝ=>beta^2*(4*S*Real.exp (K*(T-r))+588)
  have hS : 0≤S := weightedFourthJet_nonneg beta μ K hK.le
  have hT : 0≤T := sub_nonneg.mpr ha.2
  have hT1 : T≤1 := by dsimp only [T];linarith [ha.1]
  have hecont : Continuous (fun r : ℝ=>Real.exp (K*(T-r))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hEi : IntervalIntegrable E volume 0 T :=
    (((hecont.intervalIntegrable 0 T).const_mul (4*S)).add intervalIntegrable_const).const_mul (beta^2)
  have hs (r : ℝ) (hr : r∈Ioc (0 : ℝ) T) :
      ‖∫ω,scalarDynkinSource X d beta beta μ (MvPolynomial.X 3) a r ω ∂canonicalBrownianMeasure‖≤E r := by
    have hat : a+r∈Icc (0 : ℝ) 1 := ⟨by linarith [ha.1,hr.1],by dsimp only [T] at hr;linarith [hr.2]⟩
    have hpoint (ω : Paper.BrownianSample) :
        ‖scalarDynkinSource X d beta beta μ (MvPolynomial.X 3) a r ω‖≤E r := by
      let y := X r.toNNReal ω
      have hdr : d r.toNNReal ω=beta^2*parisiCDF μ (a+r)*parisiSpatialJet beta μ 1 (a+r) y := by
        simpa only [d,X,Real.coe_toNNReal _ hr.1.le,parisiSpatialJet_one] using
          canonicalParisiRestartDrift_eq beta x μ a ha.1 r.toNNReal
            (by rw [Real.coe_toNNReal _ hr.1.le];linarith [hr.2,ha.1]) ω
      rw [scalarDynkinSource_spatialJet,hdr,polynomialJetField_nonlinear_three]
      simp only [y,sub_self,zero_div,zero_mul,add_zero]
      rw [show -(beta^2*parisiCDF μ (a+r)/2)*
          (8*parisiSpatialJet beta μ 2 (a+r) y*parisiSpatialJet beta μ 4 (a+r) y+
            6*parisiSpatialJet beta μ 3 (a+r) y^2)=
          -(beta^2*parisiCDF μ (a+r))*(4*parisiSpatialJet beta μ 2 (a+r) y*
            parisiSpatialJet beta μ 4 (a+r) y+3*parisiSpatialJet beta μ 3 (a+r) y^2) by ring]
      rw [norm_mul,norm_neg,Real.norm_of_nonneg (mul_nonneg (sq_nonneg beta) (parisiCDF_nonneg μ _))]
      have hcdf : beta^2*parisiCDF μ (a+r)≤beta^2 :=
        (mul_le_mul_of_nonneg_left (parisiCDF_le_one μ _) (sq_nonneg beta)).trans_eq (mul_one _)
      have hj4 := fourthJet_le_weightedFourthJet beta μ K hK.le (a+r) hat y
      have hex : 1-(a+r)=T-r := by dsimp only [T];ring
      rw [hex] at hj4
      have hj2 : ‖parisiSpatialJet beta μ 2 (a+r) y‖≤1 := by
        rw [parisiSpatialJet_two];exact norm_parisiHessian_le_one_all beta μ _
      have hj3 := norm_parisiSpatialJet_three_le_fourteen beta hb μ (a+r) y
      have hj3sq : ‖parisiSpatialJet beta μ 3 (a+r) y‖^2≤196 := by nlinarith [norm_nonneg (parisiSpatialJet beta μ 3 (a+r) y)]
      apply (mul_le_mul_of_nonneg_right hcdf (norm_nonneg _)).trans
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg beta)
      apply (norm_add_le _ _).trans
      simp only [norm_mul,norm_pow]
      norm_num only [Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤4),
        Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤3)]
      have hprod := mul_le_mul hj2 hj4 (norm_nonneg _) zero_le_one
      dsimp only [S] at *
      nlinarith only [hprod,hj3sq]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall hpoint)
  have hi := intervalIntegral.norm_integral_le_of_norm_le hT (.of_forall hs) hEi
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
    ((hecont.intervalIntegrable 0 T).const_mul (4*S)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul] at hi
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hi
  rw [mul_comm T (588 : ℝ)] at hi
  have he := FourPapersCommon.integral_exp_backward_weight_le K T T hK
  have hbnd := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left he (show 0≤4*S by positivity))
      (mul_le_mul_of_nonneg_left hT1 (by norm_num : (0 : ℝ)≤588))) (sq_nonneg beta)
  have htail := scalarDynkin_tail hc beta hb μ (MvPolynomial.X 3) a ha
  have hstart : scalarDynkinMoment canonicalBrownianMeasure X beta μ (MvPolynomial.X 3) a 0=
      parisiSpatialJet beta μ 4 a x := by
    simp only [scalarDynkinMoment,scalarDynkinField_spatialJet,Nat.reduceAdd,
      Real.toNNReal_zero,add_zero,X,canonicalParisiRestartState_zero]
    simp
  have hterm : ‖scalarDynkinMoment canonicalBrownianMeasure X beta μ (MvPolynomial.X 3) a T‖≤10 := by
    unfold scalarDynkinMoment
    simpa only [scalarDynkinField_spatialJet,Nat.reduceAdd,T,add_sub_cancel,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=canonicalBrownianMeasure)
        (.of_forall fun ω=>norm_parisiSpatialJet_four_terminal_le beta μ (X T.toNNReal ω))
  rw [hstart] at htail
  have heq : parisiSpatialJet beta μ 4 a x=
      scalarDynkinMoment canonicalBrownianMeasure X beta μ (MvPolynomial.X 3) a T-
        ∫r in (0 : ℝ)..T,∫ω,scalarDynkinSource X d beta beta μ (MvPolynomial.X 3) a r ω ∂canonicalBrownianMeasure := by
    change _=∫r in (0 : ℝ)..T,∫ω,scalarDynkinSource X d beta beta μ (MvPolynomial.X 3) a r ω ∂canonicalBrownianMeasure at htail
    linarith
  rw [heq]
  apply ((norm_sub_le _ _).trans (add_le_add hterm (hi.trans hbnd))).trans_eq
  dsimp only [S,T]
  ring

end QuantitativeFollowup
