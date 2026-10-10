module
public import QuantitativeFollowup.ScalarDynkinGrid
public import FRSB.FiniteJetStochastic
public import FRSB.OptimalCurvatureMoment
public import Paper.ParisiRestartState

@[expose] public section

/-! A genuine Hessian difference representation on one actual restarted
diffusion. The two tested Parisi measures need not agree with each other. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper MvPolynomial
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem scalarDynkinSource_hessian {Ω : Type*}
    (X d : ℝ≥0→Ω→ℝ) (beta sigma : ℝ) (ν : Paper.ParisiMeasure)
    (a r : ℝ) (ω : Ω) :
    scalarDynkinSource X d beta sigma ν (MvPolynomial.X 1) a r ω=
      -(beta^2*parisiCDF ν (a+r))*parisiSpatialJet beta ν 2 (a+r) (X r.toNNReal ω)^2+
      (d r.toNNReal ω-beta^2*parisiCDF ν (a+r)*parisiSpatialJet beta ν 1 (a+r) (X r.toNNReal ω))*
        parisiSpatialJet beta ν 3 (a+r) (X r.toNNReal ω)+
      ((sigma^2-beta^2)/2)*parisiSpatialJet beta ν 4 (a+r) (X r.toNNReal ω) := by
  simp only [scalarDynkinSource,scalarDynkinField,dynkinTransportPolynomial,
    momentDrift0_X,momentDrift1_X,polynomialSpatialDerivative_X,
    polynomialJetField,map_zero,map_sub,map_mul,eval_C,eval_X,zero_add]
  simp only [nonlinearJetPolynomial,Finset.Icc_self,Finset.sum_singleton,
    map_mul,eval_C,eval_X]
  norm_num
  ring

theorem parisiHessian_terminal_value (beta : ℝ) (ν : Paper.ParisiMeasure) (x : ℝ) :
    parisiHessian beta ν (1,x)=sech x^2 := by
  have hd := hasDerivAt_parisiGradient_spatial_all beta ν 1 x
  have he : (fun y : ℝ=>parisiGradient beta ν (1,y))=Real.tanh :=
    funext (parisiGradient_terminal beta ν)
  rw [he] at hd
  exact hd.unique (hasDerivAt_tanh x)

def restartedHessianDifferenceSource (beta : ℝ) (μ ν : Paper.ParisiMeasure)
    (a x : ℝ) (ha : 0≤a) (r : ℝ) (ω : Paper.BrownianSample) : ℝ :=
  let y := canonicalParisiRestartState beta x μ a ha r.toNNReal ω
  beta^2*(parisiCDF μ (a+r)*parisiHessian beta μ (a+r,y)^2-
    parisiCDF ν (a+r)*parisiHessian beta ν (a+r,y)^2+
    (parisiCDF μ (a+r)*parisiGradient beta μ (a+r,y)-
      parisiCDF ν (a+r)*parisiGradient beta ν (a+r,y))*parisiSpatialJet beta ν 3 (a+r) y)

theorem parisiHessian_difference_restart_integral (beta : ℝ) (hb : beta≠0)
    (μ ν : Paper.ParisiMeasure) (a x : ℝ) (ha : a∈Icc (0 : ℝ) 1) :
    parisiHessian beta μ (a,x)-parisiHessian beta ν (a,x)=
      ∫r in (0 : ℝ)..(1-a),∫ω,restartedHessianDifferenceSource beta μ ν a x ha.1 r ω
        ∂canonicalBrownianMeasure := by
  let X := canonicalParisiRestartState beta x μ a ha.1
  let d := canonicalParisiRestartDrift beta x μ a ha.1
  let hc := boundedDriftItoCharacteristics_canonicalParisiRestartState beta x μ a ha.1
  let F : MomentPolynomial := MvPolynomial.X 1
  let S := fun τ r=>∫ω,scalarDynkinSource X d beta beta τ F a r ω ∂canonicalBrownianMeasure
  have htail (τ : Paper.ParisiMeasure) := scalarDynkin_tail hc beta hb τ F a ha
  have hstart (τ : Paper.ParisiMeasure) : scalarDynkinMoment canonicalBrownianMeasure X beta τ F a 0=
      parisiHessian beta τ (a,x) := by
    simp only [scalarDynkinMoment,scalarDynkinField,polynomialJetField,F,eval_X,
      Real.toNNReal_zero,add_zero,X,canonicalParisiRestartState_zero]
    simp
  have hterm (τ : Paper.ParisiMeasure) :
      scalarDynkinMoment canonicalBrownianMeasure X beta τ F a (1-a)=
        scalarDynkinMoment canonicalBrownianMeasure X beta μ F a (1-a) := by
    unfold scalarDynkinMoment scalarDynkinField
    apply integral_congr_ae
    exact .of_forall fun ω=>by
      simp only [polynomialJetField,F,eval_X,Nat.reduceAdd,parisiSpatialJet_two,add_sub_cancel,
        parisiHessian_terminal_value]
  have hi (τ : Paper.ParisiMeasure) : ∀l r,IntervalIntegrable (S τ) volume l r :=
    scalarDynkinSource_expected_intervalIntegrable hc beta τ F a
  have hraw : parisiHessian beta μ (a,x)-parisiHessian beta ν (a,x)=
      ∫r in (0 : ℝ)..(1-a),S ν r-S μ r := by
    have hm := htail μ
    have hn := htail ν
    rw [hstart μ] at hm
    rw [hstart ν,hterm ν] at hn
    rw [intervalIntegral.integral_sub (hi ν 0 (1-a)) (hi μ 0 (1-a))]
    change _=∫r in (0 : ℝ)..(1-a),S μ r at hm
    change _=∫r in (0 : ℝ)..(1-a),S ν r at hn
    linarith
  rw [hraw]
  apply intervalIntegral.integral_congr_Ioo_of_le (sub_nonneg.mpr ha.2)
  intro r hr
  have hint (τ : Paper.ParisiMeasure) :
      Integrable (scalarDynkinSource X d beta beta τ F a r) canonicalBrownianMeasure := by
    obtain ⟨D,hD⟩ := hc.bounded_drift
    exact (integrable_const (scalarDynkinSourceBound beta beta D F)).mono'
      ((measurable_scalarDynkinSource hc beta τ F a).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (.of_forall (norm_scalarDynkinSource_le X d beta beta D D.coe_nonneg hD τ F a r))
  dsimp only [S]
  rw [←integral_sub (hint ν) (hint μ)]
  apply integral_congr_ae
  exact .of_forall fun ω=>by
    change scalarDynkinSource X d beta beta ν (MvPolynomial.X 1) a r ω-
      scalarDynkinSource X d beta beta μ (MvPolynomial.X 1) a r ω=_
    rw [scalarDynkinSource_hessian,scalarDynkinSource_hessian]
    have hdr : d r.toNNReal ω=beta^2*parisiCDF μ (a+r)*parisiGradient beta μ (a+r,X r.toNNReal ω) := by
      simpa only [d,X,Real.coe_toNNReal _ hr.1.le] using
        canonicalParisiRestartDrift_eq beta x μ a ha.1 r.toNNReal
          (by rw [Real.coe_toNNReal _ hr.1.le];linarith [hr.2,ha.1]) ω
    rw [hdr]
    simp only [parisiSpatialJet_one,parisiSpatialJet_two,sub_self,zero_div,zero_mul,add_zero]
    dsimp only [restartedHessianDifferenceSource,X]
    ring

end QuantitativeFollowup
