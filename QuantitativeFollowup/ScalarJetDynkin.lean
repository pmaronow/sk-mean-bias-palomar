module
public import QuantitativeFollowup.ScalarHessianL1Bound

@[expose] public section

/-! Literal one-jet Dynkin sources and terminal third/fourth jets. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper MvPolynomial
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem scalarDynkinSource_spatialJet {Ω : Type*}
    (X d : ℝ≥0→Ω→ℝ) (beta sigma : ℝ) (ν : Paper.ParisiMeasure)
    (j : ℕ) (a r : ℝ) (ω : Ω) :
    scalarDynkinSource X d beta sigma ν (MvPolynomial.X j) a r ω=
      -(beta^2*parisiCDF ν (a+r)/2)*
        polynomialJetField beta ν (nonlinearJetPolynomial j) (a+r) (X r.toNNReal ω)+
      (d r.toNNReal ω-beta^2*parisiCDF ν (a+r)*parisiSpatialJet beta ν 1 (a+r) (X r.toNNReal ω))*
        parisiSpatialJet beta ν (j+2) (a+r) (X r.toNNReal ω)+
      ((sigma^2-beta^2)/2)*parisiSpatialJet beta ν (j+3) (a+r) (X r.toNNReal ω) := by
  simp only [scalarDynkinSource,scalarDynkinField,dynkinTransportPolynomial,
    momentDrift0_X,momentDrift1_X,polynomialSpatialDerivative_X,
    polynomialJetField,map_zero,map_sub,map_mul,eval_C,eval_X,zero_add,
    show j+1+1=j+2 by omega,show j+1+1+1=j+3 by omega]
  ring

theorem scalarDynkinField_spatialJet {Ω : Type*} (X : ℝ≥0→Ω→ℝ)
    (beta : ℝ) (ν : Paper.ParisiMeasure) (j : ℕ) (a r : ℝ) (ω : Ω) :
    scalarDynkinField X beta ν (MvPolynomial.X j) a r ω=
      parisiSpatialJet beta ν (j+1) (a+r) (X r.toNNReal ω) := by
  simp only [scalarDynkinField,polynomialJetField,eval_X]

theorem parisiSpatialJet_three_terminal (beta : ℝ) (ν : Paper.ParisiMeasure) (x : ℝ) :
    parisiSpatialJet beta ν 3 1 x=deriv (fun y=>sech y^2) x := by
  have hd := hasDerivAt_parisiSpatialJet_succ beta ν 1 1 x
  have he : (fun y=>parisiSpatialJet beta ν 2 1 y)=(fun y=>sech y^2) := by
    funext y
    rw [parisiSpatialJet_two,parisiHessian_terminal_value]
  change HasDerivAt (fun y=>parisiSpatialJet beta ν 2 1 y)
    (parisiSpatialJet beta ν 3 1 x) x at hd
  rw [he] at hd
  exact hd.deriv.symm

theorem parisiSpatialJet_four_terminal (beta : ℝ) (ν : Paper.ParisiMeasure) (x : ℝ) :
    parisiSpatialJet beta ν 4 1 x=4*sech x^2-6*sech x^4 := by
  have hd := hasDerivAt_parisiSpatialJet_succ beta ν 2 1 x
  change HasDerivAt (fun y=>parisiSpatialJet beta ν 3 1 y)
    (parisiSpatialJet beta ν 4 1 x) x at hd
  rw [funext (parisiSpatialJet_three_terminal beta ν)] at hd
  exact hd.unique (hasDerivAt_deriv_sech_sq x)

theorem norm_parisiSpatialJet_four_terminal_le (beta : ℝ) (ν : Paper.ParisiMeasure) (x : ℝ) :
    ‖parisiSpatialJet beta ν 4 1 x‖≤10 := by
  rw [parisiSpatialJet_four_terminal]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_mul,Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 2),
    Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 4)]
  norm_num only [Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤4),
    Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤6)]
  nlinarith [sech_sq_le_one x,sech_fourth_le_one x]

theorem polynomialJetField_nonlinear_three (beta : ℝ) (ν : Paper.ParisiMeasure) (r x : ℝ) :
    polynomialJetField beta ν (nonlinearJetPolynomial 3) r x=
      8*parisiSpatialJet beta ν 2 r x*parisiSpatialJet beta ν 4 r x+
      6*parisiSpatialJet beta ν 3 r x^2 := by
  have hs : Finset.Icc 1 3={1,2,3} := by decide
  simp only [nonlinearJetPolynomial,hs,polynomialJetField,map_sum,
    map_mul,eval_C,eval_X]
  norm_num [show Nat.choose 4 2=6 by decide]
  ring

end QuantitativeFollowup
