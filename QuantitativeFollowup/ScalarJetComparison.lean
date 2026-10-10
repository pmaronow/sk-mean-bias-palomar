module
public import QuantitativeFollowup.ScalarFourthJetExplicit

@[expose] public section

/-! Two temperatures and two tested measures compared on one genuine
restarted Brownian state. Every positive terminal jet is model independent. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem parisiSpatialJet_terminal_independent (beta gamma : ℝ)
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (x : ℝ) :
    parisiSpatialJet beta μ (j+1) 1 x=parisiSpatialJet gamma ν (j+1) 1 x := by
  rw [parisiSpatialJet_succ_eq_gradient_derivative,parisiSpatialJet_succ_eq_gradient_derivative]
  have hβ : (fun y=>parisiGradient beta μ (1,y))=Real.tanh :=
    funext (parisiGradient_terminal beta μ)
  have hγ : (fun y=>parisiGradient gamma ν (1,y))=Real.tanh :=
    funext (parisiGradient_terminal gamma ν)
  rw [hβ,hγ]

theorem parisiJet_difference_restart_integral (beta gamma : ℝ)
    (hb : beta≠0) (hg : gamma≠0) (μ ν : Paper.ParisiMeasure)
    (j : ℕ) (a x : ℝ) (ha : a∈Icc (0 : ℝ) 1) :
    parisiSpatialJet beta μ (j+1) a x-parisiSpatialJet gamma ν (j+1) a x=
      ∫r in (0 : ℝ)..(1-a),
        (∫ω,scalarDynkinSource (canonicalParisiRestartState beta x μ a ha.1)
          (canonicalParisiRestartDrift beta x μ a ha.1) gamma beta ν (MvPolynomial.X j) a r ω
          ∂canonicalBrownianMeasure)-
        (∫ω,scalarDynkinSource (canonicalParisiRestartState beta x μ a ha.1)
          (canonicalParisiRestartDrift beta x μ a ha.1) beta beta μ (MvPolynomial.X j) a r ω
          ∂canonicalBrownianMeasure) := by
  let X := canonicalParisiRestartState beta x μ a ha.1
  let hc := boundedDriftItoCharacteristics_canonicalParisiRestartState beta x μ a ha.1
  have hstart (b : ℝ) (ρ : Paper.ParisiMeasure) :
      scalarDynkinMoment canonicalBrownianMeasure X b ρ (MvPolynomial.X j) a 0=
        parisiSpatialJet b ρ (j+1) a x := by
    simp only [scalarDynkinMoment,scalarDynkinField_spatialJet,Real.toNNReal_zero,add_zero,
      X,canonicalParisiRestartState_zero]
    simp
  have hterm : scalarDynkinMoment canonicalBrownianMeasure X beta μ (MvPolynomial.X j) a (1-a)=
      scalarDynkinMoment canonicalBrownianMeasure X gamma ν (MvPolynomial.X j) a (1-a) := by
    unfold scalarDynkinMoment
    apply integral_congr_ae
    exact .of_forall fun ω=>by
      rw [scalarDynkinField_spatialJet,scalarDynkinField_spatialJet,add_sub_cancel]
      exact parisiSpatialJet_terminal_independent beta gamma μ ν j _
  have hβ := scalarDynkin_tail hc beta hb μ (MvPolynomial.X j) a ha
  have hγ := scalarDynkin_tail hc gamma hg ν (MvPolynomial.X j) a ha
  rw [hstart beta μ,hterm] at hβ
  rw [hstart gamma ν] at hγ
  rw [intervalIntegral.integral_sub
    (scalarDynkinSource_expected_intervalIntegrable hc gamma ν (MvPolynomial.X j) a 0 (1-a))
    (scalarDynkinSource_expected_intervalIntegrable hc beta μ (MvPolynomial.X j) a 0 (1-a))]
  linarith

theorem integral_scalarDynkinSource_restart_self_gradient (beta : ℝ)
    (μ : Paper.ParisiMeasure) (a x : ℝ) (ha : a∈Icc (0 : ℝ) 1)
    (r : ℝ) (hr : r∈Icc (0 : ℝ) (1-a)) :
    (∫ω,scalarDynkinSource (canonicalParisiRestartState beta x μ a ha.1)
      (canonicalParisiRestartDrift beta x μ a ha.1) beta beta μ (MvPolynomial.X 0) a r ω
      ∂canonicalBrownianMeasure)=0 := by
  apply integral_eq_zero_of_ae
  exact .of_forall fun ω=>by
    rw [scalarDynkinSource_spatialJet]
    have hdr := canonicalParisiRestartDrift_eq beta x μ a ha.1 r.toNNReal
      (by rw [Real.coe_toNNReal _ hr.1];linarith [hr.2,ha.1]) ω
    rw [Real.coe_toNNReal _ hr.1] at hdr
    rw [hdr]
    simp only [parisiSpatialJet_one,nonlinearJetPolynomial,Finset.Icc_eq_empty_of_lt (by norm_num : 0<1),
      Finset.sum_empty,polynomialJetField,map_zero,sub_self,zero_div,zero_mul,mul_zero,zero_add,add_zero,Pi.zero_apply]

end QuantitativeFollowup
