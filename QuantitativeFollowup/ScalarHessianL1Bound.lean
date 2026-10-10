module
public import QuantitativeFollowup.ScalarHessianL1

@[expose] public section

/-! The closed linear CDF-L¹ Hessian estimate.  No regularity or Dynkin
identity is supplied as a premise: both have been proved for the actual
Parisi solution and its actual restarted Brownian state. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000

theorem weightedHessianGap_contraction (beta : ℝ) (hb : beta≠0)
    (μ ν : Paper.ParisiMeasure) :
    weightedHessianGap beta μ ν (4*beta^2)≤
      beta^2*(15+14*FourPapersCommon.parisiGradientL1Constant beta)*
        FourPapersCommon.parisiCDFDistance μ ν+
      weightedHessianGap beta μ ν (4*beta^2)/2 := by
  let K := 4*beta^2
  let C := beta^2*(15+14*FourPapersCommon.parisiGradientL1Constant beta)
  let δ := FourPapersCommon.parisiCDFDistance μ ν
  let S := weightedHessianGap beta μ ν K
  have hb2 : 0<beta^2 := sq_pos_of_ne_zero hb
  have hK : 0<K := by dsimp only [K];positivity
  have hδ : 0≤δ := FourPapersCommon.parisiCDFDistance_nonneg μ ν
  have hC : 0≤C := by dsimp only [C,FourPapersCommon.parisiGradientL1Constant];positivity
  change S≤C*δ+S/2
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨p,rfl⟩
  let a : ℝ := p.1
  have ha : a∈Icc (0 : ℝ) 1 := p.1.property
  have hh := parisiHessian_difference_weighted_bound beta hb μ ν K hK a p.2 ha
  have hw := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-K*(1-a))).le
  have he : Real.exp (-K*(1-a))*Real.exp (K*(1-a))=1 := by
    rw [←Real.exp_add];simp
  have hratio : 2*beta^2/K=(1/2:ℝ) := by
    dsimp only [K]
    field_simp
    norm_num
  have hident :
      Real.exp (-K*(1-a))*(C*δ+(2*beta^2/K)*S*Real.exp (K*(1-a)))=
        C*δ*Real.exp (-K*(1-a))+S/2 := by
    rw [hratio]
    calc
      _=C*δ*Real.exp (-K*(1-a))+S/2*
        (Real.exp (-K*(1-a))*Real.exp (K*(1-a))) := by ring
      _=_ := by rw [he,mul_one]
  have he1 : Real.exp (-K*(1-a))≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hK.le,ha.2])
  change Real.exp (-K*(1-a))*‖parisiHessian beta μ (a,p.2)-parisiHessian beta ν (a,p.2)‖≤_
  exact hw.trans (hident.le.trans (add_le_add
    (mul_le_of_le_one_right (mul_nonneg hC hδ) he1) le_rfl))

def parisiHessianL1Constant (beta : ℝ) : ℝ :=
  2*beta^2*(15+14*FourPapersCommon.parisiGradientL1Constant beta)*Real.exp (4*beta^2)

theorem parisiHessian_CDF_L1_bound (beta : ℝ) (hb : beta≠0)
    (μ ν : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (x : ℝ) :
    ‖parisiHessian beta μ (a,x)-parisiHessian beta ν (a,x)‖≤
      parisiHessianL1Constant beta*Paper.parisiCDFDistance μ ν := by
  let K := 4*beta^2
  let C := beta^2*(15+14*FourPapersCommon.parisiGradientL1Constant beta)
  have hK : 0≤K := by dsimp only [K];positivity
  have hC : 0≤C := by dsimp only [C,FourPapersCommon.parisiGradientL1Constant];positivity
  have hδ := FourPapersCommon.parisiCDFDistance_nonneg μ ν
  have hs := weightedHessianGap_contraction beta hb μ ν
  have hS : weightedHessianGap beta μ ν K≤2*C*FourPapersCommon.parisiCDFDistance μ ν := by
    change weightedHessianGap beta μ ν K≤C*FourPapersCommon.parisiCDFDistance μ ν+
      weightedHessianGap beta μ ν K/2 at hs
    linarith
  have he : Real.exp (K*(1-a))≤Real.exp K := Real.exp_le_exp.mpr (by nlinarith [ha.1])
  apply (hessian_le_weightedHessianGap beta μ ν K hK a ha x).trans
  calc
    _≤(2*C*FourPapersCommon.parisiCDFDistance μ ν)*Real.exp K :=
      mul_le_mul hS he (Real.exp_pos _).le (by positivity)
    _=parisiHessianL1Constant beta*Paper.parisiCDFDistance μ ν := by
      simp only [parisiHessianL1Constant,C,K,FourPapersCommon.parisiCDFDistance,
        Paper.parisiCDFDistance,Real.norm_eq_abs]
      ring

end QuantitativeFollowup
