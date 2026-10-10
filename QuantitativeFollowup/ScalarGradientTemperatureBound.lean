module
public import QuantitativeFollowup.ScalarGradientTemperature

@[expose] public section

/-! Closed linear temperature-square gradient continuity. -/
noncomputable section
open Set Paper
open scoped NNReal Topology BoundedContinuousFunction
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000

theorem weightedGradientTemperatureGap_contraction (beta gamma : ℝ)
    (hb : beta≠0) (hg : gamma≠0) (μ : Paper.ParisiMeasure) :
    weightedGradientTemperatureGap beta gamma μ (2*beta^2)≤8*|beta^2-gamma^2|+
      weightedGradientTemperatureGap beta gamma μ (2*beta^2)/2 := by
  let K := 2*beta^2
  let S := weightedGradientTemperatureGap beta gamma μ K
  have hb2 : 0<beta^2 := sq_pos_of_ne_zero hb
  have hK : 0<K := by dsimp only [K];positivity
  change S≤8*|beta^2-gamma^2|+S/2
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨p,rfl⟩
  let a : ℝ := p.1
  have ha : a∈Icc (0 : ℝ) 1 := p.1.property
  have hh := gradient_temperature_weighted_restart_bound beta gamma hb hg μ K hK a p.2 ha
  have hw := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-K*(1-a))).le
  have he : Real.exp (-K*(1-a))*Real.exp (K*(1-a))=1 := by rw [←Real.exp_add];simp
  have hratio : beta^2/K=(1/2:ℝ) := by dsimp only [K];field_simp
  have hident : Real.exp (-K*(1-a))*(8*|beta^2-gamma^2|+(beta^2/K)*S*Real.exp (K*(1-a)))=
      8*|beta^2-gamma^2| *Real.exp (-K*(1-a))+S/2 := by
    rw [hratio]
    calc
      _=8*|beta^2-gamma^2| *Real.exp (-K*(1-a))+S/2*
        (Real.exp (-K*(1-a))*Real.exp (K*(1-a))) := by ring
      _=_ := by rw [he,mul_one]
  have he1 : Real.exp (-K*(1-a))≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hK.le,ha.2])
  change Real.exp (-K*(1-a))*‖parisiGradient beta μ (a,p.2)-parisiGradient gamma μ (a,p.2)‖≤_
  exact hw.trans (hident.le.trans (add_le_add
    (mul_le_of_le_one_right (by positivity) he1) le_rfl))

def scalarGradientTemperatureConstant (beta : ℝ) : ℝ := 16*Real.exp (2*beta^2)

theorem parisiGradient_temperature_square_bound (beta gamma : ℝ)
    (hb : beta≠0) (hg : gamma≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (x : ℝ) :
    ‖parisiGradient beta μ (a,x)-parisiGradient gamma μ (a,x)‖≤
      scalarGradientTemperatureConstant beta*|beta^2-gamma^2| := by
  let K := 2*beta^2
  have hK : 0≤K := by dsimp only [K];positivity
  have hs := weightedGradientTemperatureGap_contraction beta gamma hb hg μ
  have hS : weightedGradientTemperatureGap beta gamma μ K≤16*|beta^2-gamma^2| := by
    change weightedGradientTemperatureGap beta gamma μ K≤8*|beta^2-gamma^2|+
      weightedGradientTemperatureGap beta gamma μ K/2 at hs
    linarith
  have he : Real.exp (K*(1-a))≤Real.exp K := Real.exp_le_exp.mpr (by nlinarith [ha.1])
  exact (gradient_le_weightedTemperatureGap beta gamma μ K hK a ha x).trans
    (by
      convert mul_le_mul hS he (Real.exp_pos _).le (by positivity) using 1
      dsimp only [scalarGradientTemperatureConstant,K]
      ring)

theorem parisiGradientBCF_temperature_square_bound (beta gamma : ℝ)
    (hb : beta≠0) (hg : gamma≠0) (μ : Paper.ParisiMeasure) :
    ‖parisiGradientBCF beta μ-parisiGradientBCF gamma μ‖≤
      scalarGradientTemperatureConstant beta*|beta^2-gamma^2| := by
  apply (BoundedContinuousFunction.norm_le (by unfold scalarGradientTemperatureConstant;positivity)).mpr
  intro p
  simp only [BoundedContinuousFunction.sub_apply,parisiGradientBCF_apply]
  exact parisiGradient_temperature_square_bound beta gamma hb hg μ p.1 p.1.property p.2

end QuantitativeFollowup
