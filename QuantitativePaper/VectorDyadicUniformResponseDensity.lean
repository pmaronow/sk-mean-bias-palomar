module
public import QuantitativePaper.VectorDyadicTiltConvergence
public import QuantitativePaper.VectorDyadicGridLawAgreement

@[expose] public section

/-! Total-variation density convergence of the actual nested grid disorder
tilts on their common Gaussian/Wiener probability space. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem integrable_vectorMeasureOuterWeight (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) : Integrable (vectorMeasureOuterWeight (n := n) μ β t a) (completionLaw n) :=
  (integrable_exp_vectorMeasurePotential μ β t ht a 0).div_const _

theorem integral_vectorMeasureDisorderTilt_eq_weighted (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (F : VectorDisorderBrownianSample n → ℝ) :
    (∫ sample, F sample ∂vectorMeasureDisorderTilt μ β t a) =
      ∫ sample, vectorMeasureOuterWeight μ β t a sample.1 * F sample
        ∂vectorDisorderBrownianMeasure n := by
  rw [integral_vectorMeasureDisorderTilt μ β t a ht]
  unfold vectorMeasureOuterWeight
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]

theorem tendsto_vectorDyadicOuterWeight (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (p : Couplings n × ℝ) :
    Tendsto (fun j => vectorMeasureOuterWeight (n := n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a p) atTop
      (𝓝 (vectorMeasureOuterWeight μ β t a p)) := by
  simp_rw [vectorMeasureOuterWeight_grid_eq_finite μ _ β t a ht]
  unfold vectorOuterWeight vectorMeasureOuterWeight
  have hpot := (tendsto_vectorDyadicPotential μ β t ht p 0).const_mul a
  have hp := (Real.continuous_exp.tendsto _).comp hpot
  exact hp.div (tendsto_vectorDyadicOuterPartition μ β t a ht)
    (vectorMeasureOuterPartition_pos μ β t a ht).ne'

theorem tendsto_integral_vectorDyadicOuterWeight_abs_sub (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) :
    Tendsto (fun j => ∫ sample : VectorDisorderBrownianSample n,
      |vectorMeasureOuterWeight (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a sample.1 -
        vectorMeasureOuterWeight μ β t a sample.1| ∂vectorDisorderBrownianMeasure n)
      atTop (𝓝 0) := by
  let Z := vectorMeasureOuterPartition (n := n) μ β t a
  have hZ : 0 < Z := vectorMeasureOuterPartition_pos μ β t a ht
  let B := fun sample : VectorDisorderBrownianSample n =>
    (2*Real.exp |a| /Z+1/Z)*Real.exp (a*vectorMeasurePotential μ β t sample.1 0)
  have hε : Tendsto (fun j : ℕ => (4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).const_mul (4*(n : ℝ)*((1-t)*β^2))
  have hz := (tendsto_vectorDyadicOuterPartition (n := n) μ β t a ht).eventually
    (lt_mem_nhds (show Z/2 < Z by linarith))
  have he := hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hconv : Tendsto (fun j => ∫ sample : VectorDisorderBrownianSample n,
      |vectorMeasureOuterWeight (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a sample.1 -
        vectorMeasureOuterWeight μ β t a sample.1| ∂vectorDisorderBrownianMeasure n)
      atTop (𝓝 (∫ _sample : VectorDisorderBrownianSample n, (0 : ℝ) ∂vectorDisorderBrownianMeasure n)) := by
    apply tendsto_integral_filter_of_dominated_convergence B
    · exact .of_forall fun j => (((measurable_vectorMeasureOuterWeight _ β t a ht).comp measurable_fst).sub
        ((measurable_vectorMeasureOuterWeight μ β t a ht).comp measurable_fst)).abs.aestronglyMeasurable
    · filter_upwards [hz,he] with j hj hεj
      exact .of_forall fun sample => by
        have hpot : a*vectorDyadicPotential μ β t j sample.1 0 ≤
            |a|+a*vectorMeasurePotential μ β t sample.1 0 := by
          have hb := vectorDyadicPotential_limit_abs_sub_le μ β t ht j sample.1 0
          have hmul : a*(vectorDyadicPotential μ β t j sample.1 0-vectorMeasurePotential μ β t sample.1 0)
              ≤ |a| *((4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j) := by
            exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg a))
          have hm := mul_le_mul_of_nonneg_left hεj.le (abs_nonneg a)
          linarith
        have hnum := Real.exp_le_exp.mpr hpot
        rw [Real.exp_add] at hnum
        have hden : 0 < vectorOuterPartition (n := n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a :=
          vectorOuterPartition_pos _ β t a
        have hfrac : Real.exp (a*vectorDyadicPotential μ β t j sample.1 0)/
            vectorOuterPartition (n := n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ≤
            2*Real.exp |a| /Z*Real.exp (a*vectorMeasurePotential μ β t sample.1 0) := by
          calc
            _ ≤ Real.exp (a*vectorDyadicPotential μ β t j sample.1 0)/(Z/2) :=
              div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hj.le
            _ ≤ (Real.exp |a| *Real.exp (a*vectorMeasurePotential μ β t sample.1 0))/(Z/2) :=
              div_le_div_of_nonneg_right hnum (by positivity)
            _ = _ := by ring
        rw [Real.norm_eq_abs,abs_abs]
        calc
          _ ≤ |vectorMeasureOuterWeight (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a sample.1|+
              |vectorMeasureOuterWeight μ β t a sample.1| := abs_sub _ _
          _ ≤ B sample := by
            rw [vectorMeasureOuterWeight_grid_eq_finite μ j β t a ht]
            unfold vectorOuterWeight vectorMeasureOuterWeight
            rw [abs_of_pos (div_pos (Real.exp_pos _) hden),abs_of_pos (div_pos (Real.exp_pos _) hZ)]
            change Real.exp (a*vectorDyadicPotential μ β t j sample.1 0)/_ +
              Real.exp (a*vectorMeasurePotential μ β t sample.1 0)/Z ≤ B sample
            calc
              _ ≤ 2*Real.exp |a| /Z*Real.exp (a*vectorMeasurePotential μ β t sample.1 0)+
                  Real.exp (a*vectorMeasurePotential μ β t sample.1 0)/Z := by gcongr
              _ = B sample := by dsimp only [B]; ring
    · exact ((integrable_exp_vectorMeasurePotential μ β t ht a 0).comp_fst
        (vectorBrownianMeasure n)).const_mul _
    · exact .of_forall fun sample => by
        simpa only [sub_self,abs_zero] using
          ((tendsto_vectorDyadicOuterWeight μ β t a ht sample.1).sub_const
            (vectorMeasureOuterWeight μ β t a sample.1)).abs
  simpa only [integral_zero] using hconv

end QuantitativePaper
