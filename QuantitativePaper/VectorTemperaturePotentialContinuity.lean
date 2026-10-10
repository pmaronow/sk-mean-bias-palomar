module
public import QuantitativePaper.VectorTemperatureFiniteContinuity
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

/-! Joint physical-temperature/field continuity of the actual arbitrary
profile potential, by locally uniform convergence of genuine finite potentials. -/
noncomputable section
open MeasureTheory Set Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem tendstoUniformlyOn_vectorDyadicTailPotential_temperature_slab
    (μ : Paper.ParisiMeasure) (β a : ℝ) (ha : a ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) :
    TendstoUniformlyOn (fun j (z : ℝ × Field n) => vectorDyadicTailPotential μ β z.1 q j p z.2)
      (fun z => vectorMeasureTailPotential μ β z.1 q p z.2) atTop (Icc a 1 ×ˢ univ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he : Tendsto (fun j : ℕ => (4*(n : ℝ)*((1-a)*β^2))*(1/2 : ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).const_mul (4*(n : ℝ)*((1-a)*β^2))
  filter_upwards [he.eventually (gt_mem_nhds hε)] with j hj
  intro z hz
  rw [Real.dist_eq,abs_sub_comm]
  have hb := vectorDyadicTailPotential_limit_abs_sub_le μ β z.1 q hz.1.2 q.property j p z.2
  apply hb.trans_lt
  apply lt_of_le_of_lt _ hj
  gcongr
  exact hz.1.1

theorem continuousOn_vectorMeasureTailPotential_temperature_slab
    (μ : Paper.ParisiMeasure) (β a : ℝ) (ha : a ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) :
    ContinuousOn (fun z : ℝ × Field n => vectorMeasureTailPotential μ β z.1 q p z.2)
      (Icc a 1 ×ˢ univ) :=
  (tendstoUniformlyOn_vectorDyadicTailPotential_temperature_slab μ β a ha q p).continuousOn
    (.of_forall fun j => (continuous_vectorDyadicTailPotential_temperature_field μ β q j p).continuousOn)

theorem continuousOn_vectorMeasureTailPotential_temperature_field
    (μ : Paper.ParisiMeasure) (β : ℝ) (q : Paper.Overlap) (p : Couplings n × ℝ) :
    ContinuousOn (fun z : ℝ × Field n => vectorMeasureTailPotential μ β z.1 q p z.2)
      (Iio 1 ×ˢ univ) := by
  apply continuousOn_of_forall_continuousAt
  intro z hz
  have ht : z.1 < 1 := hz.1
  exact (continuousOn_vectorMeasureTailPotential_temperature_slab μ β (z.1-1)
    (by linarith) q p).continuousAt
    (prod_mem_nhds (Icc_mem_nhds (by linarith) ht) univ_mem)

theorem continuous_vectorMeasureTailPotential_temperature_field
    (μ : Paper.ParisiMeasure) (β : ℝ) (q : Paper.Overlap) (p : Couplings n × ℝ) :
    Continuous (fun z : Iio (1 : ℝ) × Field n => vectorMeasureTailPotential μ β z.1 q p z.2) := by
  apply ContinuousOn.comp_continuous (continuousOn_vectorMeasureTailPotential_temperature_field μ β q p)
    (continuous_subtype_val.prodMap continuous_id)
  intro z
  exact ⟨z.1.property,mem_univ _⟩

end QuantitativePaper
