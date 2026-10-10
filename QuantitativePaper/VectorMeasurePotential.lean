module
public import QuantitativePaper.VectorDyadicLimit
public import QuantitativePaper.VectorSmooth

@[expose] public section

/-! Continuity, genuine integrability, and profile stability of the
constructed arbitrary-measure vector potential at overlap zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem tendstoUniformly_vectorDyadicPotential {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) :
    TendstoUniformly
      (fun j => fun p : VectorParameter n => vectorDyadicPotential μ β t j p.1 p.2)
      (fun p => vectorMeasurePotential μ β t p.1 p.2) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hh : Tendsto (fun j : ℕ => (4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1)).const_mul
        (4*(n : ℝ)*((1-t)*β^2))
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with j hj
  intro p
  rw [Real.dist_eq,abs_sub_comm]
  exact (vectorDyadicPotential_limit_abs_sub_le μ β t ht j p.1 p.2).trans_lt hj

theorem continuous_vectorMeasurePotential_joint {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) :
    Continuous (fun p : VectorParameter n => vectorMeasurePotential μ β t p.1 p.2) := by
  apply (tendstoUniformly_vectorDyadicPotential μ β t ht).continuous
  apply Eventually.frequently
  exact Eventually.of_forall (fun j => (contDiff_vectorRecursion_joint
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t (vectorDyadicIndex j+3)).continuous)

theorem vectorMeasurePotential_CDFDistance_abs_sub_le {n : ℕ}
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (p : Couplings n×ℝ) (x : Field n) :
    |vectorMeasurePotential μ β t p x-vectorMeasurePotential ν β t p x| ≤
      (n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance μ ν := by
  have hleft := ((tendsto_vectorDyadicPotential μ β t ht p x).sub
    (tendsto_vectorDyadicPotential ν β t ht p x)).abs
  have herr : Tendsto (fun j : ℕ => (2 : ℝ)/(vectorDyadicIndex j+1 : ℕ)) atTop (𝓝 0) := by
    simp only [vectorDyadicIndex_add_one,Nat.cast_pow,Nat.cast_ofNat]
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ)<1)).const_mul (2 : ℝ)
    convert hh using 1
    · funext j
      rw [div_pow,one_pow]
      ring
    · simp
  have hright := ((tendsto_const_nhds (x:=Paper.parisiCDFDistance μ ν)).add herr).const_mul
    ((n : ℝ)*((1-t)*β^2))
  apply le_of_tendsto_of_tendsto hleft (by simpa only [add_zero] using hright)
  exact Eventually.of_forall (fun j => vectorRecursion_grid_profile_abs_sub_le μ ν
    (vectorDyadicIndex j) β t ht p x)

theorem vectorMeasurePotential_lipschitz {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) :
    LipschitzWith (Real.sqrt (n : ℝ)).toNNReal (vectorMeasurePotential μ β t p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto
    ((tendsto_vectorDyadicPotential μ β t ht p x).dist (tendsto_vectorDyadicPotential μ β t ht p y))
  exact Eventually.of_forall (fun j =>
    (vectorRecursion_lipschitz (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t p
      (vectorDyadicIndex j+3)).dist_le_mul x y)

theorem vectorMeasurePotential_disorder_bound {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (x : Field n) :
    |vectorMeasurePotential μ β t p x-vectorMeasurePotential μ β t (0,0) x| ≤
      vectorDisorderEnvelope n β t p := by
  have hseq : Tendsto (fun j : ℕ => |vectorDyadicPotential μ β t j p x-
      vectorDyadicPotential μ β t j (0,0) x|) atTop
      (𝓝 |vectorMeasurePotential μ β t p x-vectorMeasurePotential μ β t (0,0) x|) :=
    ((tendsto_vectorDyadicPotential μ β t ht p x).sub
      (tendsto_vectorDyadicPotential μ β t ht (0,0) x)).abs
  have hb : ∀j,|vectorDyadicPotential μ β t j p x-vectorDyadicPotential μ β t j (0,0) x| ≤
      vectorDisorderEnvelope n β t p := by
    intro j
    simpa only [vectorDyadicPotential] using vectorRecursion_disorder_bound (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t p (vectorDyadicIndex j+3) x
  exact le_of_tendsto hseq (Eventually.of_forall hb)

theorem integrable_exp_vectorMeasurePotential {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (a : ℝ) (x : Field n) :
    Integrable (fun p => Real.exp (a*vectorMeasurePotential μ β t p x)) (completionLaw n) := by
  have hmeas : Measurable (fun p : Couplings n×ℝ => vectorMeasurePotential μ β t p x) :=
    by
      have hg : Measurable (fun p : Couplings n×ℝ => ((p,x) : VectorParameter n)) :=
        measurable_id.prodMk measurable_const
      have hh : Measurable ((fun q : VectorParameter n => vectorMeasurePotential μ β t q.1 q.2) ∘
          (fun p : Couplings n×ℝ => ((p,x) : VectorParameter n))) :=
        (continuous_vectorMeasurePotential_joint μ β t ht).measurable.comp hg
      simpa only [Function.comp_def] using hh
  apply ((integrable_exp_vectorDisorderEnvelope n β t |a| (abs_nonneg _)).const_mul
    (Real.exp (|a| * |vectorMeasurePotential μ β t (0,0) x|))).mono'
    (Real.measurable_exp.comp (measurable_const.mul hmeas)).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  dsimp only [Function.comp_apply,Pi.mul_apply]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hbound := vectorMeasurePotential_disorder_bound μ β t ht p x
  have habs : |vectorMeasurePotential μ β t p x| ≤
      |vectorMeasurePotential μ β t (0,0) x|+vectorDisorderEnvelope n β t p := by
    have hh := abs_add_le (vectorMeasurePotential μ β t (0,0) x)
      (vectorMeasurePotential μ β t p x-vectorMeasurePotential μ β t (0,0) x)
    rw [add_sub_cancel] at hh
    linarith
  calc
    _ ≤ |a| * |vectorMeasurePotential μ β t p x| := by rw [←abs_mul];exact le_abs_self _
    _ ≤ |a| * (|vectorMeasurePotential μ β t (0,0) x|+vectorDisorderEnvelope n β t p) :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = _ := by ring

theorem vectorMeasurePotential_one {n : ℕ} (μ : Paper.ParisiMeasure) (β : ℝ)
    (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasurePotential μ β 1 p x=vectorTerminalPotential n β 1 p x := by
  apply tendsto_nhds_unique (tendsto_vectorDyadicPotential μ β 1 le_rfl p x)
  simpa only [vectorDyadicPotential,vectorRecursion_one_time] using
    (tendsto_const_nhds (x:=vectorTerminalPotential n β 1 p x))

end QuantitativePaper
