module
public import QuantitativePaper.VectorTailDyadicLimit
public import QuantitativePaper.VectorMeasurePotential

@[expose] public section

/-! Actual continuity and uniform profile/time/field estimates of the
constructed arbitrary-measure potential on the complete overlap interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 200000

theorem tendstoUniformly_vectorDyadicTailPotential {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) :
    TendstoUniformly
      (fun j => fun z : Paper.Overlap×VectorParameter n =>
        vectorDyadicTailPotential μ β t z.1 j z.2.1 z.2.2)
      (fun z => vectorMeasureTailPotential μ β t z.1 z.2.1 z.2.2) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hh : Tendsto (fun j : ℕ => (4*(n : ℝ)*((1-t)*β^2))*(1/2 : ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ)<1)).const_mul (4*(n : ℝ)*((1-t)*β^2))
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with j hj
  intro z
  rw [Real.dist_eq,abs_sub_comm]
  exact (vectorDyadicTailPotential_limit_abs_sub_le μ β t z.1 ht z.1.property j
    z.2.1 z.2.2).trans_lt hj

theorem vectorMeasureTailPotential_time_abs_sub_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t q r : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1) (hr : r∈Icc (0 : ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    |vectorMeasureTailPotential μ β t q p x-vectorMeasureTailPotential μ β t r p x| ≤
      (n : ℝ)*((1-t)*β^2)/2*|q-r| := by
  apply le_of_tendsto
    ((tendsto_vectorDyadicTailPotential μ β t q ht hq p x).sub
      (tendsto_vectorDyadicTailPotential μ β t r ht hr p x)).abs
  exact Eventually.of_forall (fun j => vectorTailRecursion_time_abs_sub_le
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t q r ht hq hr p x)

theorem vectorMeasureTailPotential_time_lipschitz {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (x : Field n) :
    LipschitzWith ((n : ℝ)*((1-t)*β^2)/2).toNNReal
      (fun q : Paper.Overlap => vectorMeasureTailPotential μ β t q p x) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [Real.dist_eq,Real.coe_toNNReal _ (by positivity)]
  exact vectorMeasureTailPotential_time_abs_sub_le μ β t q r ht q.property r.property p x

theorem vectorMeasureTailPotential_joint_lipschitz {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1) :
    LipschitzWith (vectorJointLipschitzConstant n β t)
      (fun p : VectorParameter n => vectorMeasureTailPotential μ β t q p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p z
  apply le_of_tendsto
    ((tendsto_vectorDyadicTailPotential μ β t q ht hq p.1 p.2).dist
      (tendsto_vectorDyadicTailPotential μ β t q ht hq z.1 z.2))
  apply Eventually.of_forall
  intro j
  have hh := (vectorRecursion_joint_lipschitz
    (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q hq)
      β t (vectorDyadicIndex j+3)).dist_le_mul p z
  simpa only [vectorDyadicTailPotential,
    vectorTailRecursion_eq_clamped _ β t q hq _ le_rfl] using hh

theorem continuous_vectorMeasureTailPotential {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) :
    Continuous (fun z : Paper.Overlap×VectorParameter n =>
      vectorMeasureTailPotential μ β t z.1 z.2.1 z.2.2) := by
  let f : Paper.Overlap→VectorParameter n→ℝ :=
    fun q p => vectorMeasureTailPotential μ β t q p.1 p.2
  have htime : ∀ p : VectorParameter n,
      LipschitzWith ((n : ℝ)*((1-t)*β^2)/2).toNNReal (fun q : Paper.Overlap => f q p) :=
    fun p => vectorMeasureTailPotential_time_lipschitz μ β t ht p.1 p.2
  have hjoint : ∀ q : Paper.Overlap,
      LipschitzWith (vectorJointLipschitzConstant n β t) (f q) :=
    fun q => vectorMeasureTailPotential_joint_lipschitz μ β t q ht q.property
  have hh : LipschitzWith (((n : ℝ)*((1-t)*β^2)/2).toNNReal+
      vectorJointLipschitzConstant n β t) (Function.uncurry f) :=
    LipschitzWith.uncurry htime hjoint
  exact hh.continuous

theorem vectorMeasureTailPotential_lipschitz {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1) (p : Couplings n×ℝ) :
    LipschitzWith (Real.sqrt (n : ℝ)).toNNReal (vectorMeasureTailPotential μ β t q p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto
    ((tendsto_vectorDyadicTailPotential μ β t q ht hq p x).dist
      (tendsto_vectorDyadicTailPotential μ β t q ht hq p y))
  exact Eventually.of_forall (fun j =>
    (vectorTailRecursion_lipschitz (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      β t q hq p le_rfl).dist_le_mul x y)

theorem vectorMeasureTailPotential_CDFDistance_abs_sub_le {n : ℕ}
    (μ ν : Paper.ParisiMeasure) (β t q : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    |vectorMeasureTailPotential μ β t q p x-vectorMeasureTailPotential ν β t q p x| ≤
      (n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance μ ν := by
  have hleft := ((tendsto_vectorDyadicTailPotential μ β t q ht hq p x).sub
    (tendsto_vectorDyadicTailPotential ν β t q ht hq p x)).abs
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
  exact Eventually.of_forall (fun j => vectorTailRecursion_grid_profile_abs_sub_le μ ν
    (vectorDyadicIndex j) β t q ht hq p x)

theorem tendstoUniformly_vectorMeasureTailPotential_of_CDFDistance {n : ℕ}
    {ι : Type*} {L : Filter ι} {ν : ι→Paper.ParisiMeasure} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1)
    (hν : Tendsto (fun i => Paper.parisiCDFDistance (ν i) μ) L (𝓝 0)) :
    TendstoUniformly
      (fun i => fun z : Paper.Overlap×VectorParameter n =>
        vectorMeasureTailPotential (ν i) β t z.1 z.2.1 z.2.2)
      (fun z => vectorMeasureTailPotential μ β t z.1 z.2.1 z.2.2) L := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hh := hν.const_mul ((n : ℝ)*((1-t)*β^2))
  simp only [mul_zero] at hh
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with i hi
  intro z
  rw [Real.dist_eq,abs_sub_comm]
  exact (vectorMeasureTailPotential_CDFDistance_abs_sub_le (ν i) μ β t z.1 ht
    z.1.property z.2.1 z.2.2).trans_lt hi

theorem vectorMeasureTailPotential_zero {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasureTailPotential μ β t 0 p x=vectorMeasurePotential μ β t p x := by
  apply tendsto_nhds_unique
    (tendsto_vectorDyadicTailPotential μ β t 0 ht (by constructor <;> norm_num) p x)
  simpa only [vectorDyadicTailPotential,vectorDyadicPotential,
    vectorTailRecursion_zero _ β t _ le_rfl] using tendsto_vectorDyadicPotential μ β t ht p x

theorem vectorMeasureTailPotential_one {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasureTailPotential μ β t 1 p x=vectorTerminalPotential n β t p x := by
  apply tendsto_nhds_unique
    (tendsto_vectorDyadicTailPotential μ β t 1 ht (by constructor <;> norm_num) p x)
  simpa only [vectorDyadicTailPotential,vectorTailRecursion_one _ β t _ le_rfl] using
    (tendsto_const_nhds (x:=vectorTerminalPotential n β t p x))

end QuantitativePaper
