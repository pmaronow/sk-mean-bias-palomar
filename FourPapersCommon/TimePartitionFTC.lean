module
public import FourPapersCommon.BoundedRiemannExpectation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Actual fundamental-theorem-of-calculus identities for right-endpoint
spatial states in time partitions. The data contain only time/spatial
regularity, not a supplied partition limit or stochastic formula. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped BigOperators NNReal Topology
namespace FourPapersCommon
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

structure TimeFTCData (Ω E : Type*) [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (T : ℝ≥0) where
  f : ℝ → Ω → E → ℝ
  ft : ℝ → Ω → E → ℝ
  f_measurable : Measurable (fun p : ℝ × (Ω × E) => f p.1 p.2.1 p.2.2)
  ft_measurable : Measurable (fun p : ℝ × (Ω × E) => ft p.1 p.2.1 p.2.2)
  f_continuous : ∀ sample x,ContinuousOn (fun r => f r sample x) (Icc 0 T)
  derivative : ∀ sample x r,r ∈ Ioo 0 (T : ℝ) → HasDerivAt (fun s => f s sample x) (ft r sample x) r
  ft_continuous : ∀ sample,Continuous (fun p : ℝ × E => ft p.1 sample p.2)
  bound : ℝ≥0
  spatialLip : ℝ≥0
  ft_bound : ∀ r ∈ Icc 0 (T : ℝ),∀ sample x,‖ft r sample x‖ ≤ bound
  ft_lipschitz : ∀ r ∈ Icc 0 (T : ℝ),∀ sample,LipschitzWith spatialLip (ft r sample)

variable {T : ℝ≥0}

theorem TimeFTCData.increment_eq_integral (d : TimeFTCData Ω E T)
    (a b : ℝ≥0) (hab : a ≤ b) (hb : b ≤ T) (sample : Ω) (x : E) :
    d.f b sample x-d.f a sample x =
      ∫ s in Ioc a b,d.ft s sample x ∂nonnegativeLebesgueMeasure := by
  have ha : 0 ≤ (a : ℝ) := a.coe_nonneg
  have hsub : Icc (a : ℝ) (b : ℝ) ⊆ Icc (0 : ℝ) T := by
    intro r hr
    exact ⟨ha.trans hr.1,hr.2.trans (show (b : ℝ) ≤ T from hb)⟩
  have hi : IntervalIntegrable (fun r => d.ft r sample x) volume a b :=
    ((d.ft_continuous sample).comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (a : ℝ) ≤ b from hab) ((d.f_continuous sample x).mono hsub)
    (fun r hr => d.derivative sample x r
      ⟨lt_of_le_of_lt ha hr.1,hr.2.trans_le (show (b : ℝ) ≤ T from hb)⟩) hi
  have hp : MeasurePreserving ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Ioc a b))
      (volume.restrict (Ioc (a : ℝ) (b : ℝ))) := by
    have he : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) := measurableEmbedding_nnrealCoe_iterated
    have hpre : ((↑) : ℝ≥0 → ℝ) ⁻¹' Ioc (a : ℝ) (b : ℝ) = Ioc a b := by
      ext s
      simp only [mem_preimage,mem_Ioc]
      norm_cast
    refine ⟨NNReal.continuous_coe.measurable,?_⟩
    rw [← hpre,← he.restrict_map]
    change (Measure.map ((↑) : ℝ≥0 → ℝ)
      (Measure.comap ((↑) : ℝ≥0 → ℝ) volume)).restrict (Ioc (a : ℝ) (b : ℝ)) = _
    rw [he.map_comap,NNReal.range_coe,Measure.restrict_restrict measurableSet_Ioc]
    congr 1
    ext s
    simp only [mem_inter_iff,mem_Ioc,mem_Ici]
    constructor
    · exact fun h=>h.1
    · exact fun h=>⟨h,ha.trans h.1.le⟩
  have hchange := hp.integral_comp measurableEmbedding_nnrealCoe_iterated
    (fun r : ℝ => d.ft r sample x)
  rw [← hf,intervalIntegral.integral_of_le (show (a : ℝ) ≤ b from hab)]
  exact hchange.symm

def timeRightPartitionSum (d : TimeFTCData Ω E T) (X : ℝ≥0 → Ω → E)
    (Z : Ω → ℝ) (N : ℕ) (sample : Ω) : ℝ :=
  ∑ j∈Finset.range N,Z sample*(d.f (uniformPartitionTime T N (j+1)) sample
    (X (uniformPartitionTime T N (j+1)) sample)-
    d.f (uniformPartitionTime T N j) sample (X (uniformPartitionTime T N (j+1)) sample))

end FourPapersCommon
