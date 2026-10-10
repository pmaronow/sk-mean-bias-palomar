module
public import QuantitativePaper.VectorMeasureStateStability

@[expose] public section

/-! Weak/CDF-L¹ profile convergence gives uniform convergence of the actual
same-driver states, simultaneously over every sample and physical time. -/
noncomputable section
open Set Filter FourPapersCommon
open scoped Nat NNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000

theorem exists_vectorMeasureState_stability_constant (β t : ℝ) (ht : t≤1) :
    ∃ C : ℝ,0≤C ∧ ∀ μ ν : Paper.ParisiMeasure,∀ D : ℝ,0≤D→
      (∀ q p x,‖vectorMeasureGradient (n := n) μ β t q p x-
        vectorMeasureGradient ν β t q p x‖≤D)→
      ∀ r : ℝ≥0,r≤1→∀ sample : VectorDisorderBrownianSample n,
        ‖vectorMeasureState (n := n) μ β t ht r sample-vectorMeasureState (n := n) ν β t ht r sample‖≤
          C*(Real.sqrt n*Paper.parisiCDFDistance μ ν+D) := by
  let C:ℝ:=((1-t)*β^2)*Real.exp (((1-t)*β^2)*(n : ℝ))
  refine ⟨C,mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)) (Real.exp_pos _).le,?_⟩
  intro μ ν D hD hgrad r hr sample
  exact norm_vectorMeasureState_sub_le μ ν β t ht D hD hgrad r hr sample

theorem tendstoUniformlyOn_vectorMeasureState_of_CDFDistance
    {ι : Type*} {L : Filter ι} {ν : ι→Paper.ParisiMeasure} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1)
    (hD : Tendsto (fun i=>Paper.parisiCDFDistance (ν i) μ) L (𝓝 0)) :
    TendstoUniformlyOn (fun i=>fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      vectorMeasureState (n := n) (ν i) β t ht z.1 z.2)
      (fun z=>vectorMeasureState (n := n) μ β t ht z.1 z.2) L (Icc (0 : ℝ≥0) 1 ×ˢ univ) := by
  obtain ⟨C,hC,hbound⟩:=exists_vectorMeasureState_stability_constant (n := n) β t ht
  let K:ℝ:=2*((n : ℝ)*((1-t)*β^2)+(n : ℝ))
  have hK : 0≤K := by dsimp only [K];positivity
  have hh : Tendsto (fun i=>C*(Real.sqrt n*Paper.parisiCDFDistance (ν i) μ+
      K*Real.sqrt (Paper.parisiCDFDistance (ν i) μ))) L (𝓝 0) := by
    simpa only [mul_zero,add_zero,Real.sqrt_zero] using
      ((hD.const_mul (Real.sqrt n)).add (hD.sqrt.const_mul K)).const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with i hi
  intro z hz
  rw [dist_comm,dist_eq_norm]
  apply lt_of_le_of_lt (hbound (ν i) μ (K*Real.sqrt (Paper.parisiCDFDistance (ν i) μ))
    (mul_nonneg hK (Real.sqrt_nonneg _)) (fun q p x=>by
      simpa only [←dist_eq_norm,K] using
        vectorMeasureGradient_CDFDistance_dist_le (n := n) (ν i) μ β t ht q p x) z.1 hz.1.2 z.2) hi

theorem tendstoUniformlyOn_vectorMeasureState_of_weak
    {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {ν : ι→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (β t : ℝ) (ht : t≤1)
    (hν : Tendsto ν L (𝓝 μ)) :
    TendstoUniformlyOn (fun i=>fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      vectorMeasureState (n := n) (ν i) β t ht z.1 z.2)
      (fun z=>vectorMeasureState (n := n) μ β t ht z.1 z.2) L (Icc (0 : ℝ≥0) 1 ×ˢ univ) :=
  tendstoUniformlyOn_vectorMeasureState_of_CDFDistance μ β t ht
    (FRSB.tendsto_parisiCDFDistance_of_tendsto hν)

end QuantitativePaper
