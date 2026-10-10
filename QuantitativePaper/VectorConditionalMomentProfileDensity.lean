module
public import QuantitativePaper.VectorConditionalMomentProfileContinuityCore

@[expose] public section

/-! Actual normalized disorder weights converge in fixed-base L² under
weak profile convergence. The normalizers and local Gaussian dominator
are constructed, rather than supplied as convergence hypotheses. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n:ℕ} {J:Type*} {l:Filter J} [l.IsCountablyGenerated]
variable {ν:J→Paper.ParisiMeasure} {μ:Paper.ParisiMeasure}

theorem vectorProfileExponentialDominator_bound (β t a:ℝ) (ht:t<1)
    (hν:Tendsto ν l (𝓝 μ)) :
    ∀ᶠj in l,∀p:Couplings n×ℝ,‖Real.exp (a*vectorMeasurePotential (ν j) β t p 0)‖≤
      vectorTemperatureExponentialDominator μ β a ⟨t,ht⟩ p:=by
  filter_upwards [vectorMeasurePotential_profile_local_bound (n:=n) β t ht hν] with j hj
  intro p
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hj p) (abs_nonneg a))

theorem tendsto_vectorMeasureOuterPartition_of_weak (β t a:ℝ) (ht:t<1)
    (hν:Tendsto ν l (𝓝 μ)) :
    Tendsto (fun j=>vectorMeasureOuterPartition (n:=n) (ν j) β t a) l
      (𝓝 (vectorMeasureOuterPartition (n:=n) μ β t a)):=by
  exact tendsto_integral_filter_of_dominated_convergence
    (vectorTemperatureExponentialDominator (n:=n) μ β a ⟨t,ht⟩)
    (.of_forall fun j=>(integrable_exp_vectorMeasurePotential (n:=n) (ν j) β t ht.le a 0).aestronglyMeasurable)
    ((vectorProfileExponentialDominator_bound (n:=n) β t a ht hν).mono fun j hj=>.of_forall hj)
    (integrable_vectorTemperatureExponentialDominator μ β a ⟨t,ht⟩)
    (.of_forall fun p=>(Real.continuous_exp.tendsto _).comp
      ((tendsto_vectorMeasurePotential_of_weak β t ht.le hν p 0).const_mul a))

theorem tendsto_vectorMeasureOuterWeight_of_weak (β t a:ℝ) (ht:t<1)
    (hν:Tendsto ν l (𝓝 μ)) (p:Couplings n×ℝ) :
    Tendsto (fun j=>vectorMeasureOuterWeight (ν j) β t a p) l
      (𝓝 (vectorMeasureOuterWeight μ β t a p)):=
  ((Real.continuous_exp.tendsto _).comp
    ((tendsto_vectorMeasurePotential_of_weak β t ht.le hν p 0).const_mul a)).div
    (tendsto_vectorMeasureOuterPartition_of_weak β t a ht hν)
    (vectorMeasureOuterPartition_pos μ β t a ht.le).ne'

theorem vectorBaseOuterWeight_profile_local_domination (β t a:ℝ) (ht:t<1)
    (hν:Tendsto ν l (𝓝 μ)) :
    ∃D:VectorDisorderBrownianSample n→ℝ,MemLp D 2 (vectorDisorderBrownianMeasure n)∧
      (∀ᶠj in l,∀sample,‖vectorBaseOuterWeight (ν j) β t a sample‖≤D sample)∧
      (∀sample,‖vectorBaseOuterWeight μ β t a sample‖≤D sample):=by
  let Z:=vectorMeasureOuterPartition (n:=n) μ β t a
  have hZ:0<Z:=vectorMeasureOuterPartition_pos μ β t a ht.le
  let D:VectorDisorderBrownianSample n→ℝ:=fun sample=>
    (2/Z)*vectorTemperatureExponentialDominator μ β a ⟨t,ht⟩ sample.1+‖vectorBaseOuterWeight μ β t a sample‖
  have hD:MemLp D 2 (vectorDisorderBrownianMeasure n):=by
    exact (((hasLaw_initialVectorDisorder n).memLp_comp
      (memLp_vectorTemperatureExponentialDominator μ β a ⟨t,ht⟩)).const_mul (2/Z)).add
      (memLp_vectorBaseOuterWeight μ β t a ht.le).norm
  have hz:∀ᶠj in l,Z/2<vectorMeasureOuterPartition (n:=n) (ν j) β t a:=
    (tendsto_vectorMeasureOuterPartition_of_weak β t a ht hν).eventually
      (lt_mem_nhds (by dsimp only [Z] at hZ ⊢;linarith))
  refine ⟨D,hD,?_,?_⟩
  · filter_upwards [vectorProfileExponentialDominator_bound (n:=n) β t a ht hν,hz] with j hj hzj
    intro sample
    have he:Real.exp (a*vectorMeasurePotential (ν j) β t sample.1 0)≤
        vectorTemperatureExponentialDominator μ β a ⟨t,ht⟩ sample.1:=by
      simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hj sample.1
    change ‖Real.exp (a*vectorMeasurePotential (ν j) β t sample.1 0)/vectorMeasureOuterPartition (ν j) β t a‖≤_
    rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le
      (vectorMeasureOuterPartition_pos (ν j) β t a ht.le).le)]
    calc
      _≤Real.exp (a*vectorMeasurePotential (ν j) β t sample.1 0)/(Z/2):=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hzj.le
      _≤vectorTemperatureExponentialDominator μ β a ⟨t,ht⟩ sample.1/(Z/2):=
        div_le_div_of_nonneg_right he (by positivity)
      _=(2/Z)*vectorTemperatureExponentialDominator μ β a ⟨t,ht⟩ sample.1:=by ring
      _≤D sample:=le_add_of_nonneg_right (norm_nonneg _)
  · intro sample
    exact le_add_of_nonneg_left (by
      change 0≤(2/Z)*Real.exp _
      positivity)

theorem tendsto_vectorBaseOuterWeight_toLp_of_weak (β t a:ℝ) (ht:t<1)
    (hν:Tendsto ν l (𝓝 μ)) :
    Tendsto (fun j=>(memLp_vectorBaseOuterWeight (n:=n) (ν j) β t a ht.le).toLp
      (vectorBaseOuterWeight (ν j) β t a)) l
      (𝓝 ((memLp_vectorBaseOuterWeight (n:=n) μ β t a ht.le).toLp
        (vectorBaseOuterWeight μ β t a))):=by
  obtain ⟨D,hD,hj,h0⟩:=vectorBaseOuterWeight_profile_local_domination (n:=n) β t a ht hν
  exact temperatureDensity_toLp_tendsto_of_dominated
    (fun j=>vectorBaseOuterWeight (ν j) β t a) (vectorBaseOuterWeight μ β t a)
    (fun j=>memLp_vectorBaseOuterWeight (ν j) β t a ht.le)
    (memLp_vectorBaseOuterWeight μ β t a ht.le) D hD.integrable_sq
    (hj.mono fun j hj=>.of_forall hj) (.of_forall h0)
    (.of_forall fun sample=>tendsto_vectorMeasureOuterWeight_of_weak β t a ht hν sample.1)

end QuantitativePaper
