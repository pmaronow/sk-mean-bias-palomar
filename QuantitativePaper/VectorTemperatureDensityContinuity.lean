module
public import QuantitativePaper.VectorTemperatureDensityCore

@[expose] public section

/-! Actual normalized initial-disorder densities vary continuously in
physical temperature, pointwise and in fixed-base L². The local Gaussian
envelope and normalizing-partition convergence are proved here. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped Topology NNReal ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorTemperatureExponentialDominator (μ:Paper.ParisiMeasure) (β a:ℝ)
    (t:Iio (1:ℝ)) (p:Couplings n×ℝ):ℝ:=
  Real.exp (|a| *((|vectorMeasurePotential (n:=n) μ β t (0,0) 0|+1)+
    vectorDisorderNormConstant n β 1*‖p‖))

theorem integrable_vectorTemperatureExponentialDominator (μ:Paper.ParisiMeasure) (β a:ℝ)
    (t:Iio (1:ℝ)) : Integrable (vectorTemperatureExponentialDominator (n:=n) μ β a t) (completionLaw n):=by
  have he:(vectorTemperatureExponentialDominator (n:=n) μ β a t)=fun p=>
      Real.exp (|a| *(|vectorMeasurePotential (n:=n) μ β t (0,0) 0|+1))*
        Real.exp ((|a| *vectorDisorderNormConstant n β 1)*‖p‖):=by
    funext p
    unfold vectorTemperatureExponentialDominator
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (integrable_exp_completion_norm n (|a| *vectorDisorderNormConstant n β 1)).const_mul _

theorem memLp_vectorTemperatureExponentialDominator (μ:Paper.ParisiMeasure) (β a:ℝ)
    (t:Iio (1:ℝ)) : MemLp (vectorTemperatureExponentialDominator (n:=n) μ β a t) 2 (completionLaw n):=by
  have hm:Measurable (vectorTemperatureExponentialDominator (n:=n) μ β a t):=by
    unfold vectorTemperatureExponentialDominator
    fun_prop
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  convert integrable_vectorTemperatureExponentialDominator (n:=n) μ β (2*a) t using 1
  funext p
  unfold vectorTemperatureExponentialDominator
  rw [←Real.exp_nat_mul,abs_mul]
  norm_num
  ring

theorem vectorTemperatureExponentialDominator_bound (μ:Paper.ParisiMeasure) (β a:ℝ)
    (t:Iio (1:ℝ)) :
    ∀ᶠu:Iio (1:ℝ) in 𝓝 t,∀p:Couplings n×ℝ,
      ‖Real.exp (a*vectorMeasurePotential μ β u p 0)‖≤vectorTemperatureExponentialDominator μ β a t p:=by
  filter_upwards [vectorMeasurePotential_initial_temperature_local_bound (n:=n) μ β t] with u hu
  intro p
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hu p) (abs_nonneg a))

theorem continuous_vectorMeasureOuterPartition_temperature (μ:Paper.ParisiMeasure) (β a:ℝ) :
    Continuous (fun u:Iio (1:ℝ)=>vectorMeasureOuterPartition (n:=n) μ β u a):=by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact tendsto_integral_filter_of_dominated_convergence
    (vectorTemperatureExponentialDominator (n:=n) μ β a t)
    (.of_forall fun u=>(integrable_exp_vectorMeasurePotential (n:=n) μ β u u.property.le a 0).aestronglyMeasurable)
    ((vectorTemperatureExponentialDominator_bound (n:=n) μ β a t).mono fun u hu=>.of_forall hu)
    (integrable_vectorTemperatureExponentialDominator μ β a t)
    (.of_forall fun p=>(Real.continuous_exp.comp
      ((continuous_vectorMeasurePotential_initial_temperature μ β p).const_mul a)).tendsto t)

theorem continuous_vectorMeasureOuterWeight_temperature (μ:Paper.ParisiMeasure) (β a:ℝ)
    (p:Couplings n×ℝ) : Continuous (fun u:Iio (1:ℝ)=>vectorMeasureOuterWeight μ β u a p):=by
  exact (Real.continuous_exp.comp
    ((continuous_vectorMeasurePotential_initial_temperature μ β p).const_mul a)).div
      (continuous_vectorMeasureOuterPartition_temperature μ β a)
      (fun u=>(vectorMeasureOuterPartition_pos (n:=n) μ β u a u.property.le).ne')

theorem vectorBaseOuterWeight_temperature_local_domination (μ:Paper.ParisiMeasure) (β a:ℝ)
    (t:Iio (1:ℝ)) :
    ∃D:VectorDisorderBrownianSample n→ℝ,MemLp D 2 (vectorDisorderBrownianMeasure n)∧
      (∀ᶠu:Iio (1:ℝ) in 𝓝 t,∀sample,‖vectorBaseOuterWeight μ β u a sample‖≤D sample)∧
      (∀sample,‖vectorBaseOuterWeight μ β t a sample‖≤D sample):=by
  let Z:=vectorMeasureOuterPartition (n:=n) μ β t a
  have hZ:0<Z:=vectorMeasureOuterPartition_pos μ β t a t.property.le
  let D:VectorDisorderBrownianSample n→ℝ:=fun sample=>
    (2/Z)*vectorTemperatureExponentialDominator μ β a t sample.1+‖vectorBaseOuterWeight μ β t a sample‖
  have hD:MemLp D 2 (vectorDisorderBrownianMeasure n):=by
    exact (((hasLaw_initialVectorDisorder n).memLp_comp
      (memLp_vectorTemperatureExponentialDominator μ β a t)).const_mul (2/Z)).add
      (memLp_vectorBaseOuterWeight μ β t a t.property.le).norm
  have hz:∀ᶠu:Iio (1:ℝ) in 𝓝 t,Z/2<vectorMeasureOuterPartition (n:=n) μ β u a:=
    ((continuous_vectorMeasureOuterPartition_temperature (n:=n) μ β a).tendsto t).eventually
      (lt_mem_nhds (by dsimp only [Z] at hZ ⊢;linarith))
  refine ⟨D,hD,?_,?_⟩
  · filter_upwards [vectorTemperatureExponentialDominator_bound (n:=n) μ β a t,hz] with u hu hzu
    intro sample
    have he:Real.exp (a*vectorMeasurePotential μ β u sample.1 0)≤
        vectorTemperatureExponentialDominator μ β a t sample.1:=by
      simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hu sample.1
    change ‖Real.exp (a*vectorMeasurePotential μ β u sample.1 0)/vectorMeasureOuterPartition μ β u a‖≤_
    rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le
      (vectorMeasureOuterPartition_pos μ β u a u.property.le).le)]
    calc
      _≤Real.exp (a*vectorMeasurePotential μ β u sample.1 0)/(Z/2):=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hzu.le
      _≤vectorTemperatureExponentialDominator μ β a t sample.1/(Z/2):=
        div_le_div_of_nonneg_right he (by positivity)
      _=(2/Z)*vectorTemperatureExponentialDominator μ β a t sample.1:=by ring
      _≤D sample:=le_add_of_nonneg_right (norm_nonneg _)
  · intro sample
    exact le_add_of_nonneg_left (by
      change 0≤(2/Z)*Real.exp _
      positivity)

def vectorTemperatureOuterWeightL2 (μ:Paper.ParisiMeasure) (β a:ℝ)
    (t:Iio (1:ℝ)) : Lp ℝ 2 (vectorDisorderBrownianMeasure n):=
  (memLp_vectorBaseOuterWeight μ β t a t.property.le).toLp (vectorBaseOuterWeight μ β t a)

theorem continuous_vectorTemperatureOuterWeightL2 (μ:Paper.ParisiMeasure) (β a:ℝ) :
    Continuous (vectorTemperatureOuterWeightL2 (n:=n) μ β a):=by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨D,hD,hj,h0⟩:=vectorBaseOuterWeight_temperature_local_domination (n:=n) μ β a t
  exact temperatureDensity_toLp_tendsto_of_dominated
    (fun u:Iio (1:ℝ)=>vectorBaseOuterWeight μ β u a) (vectorBaseOuterWeight μ β t a)
    (fun u=>memLp_vectorBaseOuterWeight μ β u a u.property.le)
    (memLp_vectorBaseOuterWeight μ β t a t.property.le) D hD.integrable_sq
    (hj.mono fun u hu=>.of_forall hu) (.of_forall h0)
    (.of_forall fun sample=>(continuous_vectorMeasureOuterWeight_temperature μ β a sample.1).tendsto t)

end QuantitativePaper
