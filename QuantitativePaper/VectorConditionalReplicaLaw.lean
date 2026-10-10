module
public import QuantitativePaper.VectorMeasureMarkedConditionalLaw
public import QuantitativePaper.CompletionCovariance
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-! Conditional replicas of the actual marked terminal spin. The law is
constructed from regular conditional distributions in the full Wiener past;
the two replicas are sampled independently from that genuine kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

abbrev VectorMarkedSample (n : ℕ) := VectorDisorderBrownianSample n×Configuration n

def vectorConditionalTerminalSpinKernel (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) : Kernel (VectorMarkedSample n) (Configuration n) := by
  let ambient : MeasurableSpace (VectorMarkedSample n):=inferInstance
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  let V:=vectorSpinPast n (q:ℝ).toNNReal
  let K : @Kernel (VectorMarkedSample n) (Configuration n) V inferInstance :=
    @condDistrib (VectorMarkedSample n) (VectorMarkedSample n) (Configuration n)
      inferInstance inferInstance inferInstance ambient V Prod.snd id J inferInstance
  exact @Kernel.comap (VectorMarkedSample n) (Configuration n) V inferInstance
    (VectorMarkedSample n) ambient K id
    (@measurable_id'' (VectorMarkedSample n) V ambient (vectorSpinPast_le n (q:ℝ).toNNReal))

instance vectorConditionalTerminalSpinKernel_markov (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    IsMarkovKernel (vectorConditionalTerminalSpinKernel (n:=n) μ β t a ht q) := by
  unfold vectorConditionalTerminalSpinKernel
  infer_instance

theorem vectorConditionalTerminalSpinKernel_condExp (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (d : Configuration n→ℝ) :
    (vectorMeasureSpinPathLaw μ β t a ht)[(fun z : VectorMarkedSample n=>d z.2)|
      vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht]
      fun z=>∫σ,d σ ∂vectorConditionalTerminalSpinKernel μ β t a ht q z := by
  let ambient : MeasurableSpace (VectorMarkedSample n):=inferInstance
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  let V:=vectorSpinPast n (q:ℝ).toNNReal
  have hD : Integrable (fun z : VectorMarkedSample n=>d z.2) J := by
    apply (integrable_const (∑σ : Configuration n,|d σ|)).mono'
      ((measurable_of_finite d).comp measurable_snd).aestronglyMeasurable
    exact .of_forall fun z=>by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun σ _=>abs_nonneg (d σ)) (Finset.mem_univ z.2)
  have he:=@condExp_ae_eq_integral_condDistrib
    (VectorMarkedSample n) (VectorMarkedSample n) (Configuration n) ℝ
    inferInstance inferInstance inferInstance inferInstance ambient J inferInstance
    id Prod.snd V inferInstance inferInstance
    (@measurable_id'' (VectorMarkedSample n) V ambient (vectorSpinPast_le n (q:ℝ).toNNReal))
    measurable_snd.aemeasurable d (measurable_of_finite d).stronglyMeasurable hD
  simpa only [MeasurableSpace.comap_id,id_eq,vectorConditionalTerminalSpinKernel,
    Kernel.comap_apply,J,V] using he

def vectorConditionalReplicaLaw (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    Measure (VectorMarkedSample n×(Configuration n×Configuration n)) :=
  vectorMeasureSpinPathLaw μ β t a ht ⊗ₘ
    (vectorConditionalTerminalSpinKernel μ β t a ht q ×ₖ
      vectorConditionalTerminalSpinKernel μ β t a ht q)

instance vectorConditionalReplicaLaw_probability (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    IsProbabilityMeasure (vectorConditionalReplicaLaw (n:=n) μ β t a ht q) := by
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  unfold vectorConditionalReplicaLaw
  infer_instance

theorem abs_vectorOverlap_le_one (hn : 0<n) (σ τ : Configuration n) :
    |overlap n σ τ|≤1 := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hs : |∑i : Fin n,Paper.spinSign (σ i)*Paper.spinSign (τ i)|≤(n:ℝ) := by
    calc
      _≤∑i : Fin n,|Paper.spinSign (σ i)*Paper.spinSign (τ i)| := Finset.abs_sum_le_sum_abs _ _
      _=(n:ℝ) := by simp [abs_mul,Paper.abs_spinSign]
  unfold overlap
  rw [abs_mul,abs_of_pos (one_div_pos.mpr hn0)]
  calc
    _≤(1/(n:ℝ))*(n:ℝ) := mul_le_mul_of_nonneg_left hs (one_div_pos.mpr hn0).le
    _=1 := by field_simp

def vectorConditionalReplicaDefect (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) : ℝ :=
  ∫z,(overlap n z.2.1 z.2.2-(q:ℝ))^2 ∂vectorConditionalReplicaLaw μ β t a ht q

theorem vectorConditionalReplicaDefect_bounds (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    0≤vectorConditionalReplicaDefect (n:=n) μ β t a ht q ∧
      vectorConditionalReplicaDefect (n:=n) μ β t a ht q≤4 := by
  let P:=vectorConditionalReplicaLaw (n:=n) μ β t a ht q
  haveI:=vectorConditionalReplicaLaw_probability (n:=n) μ β t a ht q
  have hm : Measurable (fun z : VectorMarkedSample n×(Configuration n×Configuration n)=>
      (overlap n z.2.1 z.2.2-(q:ℝ))^2) :=
    (measurable_of_finite (fun p : Configuration n×Configuration n=>
      (overlap n p.1 p.2-(q:ℝ))^2)).comp measurable_snd
  have hb (z : VectorMarkedSample n×(Configuration n×Configuration n)) :
      (overlap n z.2.1 z.2.2-(q:ℝ))^2≤4 := by
    have ho:=abs_vectorOverlap_le_one hn z.2.1 z.2.2
    have h1:=(abs_le.mp ho).1
    have h2:=(abs_le.mp ho).2
    nlinarith [q.property.1,q.property.2]
  have hi : Integrable (fun z : VectorMarkedSample n×(Configuration n×Configuration n)=>
      (overlap n z.2.1 z.2.2-(q:ℝ))^2) P := by
    apply (integrable_const (4:ℝ)).mono' hm.aestronglyMeasurable
    exact .of_forall fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];exact hb z
  constructor
  · exact integral_nonneg (fun _=>sq_nonneg _)
  · change (∫z,(overlap n z.2.1 z.2.2-(q:ℝ))^2∂P)≤4
    calc
      _≤∫_ : VectorMarkedSample n×(Configuration n×Configuration n),(4:ℝ)∂P :=
        integral_mono hi (integrable_const _) hb
      _=4 := by simp [P]

end QuantitativePaper
