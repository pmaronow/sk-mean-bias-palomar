module
public import QuantitativeFollowup.CavityTransferredThermalBudget
public import QuantitativeFollowup.FollowupCavityThreeEndpointMoments

@[expose] public section

/-! Conditional overlap fluctuations about their genuine full-past mean.
The identities hold for every profile, without a support contact hypothesis. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem vectorConditionalReplica_centered_square_thermal (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (q : Paper.Overlap) :
    (∫z,(overlap n z.2.1 z.2.2-vectorSelfOverlap μ β t ht.le q z.1)^2
      ∂vectorConditionalReplicaLaw (n:=n) μ β t a ht.le q)=
      foundationThermalTrace (n:=n) μ β t a ht.le q+
        2*foundationMeanCovariance (n:=n) μ β t a ht.le q := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  let K:=vectorConditionalTerminalSpinKernel (n:=n) μ β t a ht.le q
  let P:=vectorConditionalReplicaLaw (n:=n) μ β t a ht.le q
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hm : Measurable (fun z:VectorMarkedSample n×(Configuration n×Configuration n)=>
      (overlap n z.2.1 z.2.2-vectorSelfOverlap μ β t ht.le q z.1)^2) :=
    (((measurable_of_finite (fun p:Configuration n×Configuration n=>overlap n p.1 p.2)).comp
      measurable_snd).sub ((measurable_vectorSelfOverlap μ β t ht.le q).comp measurable_fst)).pow_const 2
  have hi : Integrable (fun z:VectorMarkedSample n×(Configuration n×Configuration n)=>
      (overlap n z.2.1 z.2.2-vectorSelfOverlap μ β t ht.le q z.1)^2) P := by
    apply (integrable_const (4:ℝ)).mono' hm.aestronglyMeasurable
    exact .of_forall fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have ho:=abs_le.mp (abs_vectorOverlap_le_one hn z.2.1 z.2.2)
      have hs:=vectorSelfOverlap_bounds hn μ β t ht.le q z.1
      nlinarith
  change (∫z,(overlap n z.2.1 z.2.2-vectorSelfOverlap μ β t ht.le q z.1)^2
    ∂(J⊗ₘ(K×ₖK)))=_
  rw [Measure.integral_compProd hi]
  simp only [Kernel.prod_apply]
  have h1:=ae_all_iff.2 (fun i:Fin n=>
    vectorConditionalTerminalSpinKernel_first_moment μ β t a hβ ht q i)
  have h2:=ae_all_iff.2 (fun i:Fin n=>ae_all_iff.2 (fun j:Fin n=>
    vectorConditionalTerminalSpinKernel_second_moment μ β t a ht.le q i j))
  have he : (fun z:VectorMarkedSample n=>∫σ,
      (overlap n σ.1 σ.2-vectorSelfOverlap μ β t ht.le q z)^2∂(K z).prod (K z))=ᵐ[J]
      fun z=>Matrix.trace (vectorMeasureSpinCovariance μ β t a ht.le q z.1*
          vectorMeasureSpinCovariance μ β t a ht.le q z.1)/(n:ℝ)^2+
        2*(vectorMeasureCovarianceQuadratic μ β t a ht.le q z.1
          (vectorMeasureSpinMean μ β t ht.le q z.1)/(n:ℝ)^2) := by
    filter_upwards [h1,h2] with z hz1 hz2
    rw [integral_overlap_defect_spin_product]
    dsimp only [K]
    simp_rw [hz1,hz2]
    rw [spin_matrix_defect_expansion _ (vectorMeasureSpinCovariance_symmetric μ β t a ht.le q z.1)]
    simp only [vectorSelfOverlap,vectorMeasureCovarianceQuadratic,EuclideanSpace.real_norm_sq_eq,
      one_div,div_eq_mul_inv,inv_pow]
    ring
  rw [integral_congr_ae he]
  let T:=fun sample:VectorDisorderBrownianSample n=>Matrix.trace
    (vectorMeasureSpinCovariance μ β t a ht.le q sample*vectorMeasureSpinCovariance μ β t a ht.le q sample)
  have hTi:=integrable_vectorMeasureSpinCovariance_trace_square (n:=n) μ β t a ht.le q
  have hTj : Integrable (fun z:VectorMarkedSample n=>T z.1/(n:ℝ)^2) J :=
    ((measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht.le).integrable_comp_of_integrable hTi).div_const _
  have hQj : Integrable (fun z:VectorMarkedSample n=>vectorMeasureCovarianceQuadratic μ β t a ht.le q z.1
      (vectorMeasureSpinMean μ β t ht.le q z.1)/(n:ℝ)^2) J :=
    integrable_condVar.congr (condVar_vectorMeasureOverlapScore (n:=n) μ β t a hβ ht q)
  rw [integral_add hTj (hQj.const_mul 2),integral_const_mul,integral_div]
  have hTm : Measurable T := by
    dsimp only [T,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
    exact Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
      (measurable_vectorMeasureSpinCovariance_entry μ β t a ht.le q i j).mul
        (measurable_vectorMeasureSpinCovariance_entry μ β t a ht.le q j i)
  rw [integral_vectorMeasureSpinPathLaw_sample μ β t a ht.le T hTm]
  rfl

theorem vectorConditionalReplica_centered_cubic_thermal_le (hn:0<n)
    (μ:Paper.ParisiMeasure) (β t a:ℝ) (hβ:β≠0) (ht:t<1) (q:Paper.Overlap) :
    (∫z,|overlap n z.2.1 z.2.2-vectorSelfOverlap μ β t ht.le q z.1|^3
      ∂vectorConditionalReplicaLaw (n:=n) μ β t a ht.le q)≤
      2*(foundationThermalTrace (n:=n) μ β t a ht.le q+
        2*foundationMeanCovariance (n:=n) μ β t a ht.le q) := by
  let P:=vectorConditionalReplicaLaw (n:=n) μ β t a ht.le q
  let X:=fun z:VectorMarkedSample n×(Configuration n×Configuration n)=>
    overlap n z.2.1 z.2.2-vectorSelfOverlap μ β t ht.le q z.1
  have hm : Measurable X :=
    ((measurable_of_finite (fun p:Configuration n×Configuration n=>overlap n p.1 p.2)).comp
      measurable_snd).sub ((measurable_vectorSelfOverlap μ β t ht.le q).comp measurable_fst)
  have hb (z) : |X z|≤2 := by
    have ho:=abs_le.mp (abs_vectorOverlap_le_one hn z.2.1 z.2.2)
    have hs:=vectorSelfOverlap_bounds hn μ β t ht.le q z.1
    rw [abs_le]; constructor <;> dsimp only [X] <;> linarith
  have hi (k:ℕ) : Integrable (fun z=>|X z|^k) P := by
    apply (integrable_const ((2:ℝ)^k)).mono' (hm.abs.pow_const k).aestronglyMeasurable
    exact .of_forall fun z=>by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb z) k
  have hh:=integral_mono (hi 3) ((hi 2).const_mul 2) (fun z=>by
    have hp:=mul_le_mul_of_nonneg_right (hb z) (sq_nonneg |X z|)
    nlinarith only [hp])
  simp only [Pi.mul_apply,integral_const_mul,sq_abs] at hh
  exact hh.trans_eq (by rw [vectorConditionalReplica_centered_square_thermal hn μ β t a hβ ht q])

end QuantitativeFollowup
