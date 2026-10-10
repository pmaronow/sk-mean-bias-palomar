module
public import QuantitativeFollowup.FollowupCavityThreeEndpointLaw
public import QuantitativeFollowup.FoundationDecomposition
public import QuantitativeFollowup.CavityDeletedDescendantMoments

@[expose] public section

/-! Actual normalized three-descendant SK moments. The full-past product
sampling law yields the thermal trace and mean-covariance observables. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem cavityVectorThreeDescendantLaw_normalized_difference_square (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    (∫z,(cavitySpinDifferencePairing Finset.univ z.2/(n:ℝ))^2
      ∂cavityVectorThreeDescendantLaw (n:=n) μ β t a ht.le q)=
      2*(foundationThermalTrace (n:=n) μ β t a ht.le q+
        foundationMeanCovariance (n:=n) μ β t a ht.le q) := by
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  let F:=fun z:CavityThreeTerminalSpins n=>(cavitySpinDifferencePairing Finset.univ z/(n:ℝ))^2
  let B:ℝ:=∑z:CavityThreeTerminalSpins n,‖F z‖
  have hi : Integrable (fun z:VectorMarkedSample n×CavityThreeTerminalSpins n=>F z.2)
      (cavityVectorThreeDescendantLaw μ β t a ht.le q) :=
    bounded_real_integrable _ ((measurable_of_finite F).comp measurable_snd) B
      (fun z=>Finset.single_le_sum (fun τ _=>norm_nonneg (F τ)) (Finset.mem_univ z.2))
  change (∫z,F z.2∂cavityVectorThreeDescendantLaw (n:=n) μ β t a ht.le q)=_
  rw [cavityVectorThreeDescendantLaw,Measure.integral_compProd hi]
  simp only [Kernel.prod_apply]
  have h1:=ae_all_iff.2 (fun i:Fin n=>
    vectorConditionalTerminalSpinKernel_first_moment μ β t a hβ ht q i)
  have h2:=ae_all_iff.2 (fun i:Fin n=>ae_all_iff.2 (fun j:Fin n=>
    vectorConditionalTerminalSpinKernel_second_moment μ β t a ht.le q i j))
  have he : (fun z:VectorMarkedSample n=>∫σ,F σ∂
      (((vectorConditionalTerminalSpinKernel μ β t a ht.le q z).prod
        (vectorConditionalTerminalSpinKernel μ β t a ht.le q z)).prod
        (vectorConditionalTerminalSpinKernel μ β t a ht.le q z)))=ᵐ[
          vectorMeasureSpinPathLaw μ β t a ht.le]
      fun z=>2*(Matrix.trace (vectorMeasureSpinCovariance μ β t a ht.le q z.1*
          vectorMeasureSpinCovariance μ β t a ht.le q z.1)/(n:ℝ)^2+
        vectorMeasureCovarianceQuadratic μ β t a ht.le q z.1
          (vectorMeasureSpinMean μ β t ht.le q z.1)/(n:ℝ)^2) := by
    filter_upwards [h1,h2] with z hz1 hz2
    dsimp only [F]
    simp only [div_pow,integral_div,cavitySpinKernel_three_difference_square]
    have hm (i:Fin n) : cavitySpinKernelMean (vectorConditionalTerminalSpinKernel μ β t a ht.le q z) i=
        vectorMeasureSpinMean μ β t ht.le q z.1 i:=hz1 i
    have hQ (i j:Fin n) : cavitySpinKernelSecond (vectorConditionalTerminalSpinKernel μ β t a ht.le q z) i j=
        vectorMeasureSpinCovariance μ β t a ht.le q z.1 i j+
          vectorMeasureSpinMean μ β t ht.le q z.1 i*vectorMeasureSpinMean μ β t ht.le q z.1 j:=hz2 i j
    have hC (i j:Fin n) : cavitySpinKernelCovariance (vectorConditionalTerminalSpinKernel μ β t a ht.le q z) i j=
        vectorMeasureSpinCovariance μ β t a ht.le q z.1 i j := by
      unfold cavitySpinKernelCovariance
      rw [hQ,hm i,hm j]
      ring
    simp_rw [hC,hQ,mul_add,Finset.sum_add_distrib]
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,vectorMeasureCovarianceQuadratic]
    simp_rw [vectorMeasureSpinCovariance_symmetric μ β t a ht.le q z.1]
    simp only [mul_assoc]
    ring
  rw [integral_congr_ae he,integral_const_mul]
  let T:=fun sample:VectorDisorderBrownianSample n=>Matrix.trace
    (vectorMeasureSpinCovariance μ β t a ht.le q sample*vectorMeasureSpinCovariance μ β t a ht.le q sample)
  have hTi:=integrable_vectorMeasureSpinCovariance_trace_square (n:=n) μ β t a ht.le q
  have hTj : Integrable (fun z:VectorMarkedSample n=>T z.1/(n:ℝ)^2)
      (vectorMeasureSpinPathLaw μ β t a ht.le) :=
    ((measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht.le).integrable_comp_of_integrable hTi).div_const _
  have hQj : Integrable (fun z:VectorMarkedSample n=>vectorMeasureCovarianceQuadratic μ β t a ht.le q z.1
      (vectorMeasureSpinMean μ β t ht.le q z.1)/(n:ℝ)^2)
      (vectorMeasureSpinPathLaw μ β t a ht.le) :=
    integrable_condVar.congr (condVar_vectorMeasureOverlapScore (n:=n) μ β t a hβ ht q)
  have hh:=integral_add hTj hQj
  rw [hh,integral_div]
  have hTm : Measurable T := by
    dsimp only [T,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
    exact Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
      (measurable_vectorMeasureSpinCovariance_entry μ β t a ht.le q i j).mul
        (measurable_vectorMeasureSpinCovariance_entry μ β t a ht.le q j i)
  rw [integral_vectorMeasureSpinPathLaw_sample μ β t a ht.le T hTm]
  rfl

theorem cavityVectorThreeDescendant_deleted_difference_square_le (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i : Fin n) :
    (∫z,(cavitySpinDifferencePairing (Finset.univ.erase i) z.2)^2
      ∂cavityVectorThreeDescendantLaw μ β t a ht q)≤
      2*(∫z,(cavitySpinDifferencePairing Finset.univ z.2)^2
        ∂cavityVectorThreeDescendantLaw (n:=n) μ β t a ht q)+4 := by
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  let F:=fun σ:CavityThreeTerminalSpins n=>(cavitySpinDifferencePairing (Finset.univ.erase i) σ)^2
  let G:=fun σ:CavityThreeTerminalSpins n=>(cavitySpinDifferencePairing Finset.univ σ)^2
  let P:=cavityVectorThreeDescendantLaw (n:=n) μ β t a ht q
  let K : Kernel (VectorMarkedSample n) (CavityThreeTerminalSpins n):=((vectorConditionalTerminalSpinKernel μ β t a ht q) ×ₖ
    (vectorConditionalTerminalSpinKernel μ β t a ht q)) ×ₖ
    (vectorConditionalTerminalSpinKernel μ β t a ht q)
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht
  have hi (f:CavityThreeTerminalSpins n→ℝ) : Integrable (fun z:VectorMarkedSample n×CavityThreeTerminalSpins n=>f z.2) P :=
    bounded_real_integrable _ ((measurable_of_finite f).comp measurable_snd)
      (∑σ:CavityThreeTerminalSpins n,‖f σ‖)
      (fun z=>Finset.single_le_sum (fun τ _=>norm_nonneg (f τ)) (Finset.mem_univ z.2))
  have houter (f:CavityThreeTerminalSpins n→ℝ) : Integrable (fun z=>∫σ,f σ∂K z) J := by
    apply bounded_real_integrable _
      (((measurable_of_finite f).stronglyMeasurable.integral_kernel (κ:=K)).measurable)
      (∑σ:CavityThreeTerminalSpins n,‖f σ‖)
    intro z
    simpa using norm_integral_le_of_norm_le_const (μ:=K z)
      (.of_forall fun σ=>Finset.single_le_sum (fun τ _=>norm_nonneg (f τ)) (Finset.mem_univ σ))
  change (∫z,F z.2∂P)≤2*(∫z,G z.2∂P)+4
  rw [show P=J⊗ₘK from rfl,Measure.integral_compProd (hi F),Measure.integral_compProd (hi G)]
  have hbound:=integral_mono (houter F) ((houter G).const_mul 2 |>.add (integrable_const 4))
    (fun z=>by
      change (∫σ,F σ∂K z)≤2*(∫σ,G σ∂K z)+4
      simpa only [F,G,Kernel.prod_apply,K] using
        cavitySpinKernel_three_deleted_square_le (vectorConditionalTerminalSpinKernel μ β t a ht q z) i)
  have hadd:=integral_add ((houter G).const_mul 2) (integrable_const (4:ℝ))
  simp only [Pi.add_apply,integral_const_mul,integral_const,probReal_univ,one_smul] at hadd
  exact hbound.trans_eq hadd

end QuantitativeFollowup
