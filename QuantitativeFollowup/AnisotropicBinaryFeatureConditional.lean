module
public import QuantitativeFollowup.AnisotropicBinaryFeatureNative
public import QuantitativeFollowup.AnisotropicBinaryFeatureFutureKernel
public import QuantitativeFollowup.ParisiFreeMeasure

@[expose] public section

/-! Literal arbitrary-q/full-profile node-Theta identity: the actual
binary terminal-feature second response equals one minus the right-CDF
current square and the genuine whole-past conditional strict-future integral. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem anisotropic_pair_second_conditional_stieltjes (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    anisotropicProcessPairSecond D μ q e=ᵐ[anisotropicMeasureSampleLaw D μ a]
      fun p=>1-Paper.parisiCDF μ q*(anisotropicProcessPairResponse D μ q e p)^2-
        anisotropicFuturePairSquareKernelIntegral D μ a q e p := by
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n):=inferInstance
  let P:=anisotropicMeasureSampleLaw D μ a
  let V:=anisotropicBrownianFiltration n (q:ℝ).toNNReal
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n):=ambient
  let H:=anisotropicProcessPairSecond D μ q e
  let M:=fun p=>Paper.parisiCDF μ q*(anisotropicProcessPairResponse D μ q e p)^2
  let F:=anisotropicFuturePairSquareKernelIntegral D μ a q e
  have hHi : Integrable H P:=
    (integrable_const (anisotropicPairSecondBound D e)).mono'
      ((adapted_anisotropicProcessPairSecond D μ q e).mono ((anisotropicBrownianFiltration n).le _) le_rfl).aestronglyMeasurable
      (.of_forall (norm_anisotropicProcessPairSecond_le D μ q e))
  have hMi : Integrable M P:=by
    apply Integrable.const_mul
    exact (integrable_const (1:ℝ)).mono'
      ((measurable_anisotropicProcessPairResponse D μ q e).pow_const 2).aestronglyMeasurable
      (.of_forall fun p=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _)
        (anisotropicProcessPairResponse_bound D μ q e p) 2).trans_eq (by norm_num))
  have hFi : Integrable F P:=
    (integrable_const (1:ℝ)).mono'
      ((adapted_anisotropicFuturePairSquareKernelIntegral D μ a q e).mono
        ((anisotropicBrownianFiltration n).le _)).aestronglyMeasurable
      (.of_forall (norm_anisotropicFuturePairSquareKernelIntegral_le D μ a q e))
  have hGi : Integrable (fun p=>H p+M p+F p) P:=(hHi.add hMi).add hFi
  have hGm : StronglyMeasurable[V] (fun p=>H p+M p+F p):=
    (((adapted_anisotropicProcessPairSecond D μ q e).stronglyMeasurable.add
      (((adapted_anisotropicProcessPairResponse D μ q e).pow_const 2).stronglyMeasurable.const_mul _)).add
      (adapted_anisotropicFuturePairSquareKernelIntegral D μ a q e))
  have he : (fun p=>H p+M p+F p)=ᵐ[P] P[fun _ : AnisotropicDisorderBrownianSample n=>(1:ℝ)|V] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq ((anisotropicBrownianFiltration n).le _)
      (integrable_const (1:ℝ))
    · intro A _ _
      exact hGi.integrableOn
    · intro A hA _
      let Z:=A.indicator (fun _ : AnisotropicDisorderBrownianSample n=>(1:ℝ))
      have hZ : Measurable[V] Z:=measurable_const.indicator hA
      have hZb (p : AnisotropicDisorderBrownianSample n) : ‖Z p‖ ≤ (1:ℝ≥0) := by
        by_cases hp:p∈A <;> simp [Z,hp]
      have hp:=anisotropic_native_pair_second_stieltjes_pairing D μ a q e Z hZ 1 hZb
      rw [←anisotropicFuturePairSquareKernelIntegral_weighted_pairing D μ a q e Z hZ 1 hZb] at hp
      letI : MeasurableSpace (AnisotropicDisorderBrownianSample n):=ambient
      have hAg : MeasurableSet A:=((anisotropicBrownianFiltration n).le _) A hA
      change (∫p,Z p*H p ∂P)+Paper.parisiCDF μ q*
        (∫p,Z p*(anisotropicProcessPairResponse D μ q e p)^2 ∂P)+(∫p,Z p*F p ∂P)=∫p,Z p ∂P at hp
      dsimp only [Z] at hp
      rw [integral_indicator_one_mul_eq_setIntegral P A hAg H,
        integral_indicator_one_mul_eq_setIntegral P A hAg,
        integral_indicator_one_mul_eq_setIntegral P A hAg F,integral_indicator hAg] at hp
      change (∫p in A,(H+M) p+F p ∂P)=∫p in A,(1:ℝ) ∂P
      rw [integral_add (hHi.add hMi).integrableOn hFi.integrableOn]
      simp only [Pi.add_apply]
      rw [integral_add hHi.integrableOn hMi.integrableOn]
      change _+(∫p in A,Paper.parisiCDF μ q*(anisotropicProcessPairResponse D μ q e p)^2 ∂P)+_=_
      rw [integral_const_mul]
      exact hp
    · exact hGm.aestronglyMeasurable
  rw [condExp_const ((anisotropicBrownianFiltration n).le _) (1:ℝ)] at he
  filter_upwards [he] with p hp
  change H p=1-M p-F p
  linarith

theorem anisotropicFuturePairSquareKernelIntegral_eq_free (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) (p : AnisotropicDisorderBrownianSample n) :
    anisotropicFuturePairSquareKernelIntegral D μ a q e p=
      ∫r : Paper.Overlap,if q < r then anisotropicPastPairSquareKernel D μ a q r e p else 0
        ∂parisiFreeMeasure μ a := by
  classical
  let f:=fun r : Paper.Overlap=>if q < r then anisotropicPastPairSquareKernel D μ a q r e p else 0
  have hK : Measurable (fun r : Paper.Overlap=>anisotropicPastPairSquareKernel D μ a q r e p) := by
    have hmap : @Measurable Paper.Overlap (Paper.Overlap×AnisotropicDisorderBrownianSample n)
        inferInstance ((inferInstance : MeasurableSpace Paper.Overlap).prod
          (anisotropicBrownianFiltration n (q:ℝ).toNNReal)) (fun r=>(r,p)) :=
      measurable_id.prodMk measurable_const
    simpa only [Function.comp_def] using (measurable_uncurry_anisotropicPastPairSquareKernel D μ a q e).comp hmap
  have hf : Measurable f:=Measurable.ite (measurableSet_lt measurable_const measurable_id) hK measurable_const
  have hfi : Integrable f (parisiFreeMeasure μ a):=(integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
    (.of_forall fun r=>by
      dsimp only [f]
      split_ifs
      · exact norm_anisotropicPastPairSquareKernel_le D μ a q r e p
      · simp)
  have hd : Integrable f (ENNReal.ofReal a • Measure.dirac zeroOverlap):=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  unfold anisotropicFuturePairSquareKernelIntegral
  change (∫r,f r ∂(μ:Measure Paper.Overlap))=∫r,f r ∂parisiFreeMeasure μ a
  rw [←root_add_parisiFreeMeasure μ a ha hμ,integral_add_measure hd hfi,
    integral_smul_measure,integral_dirac]
  have hz : ¬q < zeroOverlap:=not_lt_of_ge q.property.1
  simp only [f,ite_eq_right hz,smul_zero,zero_add]

theorem anisotropic_pair_second_nodeTheta (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    anisotropicProcessPairSecond D μ q e=ᵐ[anisotropicMeasureSampleLaw D μ a]
      fun p=>1-Paper.parisiCDF μ q*(anisotropicProcessPairResponse D μ q e p)^2-
        ∫r : Paper.Overlap,if q < r then anisotropicPastPairSquareKernel D μ a q r e p else 0
          ∂parisiFreeMeasure μ a := by
  filter_upwards [anisotropic_pair_second_conditional_stieltjes D μ a q e] with p hp
  rw [hp,anisotropicFuturePairSquareKernelIntegral_eq_free D μ a ha hμ q e p]

end QuantitativeFollowup
