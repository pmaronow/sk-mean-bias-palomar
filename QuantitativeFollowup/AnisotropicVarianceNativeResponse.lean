module
public import QuantitativeFollowup.AnisotropicVarianceRestartConditional
public import QuantitativeFollowup.AnisotropicVarianceDerivative
public import QuantitativeFollowup.ParisiFreeMeasure

@[expose] public section

/-! Genuine all-profile variance response under the native whole Wiener
past. The limiting response is the actual conditional future spin square. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def anisotropicNativeVarianceResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i : Fin n)
    (p : AnisotropicDisorderBrownianSample n) : ℝ :=
  (1/2:ℝ)*(1-(q:ℝ)-∫r,max 0 ((r:ℝ)-(q:ℝ))*
    anisotropicPastSpinSquareKernel D μ a q r i p ∂(μ:Measure Paper.Overlap))

theorem anisotropicRestartVarianceResponse_eq_native (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i : Fin n) :
    (fun p=>anisotropicRestartVarianceResponse D μ p.1 q (anisotropicMeasureState D μ q p) i)
      =ᵐ[anisotropicMeasureSampleLaw D μ a] anisotropicNativeVarianceResponse D μ a q i := by
  let S := fun (r : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n)=>
    max 0 ((r:ℝ)-(q:ℝ))*anisotropicRestartConditionalSpinSquare D μ q r i p
  let K := fun (r : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n)=>
    max 0 ((r:ℝ)-(q:ℝ))*anisotropicPastSpinSquareKernel D μ a q r i p
  have hmS : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>S z.1 z.2) :=
    (measurable_const.max (measurable_subtype_coe.comp measurable_fst |>.sub_const _)).mul
      (measurable_uncurry_anisotropicRestartConditionalSpinSquare D μ q i)
  have hmK0 : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      anisotropicPastSpinSquareKernel D μ a q z.1 i z.2) :=
    (measurable_uncurry_anisotropicPastSpinSquareKernel D μ a q i).mono
      (by
        dsimp only [MeasurableSpace.prod]
        exact sup_le_sup le_rfl (MeasurableSpace.comap_mono ((anisotropicBrownianFiltration n).le _))) le_rfl
  have hmK : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>K z.1 z.2) :=
    (measurable_const.max (measurable_subtype_coe.comp measurable_fst |>.sub_const _)).mul hmK0
  have he : ∀r : Paper.Overlap,S r=ᵐ[anisotropicMeasureSampleLaw D μ a] K r := by
    intro r
    by_cases hqr : q≤r
    · have hh:=(anisotropicRestartConditionalSpinSquare_condExp D μ a q r hqr i).symm.trans
        (anisotropicPastSpinSquareKernel_condExp D μ a q r i)
      filter_upwards [hh] with p hp
      exact congrArg (fun x=>max 0 ((r:ℝ)-(q:ℝ))*x) hp
    · have hc : max 0 ((r:ℝ)-(q:ℝ))=0 :=
        max_eq_left (sub_nonpos.mpr (show (r:ℝ)≤(q:ℝ) from le_of_not_ge hqr))
      exact .of_forall fun p=>by simp only [S,K,hc,zero_mul]
  have hme : MeasurableSet {z : Paper.Overlap×AnisotropicDisorderBrownianSample n|S z.1 z.2=K z.1 z.2} :=
    measurableSet_eq_fun hmS hmK
  have hh : ∀ᵐp ∂anisotropicMeasureSampleLaw D μ a,∀ᵐr ∂(μ:Measure Paper.Overlap),S r p=K r p :=
    (Measure.ae_ae_comm hme).mp (Filter.Eventually.of_forall he)
  filter_upwards [hh] with p hp
  unfold anisotropicRestartVarianceResponse anisotropicNativeVarianceResponse
  congr 2
  apply integral_congr_ae
  filter_upwards [hp] with r hr
  change max 0 ((r:ℝ)-(q:ℝ))*anisotropicRestartSpinSquare D μ p.1 q
    (anisotropicMeasureState D μ q p) i r=_
  by_cases hqr : q≤r
  · rw [←anisotropicRestartConditionalSpinSquare_eq_restart D μ q r hqr i p]
    exact hr
  · simp only [max_eq_left (sub_nonpos.mpr (show (r:ℝ)≤(q:ℝ) from le_of_not_ge hqr)),zero_mul]

theorem hasDerivAt_anisotropicMeasureTailPotential_variance_native (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i : Fin n) :
    ∀ᵐ p ∂anisotropicMeasureSampleLaw D μ a,
      HasDerivAt (fun b=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ q
        (anisotropicProcessParameter D μ q p))
        (anisotropicNativeVarianceResponse D μ a q i p) (D.variance i) := by
  filter_upwards [anisotropicRestartVarianceResponse_eq_native D μ a q i] with p hp
  have hd:=hasDerivAt_anisotropicMeasureTailPotential_variance_restart D μ i p.1 q
    (anisotropicMeasureState D μ q p) (D.variance i) (D.variance_pos i)
  rw [anisotropicReplaceVariance_self,hp] at hd
  exact hd

theorem anisotropicNativeVarianceResponse_eq_free (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (i : Fin n) (p : AnisotropicDisorderBrownianSample n) :
    anisotropicNativeVarianceResponse D μ a q i p=(1/2:ℝ)*(1-(q:ℝ)-
      ∫r : Paper.Overlap,if q<r then ((r:ℝ)-(q:ℝ))*anisotropicPastSpinSquareKernel D μ a q r i p else 0
        ∂parisiFreeMeasure μ a) := by
  classical
  let f := fun r : Paper.Overlap=>max 0 ((r:ℝ)-(q:ℝ))*anisotropicPastSpinSquareKernel D μ a q r i p
  have hmap : @Measurable Paper.Overlap (Paper.Overlap×AnisotropicDisorderBrownianSample n)
      inferInstance ((inferInstance : MeasurableSpace Paper.Overlap).prod
        (anisotropicBrownianFiltration n (q:ℝ).toNNReal)) (fun r=>(r,p)) :=
    measurable_id.prodMk measurable_const
  have hK : Measurable (fun r : Paper.Overlap=>anisotropicPastSpinSquareKernel D μ a q r i p) := by
    simpa only [Function.comp_def] using
      (measurable_uncurry_anisotropicPastSpinSquareKernel D μ a q i).comp hmap
  have hf : Measurable f := (measurable_const.max (measurable_subtype_coe.sub_const _)).mul hK
  have hfb : ∀r,‖f r‖≤1 := by
    intro r
    have hc : max 0 ((r:ℝ)-(q:ℝ))≤1 := max_le (by norm_num) (by linarith [r.property.2,q.property.1])
    rw [norm_mul,Real.norm_of_nonneg (le_max_left _ _)]
    exact (mul_le_of_le_one_right (le_max_left _ _) (norm_anisotropicPastSpinSquareKernel_le D μ a q r i p)).trans hc
  have hfi : Integrable f (parisiFreeMeasure μ a) :=
    (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable (.of_forall hfb)
  have hd : Integrable f (ENNReal.ofReal a • Measure.dirac zeroOverlap) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  unfold anisotropicNativeVarianceResponse
  change (1/2:ℝ)*(1-(q:ℝ)-∫r,f r ∂(μ:Measure Paper.Overlap))=_
  rw [←root_add_parisiFreeMeasure μ a ha hμ,integral_add_measure hd hfi,integral_smul_measure,integral_dirac]
  have hz : f zeroOverlap=0 := by
    simp only [f,zeroOverlap,Set.Icc.coe_zero,zero_sub,max_eq_left (neg_nonpos.mpr q.property.1),zero_mul]
  rw [hz,smul_zero,zero_add]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hqr : q<r
  · simp only [f,ite_eq_left hqr,max_eq_right (sub_nonneg.mpr (show (q:ℝ)≤(r:ℝ) from hqr.le))]
  · simp only [f,ite_eq_right hqr,max_eq_left (sub_nonpos.mpr (show (r:ℝ)≤(q:ℝ) from le_of_not_gt hqr)),zero_mul]

end QuantitativeFollowup
