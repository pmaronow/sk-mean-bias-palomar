module
public import QuantitativeFollowup.AnisotropicSpinSecondRegularity

@[expose] public section

/-! Jointly measurable genuine conditional strict-future square integral
under the native tilted anisotropic law, with all probability/Fubini bounds. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

def anisotropicFutureSpinSquareKernelIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : Fin n)
    (p : AnisotropicDisorderBrownianSample n) : ℝ :=
  ∫r : Paper.Overlap,if q < r then anisotropicPastSpinSquareKernel D μ a q r e p else 0
    ∂(μ:Measure Paper.Overlap)

theorem adapted_anisotropicFutureSpinSquareKernelIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : Fin n) :
    StronglyMeasurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal]
      (anisotropicFutureSpinSquareKernelIntegral D μ a q e) := by
  classical
  let V:=anisotropicBrownianFiltration n (q:ℝ).toNNReal
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n):=V
  have hK:=measurable_uncurry_anisotropicPastSpinSquareKernel D μ a q e
  have hF : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      if q < z.1 then anisotropicPastSpinSquareKernel D μ a q z.1 e z.2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) hK measurable_const
  unfold anisotropicFutureSpinSquareKernelIntegral
  exact hF.stronglyMeasurable.integral_prod_left' (μ:=(μ:Measure Paper.Overlap))

theorem norm_anisotropicFutureSpinSquareKernelIntegral_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : Fin n)
    (p : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicFutureSpinSquareKernelIntegral D μ a q e p‖ ≤ 1 := by
  unfold anisotropicFutureSpinSquareKernelIntegral
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=(μ:Measure Paper.Overlap))
    (C:=1) (.of_forall fun r=>by
      split_ifs
      · exact norm_anisotropicPastSpinSquareKernel_le D μ a q r e p
      · simp)

private theorem integral_weighted_strict_future {A : Type*} [MeasurableSpace A]
    (μ : Paper.ParisiMeasure) (P : Measure A) [IsProbabilityMeasure P] (q : Paper.Overlap)
    (K : Paper.Overlap×A→ℝ) (hK : Measurable K) (hKb : ∀z,‖K z‖ ≤ 1)
    (Z : A→ℝ) (hZ : Measurable Z) (B : ℝ≥0) (hB : ∀p,‖Z p‖ ≤ B) :
    (∫p,Z p*(∫r : Paper.Overlap,if q < r then K (r,p) else 0 ∂(μ:Measure Paper.Overlap)) ∂P)=
      ∫r : Paper.Overlap,if q < r then (∫p,Z p*K (r,p) ∂P) else 0 ∂(μ:Measure Paper.Overlap) := by
  classical
  let F:=fun z : Paper.Overlap×A=>Z z.2*(if q < z.1 then K z else 0)
  have hm : Measurable F:=(hZ.comp measurable_snd).mul
    (Measurable.ite (measurableSet_lt measurable_const measurable_fst) hK measurable_const)
  have hi : Integrable F ((μ:Measure Paper.Overlap).prod P):=
    (integrable_const (B:ℝ)).mono' hm.aestronglyMeasurable (.of_forall fun z=>by
      dsimp only [F]
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_left (show ‖if q < z.1 then K z else 0‖ ≤ 1 from ?_)
        (norm_nonneg (Z z.2))).trans
      · simpa only [mul_one] using hB z.2
      · split_ifs
        · exact hKb z
        · simp)
  calc
    _ = ∫p,(∫r : Paper.Overlap,F (r,p) ∂(μ:Measure Paper.Overlap)) ∂P := by
      apply integral_congr_ae
      exact .of_forall fun p=>(integral_const_mul (Z p) _).symm
    _ = ∫r : Paper.Overlap,(∫p,F (r,p) ∂P) ∂(μ:Measure Paper.Overlap) := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      exact .of_forall fun r=>by
        by_cases hqr:q < r
        · simp only [F,ite_eq_left hqr]
        · simp only [F,ite_eq_right hqr,mul_zero,integral_zero]

theorem anisotropicFutureSpinSquareKernelIntegral_weighted_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : Fin n)
    (Z : AnisotropicDisorderBrownianSample n→ℝ)
    (hZ : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] Z)
    (B : ℝ≥0) (hB : ∀p,‖Z p‖ ≤ B) :
    (∫p,Z p*anisotropicFutureSpinSquareKernelIntegral D μ a q e p ∂anisotropicMeasureSampleLaw D μ a)=
      ∫p,Z p*anisotropicRawFutureSpinSquare D μ q e p ∂anisotropicMeasureSampleLaw D μ a := by
  classical
  let P:=anisotropicMeasureSampleLaw D μ a
  have hinc : @Measurable (AnisotropicDisorderBrownianSample n) (AnisotropicDisorderBrownianSample n)
      inferInstance (anisotropicBrownianFiltration n (q:ℝ).toNNReal) id :=
    measurable_id'' ((anisotropicBrownianFiltration n).le _)
  have hmap : @Measurable (Paper.Overlap×AnisotropicDisorderBrownianSample n)
      (Paper.Overlap×AnisotropicDisorderBrownianSample n) inferInstance
      ((inferInstance : MeasurableSpace Paper.Overlap).prod (anisotropicBrownianFiltration n (q:ℝ).toNNReal))
      (fun z=>(z.1,id z.2)) := measurable_fst.prodMk (hinc.comp measurable_snd)
  have hK:=(measurable_uncurry_anisotropicPastSpinSquareKernel D μ a q e).comp hmap
  have hZm:=hZ.mono ((anisotropicBrownianFiltration n).le _) le_rfl
  have hraw:=(measurable_uncurry_anisotropicProcessSpinResponse D μ e).pow_const 2
  have hrawb (z : Paper.Overlap×AnisotropicDisorderBrownianSample n) :
      ‖(anisotropicProcessSpinResponse D μ z.1 e z.2)^2‖ ≤ 1 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessSpinResponse_bound D μ z.1 e z.2) 2).trans_eq (by norm_num)
  unfold anisotropicFutureSpinSquareKernelIntegral anisotropicRawFutureSpinSquare
  rw [integral_weighted_strict_future μ P q
    (fun z=>anisotropicPastSpinSquareKernel D μ a q z.1 e z.2) hK
    (fun z=>norm_anisotropicPastSpinSquareKernel_le D μ a q z.1 e z.2) Z hZm B hB,
    integral_weighted_strict_future μ P q
    (fun z=>(anisotropicProcessSpinResponse D μ z.1 e z.2)^2) hraw hrawb Z hZm B hB]
  apply integral_congr_ae
  exact .of_forall fun r=>by
    by_cases hqr:q < r
    · simp only [ite_eq_left hqr]
      exact anisotropicPastSpinSquareKernel_weighted_pairing D μ a q r e Z hZ B hB
    · simp only [ite_eq_right hqr]

end QuantitativeFollowup
