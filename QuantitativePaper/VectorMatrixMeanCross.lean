module
public import QuantitativePaper.VectorMatrixBrownianSums

@[expose] public section

/-! Actual componentwise martingale conditioning, assembled into a vector
inner-product cross identity for adapted matrix Brownian sums. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem integral_vectorMatrixBrownianSum_cross_martingale {m : ℕ}
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1)
    (M : Paper.Overlap → VectorDisorderBrownianSample n → Field n)
    (hM : ∀ l, Martingale (fun q sample => M q sample l)
      (QuantitativeFollowup.vectorOverlapFiltration n) (vectorMeasureDisorderTilt μ β t a))
    (hM2 : ∀ q l, MemLp (fun sample => M q sample l) 2 (vectorMeasureDisorderTilt μ β t a))
    (T : Fin (m+1) → Paper.Overlap) (hT : Monotone T)
    (H : Fin m → VectorDisorderBrownianSample n → (Field n →L[ℝ] Field n))
    (hH : ∀ i, Measurable[vectorBrownianFiltration n (T i.castSucc : ℝ).toNNReal] (H i))
    (K : ℝ≥0) (hK : ∀ i sample, ‖H i sample‖ ≤ K) :
    (∫ sample, inner ℝ (M (T (Fin.last m)) sample-M (T 0) sample)
      (vectorMatrixBrownianSum (fun i => (T i : ℝ).toNNReal) H sample)
        ∂vectorMeasureDisorderTilt μ β t a) =
      ∑ i : Fin m, ∫ sample, inner ℝ (M (T i.succ) sample-M (T i.castSucc) sample)
        (H i sample (disorderVectorBrownianIncrement
          (T i.castSucc : ℝ).toNNReal (T i.succ : ℝ).toNNReal sample))
          ∂vectorMeasureDisorderTilt μ β t a := by
  let P := vectorMeasureDisorderTilt (n := n) μ β t a
  let TN := fun i => (T i : ℝ).toNNReal
  have hTN : Monotone TN := fun i j hij => Real.toNNReal_mono (hT hij)
  have hR (i : Fin m) (l : Fin n) : Measurable[vectorBrownianFiltration n (TN i.castSucc)]
      (fun sample => (EuclideanSpace.proj l).comp (H i sample)) :=
    (ContinuousLinearMap.compL ℝ (Field n) (Field n) ℝ (EuclideanSpace.proj l)).continuous.measurable.comp (hH i)
  have hRb (i : Fin m) (l : Fin n) (sample : VectorDisorderBrownianSample n) :
      ‖(EuclideanSpace.proj l).comp (H i sample)‖ ≤ K :=
    (norm_vectorMatrix_row_le _ l).trans (hK i sample)
  have hS2 (l : Fin n) : MemLp (fun sample => vectorMatrixBrownianSum TN H sample l) 2 P := by
    simp_rw [vectorMatrixBrownianSum_component]
    exact memLp_vectorBrownianLinearSum μ β t a ht TN hTN _ (fun i => hR i l) K (fun i => hRb i l)
  have hpair (o z : Paper.Overlap) (i : Fin m) (l : Fin n) : Integrable
      (fun sample => (M z sample l-M o sample l)*
        (H i sample (disorderVectorBrownianIncrement (TN i.castSucc) (TN i.succ) sample) l)) P := by
    have hi := memLp_tilted_known_CLM_increment μ β t a ht
      (TN i.castSucc) (TN i.succ) (hTN (Fin.castSucc_le_succ i))
      (fun sample => (EuclideanSpace.proj l).comp (H i sample)) (hR i l)
      (memLp_tilted_bounded_CLM μ β t a ht (TN i.castSucc) _ (hR i l) K (fun sample => hRb i l sample))
    convert memLp_one_iff_integrable.mp (((hM2 z l).sub (hM2 o l)).mul hi) using 1
    funext sample
    rfl
  have hwhole (l : Fin n) : Integrable (fun sample =>
      (M (T (Fin.last m)) sample l-M (T 0) sample l)*vectorMatrixBrownianSum TN H sample l) P :=
    memLp_one_iff_integrable.mp (((hM2 _ l).sub (hM2 _ l)).mul (hS2 l))
  have hl (l : Fin n) : (∫ sample, (M (T (Fin.last m)) sample l-M (T 0) sample l)*
      vectorMatrixBrownianSum TN H sample l ∂P) =
      ∑ i : Fin m, ∫ sample, (M (T i.succ) sample l-M (T i.castSucc) sample l)*
        (H i sample (disorderVectorBrownianIncrement (TN i.castSucc) (TN i.succ) sample) l) ∂P := by
    simp_rw [vectorMatrixBrownianSum_component]
    exact integral_vectorBrownianLinearSum_cross_martingale μ β t a ht _ (hM l)
      (fun q => hM2 q l) T hT _ (fun i => hR i l) K (fun i => hRb i l)
  have he (x y : Field n) : inner ℝ x y=∑l : Fin n,x l*y l := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  simp_rw [he, PiLp.sub_apply]
  rw [integral_finsetSum Finset.univ (fun l _ => hwhole l)]
  simp_rw [hl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum Finset.univ (fun l _ => hpair (T i.castSucc) (T i.succ) i l)).symm

end QuantitativePaper
