module
public import QuantitativePaper.VectorMeanBrownianCross

@[expose] public section

/-! Literal matrix-valued Brownian left sums, their exact Hilbert-square
isometry and actual spin-mean martingale cross identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def vectorMatrixBrownianSum {m : ℕ} (T : Fin (m+1) → ℝ≥0)
    (H : Fin m → VectorDisorderBrownianSample n → (Field n →L[ℝ] Field n))
    (sample : VectorDisorderBrownianSample n) : Field n :=
  ∑ i : Fin m, H i sample (disorderVectorBrownianIncrement (T i.castSucc) (T i.succ) sample)

theorem vectorMatrixBrownianSum_component {m : ℕ} (T : Fin (m+1) → ℝ≥0)
    (H : Fin m → VectorDisorderBrownianSample n → (Field n →L[ℝ] Field n))
    (sample : VectorDisorderBrownianSample n) (l : Fin n) :
    vectorMatrixBrownianSum T H sample l =
      vectorBrownianLinearSum T (fun i sample => (EuclideanSpace.proj l).comp (H i sample)) sample := by
  change (EuclideanSpace.proj l) (∑ i : Fin m, H i sample
    (disorderVectorBrownianIncrement (T i.castSucc) (T i.succ) sample)) = _
  rw [map_sum]
  rfl

theorem norm_vectorMatrix_row_le (H : Field n →L[ℝ] Field n) (l : Fin n) :
    ‖(EuclideanSpace.proj l).comp H‖ ≤ ‖H‖ := by
  apply ((EuclideanSpace.proj l).comp H).opNorm_le_bound (norm_nonneg H)
  intro x
  exact (PiLp.norm_apply_le _ l).trans (H.le_opNorm x)

theorem memLp_vectorMatrixBrownianSum {m : ℕ} (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (T : Fin (m+1) → ℝ≥0) (hT : Monotone T)
    (H : Fin m → VectorDisorderBrownianSample n → (Field n →L[ℝ] Field n))
    (hH : ∀ i, Measurable[vectorBrownianFiltration n (T i.castSucc)] (H i))
    (K : ℝ≥0) (hK : ∀ i sample, ‖H i sample‖ ≤ K) :
    MemLp (vectorMatrixBrownianSum T H) 2 (vectorMeasureDisorderTilt μ β t a) := by
  have hR (i : Fin m) (l : Fin n) : Measurable[vectorBrownianFiltration n (T i.castSucc)]
      (fun sample => (EuclideanSpace.proj l).comp (H i sample)) :=
    (ContinuousLinearMap.compL ℝ (Field n) (Field n) ℝ (EuclideanSpace.proj l)).continuous.measurable.comp
      (hH i)
  have hRb (i : Fin m) (l : Fin n) (sample : VectorDisorderBrownianSample n) :
      ‖(EuclideanSpace.proj l).comp (H i sample)‖ ≤ K :=
    (norm_vectorMatrix_row_le _ l).trans (hK i sample)
  have hcoord (l : Fin n) : MemLp (fun sample => vectorMatrixBrownianSum T H sample l) 2
      (vectorMeasureDisorderTilt μ β t a) := by
    simp_rw [vectorMatrixBrownianSum_component]
    exact memLp_vectorBrownianLinearSum μ β t a ht T hT _ (fun i => hR i l) K (fun i => hRb i l)
  have hm (i : Fin m) : StronglyMeasurable (fun sample => H i sample
      (disorderVectorBrownianIncrement (T i.castSucc) (T i.succ) sample)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (((hH i).mono ((vectorBrownianFiltration n).le _) le_rfl).stronglyMeasurable.prodMk
        (measurable_disorderVectorBrownianIncrement _ _).stronglyMeasurable)
  have hsm : StronglyMeasurable (vectorMatrixBrownianSum T H) := by
    convert Finset.stronglyMeasurable_sum Finset.univ (fun i _ => hm i) using 1
    funext sample
    simp only [vectorMatrixBrownianSum, Finset.sum_apply]
  apply (memLp_two_iff_integrable_sq_norm hsm.aestronglyMeasurable).mpr
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact integrable_finsetSum Finset.univ (fun l _ => (hcoord l).integrable_sq)

theorem integral_vectorMatrixBrownianSum_norm_sq {m : ℕ} (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (T : Fin (m+1) → ℝ≥0) (hT : Monotone T)
    (H : Fin m → VectorDisorderBrownianSample n → (Field n →L[ℝ] Field n))
    (hH : ∀ i, Measurable[vectorBrownianFiltration n (T i.castSucc)] (H i))
    (K : ℝ≥0) (hK : ∀ i sample, ‖H i sample‖ ≤ K) :
    (∫ sample, ‖vectorMatrixBrownianSum T H sample‖^2 ∂vectorMeasureDisorderTilt μ β t a) =
      ∑ i : Fin m, ((T i.succ : ℝ)-T i.castSucc)*
        ∫ sample, vectorHessianHilbertSquare (H i sample) ∂vectorMeasureDisorderTilt μ β t a := by
  have hR (i : Fin m) (l : Fin n) : Measurable[vectorBrownianFiltration n (T i.castSucc)]
      (fun sample => (EuclideanSpace.proj l).comp (H i sample)) :=
    (ContinuousLinearMap.compL ℝ (Field n) (Field n) ℝ (EuclideanSpace.proj l)).continuous.measurable.comp (hH i)
  have hRb (i : Fin m) (l : Fin n) (sample : VectorDisorderBrownianSample n) :
      ‖(EuclideanSpace.proj l).comp (H i sample)‖ ≤ K :=
    (norm_vectorMatrix_row_le _ l).trans (hK i sample)
  have hcoord (l : Fin n) : MemLp (fun sample => vectorMatrixBrownianSum T H sample l) 2
      (vectorMeasureDisorderTilt μ β t a) := by
    simp_rw [vectorMatrixBrownianSum_component]
    exact memLp_vectorBrownianLinearSum μ β t a ht T hT _ (fun i => hR i l) K (fun i => hRb i l)
  have hbasis (i : Fin m) (l j : Fin n) : Integrable
      (fun sample => (H i sample (EuclideanSpace.single j 1) l)^2) (vectorMeasureDisorderTilt μ β t a) := by
    have := vectorMeasureDisorderTilt_probability (n := n) μ β t a ht
    apply (MemLp.of_bound
      ((((EuclideanSpace.proj l).continuous.measurable.comp
        (((ContinuousLinearMap.apply ℝ (Field n)) (EuclideanSpace.single j 1 : Field n)).continuous.measurable.comp
          ((hH i).mono ((vectorBrownianFiltration n).le _) le_rfl)))).aestronglyMeasurable)
      (K : ℝ) (.of_forall fun sample => ?_) : MemLp _ 2 _).integrable_sq
    exact (PiLp.norm_apply_le _ l).trans (((H i sample).le_opNorm _).trans (by
      simpa only [PiLp.norm_single, norm_one, mul_one] using hK i sample))
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum Finset.univ (fun l _ => (hcoord l).integrable_sq)]
  simp_rw [vectorMatrixBrownianSum_component,
    integral_vectorBrownianLinearSum_square μ β t a ht T hT _ (fun i => hR i _) K (fun i => hRb i _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  congr 1
  simp only [vectorHessianHilbertSquare, EuclideanSpace.real_norm_sq_eq, ContinuousLinearMap.comp_apply,
    EuclideanSpace.coe_proj]
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun l _ => hbasis i l j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hbasis i _ j),
    integral_finsetSum Finset.univ (fun l _ => hbasis i l _)]
  exact Finset.sum_comm

end QuantitativePaper
