module
public import QuantitativePaper.VectorTiltedLinearIsometry
public import FourPapersCommon.FiniteL2Sum

@[expose] public section

/-! Finite adapted linear sums against the actual vector Brownian motion
have exact orthogonal L² sums under every fractional disorder tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

theorem stronglyMeasurable_known_vectorLinearIncrement_at_later
    (r u v : ℝ≥0) (hru : r ≤ u) (huv : u ≤ v)
    (L : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hL : Measurable[vectorBrownianFiltration n r] L) :
    StronglyMeasurable[vectorBrownianFiltration n v]
      (fun sample => L sample (disorderVectorBrownianIncrement r u sample)) := by
  have hLv := hL.stronglyMeasurable.mono ((vectorBrownianFiltration n).mono (hru.trans huv))
  have hBv : StronglyMeasurable[vectorBrownianFiltration n v]
      (disorderVectorBrownianIncrement (n := n) r u) :=
    ((stronglyAdapted_disorderVectorBrownian n u).mono ((vectorBrownianFiltration n).mono huv)).sub
      ((stronglyAdapted_disorderVectorBrownian n r).mono
        ((vectorBrownianFiltration n).mono (hru.trans huv)))
  exact (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hLv.prodMk hBv)

theorem memLp_tilted_bounded_CLM (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1)
    (r : ℝ≥0) (L : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hL : Measurable[vectorBrownianFiltration n r] L) (K : ℝ≥0)
    (hK : ∀ sample, ‖L sample‖ ≤ K) : MemLp L 2 (vectorMeasureDisorderTilt μ β t a) := by
  have := vectorMeasureDisorderTilt_probability (n := n) μ β t a ht
  exact MemLp.of_bound ((hL.mono ((vectorBrownianFiltration n).le r) le_rfl).aestronglyMeasurable)
    K (.of_forall hK)

theorem integral_tilted_disjoint_vectorLinearIncrements (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (r u v w : ℝ≥0) (hru : r ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (L₁ L₂ : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hL₁ : Measurable[vectorBrownianFiltration n r] L₁)
    (hL₂ : Measurable[vectorBrownianFiltration n v] L₂) (K₁ K₂ : ℝ≥0)
    (hK₁ : ∀ sample, ‖L₁ sample‖ ≤ K₁) (hK₂ : ∀ sample, ‖L₂ sample‖ ≤ K₂) :
    (∫ sample, L₁ sample (disorderVectorBrownianIncrement r u sample)*
      L₂ sample (disorderVectorBrownianIncrement v w sample) ∂vectorMeasureDisorderTilt μ β t a)=0 := by
  have := vectorMeasureDisorderTilt_probability (n := n) μ β t a ht
  let Y : VectorDisorderBrownianSample n → ℝ := fun sample =>
    L₁ sample (disorderVectorBrownianIncrement r u sample)
  have hY2 := memLp_tilted_known_CLM_increment μ β t a ht r u hru L₁ hL₁
    (memLp_tilted_bounded_CLM μ β t a ht r L₁ hL₁ K₁ hK₁)
  have hYv : StronglyMeasurable[vectorBrownianFiltration n v] Y :=
    stronglyMeasurable_known_vectorLinearIncrement_at_later r u v hru huv L₁ hL₁
  let Z : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ) := fun sample => Y sample • L₂ sample
  have hZv : StronglyMeasurable[vectorBrownianFiltration n v] Z :=
    hYv.smul hL₂.stronglyMeasurable
  have hiZ : Integrable Z (vectorMeasureDisorderTilt μ β t a) := by
    apply ((hY2.integrable (by norm_num)).norm.const_mul (K₂ : ℝ)).mono'
      (hZv.mono ((vectorBrownianFiltration n).le v)).aestronglyMeasurable
    exact .of_forall fun sample => by
      dsimp only [Z]
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hK₂ sample) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have h := integral_tilted_known_CLM_increment μ β t a ht v w hvw Z hZv.measurable hiZ
  simpa only [Z, Y, ContinuousLinearMap.smul_apply, smul_eq_mul] using h

def vectorBrownianLinearSum {m : ℕ} (T : Fin (m+1) → ℝ≥0)
    (H : Fin m → VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∑ i : Fin m, H i sample (disorderVectorBrownianIncrement (T i.castSucc) (T i.succ) sample)

theorem memLp_vectorBrownianLinearSum {m : ℕ} (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (T : Fin (m+1) → ℝ≥0) (hT : Monotone T)
    (H : Fin m → VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hH : ∀ i, Measurable[vectorBrownianFiltration n (T i.castSucc)] (H i))
    (K : ℝ≥0) (hK : ∀ i sample, ‖H i sample‖ ≤ K) :
    MemLp (vectorBrownianLinearSum T H) 2 (vectorMeasureDisorderTilt μ β t a) := by
  exact memLp_finsetSum Finset.univ (fun i _ =>
    memLp_tilted_known_CLM_increment μ β t a ht _ _
      (hT (show i.castSucc ≤ i.succ by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega))
      (H i) (hH i) (memLp_tilted_bounded_CLM μ β t a ht _ (H i) (hH i) K (hK i)))

theorem integral_vectorBrownianLinearSum_square {m : ℕ} (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (T : Fin (m+1) → ℝ≥0) (hT : Monotone T)
    (H : Fin m → VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hH : ∀ i, Measurable[vectorBrownianFiltration n (T i.castSucc)] (H i))
    (K : ℝ≥0) (hK : ∀ i sample, ‖H i sample‖ ≤ K) :
    (∫ sample, (vectorBrownianLinearSum T H sample)^2 ∂vectorMeasureDisorderTilt μ β t a) =
      ∑ i : Fin m, ((T i.succ : ℝ)-T i.castSucc)*
        ∫ sample, (∑ j : Fin n, (H i sample (EuclideanSpace.single j 1))^2)
          ∂vectorMeasureDisorderTilt μ β t a := by
  classical
  let Y : Fin m → VectorDisorderBrownianSample n → ℝ := fun i sample =>
    H i sample (disorderVectorBrownianIncrement (T i.castSucc) (T i.succ) sample)
  have hstep (i : Fin m) : T i.castSucc ≤ T i.succ :=
    hT (show i.castSucc ≤ i.succ by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
  have hH2 (i : Fin m) := memLp_tilted_bounded_CLM μ β t a ht _ (H i) (hH i) K (hK i)
  have hY (i : Fin m) : MemLp (Y i) 2 (vectorMeasureDisorderTilt μ β t a) :=
    memLp_tilted_known_CLM_increment μ β t a ht _ _ (hstep i) (H i) (hH i) (hH2 i)
  have horth (i j : Fin m) (hij : i < j) :
      (∫ sample, Y i sample*Y j sample ∂vectorMeasureDisorderTilt μ β t a)=0 := by
    have hsep : T i.succ ≤ T j.castSucc :=
      hT (show i.succ ≤ j.castSucc by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        have hv : i.val < j.val := hij
        omega)
    exact integral_tilted_disjoint_vectorLinearIncrements μ β t a ht _ _ _ _
      (hstep i) hsep (hstep j) (H i) (H j) (hH i) (hH j) K K (hK i) (hK j)
  have hsum := integral_finset_sum_square (vectorMeasureDisorderTilt μ β t a) Finset.univ Y
    (fun i _ => hY i) (by
      intro i _ j _ hij
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact horth i j hlt
      · simpa only [mul_comm] using horth j i hgt)
  change (∫ sample, (∑ i : Fin m, Y i sample)^2 ∂vectorMeasureDisorderTilt μ β t a) = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_tilted_known_CLM_increment_sq μ β t a ht _ _ (hstep i) (H i) (hH i) (hH2 i)

end QuantitativePaper
