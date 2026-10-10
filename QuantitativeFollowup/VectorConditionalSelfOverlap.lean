module
public import QuantitativeFollowup.VectorScoreConditional

@[expose] public section

/-! Genuine conditional Jensen for the actual vector spin means, and the
later-level score comparison under the literal marked diffusion law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem square_condExp_le_condExp_square {Ω : Type*} [m0 : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (X : Ω→ℝ) (hX : MemLp X 2 P) :
    (fun ω=>P[X|m] ω^2)≤ᵐ[P]P[(fun ω=>X ω^2)|m] := by
  have he:=condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX
  have hn : 0≤ᵐ[P]condVar m X P :=
    condExp_nonneg (.of_forall fun ω=>sq_nonneg (X ω-P[X|m] ω))
  filter_upwards [he,hn] with ω hω hnω
  change 0≤condVar m X P ω at hnω
  change condVar m X P ω=P[(fun ω=>X ω^2)|m] ω-P[X|m] ω^2 at hω
  linarith

theorem norm_square_vectorMeasureSpinMean_le_condExp (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) {q p : Paper.Overlap} (hqp : q≤p) :
    (fun z : VectorDisorderBrownianSample n×Configuration n=>‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2)
      ≤ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
    (vectorMeasureSpinPathLaw μ β t a ht.le)[
      (fun z : VectorDisorderBrownianSample n×Configuration n=>‖vectorMeasureSpinMean μ β t ht.le p z.1‖^2)|
      vectorSpinPast n (q:ℝ).toNNReal] := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=inferInstance
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  let m:=vectorSpinPast n (q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n×Configuration n):=ambient
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  let X : Fin n→(VectorDisorderBrownianSample n×Configuration n)→ℝ:=
    fun i z=>vectorMeasureSpinMean μ β t ht.le p z.1 i
  have hX (i : Fin n) : MemLp (X i) 2 J :=
    MemLp.of_bound ((adapted_vectorMeasureSpinMean_joint μ β t ht.le p i).mono
      (vectorSpinPast_le n _) le_rfl).aestronglyMeasurable 1
      (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using
        vectorMeasureSpinMean_component_bound μ β t ht.le p z.1 i)
  have hs:=condExp_finsetSum (μ:=J) (s:=Finset.univ) (fun i _=>(hX i).integrable_sq) m
  have hall:=ae_all_iff.2 (fun i : Fin n=>square_condExp_le_condExp_square J m (vectorSpinPast_le n _) (X i) (hX i))
  have hmean:=ae_all_iff.2 (fun i : Fin n=>condExp_vectorMeasureSpinMean_joint_component μ β t a hβ ht hqp i)
  have he : (∑i : Fin n,fun z=>X i z^2)=(fun z : VectorDisorderBrownianSample n×Configuration n=>
      ‖vectorMeasureSpinMean μ β t ht.le p z.1‖^2) := by
    funext z
    simp only [Finset.sum_apply,EuclideanSpace.real_norm_sq_eq,X]
  rw [he] at hs
  filter_upwards [hs,hall,hmean] with z hs hall hmean
  change ‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2≤J[(fun z=>‖vectorMeasureSpinMean μ β t ht.le p z.1‖^2)|m] z
  rw [hs,EuclideanSpace.real_norm_sq_eq]
  simp only [Finset.sum_apply]
  apply Finset.sum_le_sum
  intro i _
  have hi:=hall i
  rw [hmean i] at hi
  exact hi

theorem condExp_vectorMeasureOverlapScore_same (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (p : Paper.Overlap) :
    (vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureOverlapScore μ β t ht.le p|
      vectorSpinPast n (p:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun z=>‖vectorMeasureSpinMean μ β t ht.le p z.1‖^2/(2*(n:ℝ)) := by
  simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] using
    condExp_vectorMeasureOverlapScore_past (n:=n) μ β t a hβ ht (p:=p) (q:=p) le_rfl

theorem vectorMeasureOverlapScore_future_comparison (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) {q p : Paper.Overlap} (hqp : q≤p) :
    (fun z : VectorDisorderBrownianSample n×Configuration n=>
      ‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ))≤ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      (fun z=>2*((vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureOverlapScore μ β t ht.le p|
        vectorSpinPast n (q:ℝ).toNNReal] z)) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hp:=condExp_vectorMeasureOverlapScore_same (n:=n) μ β t a hβ ht p
  have hsame := (condExp_condExp_of_le (f:=vectorMeasureOverlapScore (n:=n) μ β t ht.le p)
    (vectorSpinPast_mono hqp) (vectorSpinPast_le n _)).symm.trans (condExp_congr_ae hp)
  have hscale:=condExp_smul (μ:=J) (2*(n:ℝ))⁻¹
    (fun z : VectorDisorderBrownianSample n×Configuration n=>‖vectorMeasureSpinMean μ β t ht.le p z.1‖^2)
    (vectorSpinPast n (q:ℝ).toNNReal)
  have he : (fun z : VectorDisorderBrownianSample n×Configuration n=>
      ‖vectorMeasureSpinMean μ β t ht.le p z.1‖^2/(2*(n:ℝ)))=
      (2*(n:ℝ))⁻¹ •(fun z : VectorDisorderBrownianSample n×Configuration n=>
        ‖vectorMeasureSpinMean μ β t ht.le p z.1‖^2) := by
    funext z
    simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [he] at hsame
  have hnorm:=norm_square_vectorMeasureSpinMean_le_condExp (n:=n) μ β t a hβ ht hqp
  filter_upwards [hsame,hscale,hnorm] with z hz hscale hnorm
  rw [hz,hscale]
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _≤J[(fun z=>‖vectorMeasureSpinMean μ β t ht.le p z.1‖^2)|vectorSpinPast n (q:ℝ).toNNReal] z/(n:ℝ) :=
      div_le_div_of_nonneg_right hnorm (Nat.cast_nonneg n)
    _=_ := by simp only [div_eq_mul_inv,mul_inv_rev];ring

end QuantitativeFollowup
