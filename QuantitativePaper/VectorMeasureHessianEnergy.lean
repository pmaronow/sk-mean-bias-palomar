module
public import QuantitativePaper.VectorMeasureSpatialContinuity
public import QuantitativeFollowup.VectorMeanOverlap

@[expose] public section

/-! The actual continuous squared-Hessian energy along the constructed
arbitrary-profile diffusion under its normalized fractional disorder tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def vectorHessianHilbertSquare (H : Field n→L[ℝ]Field n) : ℝ :=
  ∑l : Fin n,‖H (EuclideanSpace.single l 1)‖^2

theorem vectorHessianHilbertSquare_nonneg (H : Field n→L[ℝ]Field n) :
    0≤vectorHessianHilbertSquare H := Finset.sum_nonneg fun _ _=>sq_nonneg _

theorem vectorHessianHilbertSquare_le {H : Field n→L[ℝ]Field n}
    (hH : ‖H‖≤(n : ℝ)) : vectorHessianHilbertSquare H≤(n : ℝ)^3 := by
  calc
    _≤∑_l : Fin n,(n : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro l _
      have hh : ‖H (EuclideanSpace.single l 1)‖≤(n : ℝ) := by
        simpa only [PiLp.norm_single,norm_one,mul_one] using
          ((H.le_opNorm (EuclideanSpace.single l 1)).trans
            (mul_le_mul_of_nonneg_right hH (norm_nonneg _)))
      exact pow_le_pow_left₀ (norm_nonneg _) hh 2
    _=(n : ℝ)^3 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem continuous_vectorHessianHilbertSquare :
    Continuous (vectorHessianHilbertSquare (n:=n)) := by
  unfold vectorHessianHilbertSquare
  apply continuous_finsetSum
  intro l _
  exact ((continuous_id.clm_apply continuous_const).norm.pow 2)

def vectorMeasureHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : ℝ :=
  vectorHessianHilbertSquare (vectorMeasureHessian μ β t q sample.1
    (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))

theorem vectorMeasureHessianEnergy_nonneg_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    0≤vectorMeasureHessianEnergy μ β t ht q sample ∧
      vectorMeasureHessianEnergy μ β t ht q sample≤(n : ℝ)^3 :=
  ⟨vectorHessianHilbertSquare_nonneg _,vectorHessianHilbertSquare_le
    (norm_vectorMeasureHessian_le μ β t ht q sample.1 _)⟩

theorem measurable_vectorMeasureHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    Measurable (vectorMeasureHessianEnergy (n:=n) μ β t ht q) := by
  let insert : VectorDisorderBrownianSample n→Paper.Overlap×VectorParameter n :=
    fun sample=>(q,(sample.1,vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))
  have hX : Measurable (fun sample : VectorDisorderBrownianSample n=>
      vectorMeasureState μ β t ht (q : ℝ).toNNReal sample) :=
    ((stronglyAdapted_vectorMeasureState (n:=n) μ β t ht (q : ℝ).toNNReal).measurable).mono
      ((vectorBrownianFiltration n).le _) le_rfl
  have hm : Measurable insert := by
    exact measurable_const.prodMk (measurable_fst.prodMk hX)
  have hcomp := (continuous_vectorHessianHilbertSquare (n:=n)).measurable.comp
    ((continuous_vectorMeasureHessian (n:=n) μ β t ht).measurable.comp hm)
  change Measurable (fun sample : VectorDisorderBrownianSample n=>
    vectorHessianHilbertSquare (vectorMeasureHessian μ β t q sample.1
      (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample)))
  simpa only [insert,Function.comp_def] using hcomp

theorem continuous_vectorMeasureHessianEnergy_path (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun q : Paper.Overlap=>vectorMeasureHessianEnergy μ β t ht q sample) := by
  let insert : Paper.Overlap→Paper.Overlap×VectorParameter n := fun q=>
    (q,(sample.1,vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))
  have hcX : Continuous (fun q : Paper.Overlap=>vectorMeasureState μ β t ht (q : ℝ).toNNReal sample) :=
    (continuous_vectorMeasureState μ β t ht sample).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)
  have hc : Continuous insert:=continuous_id.prodMk (continuous_const.prodMk hcX)
  have hcomp := (continuous_vectorHessianHilbertSquare (n:=n)).comp
    ((continuous_vectorMeasureHessian (n:=n) μ β t ht).comp hc)
  simpa only [vectorMeasureHessianEnergy,insert,Function.comp_def] using hcomp

theorem integrable_vectorMeasureHessianEnergy (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    Integrable (vectorMeasureHessianEnergy (n:=n) μ β t ht q) (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply (integrable_const ((n : ℝ)^3)).mono'
    (measurable_vectorMeasureHessianEnergy μ β t ht q).aestronglyMeasurable
  filter_upwards with sample
  rw [Real.norm_eq_abs,abs_of_nonneg (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).1]
  exact (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).2

def vectorMeanOverlapDerivative (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) : ℝ :=
  ((1-t)*β^2)/(n : ℝ)*∫sample : VectorDisorderBrownianSample n,vectorMeasureHessianEnergy μ β t ht q sample
    ∂vectorMeasureDisorderTilt (n:=n) μ β t a

theorem continuous_vectorMeanOverlapDerivative (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) : Continuous (vectorMeanOverlapDerivative (n:=n) μ β t a ht) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  unfold vectorMeanOverlapDerivative
  apply Continuous.const_mul
  apply continuous_of_dominated (μ:=vectorMeasureDisorderTilt (n:=n) μ β t a)
    (bound:=fun _=>(n : ℝ)^3)
  · exact fun q=>(measurable_vectorMeasureHessianEnergy μ β t ht q).aestronglyMeasurable
  · intro q
    filter_upwards with sample
    rw [Real.norm_eq_abs,abs_of_nonneg (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).1]
    exact (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).2
  · exact integrable_const _
  · exact .of_forall fun sample=>continuous_vectorMeasureHessianEnergy_path μ β t ht sample

theorem vectorMeanOverlapDerivative_nonneg (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) : 0≤vectorMeanOverlapDerivative (n:=n) μ β t a ht q := by
  unfold vectorMeanOverlapDerivative
  exact mul_nonneg (div_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)) (Nat.cast_nonneg n))
    (integral_nonneg fun sample=>(vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).1)

end QuantitativePaper
