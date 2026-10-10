module
public import HexagonPaper.CavityFixedRowMixtureNative
public import QuantitativeFollowup.FollowupCavityMixtureScaledCovariance

@[expose] public section

/-! The exact quotient-to-covariance trace calculation for the actual
arbitrary-profile fixed-row law. Physical heat factories and the genuine
row-reversal symmetry are separate inputs to this intermediate receiver. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped BigOperators ContDiff
namespace HexagonPaper
open FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

def cavityNativeFixedRowMean (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (F : AnisotropicDisorder (n+1) ×
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T → ℝ)
    (θ : QuantitativePaper.Field n) : ℝ :=
  ∫ z, F z ∂cavityNativeFixedRowLaw D μ a q T θ

def cavityNativeFixedRowCovariance (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (F G : AnisotropicDisorder (n+1) ×
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T → ℝ)
    (θ : QuantitativePaper.Field n) : ℝ :=
  cavityNativeFixedRowMean D μ a q T (fun z => F z * G z) θ -
    cavityNativeFixedRowMean D μ a q T F θ * cavityNativeFixedRowMean D μ a q T G θ

def cavityNativeGaussianRowCovariance (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (F G : AnisotropicDisorder (n+1) ×
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T → ℝ) (v : ℝ) : ℝ :=
  (∫ z, F z * G z ∂cavityNativeGaussianRowLaw D μ a q T v) -
    (∫ z, F z ∂cavityNativeGaussianRowLaw D μ a q T v) *
    (∫ z, G z ∂cavityNativeGaussianRowLaw D μ a q T v)

theorem cavityNativeGaussianRowMean_eq_weighted (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : ℝ)
    (F : AnisotropicDisorder (n+1) ×
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T → ℝ)
    (hF : Measurable F) (B : ℝ) (hb : ∀ z, ‖F z‖ ≤ B) :
    (∫ z, F z ∂cavityNativeGaussianRowLaw D μ a q T v) =
      cavityRowWeightedAverage (cavityNativeFixedRowNormalizer D μ a)
        (cavityNativeFixedRowMean D μ a q T F) v :=
  cavityNativeFixedRow_weighted_mixture_standard D μ a q T v F hF B hb

theorem cavityNativeGaussianRowCovariance_eq_weighted (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j)
    (F G : AnisotropicDisorder (n+1) ×
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (B E : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖F z‖ ≤ B) (he : ∀ z, ‖G z‖ ≤ E) (v : ℝ) :
    cavityNativeGaussianRowCovariance D μ a q T F G v =
      cavityRowWeightedAverage (cavityNativeFixedRowNormalizer D μ a)
        (cavityNativeFixedRowMean D μ a q T (fun z => F z * G z)) v -
      cavityRowWeightedAverage (cavityNativeFixedRowNormalizer D μ a)
        (cavityNativeFixedRowMean D μ a q T F) v *
      cavityRowWeightedAverage (cavityNativeFixedRowNormalizer D μ a)
        (cavityNativeFixedRowMean D μ a q T G) v := by
  have hfg (z) : ‖F z * G z‖ ≤ B * E := by
    rw [norm_mul]
    exact mul_le_mul (hb z) (he z) (norm_nonneg _) hB
  unfold cavityNativeGaussianRowCovariance
  rw [cavityNativeGaussianRowMean_eq_weighted D μ a q T v
      (fun z => F z * G z) (hF.mul hG) (B*E) hfg,
    cavityNativeGaussianRowMean_eq_weighted D μ a q T v F hF B hb,
    cavityNativeGaussianRowMean_eq_weighted D μ a q T v G hG E he]

theorem cavityNativeGaussianRowCovariance_zero_trace_from_heat_data
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (F G : AnisotropicDisorder (n+1) ×
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (B E : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖F z‖ ≤ B) (he : ∀ z, ‖G z‖ ≤ E)
    (hZ : CavityRowHeatData (cavityNativeFixedRowNormalizer D μ a))
    (hf : ContDiff ℝ 2 (cavityNativeFixedRowMean D μ a q T F))
    (hg : ContDiff ℝ 2 (cavityNativeFixedRowMean D μ a q T G))
    (hh : ContDiff ℝ 2 (cavityNativeFixedRowMean D μ a q T (fun z => F z * G z)))
    (hZf : CavityRowHeatData (fun θ => cavityNativeFixedRowNormalizer D μ a θ *
      cavityNativeFixedRowMean D μ a q T F θ))
    (hZg : CavityRowHeatData (fun θ => cavityNativeFixedRowNormalizer D μ a θ *
      cavityNativeFixedRowMean D μ a q T G θ))
    (hZh : CavityRowHeatData (fun θ => cavityNativeFixedRowNormalizer D μ a θ *
      cavityNativeFixedRowMean D μ a q T (fun z => F z * G z) θ))
    (hZzero : fderiv ℝ (cavityNativeFixedRowNormalizer D μ a) 0 = 0)
    (hfzero : fderiv ℝ (cavityNativeFixedRowMean D μ a q T F) 0 = 0)
    (α : ℝ) (hα : 0 ≤ α) :
    HasDerivWithinAt (fun u => cavityNativeGaussianRowCovariance D μ a q T F G
      (α / (n:ℝ) * u))
      (α / (2 * (n:ℝ)) * ∑ i : Fin n,
        fderiv ℝ (fderiv ℝ (cavityNativeFixedRowCovariance D μ a q T F G)) 0
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i))
      (Ici (0:ℝ)) 0 := by
  have hd := hasDerivWithinAt_cavityRowWeightedCovariance_scaled_zero
    (cavityNativeFixedRowNormalizer D μ a)
    (cavityNativeFixedRowMean D μ a q T F)
    (cavityNativeFixedRowMean D μ a q T G)
    (cavityNativeFixedRowMean D μ a q T (fun z => F z * G z))
    hZ hf hg hh hZf hZg hZh (cavityNativeFixedRowNormalizer_pos D μ a 0)
    hZzero hfzero (α / (n:ℝ)) (div_nonneg hα (Nat.cast_nonneg n))
  have hd' := hd.congr_of_mem (fun u _ =>
    (cavityNativeGaussianRowCovariance_eq_weighted D μ a q T F G hF hG B E hB hb he _))
    (show (0:ℝ) ∈ Ici (0:ℝ) by simp)
  convert hd' using 1
  unfold cavityRowHessianTrace cavityNativeFixedRowCovariance
  congr 1
  ring

end HexagonPaper
