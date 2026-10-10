module
public import QuantitativeFollowup.AnisotropicWhitenedFiniteState
public import QuantitativeFollowup.AnisotropicWhitenedIto
public import QuantitativePaper.VectorAdditiveStability

@[expose] public section

/-! Actual same-Wiener-driver stability from finite anisotropic profiles to
the arbitrary-profile Picard state. The time error is the genuine CDF L1
distance and the actual uniform Gaussian-tail response error. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 800000

theorem anisotropicWhitenedFiniteDrift_sub_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (e : ℝ) (he : 0 ≤ e)
    (hresp : ∀q P,‖anisotropicFiniteTailMagnetization D s q P-
      anisotropicMeasureTailMagnetization D μ q P‖ ≤ e)
    (r : ℝ≥0) (p : Couplings n×ℝ) (y : Field n) :
    ‖anisotropicWhitenedFiniteDrift D s g r p y-anisotropicWhitenedDrift D μ g r p y‖ ≤
      ‖anisotropicNoiseMap D‖*Real.sqrt (n : ℝ)*
        |Paper.parisiCDF (Paper.parisiSchemeMeasure s) r-Paper.parisiCDF μ r|+
      ‖anisotropicNoiseMap D‖*e := by
  let q : Paper.Overlap := projIcc (0 : ℝ) 1 zero_le_one r
  let P := anisotropicDisorderInjection n g+anisotropicUnitInput D y
  let x := anisotropicFiniteTailMagnetization D s q P
  let z := anisotropicMeasureTailMagnetization D μ q P
  let a := Paper.parisiCDF (Paper.parisiSchemeMeasure s) r
  let b := Paper.parisiCDF μ r
  have heq : a • anisotropicNoiseMap D x-b • anisotropicNoiseMap D z=
      (a-b) • anisotropicNoiseMap D x+b • anisotropicNoiseMap D (x-z) := by
    rw [map_sub,sub_smul,smul_sub]
    abel
  change ‖a • anisotropicNoiseMap D x-b • anisotropicNoiseMap D z‖ ≤ _
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ r)]
  have hx : ‖anisotropicNoiseMap D x‖ ≤ ‖anisotropicNoiseMap D‖*Real.sqrt (n : ℝ) :=
    ((anisotropicNoiseMap D).le_opNorm x).trans (mul_le_mul_of_nonneg_left
      (norm_anisotropicFiniteTailMagnetization_le D s q P) (norm_nonneg _))
  have hz : ‖anisotropicNoiseMap D (x-z)‖ ≤ ‖anisotropicNoiseMap D‖*e :=
    ((anisotropicNoiseMap D).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hresp q P) (norm_nonneg _))
  calc
    _ ≤ |a-b| *(‖anisotropicNoiseMap D‖*Real.sqrt (n : ℝ))+b*(‖anisotropicNoiseMap D‖*e) :=
      add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hz (Paper.parisiCDF_nonneg μ r))
    _ ≤ _ := by
      have hh := mul_le_of_le_one_left (mul_nonneg (norm_nonneg (anisotropicNoiseMap D)) he) (Paper.parisiCDF_le_one μ r)
      dsimp only [a,b]
      nlinarith

theorem anisotropicWhitenedFiniteState_sub_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (e : ℝ) (he : 0 ≤ e)
    (hresp : ∀q P,‖anisotropicFiniteTailMagnetization D s q P-
      anisotropicMeasureTailMagnetization D μ q P‖ ≤ e)
    (r : ℝ≥0) (hr : r ≤ 1) (sample : VectorDisorderBrownianSample n) :
    ‖anisotropicWhitenedFiniteState D s g r sample-
      vectorAdditiveState (anisotropicWhitenedDriftData D μ g) 1 0 1 r sample‖ ≤
      (‖anisotropicNoiseMap D‖*Real.sqrt (n : ℝ)*
        Paper.parisiCDFDistance (Paper.parisiSchemeMeasure s) μ+‖anisotropicNoiseMap D‖*e)*
      Real.exp (anisotropicWhitenedDriftLip D) := by
  let a := fun v : ℝ=>‖anisotropicNoiseMap D‖*Real.sqrt (n : ℝ)*
      |Paper.parisiCDF (Paper.parisiSchemeMeasure s) v-Paper.parisiCDF μ v|+‖anisotropicNoiseMap D‖*e
  have ha : IntervalIntegrable a volume 0 1 :=
    ((Paper.parisiCDF_abs_diff_intervalIntegrable _ _ 0 1).const_mul _).add intervalIntegrable_const
  have ha0 : ∀v∈Icc (0 : ℝ) 1,0 ≤ a v := by intro v _;dsimp only [a];positivity
  have hbound := norm_vectorAdditiveState_sub_le_of_L1Drift
    (anisotropicWhitenedFiniteDriftData D s g) (anisotropicWhitenedDriftData D μ g)
    1 0 1 a ha ha0 (fun v _ p y=>anisotropicWhitenedFiniteDrift_sub_le D s μ g e he hresp v p y)
    r hr sample
  have hi : (∫v in (0 : ℝ)..1,a v)=‖anisotropicNoiseMap D‖*Real.sqrt (n : ℝ)*
      Paper.parisiCDFDistance (Paper.parisiSchemeMeasure s) μ+‖anisotropicNoiseMap D‖*e := by
    rw [intervalIntegral.integral_add
      ((Paper.parisiCDF_abs_diff_intervalIntegrable _ _ 0 1).const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const,sub_zero,one_smul,Paper.parisiCDFDistance,a]
  simp only [NNReal.coe_one] at hbound
  rw [hi] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (add_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      (Paper.parisiCDFDistance_nonneg _ _)) (mul_nonneg (norm_nonneg _) he))
  apply Real.exp_le_exp.mpr
  change (anisotropicWhitenedDriftLip D : ℝ)*(r : ℝ) ≤ anisotropicWhitenedDriftLip D
  exact mul_le_of_le_one_right (anisotropicWhitenedDriftLip D).coe_nonneg hr

end QuantitativeFollowup
