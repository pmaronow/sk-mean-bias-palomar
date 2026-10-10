module
public import QuantitativePaper.VectorAdditiveL2
public import QuantitativePaper.VectorMeasureGradientStability
public import Paper.ParisiSchemeMeasure

@[expose] public section

/-! The actual arbitrary-profile vector diffusion driven by independent Wiener
coordinates and initial SK completion disorder. Its drift is the genuine
constructed arbitrary-profile gradient, with dimension-only bounded/Lipschitz data. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1000000
variable {n : ℕ}

def vectorMeasureDiffusionRate (β t : ℝ) (ht : t ≤ 1) : ℝ≥0 :=
  ⟨(1-t)*β^2,mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)⟩

def vectorMeasureDrift (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1) (r : ℝ≥0)
    (p : Couplings n×ℝ) (x : Field n) : Field n :=
  ((1-t)*β^2*Paper.parisiCDF μ r) •
    vectorMeasureGradient μ β t (projIcc (0 : ℝ) 1 zero_le_one r) p x

/-- These are verified regularity data for the actual arbitrary-profile Parisi drift. -/
def vectorMeasureDriftData (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1) : VectorAdditiveDriftData n where
  drift := vectorMeasureDrift μ β t ht
  bound := ⟨(vectorMeasureDiffusionRate β t ht : ℝ)*Real.sqrt n,by positivity⟩
  spatialLip := vectorMeasureDiffusionRate β t ht*(n : ℝ≥0)
  measurable := by
    have hCDF : Measurable (Paper.parisiCDF μ) :=
      (Paper.parisiCDF_monotone μ).measurable
    have hc : Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n) =>
        (1-t)*β^2*Paper.parisiCDF μ z.1) :=
      (measurable_const (a := (1-t)*β^2)).mul (hCDF.comp
        (NNReal.continuous_coe.measurable.comp measurable_fst))
    let insert : ℝ≥0×((Couplings n×ℝ)×Field n)→Paper.Overlap×VectorParameter n :=
      fun z => (projIcc (0 : ℝ) 1 zero_le_one z.1,z.2)
    have hInsert : Measurable insert := by unfold insert;fun_prop
    have hgrad := (measurable_vectorMeasureGradient (n := n) μ β t ht).comp hInsert
    change Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n) =>
      ((1-t)*β^2*Paper.parisiCDF μ z.1) •
        vectorMeasureGradient μ β t (projIcc (0 : ℝ) 1 zero_le_one z.1) z.2.1 z.2.2)
    convert hc.smul hgrad using 1
    funext z
    rfl
  norm_le := by
    intro r p x
    have hα := Paper.parisiCDF_nonneg μ r
    have hα1 := Paper.parisiCDF_le_one μ r
    have hc : 0 ≤ (1-t)*β^2 := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
    rw [vectorMeasureDrift,norm_smul,Real.norm_of_nonneg (mul_nonneg hc hα)]
    change (1-t)*β^2*Paper.parisiCDF μ r*
      ‖vectorMeasureGradient μ β t _ p x‖ ≤ ((1-t)*β^2)*Real.sqrt n
    calc
      _ ≤ (1-t)*β^2*Paper.parisiCDF μ r*Real.sqrt n := by
        gcongr
        exact norm_vectorMeasureGradient_le μ β t ht _ p x
      _ ≤ _ := by nlinarith [mul_nonneg hc (Real.sqrt_nonneg (n : ℝ))]
  lipschitz := by
    intro r p
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hα := Paper.parisiCDF_nonneg μ r
    have hα1 := Paper.parisiCDF_le_one μ r
    have hc : 0 ≤ (1-t)*β^2 := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
    have hg := (vectorMeasureGradient_lipschitz μ β t ht
      (projIcc (0 : ℝ) 1 zero_le_one r) p).dist_le_mul x y
    simp only [dist_eq_norm] at hg ⊢
    rw [vectorMeasureDrift,vectorMeasureDrift,←smul_sub,norm_smul,
      Real.norm_of_nonneg (mul_nonneg hc hα)]
    change (1-t)*β^2*Paper.parisiCDF μ r*
      ‖vectorMeasureGradient μ β t _ p x-vectorMeasureGradient μ β t _ p y‖ ≤
      ((1-t)*β^2*n)*‖x-y‖
    calc
      _ ≤ (1-t)*β^2*Paper.parisiCDF μ r*((n : ℝ)*‖x-y‖) :=
        mul_le_mul_of_nonneg_left hg (mul_nonneg hc hα)
      _ ≤ _ := by
        have hh : (1-t)*β^2*Paper.parisiCDF μ r ≤ (1-t)*β^2 :=
          by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hh (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg (x-y)))]

def vectorMeasureState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : Field n :=
  vectorAdditiveState (vectorMeasureDriftData μ β t ht)
    (Real.sqrt ((1-t)*β^2)) 0 1 r sample

theorem continuous_vectorMeasureState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (sample : VectorDisorderBrownianSample n) : Continuous (fun r=>vectorMeasureState μ β t ht r sample) :=
  continuous_vectorAdditiveState _ _ _ _ _

theorem measurable_uncurry_vectorMeasureState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1) :
    Measurable (Function.uncurry (vectorMeasureState (n := n) μ β t ht)) :=
  measurable_uncurry_vectorAdditiveState _ _ _ _

theorem stronglyAdapted_vectorMeasureState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1) :
    StronglyAdapted (vectorBrownianFiltration n) (vectorMeasureState (n := n) μ β t ht) :=
  stronglyAdapted_vectorAdditiveState _ _ _ _

@[simp] theorem vectorMeasureState_zero (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (sample : VectorDisorderBrownianSample n) : vectorMeasureState μ β t ht 0 sample = 0 :=
  vectorAdditiveState_zero _ _ _ _ _

theorem memLp_vectorMeasureState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1) (r : ℝ≥0) :
    MemLp (vectorMeasureState (n := n) μ β t ht r) 2 (vectorDisorderBrownianMeasure n) :=
  memLp_vectorAdditiveState _ _ _ _ _

theorem vectorMeasureState_equation (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureState μ β t ht r sample=
      Real.sqrt ((1-t)*β^2) • disorderVectorBrownian r sample+
      ∫ s in (0 : ℝ)..(r : ℝ),((1-t)*β^2*Paper.parisiCDF μ s) •
        vectorMeasureGradient μ β t (projIcc (0 : ℝ) 1 zero_le_one s) sample.1
          (vectorMeasureState μ β t ht s.toNNReal sample) := by
  have hh := vectorAdditiveState_equation (vectorMeasureDriftData μ β t ht)
    (Real.sqrt ((1-t)*β^2)) 0 1 r hr sample
  change vectorMeasureState μ β t ht r sample=0+_+_ at hh
  rw [zero_add] at hh
  refine hh.trans ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le r.coe_nonneg] at hs
  change ((1-t)*β^2*Paper.parisiCDF μ (s.toNNReal : ℝ)) •
    vectorMeasureGradient μ β t (projIcc (0 : ℝ) 1 zero_le_one (s.toNNReal : ℝ)) sample.1
      (vectorMeasureState μ β t ht s.toNNReal sample)=_
  rw [Real.coe_toNNReal s hs.1]

end QuantitativePaper
