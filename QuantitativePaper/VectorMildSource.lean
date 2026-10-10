module
public import QuantitativePaper.VectorMeasureGradientStability
public import Paper.ParisiCDFIntegral

@[expose] public section

/-! Gaussian averaging of the genuine squared gradient, including its
bounded measurable source and uniform approximation estimates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 400000

def vectorGradientHeatAverage {n : ℕ}
    (v : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
    (c q s : ℝ) (p : Couplings n×ℝ) (x : Field n) : ℝ :=
  ∫ z,‖v (projIcc (0 : ℝ) 1 zero_le_one s) p (fieldShift (c*(s-q)) x z)‖^2 ∂fieldGaussian n

theorem measurable_vectorGradientHeatAverage_time {n : ℕ}
    (v : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
    (hv : Measurable (fun z : Paper.Overlap×VectorParameter n => v z.1 z.2.1 z.2.2))
    (c q : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    Measurable (fun s : ℝ => vectorGradientHeatAverage v c q s p x) := by
  have hh : Measurable (fun z : ℝ×Field n =>
      ‖v (projIcc (0 : ℝ) 1 zero_le_one z.1) p (fieldShift (c*(z.1-q)) x z.2)‖^2) := by
    apply Measurable.pow_const
    apply Measurable.norm
    let insert : ℝ×Field n→Paper.Overlap×VectorParameter n :=
      fun z => (projIcc (0 : ℝ) 1 zero_le_one z.1,(p,fieldShift (c*(z.1-q)) x z.2))
    have hi : Measurable insert := by unfold insert fieldShift;fun_prop
    simpa only [Function.comp_def,insert] using hv.comp hi
  exact (hh.stronglyMeasurable.integral_prod_right' (ν := fieldGaussian n)).measurable

theorem vectorGradientHeatAverage_bounds {n : ℕ}
    (v : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
    (hv : ∀s p x,‖v s p x‖≤Real.sqrt (n : ℝ))
    (c q s : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    0≤vectorGradientHeatAverage v c q s p x ∧ vectorGradientHeatAverage v c q s p x≤n := by
  refine ⟨integral_nonneg (fun _ => sq_nonneg _),?_⟩
  have hh := norm_integral_le_of_norm_le_const (μ := fieldGaussian n)
    (f := fun z => ‖v (projIcc (0 : ℝ) 1 zero_le_one s) p (fieldShift (c*(s-q)) x z)‖^2)
    (C := (n : ℝ)) (Eventually.of_forall (fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [hv (projIcc (0 : ℝ) 1 zero_le_one s) p (fieldShift (c*(s-q)) x z),
        Real.sq_sqrt (Nat.cast_nonneg n),norm_nonneg
          (v (projIcc (0 : ℝ) 1 zero_le_one s) p (fieldShift (c*(s-q)) x z))]))
  simp only [probReal_univ,mul_one] at hh
  have hh' : |vectorGradientHeatAverage v c q s p x|≤(n : ℝ) := by
    simpa only [vectorGradientHeatAverage,Real.norm_eq_abs] using hh
  exact (le_abs_self _).trans hh'

theorem abs_norm_sq_sub_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    (u v : E) (R : ℝ) (hu : ‖u‖≤R) (hv : ‖v‖≤R) :
    |‖u‖^2-‖v‖^2|≤2*R*dist u v := by
  calc
    _ = |(‖u‖-‖v‖)*(‖u‖+‖v‖)| := by congr 1;ring
    _ = |‖u‖-‖v‖| * (‖u‖+‖v‖) := by
      rw [abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v))]
    _ ≤ dist u v*(2*R) := mul_le_mul
      (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le u v) (by linarith)
      (by positivity) (by positivity)
    _ = _ := by ring

theorem vectorGradientHeatAverage_sub_le {n : ℕ}
    (v w : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
    (hv : Measurable (fun z : Paper.Overlap×VectorParameter n => v z.1 z.2.1 z.2.2))
    (hw : Measurable (fun z : Paper.Overlap×VectorParameter n => w z.1 z.2.1 z.2.2))
    (hbv : ∀s p x,‖v s p x‖≤Real.sqrt (n : ℝ))
    (hbw : ∀s p x,‖w s p x‖≤Real.sqrt (n : ℝ))
    (ε : ℝ) (he : ∀s p x,dist (v s p x) (w s p x)≤ε)
    (c q s : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    |vectorGradientHeatAverage v c q s p x-vectorGradientHeatAverage w c q s p x|≤
      2*Real.sqrt (n : ℝ)*ε := by
  let z₀ := projIcc (0 : ℝ) 1 zero_le_one s
  have hme (a : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
      (ha : Measurable (fun z : Paper.Overlap×VectorParameter n => a z.1 z.2.1 z.2.2)) :
      Measurable (fun z : Field n => ‖a z₀ p (fieldShift (c*(s-q)) x z)‖^2) := by
    apply Measurable.pow_const
    apply Measurable.norm
    let insert : Field n→Paper.Overlap×VectorParameter n :=
      fun z => (z₀,(p,fieldShift (c*(s-q)) x z))
    have hi : Measurable insert := by unfold insert fieldShift;fun_prop
    simpa only [Function.comp_def,insert] using ha.comp hi
  have hi (a : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
      (ha : Measurable (fun z : Paper.Overlap×VectorParameter n => a z.1 z.2.1 z.2.2))
      (hba : ∀s p x,‖a s p x‖≤Real.sqrt (n : ℝ)) :
      Integrable (fun z : Field n => ‖a z₀ p (fieldShift (c*(s-q)) x z)‖^2) (fieldGaussian n) := by
    apply (integrable_const (n : ℝ)).mono' (hme a ha).aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hba z₀ p (fieldShift (c*(s-q)) x z),Real.sq_sqrt (Nat.cast_nonneg n),
      norm_nonneg (a z₀ p (fieldShift (c*(s-q)) x z))]
  unfold vectorGradientHeatAverage
  rw [←integral_sub (hi v hv hbv) (hi w hw hbw),←Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le_const (μ := fieldGaussian n)
    (f := fun z => ‖v z₀ p (fieldShift (c*(s-q)) x z)‖^2-
      ‖w z₀ p (fieldShift (c*(s-q)) x z)‖^2)
    (C := 2*Real.sqrt (n : ℝ)*ε) (Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs]
      exact (abs_norm_sq_sub_norm_sq_le _ _ _ (hbv _ _ _) (hbw _ _ _)).trans
        (mul_le_mul_of_nonneg_left (he _ _ _) (by positivity))))
  simpa only [probReal_univ,mul_one] using hh

def vectorMildSource {n : ℕ} (μ : Paper.ParisiMeasure)
    (v : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
    (c q s : ℝ) (p : Couplings n×ℝ) (x : Field n) : ℝ :=
  Paper.parisiCDF μ s*vectorGradientHeatAverage v c q s p x

theorem vectorMildSource_sub_le {n : ℕ} (μ ν : Paper.ParisiMeasure)
    (v w : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
    (hv : Measurable (fun z : Paper.Overlap×VectorParameter n => v z.1 z.2.1 z.2.2))
    (hw : Measurable (fun z : Paper.Overlap×VectorParameter n => w z.1 z.2.1 z.2.2))
    (hbv : ∀s p x,‖v s p x‖≤Real.sqrt (n : ℝ))
    (hbw : ∀s p x,‖w s p x‖≤Real.sqrt (n : ℝ))
    (ε : ℝ) (he : ∀s p x,dist (v s p x) (w s p x)≤ε)
    (c q s : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    |vectorMildSource μ v c q s p x-vectorMildSource ν w c q s p x|≤
      (n : ℝ)*|Paper.parisiCDF μ s-Paper.parisiCDF ν s|+2*Real.sqrt (n : ℝ)*ε := by
  have hV := vectorGradientHeatAverage_bounds v hbv c q s p x
  have hW := vectorGradientHeatAverage_bounds w hbw c q s p x
  have hE := vectorGradientHeatAverage_sub_le v w hv hw hbv hbw ε he c q s p x
  have hα := Paper.parisiCDF_nonneg ν s
  have hα1 := Paper.parisiCDF_le_one ν s
  unfold vectorMildSource
  calc
    _ ≤ |(Paper.parisiCDF μ s-Paper.parisiCDF ν s)*vectorGradientHeatAverage v c q s p x|+
      |Paper.parisiCDF ν s*(vectorGradientHeatAverage v c q s p x-
        vectorGradientHeatAverage w c q s p x)| := by
      convert abs_add_le ((Paper.parisiCDF μ s-Paper.parisiCDF ν s)*vectorGradientHeatAverage v c q s p x)
        (Paper.parisiCDF ν s*(vectorGradientHeatAverage v c q s p x-
          vectorGradientHeatAverage w c q s p x)) using 1 <;> congr 1 <;> ring
    _ ≤ _ := by
      rw [abs_mul,abs_mul,abs_of_nonneg hV.1,abs_of_nonneg hα]
      have h₁ := mul_le_mul_of_nonneg_left hV.2 (abs_nonneg (Paper.parisiCDF μ s-Paper.parisiCDF ν s))
      have h₂ := mul_le_mul_of_nonneg_right hα1
        (abs_nonneg (vectorGradientHeatAverage v c q s p x-vectorGradientHeatAverage w c q s p x))
      nlinarith

theorem vectorMildSource_bounds {n : ℕ} (μ : Paper.ParisiMeasure)
    (v : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
    (hv : ∀s p x,‖v s p x‖≤Real.sqrt (n : ℝ))
    (c q s : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    0≤vectorMildSource μ v c q s p x ∧ vectorMildSource μ v c q s p x≤n := by
  have hV := vectorGradientHeatAverage_bounds v hv c q s p x
  have hα := Paper.parisiCDF_nonneg μ s
  have hα1 := Paper.parisiCDF_le_one μ s
  unfold vectorMildSource
  constructor
  · exact mul_nonneg hα hV.1
  · nlinarith

theorem intervalIntegrable_vectorMildSource {n : ℕ} (μ : Paper.ParisiMeasure)
    (v : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
    (hv : Measurable (fun z : Paper.Overlap×VectorParameter n => v z.1 z.2.1 z.2.2))
    (hbv : ∀s p x,‖v s p x‖≤Real.sqrt (n : ℝ))
    (c q a b : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    IntervalIntegrable (fun s => vectorMildSource μ v c q s p x) volume a b := by
  have hm : Measurable (fun s => vectorMildSource μ v c q s p x) :=
    (Paper.parisiCDF_monotone μ).measurable.mul
      (measurable_vectorGradientHeatAverage_time v hv c q p x)
  apply (intervalIntegrable_const (c := (n : ℝ))).mono_fun' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro s
  change ‖vectorMildSource μ v c q s p x‖≤(n : ℝ)
  rw [Real.norm_of_nonneg (vectorMildSource_bounds μ v hbv c q s p x).1]
  exact (vectorMildSource_bounds μ v hbv c q s p x).2

theorem vectorMildSource_integral_sub_le {n : ℕ} (μ ν : Paper.ParisiMeasure)
    (v w : Paper.Overlap→(Couplings n×ℝ)→Field n→Field n)
    (hv : Measurable (fun z : Paper.Overlap×VectorParameter n => v z.1 z.2.1 z.2.2))
    (hw : Measurable (fun z : Paper.Overlap×VectorParameter n => w z.1 z.2.1 z.2.2))
    (hbv : ∀s p x,‖v s p x‖≤Real.sqrt (n : ℝ))
    (hbw : ∀s p x,‖w s p x‖≤Real.sqrt (n : ℝ))
    (ε : ℝ) (hε : 0≤ε) (he : ∀s p x,dist (v s p x) (w s p x)≤ε)
    (c : ℝ) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    |(∫ s in (q : ℝ)..1,vectorMildSource μ v c q s p x)-
      ∫ s in (q : ℝ)..1,vectorMildSource ν w c q s p x|≤
      (n : ℝ)*Paper.parisiCDFDistance μ ν+2*Real.sqrt (n : ℝ)*ε := by
  have hiv := intervalIntegrable_vectorMildSource μ v hv hbv c q q 1 p x
  have hiw := intervalIntegrable_vectorMildSource ν w hw hbw c q q 1 p x
  have hiD := Paper.parisiCDF_abs_diff_intervalIntegrable μ ν q 1
  have hI := intervalIntegral.integral_mono_interval q.property.1 q.property.2 le_rfl
    (Eventually.of_forall (fun _ => abs_nonneg _))
    (Paper.parisiCDF_abs_diff_intervalIntegrable μ ν 0 1)
  have hE : 0≤2*Real.sqrt (n : ℝ)*ε := by positivity
  rw [←intervalIntegral.integral_sub hiv hiw]
  calc
    _ ≤ ∫ s in (q : ℝ)..1,|vectorMildSource μ v c q s p x-vectorMildSource ν w c q s p x| :=
      intervalIntegral.abs_integral_le_integral_abs q.property.2
    _ ≤ ∫ s in (q : ℝ)..1,((n : ℝ)*|Paper.parisiCDF μ s-Paper.parisiCDF ν s|+
        2*Real.sqrt (n : ℝ)*ε) :=
      intervalIntegral.integral_mono q.property.2 (hiv.sub hiw).abs
        ((hiD.const_mul (n : ℝ)).add intervalIntegrable_const)
        (fun s => vectorMildSource_sub_le μ ν v w hv hw hbv hbw ε he c q s p x)
    _ = (n : ℝ)*(∫ s in (q : ℝ)..1,|Paper.parisiCDF μ s-Paper.parisiCDF ν s|)+
        (1-(q : ℝ))*(2*Real.sqrt (n : ℝ)*ε) := by
      rw [intervalIntegral.integral_add (hiD.const_mul (n : ℝ)) intervalIntegrable_const,
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const,smul_eq_mul]
    _ ≤ _ := by
      have ht : 1-(q : ℝ)≤1 := by linarith [q.property.1]
      have hc := mul_le_mul_of_nonneg_right ht hE
      have hN := mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg n)
      dsimp only [Paper.parisiCDFDistance]
      linarith

end QuantitativePaper
