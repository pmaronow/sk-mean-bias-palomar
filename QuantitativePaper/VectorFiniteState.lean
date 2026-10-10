module
public import QuantitativePaper.VectorAdditiveL2
public import QuantitativePaper.VectorFiniteTailGradient
public import Paper.ParisiSchemeMeasure

@[expose] public section

/-! The actual finite-profile vector diffusion driven by independent Wiener
coordinates and initial SK completion disorder. Its drift is the genuine
finite restarted-tail gradient, with dimension-only bounded/Lipschitz data. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1000000
variable {n k : ℕ}

def vectorDiffusionRate (β t : ℝ) (ht : t ≤ 1) : ℝ≥0 :=
  ⟨(1-t)*β^2,mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)⟩

def vectorFiniteDrift (s : RSBScheme k) (β t : ℝ) (r : ℝ≥0)
    (p : Couplings n×ℝ) (x : Field n) : Field n :=
  ((1-t)*β^2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) r) •
    vectorFiniteTailGradient (n := n) s β t (projIcc (0 : ℝ) 1 zero_le_one r) p x

theorem measurable_vectorFiniteDrift (s : RSBScheme k) (β t : ℝ) :
    Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n) => vectorFiniteDrift (n := n) s β t z.1 z.2.1 z.2.2) := by
  have hCDF : Measurable (Paper.parisiCDF (Paper.parisiSchemeMeasure s)) :=
    (Paper.parisiCDF_monotone (Paper.parisiSchemeMeasure s)).measurable
  have hc : Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n) =>
      (1-t)*β^2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) z.1) :=
    (measurable_const (a := (1-t)*β^2)).mul (hCDF.comp
      (NNReal.continuous_coe.measurable.comp measurable_fst))
  have hclamp : Measurable (fun r : ℝ≥0 =>
      (projIcc (0 : ℝ) 1 zero_le_one r : Paper.Overlap)) :=
    continuous_projIcc.measurable.comp NNReal.continuous_coe.measurable
  have harg : Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n) =>
      ((projIcc (0 : ℝ) 1 zero_le_one z.1 : Paper.Overlap),z.2)) :=
    (hclamp.comp measurable_fst).prodMk measurable_snd
  have hgrad : Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n) =>
      vectorFiniteTailGradient (n := n) s β t (projIcc (0 : ℝ) 1 zero_le_one z.1) z.2.1 z.2.2) :=
    by
      have hh := (measurable_vectorFiniteTailGradient (n := n) s β t).comp harg
      simpa only [Function.comp_def] using hh
  change Measurable (fun z : ℝ≥0×((Couplings n×ℝ)×Field n) =>
    ((1-t)*β^2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) z.1) •
      vectorFiniteTailGradient (n := n) s β t (projIcc (0 : ℝ) 1 zero_le_one z.1) z.2.1 z.2.2)
  exact hc.smul hgrad

theorem norm_vectorFiniteDrift_le (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) :
    ∀ r p x,‖vectorFiniteDrift (n := n) s β t r p x‖ ≤ ((1-t)*β^2)*Real.sqrt n := by
  intro r p x
  have hα := Paper.parisiCDF_nonneg (Paper.parisiSchemeMeasure s) r
  have hα1 := Paper.parisiCDF_le_one (Paper.parisiSchemeMeasure s) r
  have hc : 0 ≤ (1-t)*β^2 := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
  rw [vectorFiniteDrift,norm_smul,Real.norm_of_nonneg (mul_nonneg hc hα)]
  change (1-t)*β^2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) r*
    ‖vectorFiniteTailGradient (n := n) s β t _ p x‖ ≤ ((1-t)*β^2)*Real.sqrt n
  calc
    _ ≤ (1-t)*β^2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) r*Real.sqrt n := by
      gcongr
      exact norm_vectorFiniteTailGradient_le s β t _ p x
    _ ≤ _ := by nlinarith [mul_nonneg hc (Real.sqrt_nonneg (n : ℝ))]

theorem vectorFiniteDrift_lipschitz (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) :
    ∀ r p,LipschitzWith (vectorDiffusionRate β t ht*(n : ℝ≥0)) (vectorFiniteDrift (n := n) s β t r p) := by
  intro r p
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hα := Paper.parisiCDF_nonneg (Paper.parisiSchemeMeasure s) r
  have hα1 := Paper.parisiCDF_le_one (Paper.parisiSchemeMeasure s) r
  have hc : 0 ≤ (1-t)*β^2 := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
  have hg := (vectorFiniteTailGradient_lipschitz s β t
    (projIcc (0 : ℝ) 1 zero_le_one r) p).dist_le_mul x y
  simp only [dist_eq_norm,vectorFiniteDrift] at hg ⊢
  rw [← smul_sub,norm_smul,Real.norm_of_nonneg (mul_nonneg hc hα)]
  change (1-t)*β^2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) r*
    ‖vectorFiniteTailGradient (n := n) s β t _ p x-vectorFiniteTailGradient (n := n) s β t _ p y‖ ≤
    ((1-t)*β^2*n)*‖x-y‖
  calc
    _ ≤ (1-t)*β^2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) r*((n : ℝ)*‖x-y‖) :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg hc hα)
    _ ≤ _ := by
      have hh : (1-t)*β^2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) r ≤ (1-t)*β^2 :=
        by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hh (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg (x-y)))]

/-- Verified regularity data for the actual finite Parisi drift. -/
def vectorFiniteDriftData (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) : VectorAdditiveDriftData n where
  drift := vectorFiniteDrift (n := n) s β t
  bound := ⟨(vectorDiffusionRate β t ht : ℝ)*Real.sqrt n,by positivity⟩
  spatialLip := vectorDiffusionRate β t ht*(n : ℝ≥0)
  measurable := measurable_vectorFiniteDrift (n := n) s β t
  norm_le := norm_vectorFiniteDrift_le (n := n) s β t ht
  lipschitz := vectorFiniteDrift_lipschitz (n := n) s β t ht

def vectorFiniteState (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : Field n :=
  vectorAdditiveState (vectorFiniteDriftData s β t ht)
    (Real.sqrt ((1-t)*β^2)) 0 1 r sample

theorem continuous_vectorFiniteState (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1)
    (sample : VectorDisorderBrownianSample n) : Continuous (fun r=>vectorFiniteState s β t ht r sample) :=
  continuous_vectorAdditiveState _ _ _ _ _

theorem measurable_uncurry_vectorFiniteState (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) :
    Measurable (Function.uncurry (vectorFiniteState (n := n) s β t ht)) :=
  measurable_uncurry_vectorAdditiveState _ _ _ _

theorem stronglyAdapted_vectorFiniteState (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) :
    StronglyAdapted (vectorBrownianFiltration n) (vectorFiniteState (n := n) s β t ht) :=
  stronglyAdapted_vectorAdditiveState _ _ _ _

@[simp] theorem vectorFiniteState_zero (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1)
    (sample : VectorDisorderBrownianSample n) : vectorFiniteState s β t ht 0 sample = 0 :=
  vectorAdditiveState_zero _ _ _ _ _

theorem memLp_vectorFiniteState (s : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) (r : ℝ≥0) :
    MemLp (vectorFiniteState (n := n) s β t ht r) 2 (vectorDisorderBrownianMeasure n) :=
  memLp_vectorAdditiveState _ _ _ _ _

end QuantitativePaper
