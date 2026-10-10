module
public import QuantitativePaper.VectorFiniteControlCells
public import QuantitativePaper.VectorBoundedTimeIntegral

@[expose] public section

/-! Genuine bounded measurable global square-gap source for a finite
profile, evaluated along the constructed controlled diffusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

def vectorFiniteControlGradient (s : RSBScheme k) (β t : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : Field n :=
  vectorFiniteTailGradient s β t (projIcc (0 : ℝ) 1 zero_le_one r) sample.1
    (vectorControlledState ((1-t)*β^2) μ A r sample)

def vectorFiniteControlSource (s : RSBScheme k) (β t : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  ((1-t)*β^2)/2*Paper.parisiCDF μ r*‖A r sample‖^2-
    ((1-t)*β^2)/2*Paper.parisiCDF μ r*
      ‖vectorFiniteControlGradient s β t μ A r sample-A r sample‖^2+
    ((1-t)*β^2)/2*(Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r)*
      ‖vectorFiniteControlGradient s β t μ A r sample‖^2

theorem measurable_vectorFiniteControlGradient (s : RSBScheme k) (β t : ℝ)
    (μ : Paper.ParisiMeasure) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hA : IsVectorParisiControl A) :
    Measurable (Function.uncurry (vectorFiniteControlGradient s β t μ A)) := by
  simpa only [Function.comp_def,vectorFiniteControlGradient,Function.uncurry_def] using
    (measurable_vectorFiniteTailGradient s β t).comp
      (show Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n =>
        (projIcc (0 : ℝ) 1 zero_le_one z.1,
          (z.2.1,vectorControlledState ((1-t)*β^2) μ A z.1 z.2))) from
        (((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp NNReal.continuous_coe).measurable.comp measurable_fst).prodMk
          ((measurable_fst.comp measurable_snd).prodMk (measurable_vectorControlledState _ μ A hA)))

theorem measurable_vectorFiniteControlSource (s : RSBScheme k) (β t : ℝ)
    (μ : Paper.ParisiMeasure) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hA : IsVectorParisiControl A) :
    Measurable (Function.uncurry (vectorFiniteControlSource s β t μ A)) := by
  have hG := measurable_vectorFiniteControlGradient s β t μ A hA
  have hμ : Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n => Paper.parisiCDF μ z.1) := (Paper.parisiCDF_monotone μ).measurable.comp
    (NNReal.continuous_coe.measurable.comp measurable_fst)
  have hs : Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n => Paper.parisiCDF (Paper.parisiSchemeMeasure s) z.1) := (Paper.parisiCDF_monotone (Paper.parisiSchemeMeasure s)).measurable.comp
    (NNReal.continuous_coe.measurable.comp measurable_fst)
  exact ((measurable_const.mul hμ).mul (hA.measurable.norm.pow_const 2)).sub
    ((measurable_const.mul hμ).mul ((hG.sub hA.measurable).norm.pow_const 2)) |>.add
      ((measurable_const.mul (hμ.sub hs)).mul (hG.norm.pow_const 2))

theorem norm_vectorFiniteControlSource_le (s : RSBScheme k) (β t : ℝ)
    (μ : Paper.ParisiMeasure) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (hA : IsVectorParisiControl A) (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖vectorFiniteControlSource s β t μ A r sample‖≤3*|((1-t)*β^2)| *(n : ℝ) := by
  let G := vectorFiniteControlGradient s β t μ A r sample
  let c := (1-t)*β^2
  have hG : ‖G‖≤Real.sqrt (n : ℝ) := norm_vectorFiniteTailGradient_le s β t _ _ _
  have hAs := hA.norm_le r sample
  have hG2 : ‖G‖^2≤(n : ℝ) := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),norm_nonneg G]
  have hA2 : ‖A r sample‖^2≤(n : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),norm_nonneg (A r sample)]
  have hGA : ‖G-A r sample‖≤2*Real.sqrt (n : ℝ) :=
    (norm_sub_le _ _).trans (by linarith)
  have hGA2 : ‖G-A r sample‖^2≤4*(n : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),norm_nonneg (G-A r sample),Real.sqrt_nonneg (n : ℝ)]
  have hμ := Paper.parisiCDF_nonneg μ r
  have hμ1 := Paper.parisiCDF_le_one μ r
  have hs := Paper.parisiCDF_nonneg (Paper.parisiSchemeMeasure s) r
  have hs1 := Paper.parisiCDF_le_one (Paper.parisiSchemeMeasure s) r
  have hd : |Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r|≤1 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  have hc := abs_nonneg c
  have h1 : |c/2*Paper.parisiCDF μ r*‖A r sample‖^2|≤|c| /2*(n : ℝ) := by
    simp only [abs_mul,abs_div,abs_of_nonneg (by norm_num : (0 : ℝ)≤2),abs_of_nonneg hμ,abs_pow,abs_norm]
    calc
      _ ≤ (|c| / 2*1)*(n : ℝ) := by gcongr
      _ = _ := by ring
  have h2 : |c/2*Paper.parisiCDF μ r*‖G-A r sample‖^2|≤|c| /2*(4*(n : ℝ)) := by
    simp only [abs_mul,abs_div,abs_of_nonneg (by norm_num : (0 : ℝ)≤2),abs_of_nonneg hμ,abs_pow,abs_norm]
    calc
      _ ≤ (|c| / 2*1)*(4*(n : ℝ)) := by gcongr
      _ = _ := by ring
  have h3 : |c/2*(Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r)*‖G‖^2|
      ≤|c| /2*(n : ℝ) := by
    simp only [abs_mul,abs_div,abs_of_nonneg (by norm_num : (0 : ℝ)≤2),abs_pow,abs_norm]
    calc
      _ ≤ (|c| / 2*1)*(n : ℝ) := by gcongr
      _ = _ := by ring
  rw [Real.norm_eq_abs]
  change |c/2*Paper.parisiCDF μ r*‖A r sample‖^2-c/2*Paper.parisiCDF μ r*‖G-A r sample‖^2+
    c/2*(Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r)*‖G‖^2|≤_
  have htri := norm_add_le (c/2*Paper.parisiCDF μ r*‖A r sample‖^2-
    c/2*Paper.parisiCDF μ r*‖G-A r sample‖^2)
    (c/2*(Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r)*‖G‖^2)
  have htri2 := norm_sub_le (c/2*Paper.parisiCDF μ r*‖A r sample‖^2)
    (c/2*Paper.parisiCDF μ r*‖G-A r sample‖^2)
  simp only [Real.norm_eq_abs] at htri htri2
  change _≤3*|c| *(n : ℝ)
  linarith

theorem vectorFiniteControlSource_eq_cell (s : RSBScheme k) (β t : ℝ)
    (μ : Paper.ParisiMeasure) (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (i : ℕ) (hi : i≤k+1) (r : ℝ≥0) (hr : (r : ℝ)∈Ico (s.q i) (s.q (i+1)))
    (sample : VectorDisorderBrownianSample n) :
    vectorFiniteControlSource s β t μ A r sample=
      vectorFiniteControlCellSource s β t μ sample.1 i r
        (vectorControlledState ((1-t)*β^2) μ A r sample) (A r sample) := by
  have hr01 : (r : ℝ)∈Icc (0 : ℝ) 1 :=
    ⟨(s.q_nonneg (by omega)).trans hr.1,hr.2.le.trans (s.q_le_one (by omega))⟩
  have hG : vectorFiniteControlGradient s β t μ A r sample=
      gradient (vectorFiniteCellPotential s β t sample.1 i r)
        (vectorControlledState ((1-t)*β^2) μ A r sample) := by
    unfold vectorFiniteControlGradient vectorFiniteTailGradient
    rw [projIcc_of_mem zero_le_one hr01]
    congr 1
    exact vectorTailRecursion_eq_finiteCell s β t r sample.1 i hi ⟨hr.1,hr.2.le⟩
  rw [vectorFiniteControlSource,vectorFiniteControlCellSource,hG,Paper.parisiCDF_scheme_cell s hi hr]

end QuantitativePaper
