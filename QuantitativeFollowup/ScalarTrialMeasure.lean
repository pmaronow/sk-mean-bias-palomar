module
public import QuantitativeFollowup.ScalarTrial
public import QuantitativePaper.ScalarVariational

@[expose] public section

/-! Actual probability measure whose CDF is the clipped scalar trial.
The construction uses the free Stieltjes measure and adds the atom at zero;
the CDF formula and the constrained-minimum admissibility are proved. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB
open scoped Topology ENNReal
namespace QuantitativeFollowup

def scalarClippedRealMeasure (s : ℝ) (μ : Paper.ParisiMeasure) : Measure ℝ :=
  (scalarTrialStieltjes 1 (by norm_num) s μ).measure +
    ENNReal.ofReal s • Measure.dirac 0

theorem scalarTrialStieltjes_leftLim_zero (s : ℝ) (hs : 0 ≤ s)
    (μ : Paper.ParisiMeasure) :
    Function.leftLim (scalarTrialStieltjes 1 (by norm_num) s μ) 0 = s := by
  apply tendsto_nhds_unique ((scalarTrialStieltjes 1 (by norm_num) s μ).mono.tendsto_leftLim 0)
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [mem_Iio] at hx
  simp [scalarTrialStieltjes_apply,scalarTrialProfile,parisiCDF_eq_zero_of_lt_zero μ hx,
    max_eq_left hs]

theorem scalarClippedRealMeasure_Icc (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (x : ℝ) (hx : 0 ≤ x) :
    scalarClippedRealMeasure s μ (Icc 0 x) = ENNReal.ofReal (max s (parisiCDF μ x)) := by
  rw [scalarClippedRealMeasure,Measure.add_apply,StieltjesFunction.measure_Icc,
    scalarTrialStieltjes_leftLim_zero s hs.1 μ,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' 0 measurableSet_Icc]
  simp only [indicator_of_mem (show (0 : ℝ) ∈ Icc 0 x from ⟨le_rfl,hx⟩),Pi.one_apply,mul_one,
    scalarTrialStieltjes_apply,scalarTrialProfile,one_mul]
  rw [←ENNReal.ofReal_add (sub_nonneg.mpr (le_max_left _ _)) hs.1]
  congr 1
  ring

theorem scalarClippedRealMeasure_Icc_zero_one (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) : scalarClippedRealMeasure s μ (Icc 0 1) = 1 := by
  rw [scalarClippedRealMeasure_Icc s hs μ 1 (by norm_num)]
  have hCDF : parisiCDF μ 1 = 1 := parisiCDF_eq_one_above_support μ
    (fun z hz => by obtain ⟨w,hw,rfl⟩ := hz; exact w.property.2) le_rfl
  rw [hCDF,max_eq_right hs.2,ENNReal.ofReal_one]

def scalarClippedOverlapMeasure (s : ℝ) (μ : Paper.ParisiMeasure) : Measure Paper.Overlap :=
  (scalarClippedRealMeasure s μ).comap (Subtype.val : Paper.Overlap → ℝ)

theorem scalarClippedOverlap_probability (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) : IsProbabilityMeasure (scalarClippedOverlapMeasure s μ) := by
  constructor
  rw [scalarClippedOverlapMeasure,comap_subtype_coe_apply measurableSet_Icc,
    image_univ,Subtype.range_coe,scalarClippedRealMeasure_Icc_zero_one s hs μ]

def scalarClippedTrialMeasure (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) : Paper.ParisiMeasure :=
  ⟨scalarClippedOverlapMeasure s μ,scalarClippedOverlap_probability s hs μ⟩

theorem scalarClippedTrialMeasure_cdf (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    parisiCDF (scalarClippedTrialMeasure s hs μ) x = max s (parisiCDF μ x) := by
  have hi : (Subtype.val : Paper.Overlap → ℝ) '' {r : Paper.Overlap | (r : ℝ) ≤ x} =
      Icc (0 : ℝ) x := by
    ext y
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact ⟨r.property.1,hr⟩
    · intro hy
      exact ⟨⟨y,⟨hy.1,hy.2.trans hx.2⟩⟩,hy.2,rfl⟩
  unfold parisiCDF
  change ((scalarClippedOverlapMeasure s μ) {r : Paper.Overlap | (r : ℝ) ≤ x}).toReal = _
  rw [scalarClippedOverlapMeasure,comap_subtype_coe_apply measurableSet_Icc,
    hi,scalarClippedRealMeasure_Icc s hs μ x hx.1,ENNReal.toReal_ofReal
      (hs.1.trans (le_max_left _ _))]
  rfl

theorem scalarClippedTrialMeasure_mem_floor (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) : scalarClippedTrialMeasure s hs μ ∈ QuantitativePaper.scalarFloor s := by
  rw [QuantitativePaper.mem_scalarFloor_iff]
  have he : QuantitativePaper.zeroMass (scalarClippedTrialMeasure s hs μ) =
      parisiCDF (scalarClippedTrialMeasure s hs μ) 0 := by
    unfold QuantitativePaper.zeroMass parisiCDF
    congr 2
    ext r
    simp only [mem_singleton_iff,mem_ofPred_eq]
    constructor
    · rintro rfl
      rfl
    · intro hr
      apply Subtype.ext
      exact le_antisymm hr r.property.1
  rw [he,scalarClippedTrialMeasure_cdf s hs μ 0 (by norm_num)]
  exact le_max_left _ _

end QuantitativeFollowup
