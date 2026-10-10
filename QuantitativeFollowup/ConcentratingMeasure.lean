module
public import QuantitativeFollowup.ConcentratingRoom
public import QuantitativePaper.ScalarVariational

@[expose] public section

/-! An actual admissible probability measure for the concentrating move.
The original CDF is moved only in a strict interior interval, so both the
normalization and the prescribed atom at zero are preserved. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB
open scoped Topology ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def parisiCDFPrimitive (μ : Paper.ParisiMeasure) : StieltjesFunction ℝ where
  toFun := parisiCDF μ
  mono' := parisiCDF_monotone μ
  right_continuous' := parisiCDF_right_continuous μ

@[simp] theorem parisiCDFPrimitive_apply (μ : Paper.ParisiMeasure) (x : ℝ) :
    parisiCDFPrimitive μ x = parisiCDF μ x := rfl

theorem parisiCDFPrimitive_measure (μ : Paper.ParisiMeasure) :
    (parisiCDFPrimitive μ).measure = (μ : Measure Paper.Overlap).map Subtype.val := by
  have he : parisiCDFPrimitive μ = ProbabilityTheory.cdf ((μ : Measure Paper.Overlap).map Subtype.val) := by
    ext x
    exact parisiCDF_eq_realCDF μ x
  rw [he, ProbabilityTheory.measure_cdf]

theorem concentratingMovedCDF_leftLim_zero (μ : Paper.ParisiMeasure)
    (a ell kappa tau : ℝ) (ha : 0 < a) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) :
    Function.leftLim
      (concentratingMovedStieltjes (parisiCDFPrimitive μ) a ell kappa tau hell hkappa htau hdensity) 0 = 0 := by
  apply tendsto_nhds_unique
    ((concentratingMovedStieltjes (parisiCDFPrimitive μ) a ell kappa tau hell hkappa htau hdensity).mono.tendsto_leftLim 0)
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x < 0 := hx
  rw [concentratingMovedStieltjes_eq_outside _ a ell kappa tau hell hkappa htau hdensity x
    (fun hh => not_lt_of_ge (hx0.le.trans ha.le) hh.1), parisiCDFPrimitive_apply,
    parisiCDF_eq_zero_of_lt_zero μ hx0]

theorem concentratingMovedCDF_measure_Icc (μ : Paper.ParisiMeasure)
    (a ell kappa tau : ℝ) (ha : 0 < a) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) (x : ℝ) :
    (concentratingMovedStieltjes (parisiCDFPrimitive μ) a ell kappa tau hell hkappa htau hdensity).measure (Icc 0 x) =
      ENNReal.ofReal (parisiCDF μ x - tau*concentratingIntervalIncrement a ell x) := by
  rw [StieltjesFunction.measure_Icc,
    concentratingMovedCDF_leftLim_zero μ a ell kappa tau ha hell hkappa htau hdensity,
    sub_zero, concentratingMovedStieltjes_apply, parisiCDFPrimitive_apply]

def concentratingOverlapMeasure (μ : Paper.ParisiMeasure)
    (a ell kappa tau : ℝ) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) : Measure Paper.Overlap :=
    (concentratingMovedStieltjes (parisiCDFPrimitive μ) a ell kappa tau hell hkappa htau hdensity).measure.comap Subtype.val

theorem concentratingOverlapMeasure_probability (μ : Paper.ParisiMeasure)
    (a ell kappa tau : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) :
    IsProbabilityMeasure (concentratingOverlapMeasure μ a ell kappa tau hell hkappa htau hdensity) := by
  constructor
  rw [concentratingOverlapMeasure, comap_subtype_coe_apply measurableSet_Icc,
    image_univ, Subtype.range_coe,
    concentratingMovedCDF_measure_Icc μ a ell kappa tau ha hell hkappa htau hdensity,
    concentratingIntervalIncrement_zero_outside a ell 1 hell (fun h => not_lt_of_ge he.le h.2),
    mul_zero, sub_zero]
  have hCDF : parisiCDF μ 1 = 1 := by
    unfold parisiCDF
    have hs : {q : Paper.Overlap | (q : ℝ) ≤ 1} = univ :=
      Set.eq_univ_of_forall (fun q => q.property.2)
    rw [hs, measure_univ, ENNReal.toReal_one]
  rw [hCDF, ENNReal.ofReal_one]

def concentratingParisiMeasure (μ : Paper.ParisiMeasure)
    (a ell kappa tau : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) : Paper.ParisiMeasure :=
    ⟨concentratingOverlapMeasure μ a ell kappa tau hell hkappa htau hdensity,
      concentratingOverlapMeasure_probability μ a ell kappa tau ha he hell hkappa htau hdensity⟩

theorem concentratingParisiMeasure_cdf (μ : Paper.ParisiMeasure)
    (a ell kappa tau : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    parisiCDF (concentratingParisiMeasure μ a ell kappa tau ha he hell hkappa htau hdensity) x =
      parisiCDF μ x - tau*concentratingIntervalIncrement a ell x := by
  have hi : (Subtype.val : Paper.Overlap → ℝ) '' {r : Paper.Overlap | (r : ℝ) ≤ x} = Icc (0 : ℝ) x := by
    ext y
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact ⟨r.property.1,hr⟩
    · intro hy
      exact ⟨⟨y,⟨hy.1,hy.2.trans hx.2⟩⟩,hy.2,rfl⟩
  have hn : 0 ≤ parisiCDF μ x-tau*concentratingIntervalIncrement a ell x := by
    have hm := (concentratingMovedStieltjes (parisiCDFPrimitive μ) a ell kappa tau hell hkappa htau hdensity).mono
      (show (-1 : ℝ) ≤ x by linarith [hx.1])
    rw [concentratingMovedStieltjes_eq_outside _ a ell kappa tau hell hkappa htau hdensity (-1)
      (fun h => by linarith [h.1]), parisiCDFPrimitive_apply,
      parisiCDF_eq_zero_of_lt_zero μ (by norm_num), concentratingMovedStieltjes_apply,
      parisiCDFPrimitive_apply] at hm
    exact hm
  unfold parisiCDF
  change ((concentratingOverlapMeasure μ a ell kappa tau hell hkappa htau hdensity)
    {r : Paper.Overlap | (r : ℝ) ≤ x}).toReal = _
  rw [concentratingOverlapMeasure, comap_subtype_coe_apply measurableSet_Icc, hi,
    concentratingMovedCDF_measure_Icc μ a ell kappa tau ha hell hkappa htau hdensity x,
    ENNReal.toReal_ofReal hn]
  rfl

theorem concentratingParisiMeasure_preserves_floor (μ : Paper.ParisiMeasure)
    (a ell kappa tau s : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)))
    (hfloor : μ ∈ QuantitativePaper.scalarFloor s) :
    concentratingParisiMeasure μ a ell kappa tau ha he hell hkappa htau hdensity ∈ QuantitativePaper.scalarFloor s := by
  rw [QuantitativePaper.mem_scalarFloor_iff] at hfloor ⊢
  have hmass : ∀ ν : Paper.ParisiMeasure, QuantitativePaper.zeroMass ν = parisiCDF ν 0 := by
    intro ν
    unfold QuantitativePaper.zeroMass parisiCDF
    congr 2
    ext r
    simp only [mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro rfl
      rfl
    · intro hr
      apply Subtype.ext
      exact le_antisymm hr r.property.1
  rw [hmass, concentratingParisiMeasure_cdf μ a ell kappa tau ha he hell hkappa htau hdensity 0 (by norm_num),
    concentratingIntervalIncrement_zero_outside a ell 0 hell (fun h => not_lt_of_ge ha.le h.1),
    mul_zero, sub_zero, ←hmass]
  exact hfloor

end QuantitativeFollowup
