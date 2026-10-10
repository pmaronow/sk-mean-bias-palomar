module
public import QuantitativeFollowup.ConcentratingDensity
public import QuantitativeFollowup.ParisiFreeMeasure

@[expose] public section

/-! The room-for-move construction in the paper's energy normalization.
The actual normalized CDF is multiplied by beta; its free measure is the
actual root-subtracted probability measure, not a hypothetical profile. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB QuantitativePaper
open scoped Topology ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem concentrating_normalized_density (μ : Paper.ParisiMeasure)
    (beta a ell kappa : ℝ) (hbeta : 0 < beta) (_hkappa : 0 ≤ kappa)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) :
    ENNReal.ofReal (kappa/beta) • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)) := by
  have hb : 0 ≤ 1/beta := by positivity
  calc
    _ = ENNReal.ofReal (1/beta) •
        (ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell))) := by
      rw [smul_smul, ←ENNReal.ofReal_mul hb]
      congr 2
      ring
    _ ≤ ENNReal.ofReal (1/beta) •
        (ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) := by
      intro S
      exact mul_le_mul_of_nonneg_left (hdensity S) (by positivity)
    _ = _ := by
      rw [smul_smul, ←ENNReal.ofReal_mul hb, one_div_mul_cancel hbeta.ne', ENNReal.ofReal_one, one_smul]

theorem concentrating_normalized_parameter (beta ell kappa tau : ℝ) (hbeta : 0 < beta)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32)) :
    tau/beta ∈ Icc (0 : ℝ) ((kappa/beta)*ell^2/32) := by
  refine ⟨div_nonneg htau.1 hbeta.le, ?_⟩
  have h := div_le_div_of_nonneg_right htau.2 hbeta.le
  convert h using 1
  ring

def concentratingEnergyMeasure (μ : Paper.ParisiMeasure)
    (beta a ell kappa tau : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) : Paper.ParisiMeasure :=
  concentratingParisiMeasure μ a ell (kappa/beta) (tau/beta) ha he hell (by positivity)
    (concentrating_normalized_parameter beta ell kappa tau hbeta htau)
    (concentrating_normalized_density μ beta a ell kappa hbeta hkappa hdensity)

theorem concentratingEnergyMeasure_profile (μ : Paper.ParisiMeasure)
    (beta a ell kappa tau : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) (x : ℝ) :
    beta*parisiCDF (concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity) x =
      beta*parisiCDF μ x - tau*concentratingIntervalIncrement a ell x := by
  rw [concentratingEnergyMeasure, concentratingParisiMeasure_cdf_all]
  field_simp

theorem concentratingEnergyMeasure_preserves_floor (μ : Paper.ParisiMeasure)
    (beta a ell kappa tau s : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)))
    (hfloor : μ ∈ scalarFloor s) :
    concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity ∈ scalarFloor s :=
  concentratingParisiMeasure_preserves_floor μ a ell (kappa/beta) (tau/beta) s ha he hell (by positivity)
    (concentrating_normalized_parameter beta ell kappa tau hbeta htau)
    (concentrating_normalized_density μ beta a ell kappa hbeta hkappa hdensity) hfloor

instance concentratingRootRealMeasure_finite (s : ℝ) :
    IsFiniteMeasure (((ENNReal.ofReal s • Measure.dirac zeroOverlap).map Subtype.val) : Measure ℝ) := by
  constructor
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp only [preimage_univ, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _),
    smul_eq_mul, mul_one]
  exact ENNReal.ofReal_lt_top

theorem parisiFreeMeasure_signed_root (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (hfloor : μ ∈ scalarFloor s) :
    (((ENNReal.ofReal s • Measure.dirac zeroOverlap).map Subtype.val) : Measure ℝ).toSignedMeasure +
      ((parisiFreeMeasure μ s).map Subtype.val).toSignedMeasure =
        ((μ : Measure Paper.Overlap).map Subtype.val).toSignedMeasure := by
  have hsum : (ENNReal.ofReal s • Measure.dirac zeroOverlap).map Subtype.val +
      (parisiFreeMeasure μ s).map Subtype.val = (μ : Measure Paper.Overlap).map Subtype.val := by
    rw [←Measure.map_add _ _ measurable_subtype_coe, root_add_parisiFreeMeasure μ s hs hfloor]
  rw [←Measure.toSignedMeasure_add]
  exact Measure.toSignedMeasure_congr hsum

theorem concentratingParisiMeasure_free_signed_density (μ : Paper.ParisiMeasure)
    (a ell kappa tau s : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)))
    (hs : s ∈ Icc (0 : ℝ) 1) (hfloor : μ ∈ scalarFloor s) :
    ((parisiFreeMeasure (concentratingParisiMeasure μ a ell kappa tau ha he hell hkappa htau hdensity) s).map Subtype.val).toSignedMeasure =
      ((parisiFreeMeasure μ s).map Subtype.val).toSignedMeasure -
        tau • volume.withDensityᵥ (deriv (concentratingIntervalIncrement a ell)) := by
  have hnew := concentratingParisiMeasure_preserves_floor μ a ell kappa tau s ha he hell hkappa htau hdensity hfloor
  have h1 := parisiFreeMeasure_signed_root μ s hs hfloor
  have h2 := parisiFreeMeasure_signed_root
    (concentratingParisiMeasure μ a ell kappa tau ha he hell hkappa htau hdensity) s hs hnew
  have hd := concentratingParisiMeasure_signed_density μ a ell kappa tau ha he hell hkappa htau hdensity
  apply add_left_cancel (a := (((ENNReal.ofReal s • Measure.dirac zeroOverlap).map Subtype.val) : Measure ℝ).toSignedMeasure)
  rw [h2, hd, ←h1]
  abel

theorem concentratingEnergyMeasure_free_signed_density (μ : Paper.ParisiMeasure)
    (beta a ell kappa tau s : ℝ) (hbeta : 0 < beta)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/32))
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)))
    (hs : s ∈ Icc (0 : ℝ) 1) (hfloor : μ ∈ scalarFloor s) :
    beta • ((parisiFreeMeasure (concentratingEnergyMeasure μ beta a ell kappa tau hbeta ha he hell hkappa htau hdensity) s).map Subtype.val).toSignedMeasure =
      beta • ((parisiFreeMeasure μ s).map Subtype.val).toSignedMeasure -
        tau • volume.withDensityᵥ (deriv (concentratingIntervalIncrement a ell)) := by
  rw [concentratingEnergyMeasure, concentratingParisiMeasure_free_signed_density μ a ell (kappa/beta) (tau/beta) s ha he hell (by positivity)
    (concentrating_normalized_parameter beta ell kappa tau hbeta htau)
    (concentrating_normalized_density μ beta a ell kappa hbeta hkappa hdensity) hs hfloor,
    smul_sub, smul_smul]
  have ht : beta*(tau/beta)=tau := by field_simp
  rw [ht]

end QuantitativeFollowup
