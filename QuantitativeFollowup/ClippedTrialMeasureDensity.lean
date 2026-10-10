module
public import QuantitativeFollowup.ConcentratingMeasure
public import QuantitativeFollowup.ScalarTrialMeasure

@[expose] public section

/-! Equality of the actual clipped-trial probability density and its
energy Stieltjes density away from the prescribed root atom. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem scalarTrialStieltjes_scale (beta lam : ℝ) (hbeta : 0 < beta)
    (μ : Paper.ParisiMeasure) :
    Real.toNNReal beta • scalarTrialStieltjes 1 (by norm_num) (lam/beta) μ=
      scalarTrialStieltjes beta hbeta.le lam μ := by
  ext x
  change (Real.toNNReal beta : ℝ)*max (lam/beta) (1*parisiCDF μ x)=max lam (beta*parisiCDF μ x)
  rw [Real.coe_toNNReal beta hbeta.le,one_mul,mul_max_of_nonneg _ _ hbeta.le]
  congr 1
  field_simp

theorem scalarClippedTrialMeasure_energy_density (beta lam : ℝ)
    (hbeta : 0 < beta) (hlam : lam ∈ Icc (0 : ℝ) beta) (μ : Paper.ParisiMeasure)
    (I : Set ℝ) (hI : MeasurableSet I) (hunit : I ⊆ Icc (0 : ℝ) 1) (hzero : (0 : ℝ) ∉ I) :
    (ENNReal.ofReal beta •
      (parisiCDFPrimitive (scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 hbeta.le,(div_le_one hbeta).mpr hlam.2⟩ μ)).measure).restrict I=
      (scalarTrialStieltjes beta hbeta.le lam μ).measure.restrict I := by
  classical
  rw [parisiCDFPrimitive_measure]
  change (ENNReal.ofReal beta •
    ((scalarClippedRealMeasure (lam/beta) μ).comap (Subtype.val : Paper.Overlap → ℝ)).map Subtype.val).restrict I=_
  rw [map_comap_subtype_coe measurableSet_Icc,Measure.restrict_smul,
    Measure.restrict_restrict hI,inter_eq_left.mpr hunit,scalarClippedRealMeasure,
    Measure.restrict_add,Measure.restrict_smul,restrict_dirac' hI,
    ite_eq_right hzero,smul_zero,add_zero]
  rw [←scalarTrialStieltjes_scale beta lam hbeta μ,StieltjesFunction.measure_smul,Measure.restrict_smul]
  congr 1

end QuantitativeFollowup
