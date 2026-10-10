module
public import QuantitativeFollowup.ConcentratingAdmissibleCost

@[expose] public section

/-! Actual local density inherited by a probability mixing segment, and
room for both the pushed point and its doubling. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem parisiCDFPrimitive_mix_measure (μ ν : Paper.ParisiMeasure) (theta : ℝ)
    (htheta : theta ∈ Icc (0 : ℝ) 1) :
    (parisiCDFPrimitive (parisiMix μ ν theta)).measure=
      ENNReal.ofReal (1-theta) • (parisiCDFPrimitive μ).measure+
        ENNReal.ofReal theta • (parisiCDFPrimitive ν).measure := by
  rw [parisiCDFPrimitive_measure,parisiMix_measure μ ν theta htheta,
    Measure.map_add _ _ measurable_subtype_coe,Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    parisiCDFPrimitive_measure,parisiCDFPrimitive_measure]

theorem concentrating_mixed_density (μ ν : Paper.ParisiMeasure)
    (beta a ell kappa theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) 1)
    (hdensity : ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell))) :
    ENNReal.ofReal (theta*kappa) • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive (parisiMix μ ν theta)).measure.restrict (Ioo a (a+ell)) := by
  calc
    _ = ENNReal.ofReal theta • (ENNReal.ofReal kappa • volume.restrict (Ioo a (a+ell))) := by
      rw [smul_smul,ENNReal.ofReal_mul htheta.1]
    _ ≤ ENNReal.ofReal theta • (ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell))) := by
      intro S
      exact mul_le_mul_of_nonneg_left (hdensity S) (by positivity)
    _ ≤ _ := by
      rw [parisiCDFPrimitive_mix_measure μ ν theta htheta,Measure.restrict_add,
        Measure.restrict_smul,Measure.restrict_smul,smul_add,smul_smul,smul_smul]
      intro S
      simp only [Measure.smul_apply,Measure.add_apply,smul_eq_mul,←mul_assoc]
      change (ENNReal.ofReal theta*ENNReal.ofReal beta)*((parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell))) S ≤
        (ENNReal.ofReal beta*ENNReal.ofReal (1-theta))*((parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell))) S+
          (ENNReal.ofReal beta*ENNReal.ofReal theta)*((parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell))) S
      rw [mul_comm (ENNReal.ofReal theta) (ENNReal.ofReal beta)]
      exact le_add_self

theorem concentrating_mixed_parameter (ell kappa tau theta : ℝ) (hkappa : 0 ≤ kappa)
    (htau : tau ∈ Icc (0 : ℝ) (kappa*ell^2/64)) (htheta : theta ∈ Icc (0 : ℝ) 1) :
    theta*tau ∈ Icc (0 : ℝ) ((theta*kappa)*ell^2/32) ∧
    2*theta*tau ∈ Icc (0 : ℝ) ((theta*kappa)*ell^2/32) := by
  have hprod := mul_le_mul_of_nonneg_left htau.2 htheta.1
  have hkn := mul_nonneg (mul_nonneg htheta.1 hkappa) (sq_nonneg ell)
  constructor <;> constructor
  · exact mul_nonneg htheta.1 htau.1
  · nlinarith
  · exact mul_nonneg (mul_nonneg (by norm_num) htheta.1) htau.1
  · nlinarith

end QuantitativeFollowup
