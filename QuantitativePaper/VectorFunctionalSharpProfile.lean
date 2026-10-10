module
public import QuantitativePaper.VectorSharpProfileStability
public import QuantitativePaper.ResponseFunctional

@[expose] public section

/-! Sharp actual functional profile continuity. The potential and penalty
each cost one half of the coefficient distance; both are genuine constructed
objects and no differentiability of the outer tilt is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1500000

theorem vectorMeasureFunctional_sharp_CDFDistance_abs_sub_le (n : ℕ) (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1) :
    |vectorMeasureFunctional n μ β t a-vectorMeasureFunctional n ν β t a| ≤
      ((1-t)*β^2)*Paper.parisiCDFDistance μ ν := by
  have hnpos : (0 : ℝ)<n := by exact_mod_cast hn
  have houter := normalizedCGF_sup_distance_bound (completionLaw n)
    (fun p => vectorMeasurePotential μ β t p 0) (fun p => vectorMeasurePotential ν β t p 0)
    ((n : ℝ)*((1-t)*β^2)/2*Paper.parisiCDFDistance μ ν)
    (fun m => integrable_exp_vectorMeasurePotential μ β t ht m 0)
    (fun m => integrable_exp_vectorMeasurePotential ν β t ht m 0)
    (fun p => by
      have H := vectorMeasureTailPotential_tail_distance_abs_sub_le_half μ ν β t 0 ht
        (by constructor <;> norm_num) p 0
      rw [vectorMeasureTailPotential_zero μ β t ht p 0,
        vectorMeasureTailPotential_zero ν β t ht p 0] at H
      exact H) a
  have houter' : |normalizedCGF (completionLaw n) (fun p => vectorMeasurePotential μ β t p 0) a/(n : ℝ)-
      normalizedCGF (completionLaw n) (fun p => vectorMeasurePotential ν β t p 0) a/(n : ℝ)| ≤
      ((1-t)*β^2)/2*Paper.parisiCDFDistance μ ν := by
    rw [←sub_div,abs_div,abs_of_pos hnpos]
    apply (div_le_iff₀ hnpos).mpr
    convert houter using 1
    ring
  have hcorr := Paper.parisiCorrection_sub_le β μ ν
  have hcorr' : |(1-t)*(β^2/2*∫q in (0 : ℝ)..1,q*Paper.parisiCDF μ q)-
      (1-t)*(β^2/2*∫q in (0 : ℝ)..1,q*Paper.parisiCDF ν q)| ≤
      ((1-t)*β^2)/2*Paper.parisiCDFDistance μ ν := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht)]
    have hh := mul_le_mul_of_nonneg_left hcorr (sub_nonneg.mpr ht)
    rw [Real.norm_eq_abs] at hh
    convert hh using 1
    ring
  unfold vectorMeasureFunctional
  calc
    _ ≤ |normalizedCGF (completionLaw n) (fun p => vectorMeasurePotential μ β t p 0) a/(n : ℝ)-
        normalizedCGF (completionLaw n) (fun p => vectorMeasurePotential ν β t p 0) a/(n : ℝ)|+
      |(1-t)*(β^2/2*∫q in (0 : ℝ)..1,q*Paper.parisiCDF μ q)-
        (1-t)*(β^2/2*∫q in (0 : ℝ)..1,q*Paper.parisiCDF ν q)| := by
      have he : ∀A B C D : ℝ,(A-B)-(C-D)=(A-C)-(B-D) := by intros;ring
      rw [he]
      exact abs_sub _ _
    _ ≤ ((1-t)*β^2)/2*Paper.parisiCDFDistance μ ν+((1-t)*β^2)/2*Paper.parisiCDFDistance μ ν :=
      add_le_add houter' hcorr'
    _ = _ := by ring

theorem responseProfile_L1_distance (μ ν : Paper.ParisiMeasure) (β : ℝ) (hβ : 0 < β) :
    (∫ q in (0:ℝ)..1, |responseProfile μ β q-responseProfile ν β q|) =
      β * Paper.parisiCDFDistance μ ν := by
  unfold responseProfile Paper.parisiCDFDistance
  have he : (fun q : ℝ => |β*Paper.parisiCDF μ q-β*Paper.parisiCDF ν q|) =
      fun q => β*|Paper.parisiCDF μ q-Paper.parisiCDF ν q| := by
    funext q
    rw [←mul_sub,abs_mul,abs_of_pos hβ]
  rw [he,intervalIntegral.integral_const_mul]

theorem responseEnergyFunctional_profile_L1_abs_sub_le (n : ℕ) (hn : 0 < n)
    (μ ν : Paper.ParisiMeasure) (β t lam : ℝ) (hβ : 0 < β) (ht : t ≤ 1) :
    |responseEnergyFunctional n μ β t lam-responseEnergyFunctional n ν β t lam| ≤
      (1-t) * ∫ q in (0:ℝ)..1, |responseProfile μ β q-responseProfile ν β q| := by
  rw [responseEnergyFunctional,responseEnergyFunctional,←sub_div,abs_div,abs_of_pos hβ,
    responseProfile_L1_distance μ ν β hβ]
  have H := div_le_div_of_nonneg_right
    (vectorMeasureFunctional_sharp_CDFDistance_abs_sub_le n hn μ ν β t (lam/β) ht) hβ.le
  convert H using 1
  field_simp
  <;> ring

end QuantitativePaper
