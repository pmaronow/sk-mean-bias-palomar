module
public import QuantitativePaper.VectorMeasureEndpoints
public import QuantitativePaper.NormalizedMomentStability
public import QuantitativePaper.FiniteVectorFunctional
public import Paper.ParisiCorrectionStability

@[expose] public section

/-! The interpolating probability-measure functional built from the proved
dyadic Gaussian limit, with genuine outer moments and its physical endpoints. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace QuantitativePaper
open FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

def vectorMeasureFunctional (n : ℕ) (μ : Paper.ParisiMeasure) (β t a : ℝ) : ℝ :=
  normalizedCGF (completionLaw n) (fun p => vectorMeasurePotential μ β t p 0) a/(n : ℝ)-
    (1-t)*(β^2/2*∫q in (0 : ℝ)..1,q*Paper.parisiCDF μ q)

theorem vectorMeasureFunctional_of_ne (n : ℕ) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ha : a≠0) :
    vectorMeasureFunctional n μ β t a=
      Real.log (∫p,Real.exp (a*vectorMeasurePotential μ β t p 0) ∂completionLaw n)/((n : ℝ)*a)-
        (1-t)*(β^2/2*∫q in (0 : ℝ)..1,q*Paper.parisiCDF μ q) := by
  rw [vectorMeasureFunctional,normalizedCGF_of_ne _ _ ha]
  simp only [cgf,mgf]
  congr 1
  ring

theorem vectorMeasureFunctional_CDFDistance_abs_sub_le (n : ℕ) (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1) :
    |vectorMeasureFunctional n μ β t a-vectorMeasureFunctional n ν β t a| ≤
      (3/2 : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance μ ν := by
  have hnpos : (0 : ℝ)<n := by exact_mod_cast hn
  have houter := normalizedCGF_sup_distance_bound (completionLaw n)
    (fun p => vectorMeasurePotential μ β t p 0) (fun p => vectorMeasurePotential ν β t p 0)
    ((n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance μ ν)
    (fun m => integrable_exp_vectorMeasurePotential μ β t ht m 0)
    (fun m => integrable_exp_vectorMeasurePotential ν β t ht m 0)
    (fun p => vectorMeasurePotential_CDFDistance_abs_sub_le μ ν β t ht p 0) a
  have houter' : |normalizedCGF (completionLaw n) (fun p => vectorMeasurePotential μ β t p 0) a/(n : ℝ)-
      normalizedCGF (completionLaw n) (fun p => vectorMeasurePotential ν β t p 0) a/(n : ℝ)| ≤
      ((1-t)*β^2)*Paper.parisiCDFDistance μ ν := by
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
    _ ≤ ((1-t)*β^2)*Paper.parisiCDFDistance μ ν+((1-t)*β^2)/2*Paper.parisiCDFDistance μ ν :=
      add_le_add houter' hcorr'
    _ = _ := by ring

theorem vectorMeasureFunctional_zero (n : ℕ) (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β : ℝ) (hβ : β≠0) (a : ℝ) :
    vectorMeasureFunctional n μ β 0 a=scalarParisiFunctional β μ := by
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have he : (fun p : Couplings n×ℝ => vectorMeasurePotential μ β 0 p 0)=
      fun _ => (n : ℝ)*(Real.log 2+Paper.parisiPotential β μ (0,0)) := by
    funext p
    rw [vectorMeasurePotential_zero μ β hβ p 0]
    simp
    ring
  unfold vectorMeasureFunctional
  rw [he]
  have hconst : normalizedCGF (completionLaw n)
      (fun _ : Couplings n×ℝ => (n : ℝ)*(Real.log 2+Paper.parisiPotential β μ (0,0))) a=
      (n : ℝ)*(Real.log 2+Paper.parisiPotential β μ (0,0)) := by
    by_cases ha : a=0
    · subst a
      rw [normalizedCGF_zero]
      · simp
      · simp [integrableExpSet]
    · rw [normalizedCGF_of_ne _ _ ha]
      simp only [cgf,mgf,integral_const,probReal_univ,one_smul,Real.log_exp]
      field_simp
  rw [hconst,mul_div_cancel_left₀ _ hn0]
  unfold scalarParisiFunctional Paper.parisiPDEFunctional Paper.parisiFunctional
  simp

theorem vectorMeasureFunctional_one (n : ℕ) (μ : Paper.ParisiMeasure) (β a : ℝ)
    (ha : a≠0) :
    vectorMeasureFunctional n μ β 1 a=completedFractionalPressure n β a := by
  rw [vectorMeasureFunctional_of_ne n μ β 1 a ha]
  simp only [vectorMeasurePotential_one_zero,sub_self,zero_mul,sub_zero]
  unfold completedFractionalPressure
  rw [ite_eq_right ha]
  rfl

end QuantitativePaper
