module
public import QuantitativePaper.VectorPrefixDensityLipschitz
public import FourPapersCommon.GaussianTiltedCurvatureRaw
public import QuantitativePaper.ResponseModel

@[expose] public section

/-! Genuine incident-site conditional curvature lower bound for an actual
finite prefix. The only stage conditions are the literal incoming and
outgoing physical masses at the chosen first crossing. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

def prefixIncomingMass {k : ℕ} (s : RSBScheme k) (a : ℝ) (N : ℕ) : ℝ :=
  if N=0 then a else s.m (N-1)

theorem sitePrefixGaussian_curvature_raw_lower {n k N : ℕ} (s : RSBScheme k)
    (β t a U : ℝ) (hβ : 0<β) (ht : t∈Icc 0 1) (ha0 : 0 ≤ a) (ha : a  ≤  s.m 0)
    (hN : N ≤ k+2) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (hm : 1 ≤ β*observableDepthMass s (k+2-N))
    (hin : β*prefixIncomingMass s a N ≤ max 1 U) :
    Integrable (fun g=>Real.exp (sitePrefixGaussianLogWeight s β t a i b g))
      (SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i)) ∧
    Integrable (fun g=>Real.exp (sitePrefixGaussianLogWeight s β t a i b g)*
      sitePrefixGaussianCurvature s β t i b g)
      (SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i)) ∧
    responseCurvatureConstant U*
      (∫g,Real.exp (sitePrefixGaussianLogWeight s β t a i b g)
        ∂SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i))  ≤ 
      ∫g,Real.exp (sitePrefixGaussianLogWeight s β t a i b g)*
        sitePrefixGaussianCurvature s β t i b g
        ∂SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i) := by
  have hMU : 0 < max (1:ℝ) U := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hDV (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
      ‖fderiv ℝ (sitePrefixGaussianLogWeight s β t a i b) g‖ ≤ 2*max 1 U := by
    by_cases h0 : N=0
    · subst N
      have hh := norm_fderiv_sitePrefixGaussianLogWeight_zero_le s β t a hβ.le ht ha0 i b g
      simp only [prefixIncomingMass,ite_true] at hin
      nlinarith
    · have hh := norm_fderiv_sitePrefixGaussianLogWeight_le s β t a hβ.le ht ha0 ha
        (by omega) hN i b g
      simp only [prefixIncomingMass,if_neg h0] at hin
      nlinarith
  have hh := gaussian_tilted_curvature_raw
    (sitePrefixGaussianLogWeight s β t a i b) (sitePrefixGaussianMagnetization s β t i b)
    (sitePrefixGaussianCurvature s β t i b)
    ((contDiff_sitePrefixGaussianLogWeight s β t a i b).of_le (by simp))
    ((contDiff_sitePrefixGaussianMagnetization s β t i b).of_le (by simp))
    (continuous_sitePrefixGaussianCurvature s β t i b) (2*max 1 U) β (by positivity)
    (abs_sitePrefixGaussianCurvature_le s β t hβ.le i b) hDV
    (norm_fderiv_sitePrefixGaussianMagnetization_le s β t hβ ht hN i b)
    (abs_sitePrefixGaussianMagnetization_le_one s β t i b)
    (fun g=>sitePrefixGaussianCurvature_diagonal_bound s β t hβ.le i b g hm)
    (sitePrefixGaussianLogWeight_even s β t a i b)
    (sitePrefixGaussianMagnetization_odd s β t i b)
  convert hh using 1
  unfold responseCurvatureConstant responsePoincareConstant
  congr 3
  ring

end QuantitativePaper
