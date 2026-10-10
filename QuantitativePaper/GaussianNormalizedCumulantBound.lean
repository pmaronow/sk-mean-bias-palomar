module
public import QuantitativePaper.VectorSharpMassBounds

@[expose] public section

/-! A genuine finite-dimensional Gaussian normalized-cumulant derivative
bound on arbitrary finite coordinates, including zero-dimensional disorder. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem gaussian_normalizedCGF_deriv_le_half_finite {ι : Type} [Fintype ι]
    (F : EuclideanSpace ℝ ι→ℝ) (hJets : BoundedPositiveJets F)
    (hconv : ConvexOn ℝ univ F) (L : ℝ) (hL : 0≤L)
    (hLip : LipschitzWith L.toNNReal F)
    (hExp : ∀a,Integrable (fun z=>Real.exp (a*F z)) (stdGaussian (EuclideanSpace ℝ ι)))
    (m : ℝ) : deriv (normalizedCGF (stdGaussian (EuclideanSpace ℝ ι)) F) m≤L^2/2:=by
  let P:=stdGaussian (EuclideanSpace ℝ ι)
  have hP : SYK.standardGaussianMeasureOnEuclidean ι=P:=map_pi_eq_stdGaussian
  have hmem (a : ℝ) : a∈interior (integrableExpSet F P):=by
    rw [show integrableExpSet F P=univ from Set.eq_univ_iff_forall.mpr hExp,interior_univ]
    trivial
  have hcgf : Differentiable ℝ (cgf F P):=fun a=>(analyticAt_cgf (hmem a)).differentiableAt
  have hgrad (z : EuclideanSpace ℝ ι) : ‖gradient F z‖≤L:=by
    rw [gradient,LinearIsometryEquiv.norm_map]
    simpa only [Real.coe_toNNReal _ hL] using norm_fderiv_le_of_lipschitz ℝ hLip (x₀:=z)
  have hderiv (a : ℝ) : |deriv (cgf F P) a-∫z,F z ∂P|≤L^2*|a|:=by
    have hc:=SYK.gaussian_cov_bound_smooth F L hL (hJets.1.of_le (by simp)) hgrad a
    rw [hP] at hc
    rw [deriv_cgf (hmem a),div_sub',abs_div,abs_of_pos (mgf_pos (hExp a))]
    · apply (div_le_iff₀ (mgf_pos (hExp a))).mpr
      simpa only [mgf,mul_comm] using hc
    · exact (mgf_pos (hExp a)).ne'
  have hquad (a : ℝ) : cgf F P a≤(∫z,F z ∂P)*a+L^2*a^2/2:=
    SYK.quadratic_bound_of_deriv_sub_le hcgf (by simp) hderiv a
  have hc : ConvexOn ℝ univ (normalizedCGF P F):=convexOn_normalizedCGF_stdGaussian hJets hconv
  have hd : Differentiable ℝ (normalizedCGF P F):=by
    intro a
    by_cases ha : a=0
    · subst a
      exact (analyticAt_normalizedCGF_zero P F (hmem 0)).differentiableAt
    · have he : normalizedCGF P F=ᶠ[𝓝 a] fun b=>cgf F P b/b:=by
        filter_upwards [eventually_ne_nhds ha] with b hb
        exact normalizedCGF_of_ne P F hb
      exact ((hcgf a).div differentiableAt_id ha).congr_of_eventuallyEq he
  apply convex_deriv_le_of_positive_affine_bound _ hc hd (∫z,F z ∂P) (L^2/2)
  intro a ha
  rw [normalizedCGF_of_ne P F ha.ne']
  apply (div_le_iff₀ ha).mpr
  convert hquad a using 1 <;> ring

end QuantitativePaper
