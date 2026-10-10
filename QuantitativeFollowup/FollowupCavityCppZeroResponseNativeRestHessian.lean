module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeSchemeFeature
public import QuantitativeFollowup.FollowupCavitySignedResponseTraceMoments

@[expose] public section

/-! The actual finite rest-spin susceptibility at every original node is
the native field Hessian entry. This is a function-level potential identity
followed by differentiation, and does not differentiate an AE state law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem fderiv_anisotropicFiniteSpinMean_eq_hessian (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) (i l : Fin n) :
    fderiv ℝ (anisotropicFiniteFeatureMean D s j (fun σ=>Paper.spinSign (σ i))) P
      (anisotropicCoordinateDirection n l)=
      fderiv ℝ (fderiv ℝ (anisotropicFinitePotential D s j)) P
        (anisotropicCoordinateDirection n l) (anisotropicCoordinateDirection n i) :=by
  have he:anisotropicFiniteFeatureMean D s j (fun σ=>Paper.spinSign (σ i))=
      fun Q=>fderiv ℝ (anisotropicFinitePotential D s j) Q (anisotropicCoordinateDirection n i):=by
    funext Q
    exact (anisotropicMagnetization_eq_spin_mean D s j Q i).symm
  rw [he]
  have hc:=hasFDerivAt_exponential_directional_field (anisotropicFinitePotential D s j)
    ((contDiff_anisotropicFinitePotential D s j).of_le (by simp)) P
    (anisotropicCoordinateDirection n i)
  rw [hc.fderiv]
  rfl

theorem cavityFiniteRestSpinMean_at_native_scheme_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (hj : j≤k+2) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicFiniteFeatureMean D s j (fun σ=>Paper.spinSign (σ i))
      (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-j) (by omega)) sample)=
      anisotropicProcessSpinResponse D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-j) (by omega)) i sample :=by
  rw [anisotropicProcessSpinResponse_scheme_eq_finite]
  unfold anisotropicFiniteProcessMagnetization
  rw [anisotropicFiniteTailMagnetization_node,
    show k+2-(k+2-j)=j from by omega,←anisotropicProcessParameter_scheme_eq_finite]
  exact (anisotropicMagnetization_eq_spin_mean D s j _ i).symm

theorem cavityFiniteRestHessian_at_native_scheme_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (hj : j≤k+2) (i l : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) :
    fderiv ℝ (anisotropicFiniteFeatureMean D s j (fun σ=>Paper.spinSign (σ i)))
      (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-j) (by omega)) sample) (anisotropicCoordinateDirection n l)=
      nativeAnisotropicProcessHessianMatrix D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-j) (by omega)) sample l i :=by
  rw [fderiv_anisotropicFiniteSpinMean_eq_hessian]
  have he:anisotropicMeasureTailPotential D (Paper.parisiSchemeMeasure s)
      (anisotropicSchemeNode s (k+2-j) (by omega))=anisotropicFinitePotential D s j :=by
    funext P
    rw [anisotropicMeasureTailPotential_scheme_eq_finite]
    change anisotropicFiniteTailPotential D s (anisotropicSchemeNode s (k+2-j) (by omega)) P = _
    rw [anisotropicFiniteTailPotential_node,show k+2-(k+2-j)=j from by omega]
  rw [nativeAnisotropicProcessHessianMatrix,he]
  rfl

end QuantitativeFollowup
