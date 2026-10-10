module
public import QuantitativeFollowup.ScalarTransportActualPartials

@[expose] public section

/-! The actual moved-level scalar moment has the normalized Gaussian score
derivative. Every parameter partial, normalization and differentiation-under-
integral hypothesis is discharged for the genuine finite-scheme family. The
identification of this derivative with the seven-term J is separate. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTransportGaussianResponse (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) : ℝ :=
  let A:=scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2)
  let B:=scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ 0) (k+2)
  let center:=FRSB.Gamma β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p)
  (1/2:ℝ)*∑e : Bool,∫z,Real.exp (scalarTransportEuclideanExponent s β φ e 0 (A z))*(
    scalarTransportSquarePartial s β φ p 0 (A z)+
    (scalarTransportGradientSquare s β φ p 0 (A z)-center)*scalarTransportExponentPartial s β φ 0 (A z)+
    ∑i : Fin (k+2),gaussianScoreBilinear (scalarTransportEuclideanExponent s β φ e 0)
      (scalarTransportGradientSquare s β φ p 0) (A z)
      (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) center)
    ∂fieldGaussian (k+2)

theorem hasDerivAt_scalarTransportGamma_gaussianResponse
    (s : RSBScheme k) (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (p : Fin (k+3)) :
    HasDerivAt (fun u=>FRSB.Gamma β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
      (scalarLevelTransport φ u (scalarSchemeTransportNode s p)))
      (scalarTransportGaussianResponse s β φ p) 0 := by
  have hd:=hasDerivAt_scalarTransportGamma_of_actual_partials s β hβ.ne' φ L hφ h0 h1
    δ hδ hsmall p (fun _=>scalarTransportExponentPartial s β φ)
    (scalarTransportSquarePartial s β φ p)
    (fun e u hu x=>hasDerivAt_scalarTransportEuclideanExponent_parameter s β hβ φ L hφ h0 h1
      δ u hδ hsmall (abs_lt.mpr hu) e x)
    (fun u hu x=>hasDerivAt_scalarTransportGradientSquare_parameter s β hβ φ L hφ h0 h1
      δ u hδ hsmall (abs_lt.mpr hu) p x)
    (fun _=>(continuous_scalarTransportExponentPartial s β hβ.ne' φ).continuousOn)
    (continuous_scalarTransportSquarePartial s β hβ.ne' φ p).continuousOn
    (3*β^2/2*‖φ‖) (2*scalarTransportVariationSpatialBound β φ)
    (by positivity) (mul_nonneg (by norm_num) (scalarTransportVariationSpatialBound_nonneg β φ))
    (fun _ u _ x=>norm_scalarTransportExponentPartial_le s β φ u x)
    (fun u _ x=>norm_scalarTransportSquarePartial_le s β φ p u x)
  exact hd

end QuantitativeFollowup
