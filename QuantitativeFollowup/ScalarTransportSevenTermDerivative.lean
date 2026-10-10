module
public import QuantitativeFollowup.ScalarTransportResponse
public import QuantitativeFollowup.ScalarObservationRefinement

@[expose] public section

/-! The literal derivative in Lemma 6.3 for every observed overlap, obtained
from actual same-measure refinements. Covariance-parameter C∞ regularity is
a separate obligation and is not asserted here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper FRSB
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem hasDerivAt_scalarTransportGamma_seven_terms_node (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : Paper.parisiSchemeMeasure s∈scalarFloor a)
    (p : Fin (k+3)) :
    HasDerivAt (fun u=>Gamma β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
      (scalarLevelTransport φ u (scalarSchemeTransportNode s p)))
      (scalarResponseOperator β hβ.ne' (Paper.parisiSchemeMeasure s) a φ (scalarSchemeTransportNode s p)) 0 := by
  rw [←scalarTransportGaussianResponse_eq_operator s β hβ.ne' φ L hφ h0 h1 a ha hμ p]
  exact hasDerivAt_scalarTransportGamma_gaussianResponse s β hβ φ L hφ h0 h1 δ hδ hsmall p

theorem hasDerivAt_scalarTransportGamma_seven_terms (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : Paper.parisiSchemeMeasure s∈scalarFloor a)
    (p : Paper.Overlap) :
    HasDerivAt (fun u=>Gamma β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
      (scalarLevelTransport φ u p))
      (scalarResponseOperator β hβ.ne' (Paper.parisiSchemeMeasure s) a φ p) 0 := by
  obtain ⟨K,r,j,hm,hq⟩:=exists_scalar_same_measure_scheme_node s p
  have hd:=hasDerivAt_scalarTransportGamma_seven_terms_node r β hβ φ L hφ h0 h1
    δ hδ hsmall a ha (by simpa only [hm] using hμ) j
  simpa only [hm,hq] using hd

end QuantitativeFollowup
