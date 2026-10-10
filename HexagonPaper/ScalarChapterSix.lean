module
public import HexagonPaper.ScalarGeneralTransportResponse
public import HexagonPaper.ScalarGeneralPotentialVariation
public import HexagonPaper.ScalarTransportHessian

@[expose] public section

/-! Source-coefficient wrappers for Chapter 6. A physical coefficient d is
represented by native inverse temperature sqrt(d), whose square is exactly d.
The free measure removes precisely the prescribed root atom. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff ENNReal
namespace HexagonPaper
open Paper FRSB QuantitativePaper FourPapersCommon SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

 theorem scalar_response_identity (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (f : ℝ→ℝ) (hf : ContDiffOn ℝ ∞ f (Icc (0:ℝ) 1)) (h0 : f 0=0) (h1 : f 1=0) :
    ∃δ : ℝ,0<δ ∧ ∀p : Paper.Overlap,
      ContDiffOn ℝ 1 (fun v=>Gamma (Real.sqrt d)
        (scalarTransportMeasure μ (scalarSmoothTransportTest f hf) v)
        (scalarLevelTransport (scalarSmoothTransportTest f hf) v p)) (Ioo (-δ) δ) ∧
      HasDerivAt (fun v=>Gamma (Real.sqrt d)
        (scalarTransportMeasure μ (scalarSmoothTransportTest f hf) v)
        (scalarLevelTransport (scalarSmoothTransportTest f hf) v p))
        (scalarResponseOperator (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne'
          μ s (scalarSmoothTransportTest f hf) p) 0 :=
  scalar_general_response_smooth_test (Real.sqrt d) (Real.sqrt_pos.mpr hd) μ s hs hμ f hf h0 h1

 theorem setIntegral_parisiFreeMeasure_strict_future (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s) (q : Paper.Overlap) (F : Paper.Overlap→ℝ) :
    (∫r in Ioi q,F r ∂parisiFreeMeasure μ s)=∫r in Ioi q,F r ∂(μ:Measure Paper.Overlap) := by
  classical
  have hz : zeroOverlap∉Ioi q := by
    change ¬q<(0:Paper.Overlap)
    exact not_lt.mpr q.property.1
  have hr : (ENNReal.ofReal s • Measure.dirac zeroOverlap).restrict (Ioi q)=0 := by
    rw [Measure.restrict_smul,restrict_dirac' measurableSet_Ioi]
    simp only [hz,ite_false,smul_zero]
  rw [←root_add_parisiFreeMeasure μ s hs hμ,Measure.restrict_add,hr,zero_add]

 theorem scalar_node_variation (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (q : Paper.Overlap) (x : ℝ) :
    HasDerivAt (fun v=>Real.log 2+parisiPotential (Real.sqrt d)
      (scalarTransportMeasure μ φ v) ((scalarLevelTransport φ v q:ℝ),x))
      (-(d/2)*(φ q*(parisiHessian (Real.sqrt d) μ ((q:ℝ),x)+
        parisiCDF μ q*parisiGradient (Real.sqrt d) μ ((q:ℝ),x)^2)+
        ∫r in Ioi q,φ r*scalarFutureSquareExtended (Real.sqrt d) μ q r x
          ∂parisiFreeMeasure μ s)) 0 := by
  have hz : (0:ℝ)∈Ioo (-δ) δ := ⟨by linarith,hδ⟩
  have hh := (hasDerivAt_scalarTransportPotential_general_at (Real.sqrt d)
    (Real.sqrt_pos.mpr hd) μ φ L hφ h0 h1 δ hδ hsmall q x 0 hz).const_add (Real.log 2)
  apply hh.congr_deriv
  simp only [scalarTransportPotentialVariation,scalarTransportFutureSquare,
    scalarTransportMeasure_zero,scalarLevelTransport_zero,Real.sq_sqrt hd.le]
  rw [setIntegral_parisiFreeMeasure_strict_future μ s hs hμ q]

 theorem scalar_transport_hessian (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : endpointFixedLipschitzTests) (L : ℝ≥0) (hφ : LipschitzWith L φ.val)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) :
    (∀u : ℝ,u∈Ioo (-δ) δ → HasDerivAt (scalarTransportFunctional (Real.sqrt d) μ φ.val)
      (d/2*(∫q : Paper.Overlap,φ.val q*((scalarLevelTransport φ.val u q:ℝ)-
        Gamma (Real.sqrt d) (scalarTransportMeasure μ φ.val u)
          (scalarLevelTransport φ.val u q)) ∂parisiFreeMeasure μ s)) u) ∧
    (let f := endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ s) φ
    HasDerivAt (deriv (scalarTransportFunctional (Real.sqrt d) μ φ.val))
      (d/2*inner ℝ f (f-scalarResponseL2Operator (Real.sqrt d)
        (Real.sqrt_pos.mpr hd).ne' μ s hs hμ f)) 0) := by
  constructor
  · intro u hu
    simpa only [Real.sq_sqrt hd.le] using
      scalar_transport_first_variation (Real.sqrt d) (Real.sqrt_pos.mpr hd) μ s hs hμ
        φ.val L hφ φ.property.1 φ.property.2.1 δ hδ hsmall u hu
  · simpa only [Real.sq_sqrt hd.le] using
      scalar_transport_second_variation_inner (Real.sqrt d) (Real.sqrt_pos.mpr hd)
        μ s hs hμ φ L hφ δ hδ hsmall

end HexagonPaper
