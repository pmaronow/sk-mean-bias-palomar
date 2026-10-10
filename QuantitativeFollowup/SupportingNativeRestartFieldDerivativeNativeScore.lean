module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeMovingScore

@[expose] public section

/-! The genuine derivative of the arbitrary-profile restarted spin-square
expectation equals its physical Hessian term and its literal future score.
Finite posterior derivatives, actual field/state limits and bounded DCT
supply every analytic input. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n : ℕ}
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128

theorem tendsto_anisotropicFiniteRestartWienerSquareResponse_dyadic (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (x w : Field n) (sample : VectorDisorderBrownianSample n) (i : Fin n) :
    Tendsto (fun j=>anisotropicFiniteRestartWienerSquareResponse D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g q x w
      (vectorDyadicTimeIndex r j) i sample) atTop
      (𝓝 (cavityRestartSquareFieldResponse D μ g q x w r sample i)) := by
  have he j : anisotropicFiniteRestartWienerSquareResponse D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g q x w
      (vectorDyadicTimeIndex r j) i sample=
      cavityRestartSquareFieldResponse D
        (Paper.parisiSchemeMeasure (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)))
        g q x w (Paper.parisiGridRound (vectorDyadicIndex j) r) sample i := by
    have hv : vectorDyadicTimeIndex r j≤vectorDyadicIndex j+3:=
      (vectorDyadicTimeIndex_le r j).trans (by omega)
    have hn : anisotropicSchemeNode (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (vectorDyadicTimeIndex r j) hv=Paper.parisiGridRound (vectorDyadicIndex j) r :=
      Subtype.ext (vectorDyadicTimeIndex_node μ r j)
    simpa only [hn,max_eq_right (hqr.trans (Paper.le_parisiGridRound _ r))] using
      anisotropicFiniteRestartWienerSquareResponse_eq_physical D
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g q x w _ hv i sample
  simp_rw [he]
  exact tendsto_cavityRestartSquareFieldResponse_dyadic_node D μ g q r hqr x w sample i

theorem integrable_cavityRestartSquareFieldResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (x w : Field n) (i : Fin n) :
    Integrable (fun sample=>cavityRestartSquareFieldResponse D μ g q x w r sample i)
      (vectorDisorderBrownianMeasure n) := by
  let F:=fun j=>anisotropicFiniteRestartWienerSquareResponse D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g q x w (vectorDyadicTimeIndex r j) i
  have ht:=fun sample=>tendsto_anisotropicFiniteRestartWienerSquareResponse_dyadic D μ g q r hqr x w sample i
  have hm:=aestronglyMeasurable_of_tendsto_ae (μ:=vectorDisorderBrownianMeasure n) atTop
    (fun j=>(measurable_anisotropicFiniteRestartWienerSquareResponse D _ g q x w _ i).aestronglyMeasurable)
    (.of_forall ht)
  exact Integrable.of_bound hm
    (4*‖cavityCoordinateFeature i‖^2*‖anisotropicEnergyMap D (anisotropicFieldInjection n w)‖)
    (.of_forall fun sample=>le_of_tendsto ((ht sample).norm)
      (.of_forall fun j=>anisotropicFiniteRestartWienerSquareResponse_bound D _ g q x w _ i sample))

theorem fderiv_anisotropicRestartSpinSquare_field_score (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (i : Fin n) (x w : Field n) :
    fderiv ℝ (fun y=>anisotropicRestartSpinSquare D μ g q y i r) x w=
      ∫sample,cavityRestartSquareFieldResponse D μ g q x w r sample i
        ∂vectorDisorderBrownianMeasure n := by
  have hlim:=tendsto_integral_filter_of_dominated_convergence (μ:=vectorDisorderBrownianMeasure n)
    (fun _=>4*‖cavityCoordinateFeature i‖^2*‖anisotropicEnergyMap D (anisotropicFieldInjection n w)‖)
    (.of_forall fun j=>(measurable_anisotropicFiniteRestartWienerSquareResponse D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g q x w (vectorDyadicTimeIndex r j) i).aestronglyMeasurable)
    (.of_forall fun j=>.of_forall fun sample=>anisotropicFiniteRestartWienerSquareResponse_bound D _ g q x w _ i sample)
    (integrable_const _) (.of_forall fun sample=>tendsto_anisotropicFiniteRestartWienerSquareResponse_dyadic
      D μ g q r hqr x w sample i)
  have hd:=(tendstoLocallyUniformlyOn_univ.mpr
    (anisotropicRestartSpinSquare_field_derivative_limit D μ g q r hqr i).1).tendsto_at (mem_univ x)
  have hev : Continuous (fun T : Field n→L[ℝ]ℝ=>T w) := continuous_id.clm_apply continuous_const
  have hder:=hev.continuousAt.tendsto.comp hd
  simp only [Function.comp_def,anisotropicDyadicRestartPosteriorSquare,
    fderiv_anisotropicFiniteRestartPosteriorSquare_wiener] at hder
  exact tendsto_nhds_unique hder hlim

end QuantitativeFollowup
