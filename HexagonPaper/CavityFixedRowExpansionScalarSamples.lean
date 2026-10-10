module
public import QuantitativeFollowup.ScalarResponseSamples
public import QuantitativeFollowup.ScalarResponseKernelContinuity
public import FourPapersCommon.IntegrableBoundedFamilies

@[expose] public section

/-! Joint measurability of the genuine marked scalar coefficients at all
levels and all probability profiles. This removes the finite-atom restriction
from subsequent response Fubini arguments. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup FRSB
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev CavityScalarSampleLevels:=Paper.Overlap×(Paper.Overlap×Paper.Overlap)

theorem continuous_cavityScalarResponseSample_levels (j : Fin 8) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (z : Paper.BrownianSample×Bool) :
    Continuous (fun x : CavityScalarSampleLevels=>scalarResponseSample j β μ x.1 x.2.1 x.2.2 z) := by
  have hm : Continuous (fun x : CavityScalarSampleLevels=>M β μ x.1 z.1):=
    continuous_scalarM_comp β hβ z.1 _ continuous_const _ continuous_fst
  have hc : Continuous (fun x : CavityScalarSampleLevels=>C β μ x.1 z.1):=
    continuous_scalarC_comp β hβ z.1 _ continuous_const _ continuous_fst
  have hr : Continuous (fun x : CavityScalarSampleLevels=>M β μ x.2.1 z.1):=
    continuous_scalarM_comp β hβ z.1 _ continuous_const _ (by fun_prop)
  have hl : Continuous (fun x : CavityScalarSampleLevels=>M β μ x.2.2 z.1):=
    continuous_scalarM_comp β hβ z.1 _ continuous_const _ (by fun_prop)
  have hcent : Continuous (fun x : CavityScalarSampleLevels=>scalarCenteredSquare β μ x.1 z.1):=
    continuous_scalarCentered_comp β hβ z.1 _ continuous_const _ continuous_fst
  have hfuture : Continuous (fun x : CavityScalarSampleLevels=>scalarFutureSquareExtended β μ x.2.1 x.2.2
      (parisiPhysicalSplitState β 0 μ x.2.1 z.1)):=
    continuous_scalarFutureSquare_comp β z.1 _ continuous_const _ _ (by fun_prop) (by fun_prop)
  have hfutureD : Continuous (fun x : CavityScalarSampleLevels=>scalarFutureSquareDerivativeExtended β μ x.1 x.2.1
      (parisiPhysicalSplitState β 0 μ x.1 z.1)):=
    continuous_scalarFutureSquareDerivative_comp β hβ z.1 _ continuous_const _ _ continuous_fst (by fun_prop)
  fin_cases j
  · exact hc.pow 2
  · exact (hm.pow 2).mul hc
  · exact hm.mul hfutureD
  · exact (hm.mul hc).mul hr
  · exact (hcent.mul continuous_const).mul hr
  · exact hcent.mul (hr.pow 2)
  · exact (hcent.mul hr).mul hl
  · exact hcent.mul hfuture

theorem measurable_cavityScalarResponseSample_levels (j : Fin 8) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun x : CavityScalarSampleLevels×(Paper.BrownianSample×Bool)=>
      scalarResponseSample j β μ x.1.1 x.1.2.1 x.1.2.2 x.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (continuous_cavityScalarResponseSample_levels j β hβ μ)
    (fun x=>measurable_scalarResponseSample j β hβ μ x.1 x.2.1 x.2.2)

theorem cavityBoundedIntegral_swap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (F : X×Y→ℝ) (hF : Measurable F) (B : ℝ) (hb : ∀z,‖F z‖≤B) :
    (∫x,∫y,F (x,y)∂Q∂P)=∫y,∫x,F (x,y)∂P∂Q :=
  integral_integral_swap ((integrable_const B).mono' hF.aestronglyMeasurable (.of_forall hb))

end HexagonPaper
