module
public import QuantitativePaper.ResponseC1ActualCurvature
public import QuantitativePaper.ResponseLipschitzLimits
public import QuantitativePaper.ResponseMeanUpper
public import QuantitativePaper.ResponseTentPhysicalSignalBounds
public import QuantitativePaper.VectorProfileFunctionalRegularity
public import FourPapersCommon.SquaredResponseToSquareRoot

@[expose] public section

/-! The literal arbitrary-measure functional curvature response for every
Lipschitz test vanishing at the endpoints. The measurable a.e. slope enters
the time energy; weak Stieltjes convergence retains every interior atom. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem response_Lipschitz_actual_functional_curvature_bound (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t lam θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hlam : 0≤lam) (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseLipschitzTest) :
    (1-t)^3*(responseLipschitzSignal (n:=n) μ ν β t lam θ ht.le w)^2≤
      iteratedDeriv 2 (fun y=>responseEnergyFunctional n (Paper.parisiMix μ ν y) β t lam) θ*
        responseLipschitzEnergyDenominator (n:=n) μ ν β t lam θ ht.le w := by
  have hc:=tendsto_iteratedDeriv_two_response_grid_mix hn μ ν β t lam θ hβ.ne' ht hθ
  have hs:=tendsto_responseLipschitzSignal_grid (n:=n) μ ν β t lam θ ht ⟨hθ.1.le,hθ.2.le⟩ w
  have hd:=tendsto_responseLipschitzEnergyDenominator_grid (n:=n) μ ν β t lam θ ht ⟨hθ.1.le,hθ.2.le⟩ w
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul (hs.pow 2)) (hc.mul hd)
    (.of_forall fun j=>response_grid_Lipschitz_functional_curvature_bound hn μ ν j β t lam θ hβ ht hlam hθ w)

theorem responseEnergyFunctional_mix_curvature_nonneg (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t lam θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hlam : 0≤lam) (hθ : θ∈Ioo (0:ℝ) 1) :
    0 ≤ iteratedDeriv 2 (fun y=>responseEnergyFunctional n (Paper.parisiMix μ ν y) β t lam) θ := by
  exact ge_of_tendsto
    (tendsto_iteratedDeriv_two_response_grid_mix hn μ ν β t lam θ hβ.ne' ht hθ)
    (.of_forall fun j => iteratedDeriv2_vectorGridResponseFunctional_mix_nonneg hn μ ν j
      β t lam θ hβ ht hlam hθ)

def responseLipschitzMeanEnergy (μ ν : Paper.ParisiMeasure) (β t lam θ : ℝ)
    (ht : t≤1) (w : ResponseLipschitzTest) : ℝ :=
  ∫q in (0:ℝ)..1,(w.slope q)^2*
    responseMeanHessianReal (n:=n) (Paper.parisiMix μ ν θ) β t lam ht q

def responseLipschitzCurvatureEnergy (μ ν : Paper.ParisiMeasure) (β t lam θ : ℝ)
    (ht : t≤1) (w : ResponseLipschitzTest) : ℝ :=
  (1-t)*β*(∫q : Paper.Overlap,(w.value q)^2*
    responseAveragedCurvature (n:=n) (Paper.parisiMix μ ν θ) β t lam ht q
    ∂(Paper.parisiMix μ ν θ : Measure Paper.Overlap))

theorem responseLipschitzMeanEnergy_nonneg (μ ν : Paper.ParisiMeasure)
    (β t lam θ : ℝ) (hβ : 0≤β) (ht : t≤1) (w : ResponseLipschitzTest) :
    0≤responseLipschitzMeanEnergy (n:=n) μ ν β t lam θ ht w := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro q _
  exact mul_nonneg (sq_nonneg _) (responseMeanHessian_nonneg _ β t lam hβ ht _)

theorem responseLipschitzCurvatureEnergy_nonneg (μ ν : Paper.ParisiMeasure)
    (β t lam θ : ℝ) (hβ : 0≤β) (ht : t≤1) (w : ResponseLipschitzTest) :
    0≤responseLipschitzCurvatureEnergy (n:=n) μ ν β t lam θ ht w := by
  apply mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) hβ)
  exact integral_nonneg (fun q=>mul_nonneg (sq_nonneg _)
    (responseAveragedCurvature_nonneg _ β t lam ht q))

theorem responseLipschitzEnergyDenominator_eq (μ ν : Paper.ParisiMeasure)
    (β t lam θ : ℝ) (ht : t≤1) (w : ResponseLipschitzTest) :
    responseLipschitzEnergyDenominator (n:=n) μ ν β t lam θ ht w=
      responseLipschitzMeanEnergy (n:=n) μ ν β t lam θ ht w+
        2*responseLipschitzCurvatureEnergy (n:=n) μ ν β t lam θ ht w := by
  unfold responseLipschitzEnergyDenominator responseLipschitzMeanEnergy responseLipschitzCurvatureEnergy
  ring

theorem response_Lipschitz_actual_squareRoot_bound (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t lam θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hlam : 0≤lam) (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseLipschitzTest) :
    (1-t)*|responseLipschitzSignal (n:=n) μ ν β t lam θ ht.le w|≤
      Real.sqrt (iteratedDeriv 2
        (fun y=>responseEnergyFunctional n (Paper.parisiMix μ ν y) β t lam) θ/(1-t))*
      (Real.sqrt (responseLipschitzMeanEnergy (n:=n) μ ν β t lam θ ht.le w)+
        2*Real.sqrt (responseLipschitzMeanEnergy (n:=n) μ ν β t lam θ ht.le w+
          responseLipschitzCurvatureEnergy (n:=n) μ ν β t lam θ ht.le w)) := by
  apply squareRoot_response_of_squared (sub_pos.mpr ht)
    (responseEnergyFunctional_mix_curvature_nonneg hn μ ν β t lam θ hβ ht hlam hθ)
    (responseLipschitzMeanEnergy_nonneg μ ν β t lam θ hβ.le ht.le w)
    (responseLipschitzCurvatureEnergy_nonneg μ ν β t lam θ hβ.le ht.le w)
  rw [←responseLipschitzEnergyDenominator_eq]
  exact response_Lipschitz_actual_functional_curvature_bound hn μ ν β t lam θ hβ ht hlam hθ w

end QuantitativePaper
