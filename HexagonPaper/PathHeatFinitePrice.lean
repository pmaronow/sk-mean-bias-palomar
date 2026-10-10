module
public import HexagonPaper.PathHeatClockFactorBounds
public import QuantitativeFollowup.GaussianWeakParameterResponse

@[expose] public section

/-! Actual finite Gaussian Price differentiation for clock-increment
coordinates. The covariance direction is independently differentiated
from the clock variances, and the exponential normalizer is proved
strictly positive. This is the finite analytic step of the path proof. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem gaussianLinear_exp_normalizer_pos (V : Field m→ℝ)
    (d : VectorHeatDatum (fun y=>Real.exp (V y)))
    (A : Field n→L[ℝ]Field m) (x : Field m) :
    0<gaussianLinearMean (fun y=>Real.exp (V y)) A x := by
  exact integral_exp_pos (integrable_gaussianLinear_input d A x)

theorem pathHeat_finiteClock_score_contraction (V F : Field m→ℝ)
    (hV : ContDiff ℝ 2 V) (hF : ContDiff ℝ 2 F) (y : Field m) (c : ℝ)
    (v dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m) (z : ℝ)
    (hv : ∀i,0<v z i) :
    (∑i : Fin n,gaussianScoreBilinear V F y
      (pathHeatVarianceFactor v mask z (EuclideanSpace.single i 1))
      (pathHeatVarianceFactorDerivative v dv mask z (EuclideanSpace.single i 1)) c)=
      (1/2:ℝ)*∑j : Fin m,∑k : Fin m,
        pathHeatVarianceCovarianceDerivative dv mask z j k*
          gaussianScoreBilinear V F y (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) c := by
  rw [gaussian_covariance_score_contraction V F hV hF]
  simp only [pathHeatVarianceFactor_covariance_direction v dv mask z hv]

/-- Finite Price response with the literal clock covariance derivative.
The hypotheses are genuine finite differentiability and exponential
growth hypotheses; no Gaussian response or normalizer conclusion is
supplied as an assumption. -/
theorem hasDerivAt_pathHeat_finiteClock_response
    (V F : ℝ→Field m→ℝ) (v dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m)
    (a : ℝ) (S : Set ℝ) (hS : S∈𝓝 a)
    (hv : ∀u∈S,∀i,0<v u i)
    (hdv : ∀u∈S,∀i,HasDerivAt (fun z=>v z i) (dv u i) u)
    (hV : ∀u∈S,∀y,DifferentiableAt ℝ (Function.uncurry V) (u,y))
    (hF : ∀u∈S,∀y,DifferentiableAt ℝ (Function.uncurry F) (u,y))
    (hVa : ContDiff ℝ 2 (V a)) (hFa : ContDiff ℝ 2 (F a))
    (hmV : Measurable (gaussianParameterDerivative V a))
    (hmF : Measurable (gaussianParameterDerivative F a))
    (dF : ∀u,VectorHeatDatum (fun y=>Real.exp (V u y)*F u y))
    (dH : ∀u,VectorHeatDatum (fun y=>Real.exp (V u y)))
    (C R K L : ℝ≥0)
    (hA : ∀u∈S,‖pathHeatVarianceFactor v mask u‖≤K)
    (hB : ∀u∈S,‖pathHeatVarianceFactorDerivative v dv mask u‖≤L)
    (hfirstF : ∀u∈S,∀y,‖fderiv ℝ (fun z=>Real.exp (V u z)*F u z) y‖≤C*Real.exp (R*‖y‖))
    (hfirstH : ∀u∈S,∀y,‖fderiv ℝ (fun z=>Real.exp (V u z)) y‖≤C*Real.exp (R*‖y‖))
    (hpartialF : ∀u∈S,∀y,‖gaussianParameterDerivative (fun z y=>Real.exp (V z y)*F z y) u y‖≤C*Real.exp (R*‖y‖))
    (hpartialH : ∀u∈S,∀y,‖gaussianParameterDerivative (fun z y=>Real.exp (V z y)) u y‖≤C*Real.exp (R*‖y‖))
    (x : Field m) :
    HasDerivAt (fun u=>gaussianLinearNormalizedMean (fun y=>Real.exp (V u y)*F u y)
      (fun y=>Real.exp (V u y)) (pathHeatVarianceFactor v mask u) x)
      ((∫g,Real.exp (V a (x+pathHeatVarianceFactor v mask a g))*
        (gaussianExplicitCenteredScore V F a (x+pathHeatVarianceFactor v mask a g)
          (gaussianLinearNormalizedMean (fun y=>Real.exp (V a y)*F a y)
            (fun y=>Real.exp (V a y)) (pathHeatVarianceFactor v mask a) x)+
          (1/2:ℝ)*∑j : Fin m,∑k : Fin m,pathHeatVarianceCovarianceDerivative dv mask a j k*
            gaussianScoreBilinear (V a) (F a) (x+pathHeatVarianceFactor v mask a g)
              (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
              (gaussianLinearNormalizedMean (fun y=>Real.exp (V a y)*F a y)
                (fun y=>Real.exp (V a y)) (pathHeatVarianceFactor v mask a) x))
        ∂fieldGaussian n)/gaussianLinearMean (fun y=>Real.exp (V a y)) (pathHeatVarianceFactor v mask a) x) a := by
  have ha := mem_of_mem_nhds hS
  have he := hasDerivAt_gaussian_weighted_parameter_response_of_partials V F
    (pathHeatVarianceFactor v mask) (pathHeatVarianceFactorDerivative v dv mask) a S hS
    hV hF hVa hFa hmV hmF dF dH
    (fun u hu=>hasDerivAt_pathHeatVarianceFactor v dv mask u (hv u hu) (hdv u hu))
    C R K L hA hB hfirstF hfirstH hpartialF hpartialH x
    (gaussianLinear_exp_normalizer_pos (V a) (dH a) _ x).ne'
  convert he using 1
  congr 2
  funext g
  rw [pathHeat_finiteClock_score_contraction (V a) (F a) hVa hFa _ _ v dv mask a (hv a ha)]

end HexagonPaper
