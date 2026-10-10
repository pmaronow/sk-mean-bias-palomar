module
public import HexagonPaper.PathHeatSignedSourceFiniteData

@[expose] public section

/-! Raw finite numerator differentiation, before normalization or auxiliary
integration. This exact analytic step consumes data constructed in the
source module, and retains the independently differentiated clock covariance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff BigOperators
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem hasDerivAt_pathHeat_finiteClock_numerator
    (V F : ℝ→Field m→ℝ) (v dv : ℝ→Fin n→ℝ) (mask : Fin n→Field m)
    (a : ℝ) (U : Set ℝ) (hU : U∈𝓝 a)
    (C R K L : ℝ≥0) (data : PathHeatFiniteAnalyticData V F U C R)
    (hv : ∀u∈U,∀i,0<v u i)
    (hdv : ∀u∈U,∀i,HasDerivAt (fun z=>v z i) (dv u i) u)
    (hA : ∀u∈U,‖pathHeatVarianceFactor v mask u‖≤K)
    (hB : ∀u∈U,‖pathHeatVarianceFactorDerivative v dv mask u‖≤L)
    (x : Field m) :
    HasDerivAt (fun u=>gaussianLinearMean (fun y=>Real.exp (V u y)*F u y)
      (pathHeatVarianceFactor v mask u) x)
      (∫g,Real.exp (V a (x+pathHeatVarianceFactor v mask a g))*
        (gaussianParameterDerivative F a (x+pathHeatVarianceFactor v mask a g)+
          F a (x+pathHeatVarianceFactor v mask a g)*
            gaussianParameterDerivative V a (x+pathHeatVarianceFactor v mask a g)+
          (1/2:ℝ)*∑j : Fin m,∑k : Fin m,
            pathHeatVarianceCovarianceDerivative dv mask a j k*
              gaussianScoreBilinear (V a) (F a) (x+pathHeatVarianceFactor v mask a g)
                (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) 0)
        ∂fieldGaussian n) a := by
  let WF := fun u (y : Field m)=>Real.exp (V u y)*F u y
  let A := pathHeatVarianceFactor v mask
  let B := pathHeatVarianceFactorDerivative v dv mask
  have ha := mem_of_mem_nhds hU
  have hVa := data.spatialV a ha
  have hFa := data.spatialF a ha
  have hmWF : Measurable (gaussianParameterDerivative WF a) := by
    have he : gaussianParameterDerivative WF a=fun y=>
        Real.exp (V a y)*(gaussianParameterDerivative F a y+F a y*gaussianParameterDerivative V a y) :=
      funext fun y=>gaussianParameterDerivative_exp_mul V F (data.jointV a ha y) (data.jointF a ha y)
    rw [he]
    exact hVa.continuous.measurable.exp.mul
      ((data.parameterF a ha).add (hFa.continuous.measurable.mul (data.parameterV a ha)))
  have hpa : AEStronglyMeasurable (fun g=>gaussianParameterDerivative WF a (x+A a g)) (fieldGaussian n) :=
    (hmWF.comp (continuous_const.add (A a).continuous).measurable).aestronglyMeasurable
  have hd := hasDerivAt_gaussianLinearParameterMean WF A B a U hU data.numerator
    (fun u hu y=>(data.jointV u hu y).exp.mul (data.jointF u hu y))
    (fun u hu=>hasDerivAt_pathHeatVarianceFactor v dv mask u (hv u hu) (hdv u hu))
    C R K L hA hB data.firstNumerator data.partialNumerator x hpa
  have hip : Integrable (fun g=>gaussianParameterDerivative WF a (x+A a g)) (fieldGaussian n) := by
    apply ((SYK.integrable_exp_mul_norm (ι:=Fin n) (R*K)).const_mul
      (C*Real.exp (R*‖x‖))).mono' hpa
    exact .of_forall (gaussianParameterDerivative_input_bound WF (A a) a x C R K
      (data.partialNumerator a ha) (hA a ha))
  have hih : Integrable (fun g=>∑i : Fin n,vectorHessian (WF a) (x+A a g)
      (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1))) (fieldGaussian n) :=
    integrable_finsetSum Finset.univ (fun i _=>(gaussianLinearFirst_stein (data.numerator a) (A a) (B a) x i).2.1)
  apply hd.congr_deriv
  rw [←integral_add hip hih]
  apply integral_congr_ae
  exact .of_forall fun g=>by
    dsimp only [WF,A,B]
    rw [gaussianParameterDerivative_exp_mul V F (data.jointV a ha _) (data.jointF a ha _)]
    have he (i : Fin n) := gaussianScoreBilinear_exp_identity (V a) (F a) hVa hFa
      (x+pathHeatVarianceFactor v mask a g)
      (pathHeatVarianceFactor v mask a (EuclideanSpace.single i 1))
      (pathHeatVarianceFactorDerivative v dv mask a (EuclideanSpace.single i 1)) 0
    simp only [zero_mul,sub_zero] at he
    simp_rw [←he]
    rw [←Finset.mul_sum,pathHeat_finiteClock_score_contraction (V a) (F a) hVa hFa _ 0 v dv mask a (hv a ha)]
    ring

end HexagonPaper
