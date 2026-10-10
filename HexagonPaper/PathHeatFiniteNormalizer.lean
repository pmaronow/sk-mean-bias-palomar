module
public import HexagonPaper.PathHeatFinitePrice
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! Actual finite clock differentiation of the positive exponential
normalizer. The logarithmic derivative is proved by differentiating the
unnormalized integral, with genuine Gaussian integration by parts. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def pathHeatFiniteNormalizerScore (V : ℝ→QuantitativePaper.Field m→ℝ)
    (dv : ℝ→Fin n→ℝ) (mask : Fin n→QuantitativePaper.Field m) (a : ℝ)
    (y : QuantitativePaper.Field m) : ℝ :=
  gaussianParameterDerivative V a y+(1/2:ℝ)*∑j : Fin m,∑k : Fin m,
    pathHeatVarianceCovarianceDerivative dv mask a j k*
      (vectorHessian (V a) y (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)+
        fderiv ℝ (V a) y (EuclideanSpace.single j 1)*fderiv ℝ (V a) y (EuclideanSpace.single k 1))

theorem pathHeat_finiteClock_expHessian_contraction (V : QuantitativePaper.Field m→ℝ)
    (hV : ContDiff ℝ 2 V) (y : QuantitativePaper.Field m)
    (v dv : ℝ→Fin n→ℝ) (mask : Fin n→QuantitativePaper.Field m) (a : ℝ)
    (hv : ∀i,0<v a i) :
    (∑i : Fin n,vectorHessian (fun u=>Real.exp (V u)) y
      (pathHeatVarianceFactor v mask a (EuclideanSpace.single i 1))
      (pathHeatVarianceFactorDerivative v dv mask a (EuclideanSpace.single i 1)))=
      Real.exp (V y)*((1/2:ℝ)*∑j : Fin m,∑k : Fin m,
        pathHeatVarianceCovarianceDerivative dv mask a j k*
          (vectorHessian V y (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)+
            fderiv ℝ V y (EuclideanSpace.single j 1)*fderiv ℝ V y (EuclideanSpace.single k 1))) := by
  have hs : ∀h k,vectorHessian (fun u=>Real.exp (V u)) y h k=
      vectorHessian (fun u=>Real.exp (V u)) y k h :=
    fun h k=>(hV.exp.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq h k
  rw [pathHeatVarianceFactor_bilinear_contraction v dv mask a hv _ hs]
  simp only [vectorHessian_exp_potential V hV,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem hasDerivAt_pathHeat_finiteClock_normalizer
    (V : ℝ→QuantitativePaper.Field m→ℝ) (v dv : ℝ→Fin n→ℝ)
    (mask : Fin n→QuantitativePaper.Field m) (a : ℝ) (S : Set ℝ) (hS : S∈𝓝 a)
    (hv : ∀u∈S,∀i,0<v u i)
    (hdv : ∀u∈S,∀i,HasDerivAt (fun z=>v z i) (dv u i) u)
    (hV : ∀u∈S,∀y,DifferentiableAt ℝ (Function.uncurry V) (u,y))
    (hVa : ContDiff ℝ 2 (V a)) (hmV : Measurable (gaussianParameterDerivative V a))
    (dH : ∀u,VectorHeatDatum (fun y=>Real.exp (V u y))) (C R K L : ℝ≥0)
    (hA : ∀u∈S,‖pathHeatVarianceFactor v mask u‖≤K)
    (hB : ∀u∈S,‖pathHeatVarianceFactorDerivative v dv mask u‖≤L)
    (hfirstH : ∀u∈S,∀y,‖fderiv ℝ (fun z=>Real.exp (V u z)) y‖≤C*Real.exp (R*‖y‖))
    (hpartialH : ∀u∈S,∀y,‖gaussianParameterDerivative (fun z y=>Real.exp (V z y)) u y‖≤C*Real.exp (R*‖y‖))
    (x : QuantitativePaper.Field m) :
    HasDerivAt (fun u=>gaussianLinearMean (fun y=>Real.exp (V u y))
      (pathHeatVarianceFactor v mask u) x)
      (∫g,Real.exp (V a (x+pathHeatVarianceFactor v mask a g))*
        pathHeatFiniteNormalizerScore V dv mask a (x+pathHeatVarianceFactor v mask a g)
          ∂fieldGaussian n) a := by
  let WH := fun u (y : QuantitativePaper.Field m)=>Real.exp (V u y)
  let A := pathHeatVarianceFactor v mask
  let B := pathHeatVarianceFactorDerivative v dv mask
  have ha := mem_of_mem_nhds hS
  have hmWH : Measurable (gaussianParameterDerivative WH a) := by
    have he : gaussianParameterDerivative WH a=fun y=>Real.exp (V a y)*gaussianParameterDerivative V a y :=
      funext (fun y=>gaussianParameterDerivative_exp V (hV a ha y))
    rw [he]
    exact hVa.continuous.measurable.exp.mul hmV
  have hpa : AEStronglyMeasurable (fun g=>gaussianParameterDerivative WH a (x+A a g))
      (fieldGaussian n) :=
    (hmWH.comp (continuous_const.add (A a).continuous).measurable).aestronglyMeasurable
  have hd := hasDerivAt_gaussianLinearParameterMean WH A B a S hS dH
    (fun u hu y=>(hV u hu y).exp)
    (fun u hu=>hasDerivAt_pathHeatVarianceFactor v dv mask u (hv u hu) (hdv u hu))
    C R K L hA hB hfirstH hpartialH x hpa
  have hip : Integrable (fun g=>gaussianParameterDerivative WH a (x+A a g)) (fieldGaussian n) := by
    apply ((SYK.integrable_exp_mul_norm (ι:=Fin n) (R*K)).const_mul
      (C*Real.exp (R*‖x‖))).mono' hpa
    exact .of_forall (gaussianParameterDerivative_input_bound WH (A a) a x C R K
      (hpartialH a ha) (hA a ha))
  have hih : Integrable (fun g=>∑i : Fin n,vectorHessian (WH a) (x+A a g)
      (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1))) (fieldGaussian n) :=
    integrable_finsetSum Finset.univ (fun i _=>(gaussianLinearFirst_stein (dH a) (A a) (B a) x i).2.1)
  apply hd.congr_deriv
  rw [←integral_add hip hih]
  apply integral_congr_ae
  exact .of_forall fun g=>by
    dsimp only [WH, A, B]
    rw [gaussianParameterDerivative_exp V (hV a ha _),
      pathHeat_finiteClock_expHessian_contraction (V a) hVa _ v dv mask a (hv a ha)]
    unfold pathHeatFiniteNormalizerScore
    ring

end HexagonPaper
