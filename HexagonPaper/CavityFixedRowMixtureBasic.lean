module
public import FourPapersCommon.FiniteStateGaussianConvolutionKernels

@[expose] public section

/-! Normalizer-weighted disintegration of a Gaussian incident row.
The child kernel is arbitrary and genuinely Markov; no finite-profile
cascade representation is required. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  {Y : Type} [MeasurableSpace Y]

def cavityGaussianRootNormalizer (U : FiniteStateField S → ℝ) (a : ℝ)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) : ℝ :=
  ∫ g, Real.exp (a * U (H + R g)) ∂stdGaussian (FiniteStateGaussianInput J)

def cavityGaussianRootJoint (U : FiniteStateField S → ℝ) (a : ℝ)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) (K : Kernel (FiniteStateField S) Y) :
    Measure (FiniteStateField S × Y) :=
  (finiteStateGaussianStepLaw a R U H) ⊗ₘ K

theorem cavityGaussianRootNormalizer_pos (U : FiniteStateField S → ℝ)
    {C : NNReal} (hU : LipschitzWith C U) (a : ℝ)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) : 0 < cavityGaussianRootNormalizer U a R H :=
  integral_exp_pos (integrable_exp_finiteStateGaussian_lipschitz U hU R H a)

theorem cavityGaussianRootJoint_probability (U : FiniteStateField S → ℝ)
    {C : NNReal} (hU : LipschitzWith C U) (a : ℝ)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) (K : Kernel (FiniteStateField S) Y) [IsMarkovKernel K] :
    IsProbabilityMeasure (cavityGaussianRootJoint U a R H K) := by
  haveI := isProbabilityMeasure_finiteStateGaussianStepLaw a R U hU.continuous.measurable H
    (integrable_exp_finiteStateGaussian_lipschitz U hU R H a)
  unfold cavityGaussianRootJoint
  infer_instance

theorem cavityGaussianRootJoint_integral (U : FiniteStateField S → ℝ)
    {C : NNReal} (hU : LipschitzWith C U) (a : ℝ)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) (K : Kernel (FiniteStateField S) Y) [IsMarkovKernel K]
    (F : FiniteStateField S × Y → ℝ) (hF : Measurable F)
    (B : ℝ) (hb : ∀ z, ‖F z‖ ≤ B) :
    (∫ z, F z ∂cavityGaussianRootJoint U a R H K) =
      (∫ g, Real.exp (a * U (H + R g)) *
        (∫ y, F (H + R g, y) ∂K (H + R g))
        ∂stdGaussian (FiniteStateGaussianInput J)) /
        cavityGaussianRootNormalizer U a R H := by
  haveI := cavityGaussianRootJoint_probability U hU a R H K
  haveI := isProbabilityMeasure_finiteStateGaussianStepLaw a R U hU.continuous.measurable H
    (integrable_exp_finiteStateGaussian_lipschitz U hU R H a)
  have hi : Integrable F (cavityGaussianRootJoint U a R H K) :=
    (integrable_const B).mono' hF.aestronglyMeasurable (.of_forall hb)
  have hM : Measurable (fun Q => ∫ y, F (Q, y) ∂K Q) :=
    (hF.stronglyMeasurable.integral_kernel_prod_right').measurable
  rw [cavityGaussianRootJoint, Measure.integral_compProd hi]
  exact integral_finiteStateGaussianStepLaw_gaussian a R U _
    hU.continuous.measurable hM H

theorem cavityGaussianRootNormalizer_sumMap (U : FiniteStateField S → ℝ)
    {C : NNReal} (hU : LipschitzWith C U) (a : ℝ)
    (M : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) :
    (∫ θ, cavityGaussianRootNormalizer U a R (H + M θ)
      ∂stdGaussian (FiniteStateGaussianInput I)) =
      cavityGaussianRootNormalizer U a (finiteStateGaussianSumMap M R) H := by
  unfold cavityGaussianRootNormalizer
  rw [←integral_prod _ (integrable_exp_finiteStateGaussian_product_lipschitz M R U hU H a)]
  have hs := (hasLaw_finiteGaussianSplit (I := I) (J := J)).integral_comp
    (f := fun z : FiniteStateGaussianInput I × FiniteStateGaussianInput J =>
      Real.exp (a * U (H + M z.1 + R z.2)))
    ((hU.continuous.measurable.comp (by fun_prop)).const_mul a).exp.aestronglyMeasurable
  simpa only [Function.comp_def, finiteGaussianSplit, finiteStateGaussianSumMap_apply,
    add_assoc] using hs.symm

theorem cavityGaussianRootJoint_weighted_mixture (U : FiniteStateField S → ℝ)
    {C : NNReal} (hU : LipschitzWith C U) (a : ℝ)
    (M : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) (K : Kernel (FiniteStateField S) Y) [IsMarkovKernel K]
    (F : FiniteStateField S × Y → ℝ) (hF : Measurable F)
    (B : ℝ) (hb : ∀ z, ‖F z‖ ≤ B) :
    (∫ z, F z ∂cavityGaussianRootJoint U a (finiteStateGaussianSumMap M R) H K) =
      (∫ θ, cavityGaussianRootNormalizer U a R (H + M θ) *
        (∫ z, F z ∂cavityGaussianRootJoint U a R (H + M θ) K)
        ∂stdGaussian (FiniteStateGaussianInput I)) /
      (∫ θ, cavityGaussianRootNormalizer U a R (H + M θ)
        ∂stdGaussian (FiniteStateGaussianInput I)) := by
  let G := fun Q => ∫ y, F (Q, y) ∂K Q
  have hm : Measurable G := (hF.stronglyMeasurable.integral_kernel_prod_right').measurable
  have hG (Q) : ‖G Q‖ ≤ B := by
    simpa only [G, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := K Q) (f := fun y => F (Q, y))
        (C := B) (.of_forall fun y => hb (Q, y))
  have hinput : Measurable (fun z : FiniteStateGaussianInput I × FiniteStateGaussianInput J =>
    H + M z.1 + R z.2) := by fun_prop
  have hnumMeas : Measurable (fun z : FiniteStateGaussianInput I × FiniteStateGaussianInput J =>
    Real.exp (a * U (H + M z.1 + R z.2)) * G (H + M z.1 + R z.2)) :=
    (((hU.continuous.measurable.comp hinput).const_mul a).exp).mul (hm.comp hinput)
  have hi := integrable_exp_finiteStateGaussian_product_lipschitz M R U hU H a
  have hnum : Integrable (fun z : FiniteStateGaussianInput I × FiniteStateGaussianInput J =>
      Real.exp (a * U (H + M z.1 + R z.2)) * G (H + M z.1 + R z.2))
      ((stdGaussian (FiniteStateGaussianInput I)).prod (stdGaussian (FiniteStateGaussianInput J))) := by
    apply (hi.mul_const B).mono' hnumMeas.aestronglyMeasurable
    exact .of_forall fun z => by
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hG _) (Real.exp_pos _).le
  have hcancel (θ) : cavityGaussianRootNormalizer U a R (H + M θ) *
      (∫ z, F z ∂cavityGaussianRootJoint U a R (H + M θ) K) =
      ∫ g, Real.exp (a * U (H + M θ + R g)) * G (H + M θ + R g)
        ∂stdGaussian (FiniteStateGaussianInput J) := by
    rw [cavityGaussianRootJoint_integral U hU a R (H + M θ) K F hF B hb]
    exact mul_div_cancel₀ _ (cavityGaussianRootNormalizer_pos U hU a R _).ne'
  rw [cavityGaussianRootJoint_integral U hU a _ H K F hF B hb,
    cavityGaussianRootNormalizer_sumMap U hU a M R H]
  congr 1
  simp_rw [hcancel]
  rw [←integral_prod _ hnum]
  have hs := (hasLaw_finiteGaussianSplit (I := I) (J := J)).integral_comp
    (f := fun z : FiniteStateGaussianInput I × FiniteStateGaussianInput J =>
      Real.exp (a * U (H + M z.1 + R z.2)) * G (H + M z.1 + R z.2))
    hnumMeas.aestronglyMeasurable
  simpa only [Function.comp_def, finiteGaussianSplit, finiteStateGaussianSumMap_apply,
    add_assoc, G] using hs

end HexagonPaper
