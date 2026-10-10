module
public import FourPapersCommon.FiniteCascadeTreeGaussianDensity
public import FourPapersCommon.FiniteStateGaussianConvolutionKernels

@[expose] public section

/-! Gaussian incident rows are averaged with their genuine fractional
normalizer. Every root field, intermediate field and terminal spin is
retained in the mixture identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I J K : Type} [Fintype S] [Fintype I] [Fintype J] [Fintype K]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem cavityGaussianTree_integral_root_gaussian (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (outer : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (B : ℝ) (hB : 0≤B) (hb : ∀z,‖F z‖≤B) :
    (∫z,F z ∂finiteCascadeTreeGaussianJointLaw V a L outer T R H)=
      (∫g,Real.exp (outer*finiteStateGaussianTerminalCascade V a L j (H+R g))*
        (∫r,F (H+R g,r) ∂finiteCascadeTreeRecordKernel V a L T (H+R g))
        ∂stdGaussian (FiniteStateGaussianInput J))/
        finiteCascadeTreeGaussianNormalizer V a L outer j R H := by
  haveI:=isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI:=finiteCascadeTreeGaussianJointLaw_probability V a ha L outer T R H
  have hi : Integrable F (finiteCascadeTreeGaussianJointLaw V a L outer T R H) :=
    (integrable_const B).mono' hF.aestronglyMeasurable (.of_forall hb)
  have hM : Measurable (fun Q=>∫r,F (Q,r) ∂finiteCascadeTreeRecordKernel V a L T Q) :=
    (hF.stronglyMeasurable.integral_kernel_prod_right').measurable
  rw [finiteCascadeTreeGaussianJointLaw,Measure.integral_compProd hi]
  change (∫Q,(∫r,F (Q,r) ∂finiteCascadeTreeRecordKernel V a L T Q)
    ∂finiteStateGaussianStepLaw outer R (finiteStateGaussianTerminalCascade V a L j) H)=_
  rw [show finiteCascadeTreeGaussianNormalizer V a L outer j R H=
    ∫g,Real.exp (outer*finiteStateGaussianTerminalCascade V a L j (H+R g))
      ∂stdGaussian (FiniteStateGaussianInput J) by
        rw [finiteCascadeTreeGaussianNormalizer,finiteStateGaussianRawKernel_apply,
          integral_map (by fun_prop)
            (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.const_mul outer).exp.aestronglyMeasurable)]]
  exact integral_finiteStateGaussianStepLaw_gaussian outer R _ _
    (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable hM H

theorem cavityGaussianTree_normalizer_sumMap (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (outer : ℝ) (j : ℕ)
    (M : FiniteStateGaussianInput K→L[ℝ]FiniteStateField S)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    (∫theta,finiteCascadeTreeGaussianNormalizer V a L outer j R (H+M theta)
      ∂stdGaussian (FiniteStateGaussianInput K))=
      finiteCascadeTreeGaussianNormalizer V a L outer j (finiteStateGaussianSumMap M R) H := by
  have hU:Measurable (fun Q=>Real.exp (outer*finiteStateGaussianTerminalCascade V a L j Q)) :=
    ((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.const_mul outer).exp
  have hz (A : FiniteStateField S) : finiteCascadeTreeGaussianNormalizer V a L outer j R A=
      ∫g,Real.exp (outer*finiteStateGaussianTerminalCascade V a L j (A+R g))
        ∂stdGaussian (FiniteStateGaussianInput J) := by
    rw [finiteCascadeTreeGaussianNormalizer,finiteStateGaussianRawKernel_apply,
      integral_map (by fun_prop) hU.aestronglyMeasurable]
  rw [finiteCascadeTreeGaussianNormalizer,finiteStateGaussianRawKernel_apply,
    integral_map (by fun_prop) hU.aestronglyMeasurable]
  simp_rw [hz]
  rw [←integral_prod _ (integrable_exp_finiteStateGaussian_product_lipschitz M R _
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L j) H outer)]
  have hs:=(hasLaw_finiteGaussianSplit (I:=K) (J:=J)).integral_comp
    (f:=fun z : FiniteStateGaussianInput K×FiniteStateGaussianInput J=>
      Real.exp (outer*finiteStateGaussianTerminalCascade V a L j (H+M z.1+R z.2)))
    ((hU.comp (by fun_prop)).aestronglyMeasurable)
  simpa only [Function.comp_def,finiteGaussianSplit,finiteStateGaussianSumMap_apply,add_assoc] using hs.symm

theorem cavityGaussianTree_integral_weighted_mixture (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0≤a j) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (outer : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (M : FiniteStateGaussianInput K→L[ℝ]FiniteStateField S)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
    (hF : Measurable F) (B : ℝ) (hB : 0≤B) (hb : ∀z,‖F z‖≤B) :
    (∫z,F z ∂finiteCascadeTreeGaussianJointLaw V a L outer T (finiteStateGaussianSumMap M R) H)=
      (∫theta,finiteCascadeTreeGaussianNormalizer V a L outer j R (H+M theta)*
        (∫z,F z ∂finiteCascadeTreeGaussianJointLaw V a L outer T R (H+M theta))
        ∂stdGaussian (FiniteStateGaussianInput K))/
      (∫theta,finiteCascadeTreeGaussianNormalizer V a L outer j R (H+M theta)
        ∂stdGaussian (FiniteStateGaussianInput K)) := by
  haveI:=isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  let U:=finiteStateGaussianTerminalCascade V a L j
  let G:=fun Q=>∫r,F (Q,r) ∂finiteCascadeTreeRecordKernel V a L T Q
  have hm : Measurable G := (hF.stronglyMeasurable.integral_kernel_prod_right').measurable
  have hG (Q) : ‖G Q‖≤B := by
    simpa only [G,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=finiteCascadeTreeRecordKernel V a L T Q)
        (f:=fun r=>F (Q,r)) (C:=B) (.of_forall fun r=>hb (Q,r))
  have hinput : Measurable (fun z : FiniteStateGaussianInput K×FiniteStateGaussianInput J=>
    H+M z.1+R z.2) := by fun_prop
  have hnumMeas : Measurable (fun z : FiniteStateGaussianInput K×FiniteStateGaussianInput J=>
    Real.exp (outer*U (H+M z.1+R z.2))*G (H+M z.1+R z.2)) :=
    (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.comp
      hinput).const_mul outer).exp.mul (hm.comp hinput)
  have hi := integrable_exp_finiteStateGaussian_product_lipschitz M R U
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L j) H outer
  have hnum : Integrable (fun z : FiniteStateGaussianInput K×FiniteStateGaussianInput J=>
      Real.exp (outer*U (H+M z.1+R z.2))*G (H+M z.1+R z.2))
      ((stdGaussian (FiniteStateGaussianInput K)).prod (stdGaussian (FiniteStateGaussianInput J))) := by
    apply (hi.mul_const B).mono' hnumMeas.aestronglyMeasurable
    exact .of_forall fun z=>by
      rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hG _) (Real.exp_pos _).le
  have hcancel (theta) :
      finiteCascadeTreeGaussianNormalizer V a L outer j R (H+M theta)*
        (∫z,F z ∂finiteCascadeTreeGaussianJointLaw V a L outer T R (H+M theta))=
      ∫g,Real.exp (outer*U (H+M theta+R g))*G (H+M theta+R g)
        ∂stdGaussian (FiniteStateGaussianInput J) := by
    rw [cavityGaussianTree_integral_root_gaussian V a ha L outer T R (H+M theta) F hF B hB hb]
    exact mul_div_cancel₀ _ (finiteCascadeTreeGaussianNormalizer_pos V a ha L outer j R _).ne'
  rw [cavityGaussianTree_integral_root_gaussian V a ha L outer T _ H F hF B hB hb,
    cavityGaussianTree_normalizer_sumMap V a ha L outer j M R H]
  congr 1
  simp_rw [hcancel]
  rw [←integral_prod _ hnum]
  have hs:=(hasLaw_finiteGaussianSplit (I:=K) (J:=J)).integral_comp
    (f:=fun z : FiniteStateGaussianInput K×FiniteStateGaussianInput J=>
      Real.exp (outer*U (H+M z.1+R z.2))*G (H+M z.1+R z.2)) hnumMeas.aestronglyMeasurable
  simpa only [Function.comp_def,finiteGaussianSplit,finiteStateGaussianSumMap_apply,add_assoc,U,G] using hs

end QuantitativeFollowup
