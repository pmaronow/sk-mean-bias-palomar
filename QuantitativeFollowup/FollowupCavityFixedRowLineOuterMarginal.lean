module
public import QuantitativeFollowup.FollowupCavityFixedRowLineMarginal
public import QuantitativeFollowup.FollowupCavityMixtureGaussian

@[expose] public section

/-! The selected-depth field under the actual Gaussian-root recorded law.
The root tilt and the normalized future continuation are both retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon SpinGlass.AT OverlapPaper FiniteTerminalGenealogy
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem integral_cavityFixedRowLineField_jointLaw_eq_outer_expectation
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (outer : ℝ) (j d : ℕ) (hd : d≤j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S→ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀P,|F P|≤C) :
    (∫z,F (cavityFixedRowLineField j d z.1 z.2)
      ∂finiteCascadeTreeGaussianJointLaw V a L outer (observationLinearTree j) R H)=
      ∫Q,sourceKernelExpectation
        (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (d+r))
        (j-d) F Q∂(finiteStateGaussianRawKernel R H).tilted
          (fun Q=>outer*finiteStateGaussianTerminalCascade V a L j Q) := by
  haveI:=isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (observationLinearTree j)
  haveI:=finiteCascadeTreeGaussianJointLaw_probability V a ha L outer (observationLinearTree j) R H
  have hm : Measurable (fun z : FiniteStateField S×Records (FiniteStateField S) S (observationLinearTree j)=>
      F (cavityFixedRowLineField j d z.1 z.2)):=
    hF.comp (measurable_cavityFixedRowLineField_marginal (E:=FiniteStateField S) (S:=S) j d)
  have hi : Integrable (fun z : FiniteStateField S×Records (FiniteStateField S) S (observationLinearTree j)=>
      F (cavityFixedRowLineField j d z.1 z.2))
      (finiteCascadeTreeGaussianJointLaw V a L outer (observationLinearTree j) R H):=
    (integrable_const C).mono' hm.aestronglyMeasurable
      (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hC _)
  rw [finiteCascadeTreeGaussianJointLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun Q=>integral_cavityFixedRowLineField_eq_sourceKernelExpectation
    V a ha L j d hd Q F hF C hC

theorem integral_cavityFixedRowLineField_jointLaw_eq_gaussian_quotient
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (outer : ℝ) (j d : ℕ) (hd : d≤j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S→ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀P,|F P|≤C) :
    (∫z,F (cavityFixedRowLineField j d z.1 z.2)
      ∂finiteCascadeTreeGaussianJointLaw V a L outer (observationLinearTree j) R H)=
      (∫g,Real.exp (outer*finiteStateGaussianTerminalCascade V a L j (H+R g))*
        sourceKernelExpectation
          (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (d+r))
          (j-d) F (H+R g)∂stdGaussian (FiniteStateGaussianInput J))/
        finiteCascadeTreeGaussianNormalizer V a L outer j R H := by
  have hC0 : 0≤C:=(abs_nonneg (F 0)).trans (hC 0)
  rw [cavityGaussianTree_integral_root_gaussian V a ha L outer (observationLinearTree j) R H
    (fun z : FiniteStateField S×Records (FiniteStateField S) S (observationLinearTree j)=>
      F (cavityFixedRowLineField j d z.1 z.2))
    (hF.comp (measurable_cavityFixedRowLineField_marginal (E:=FiniteStateField S) (S:=S) j d)) C hC0
    (fun z=>by simpa only [Real.norm_eq_abs] using hC _)]
  simp_rw [integral_cavityFixedRowLineField_eq_sourceKernelExpectation V a ha L j d hd _ F hF C hC]

theorem integral_cavityFixedRowLineField_jointLaw_eq_tilted_gaussian
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀r,0≤a r)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (outer : ℝ) (j d : ℕ) (hd : d≤j)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S→ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀P,|F P|≤C) :
    (∫z,F (cavityFixedRowLineField j d z.1 z.2)
      ∂finiteCascadeTreeGaussianJointLaw V a L outer (observationLinearTree j) R H)=
      ∫g,sourceKernelExpectation
        (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (d+r))
        (j-d) F (H+R g)∂(stdGaussian (FiniteStateGaussianInput J)).tilted
          (fun g=>outer*finiteStateGaussianTerminalCascade V a L j (H+R g)) := by
  rw [integral_cavityFixedRowLineField_jointLaw_eq_gaussian_quotient V a ha L outer j d hd R H F hF C hC,
    integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]
  congr 1
  rw [finiteCascadeTreeGaussianNormalizer,finiteStateGaussianRawKernel_apply,
    integral_map (by fun_prop)
      (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.const_mul outer).exp.aestronglyMeasurable)]

end QuantitativeFollowup
