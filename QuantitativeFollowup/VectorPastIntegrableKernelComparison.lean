module
public import QuantitativeFollowup.VectorIntegrableKernelMean
public import QuantitativeFollowup.VectorPastKernelComparison

@[expose] public section

/-! The literal earlier-kernel comparison for arbitrary nonnegative
normalized L1 kernels, including every L2 kernel in Lemma 3.1. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeasureWeightedOverlapScore_past_comparison_of_integrable (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hiκ : Integrable κ (parisiFreeMeasure μ s))
    (hκpos : ∀p,0≤κ p) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1) (q : Paper.Overlap)
    (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→p≤q) :
    (fun z : VectorDisorderBrownianSample n×Configuration n=>‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2/(n:ℝ))
      =ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
    (fun z=>2*((vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureWeightedOverlapScore μ s β t ht.le κ|
        vectorSpinPast n (q:ℝ).toNNReal] z)+
      (∫p,κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2
        ∂parisiFreeMeasure μ s)/(n:ℝ)) := by
  have hmean:=adapted_vectorMeasureKernelMean (n:=n) μ s β t ht.le κ hκ q hSupport
  have hoff:=adapted_vectorMeasureKernelOffset (n:=n) μ s β t ht.le κ hκ q hSupport
  have hb (i : Fin n) : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal]
      (fun sample=>vectorMeasureKernelMean μ s β t ht.le κ sample i):=
    (EuclideanSpace.proj i).continuous.measurable.comp hmean.measurable
  have hce:=condExp_vectorMeasure_past_affine_score μ β t a hβ ht q
    (vectorMeasureKernelMean μ s β t ht.le κ) (vectorMeasureKernelOffset μ s β t ht.le κ)
    hb hoff.measurable 1 ((n:ℝ)/2) (by norm_num)
    (fun sample i=>vectorMeasureKernelMean_component_bound_normalized μ s β t ht.le κ hκ hiκ hκpos hnormal sample i)
    (vectorMeasureKernelOffset_bound_normalized μ s β t ht.le κ hκ hiκ hκpos hnormal)
  have haff : vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.le κ=
      vectorMeasurePastAffineSpinScore (vectorMeasureKernelMean μ s β t ht.le κ)
        (vectorMeasureKernelOffset μ s β t ht.le κ) := by
    funext z
    exact vectorMeasureWeightedOverlapScore_eq_affine_of_integrable μ s β t ht.le κ hκ hiκ z
  rw [←haff] at hce
  filter_upwards [hce] with z hz
  have hm : Measurable (fun p : Paper.Overlap=>vectorMeasureSpinMean μ β t ht.le p z.1):=
    (continuous_vectorMeasureSpinMean_path μ β t ht.le z.1).measurable
  have hiR : Integrable (fun p=>κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-
      vectorMeasureSpinMean μ β t ht.le p z.1‖^2) (parisiFreeMeasure μ s) := by
    apply (hiκ.norm.mul_const (4*(n:ℝ))).mono'
      (hκ.mul ((measurable_const.sub hm).norm.pow_const 2)).aestronglyMeasurable
    exact .of_forall fun p=>by
      change ‖κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-
        vectorMeasureSpinMean μ β t ht.le p z.1‖^2‖≤‖κ p‖*(4*(n:ℝ))
      rw [norm_mul,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (norm_sq_vectorMeasureSpinMean_sub_le μ β t ht.le p q z.1)
        (norm_nonneg (κ p))
  have hiC : Integrable (fun p=>κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2)
      (parisiFreeMeasure μ s):=hiκ.mul_const _
  have hiM:=integrable_vectorMeasureKernelMean_of_integrable μ s β t ht.le κ hκ hiκ z.1
  have hiI:=(innerSL ℝ (vectorMeasureSpinMean μ β t ht.le q z.1)).integrable_comp hiM
  have hlin:=(innerSL ℝ (vectorMeasureSpinMean μ β t ht.le q z.1)).integral_comp_comm hiM
  simp only [innerSL_apply_apply,inner_smul_right,smul_eq_mul] at hiI hlin
  have hiI' : Integrable (fun p=>κ p*inner ℝ (vectorMeasureSpinMean μ β t ht.le p z.1)
      (vectorMeasureSpinMean μ β t ht.le q z.1)) (parisiFreeMeasure μ s) := by
    simpa only [real_inner_comm] using hiI
  have hlin' : (∫p,κ p*inner ℝ (vectorMeasureSpinMean μ β t ht.le p z.1)
      (vectorMeasureSpinMean μ β t ht.le q z.1) ∂parisiFreeMeasure μ s)=
      inner ℝ (vectorMeasureKernelMean μ s β t ht.le κ z.1) (vectorMeasureSpinMean μ β t ht.le q z.1) := by
    simpa only [vectorMeasureKernelMean,real_inner_comm,mul_comm] using hlin
  have ho:=integrable_vectorMeasureKernelOffset_of_integrable μ s β t ht.le κ hκ hiκ z.1
  have hpalg (p : Paper.Overlap) : κ p*(‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2-
      ‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2)=
      2*(κ p*inner ℝ (vectorMeasureSpinMean μ β t ht.le p z.1) (vectorMeasureSpinMean μ β t ht.le q z.1))-
      2*(κ p*‖vectorMeasureSpinMean μ β t ht.le p z.1‖^2/2) := by
    rw [norm_sub_sq_real,real_inner_comm (vectorMeasureSpinMean μ β t ht.le q z.1)
      (vectorMeasureSpinMean μ β t ht.le p z.1)]
    ring
  have he : ‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2-
      (∫p,κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2
        ∂parisiFreeMeasure μ s)=
      2*inner ℝ (vectorMeasureKernelMean μ s β t ht.le κ z.1) (vectorMeasureSpinMean μ β t ht.le q z.1)-
        2*vectorMeasureKernelOffset μ s β t ht.le κ z.1 := by
    calc
      _=∫p,κ p*(‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2-
          ‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2)
            ∂parisiFreeMeasure μ s := by
        simp_rw [mul_sub]
        rw [integral_sub hiC hiR,integral_mul_const,hnormal,one_mul]
      _=∫p,2*(κ p*inner ℝ (vectorMeasureSpinMean μ β t ht.le p z.1) (vectorMeasureSpinMean μ β t ht.le q z.1))-
          2*(κ p*‖vectorMeasureSpinMean μ β t ht.le p z.1‖^2/2) ∂parisiFreeMeasure μ s :=
        integral_congr_ae (.of_forall hpalg)
      _=_ := by rw [integral_sub (hiI'.const_mul 2) (ho.const_mul 2),integral_const_mul,integral_const_mul,hlin'];rfl
  change _=2*((vectorMeasureSpinPathLaw μ β t a ht.le)[vectorMeasureWeightedOverlapScore μ s β t ht.le κ|
    vectorSpinPast n (q:ℝ).toNNReal] z)+_
  rw [hz]
  have hnumer : ‖vectorMeasureSpinMean μ β t ht.le q z.1‖^2=
      2*inner ℝ (vectorMeasureKernelMean μ s β t ht.le κ z.1) (vectorMeasureSpinMean μ β t ht.le q z.1)-
        2*vectorMeasureKernelOffset μ s β t ht.le κ z.1+
      (∫p,κ p*‖vectorMeasureSpinMean μ β t ht.le q z.1-vectorMeasureSpinMean μ β t ht.le p z.1‖^2
        ∂parisiFreeMeasure μ s) := by linarith
  rw [hnumer]
  ring

end QuantitativeFollowup
