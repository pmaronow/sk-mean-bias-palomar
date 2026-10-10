module
public import QuantitativeFollowup.VectorCenteredKernelComparison
public import FourPapersCommon.OneSidedSquareTail

@[expose] public section

/-! Literal factor-sixteen upper and lower self-overlap tails.  The random
variables are the actual marked diffusion observables; conditional moments
are bounded by the genuine minimizing-profile score variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorSelfOverlap (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (z : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  ‖vectorMeasureSpinMean μ β t ht q z.1‖^2/(n:ℝ)

def vectorCenteredSelfOverlap (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (z : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  vectorSelfOverlap μ β t ht q z-(q:ℝ)

theorem measurable_vectorSelfOverlap (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) : Measurable (vectorSelfOverlap (n:=n) μ β t ht q) := by
  exact ((((adapted_vectorMeasureSpinMean μ β t ht q).mono
    ((vectorBrownianFiltration n).le _) le_rfl).comp measurable_fst).norm.pow_const 2).div_const _

theorem vectorSelfOverlap_bounds (hn : 0<n) (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (z : VectorDisorderBrownianSample n×Configuration n) :
    0≤vectorSelfOverlap μ β t ht q z ∧ vectorSelfOverlap μ β t ht q z≤1 := by
  have hnorm : ‖vectorMeasureSpinMean μ β t ht q z.1‖^2≤(n:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _≤∑i : Fin n,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi:=vectorMeasureSpinMean_component_bound μ β t ht q z.1 i
        have h:=sq_le_sq₀ (abs_nonneg _) zero_le_one |>.mpr hi
        simpa only [sq_abs,one_pow] using h
      _=_ := by simp
  exact ⟨div_nonneg (sq_nonneg _) (Nat.cast_nonneg n),
    (div_le_one₀ (by positivity : (0:ℝ)<n)).mpr hnorm⟩

theorem memLp_vectorCenteredSelfOverlap (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    MemLp (vectorCenteredSelfOverlap (n:=n) μ β t ht q) 2
      (vectorMeasureSpinPathLaw μ β t a ht) := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  apply MemLp.of_bound ((measurable_vectorSelfOverlap μ β t ht q).sub measurable_const).aestronglyMeasurable 1
  exact .of_forall fun z=>by
    rw [Real.norm_eq_abs,abs_le]
    have hb:=vectorSelfOverlap_bounds hn μ β t ht q z
    change -1≤vectorSelfOverlap μ β t ht q z-(q:ℝ) ∧
      vectorSelfOverlap μ β t ht q z-(q:ℝ)≤1
    constructor <;> linarith [q.property.1,q.property.2]

theorem memLp_vectorCenteredKernelScore_normalized (μ : Paper.ParisiMeasure)
    (s β t a : ℝ) (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hiκ : Integrable κ (parisiFreeMeasure μ s)) (hκpos : ∀p,0≤κ p)
    (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1) :
    MemLp (vectorCenteredKernelScore (n:=n) μ s β t ht κ) 2
      (vectorMeasureSpinPathLaw μ β t a ht) := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hF : MemLp (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht κ) 2
      (vectorMeasureSpinPathLaw μ β t a ht):=
    MemLp.of_bound (measurable_vectorMeasureWeightedOverlapScore μ s β t ht κ hκ).aestronglyMeasurable (3/2)
      (.of_forall fun z=>by simpa only [hnormal,mul_one] using
        vectorMeasureWeightedOverlapScore_nonneg_kernel_bound μ s β t ht κ hκ hiκ hκpos z)
  exact hF.sub (memLp_const _)

theorem vectorCenteredSelfOverlap_upper_tail (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hκpos : ∀p,0≤κ p)
    (hL : MemLp κ 2 (parisiFreeMeasure μ s)) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1)
    (q : Paper.Overlap) (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→q≤p)
    (θ : ℝ) (hθ : 0<θ) (hd : vectorKernelOverlapLevel μ s κ-(q:ℝ)≤θ/2) :
    (∫z,{z | θ<vectorCenteredSelfOverlap (n:=n) μ β t ht.le q z}.indicator
      (fun z=>vectorCenteredSelfOverlap μ β t ht.le q z^2) z
      ∂vectorMeasureSpinPathLaw μ β t s ht.le)≤
      16*variance (vectorCenteredKernelScore (n:=n) μ s β t ht.le κ)
        (vectorMeasureSpinPathLaw μ β t s ht.le) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t s ht.le
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t s ht.le
  have hiκ:=hL.integrable one_le_two
  have hΛ:=memLp_vectorCenteredKernelScore_normalized (n:=n) μ s β t s ht.le κ hκ hiκ hκpos hnormal
  have hX : Measurable (vectorCenteredSelfOverlap (n:=n) μ β t ht.le q):=
    (measurable_vectorSelfOverlap μ β t ht.le q).sub measurable_const
  have h:=upper_square_tail_bound J (vectorCenteredSelfOverlap μ β t ht.le q)
    (J[vectorCenteredKernelScore μ s β t ht.le κ|vectorSpinPast n (q:ℝ).toNNReal]) hX
    (memLp_vectorCenteredSelfOverlap hn μ β t s ht.le q) (hΛ.condExp one_le_two)
    (vectorKernelOverlapLevel μ s κ-(q:ℝ)) θ hθ hd
    (vectorCenteredKernelScore_future_comparison hn μ s β t s hβ ht κ hκ hiκ hκpos hnormal q hSupport)
  exact h.trans (mul_le_mul_of_nonneg_left
    (vectorCenteredKernelScore_conditional_square_variance hn μ s β t hβ ht hs hμ hmin κ hκ hκpos hL hnormal q).1
    (by norm_num))

theorem vectorCenteredSelfOverlap_lower_tail (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hκpos : ∀p,0≤κ p)
    (hL : MemLp κ 2 (parisiFreeMeasure μ s)) (hnormal : (∫p,κ p ∂parisiFreeMeasure μ s)=1)
    (q : Paper.Overlap) (hSupport : ∀ᵐp ∂parisiFreeMeasure μ s,κ p≠0→p≤q)
    (θ : ℝ) (hθ : 0<θ) (hd : (q:ℝ)-vectorKernelOverlapLevel μ s κ≤θ/2) :
    (∫z,{z | vectorCenteredSelfOverlap (n:=n) μ β t ht.le q z< -θ}.indicator
      (fun z=>vectorCenteredSelfOverlap μ β t ht.le q z^2) z
      ∂vectorMeasureSpinPathLaw μ β t s ht.le)≤
      16*variance (vectorCenteredKernelScore (n:=n) μ s β t ht.le κ)
        (vectorMeasureSpinPathLaw μ β t s ht.le) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t s ht.le
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t s ht.le
  have hiκ:=hL.integrable one_le_two
  have hΛ:=memLp_vectorCenteredKernelScore_normalized (n:=n) μ s β t s ht.le κ hκ hiκ hκpos hnormal
  have hX : Measurable (vectorCenteredSelfOverlap (n:=n) μ β t ht.le q):=
    (measurable_vectorSelfOverlap μ β t ht.le q).sub measurable_const
  have h:=lower_square_tail_bound J (vectorCenteredSelfOverlap μ β t ht.le q)
    (J[vectorCenteredKernelScore μ s β t ht.le κ|vectorSpinPast n (q:ℝ).toNNReal]) hX
    (memLp_vectorCenteredSelfOverlap hn μ β t s ht.le q) (hΛ.condExp one_le_two)
    (vectorKernelOverlapLevel μ s κ-(q:ℝ)) θ hθ (by linarith)
    (vectorCenteredKernelScore_past_lower_comparison (n:=n) μ s β t s hβ ht κ hκ hiκ hκpos hnormal q hSupport)
  exact h.trans (mul_le_mul_of_nonneg_left
    (vectorCenteredKernelScore_conditional_square_variance hn μ s β t hβ ht hs hμ hmin κ hκ hκpos hL hnormal q).1
    (by norm_num))

end QuantitativeFollowup
