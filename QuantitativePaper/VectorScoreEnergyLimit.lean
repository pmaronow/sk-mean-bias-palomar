module
public import QuantitativePaper.VectorFiniteScoreBudget

@[expose] public section

/-! Dominated passage of the genuine finite posterior energy budgets. The
root atom bounds every reciprocal CDF, including at discontinuities. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem parisiCDF_floor_at_overlap (μ : Paper.ParisiMeasure) (a : ℝ)
    (hμ : μ∈scalarFloor a) (q : Paper.Overlap) : a≤Paper.parisiCDF μ q := by
  have h:=(mem_scalarFloor_iff a μ).mp hμ
  rw [zeroMass_eq_parisiCDF_zero] at h
  exact h.trans (Paper.parisiCDF_monotone μ q.property.1)

theorem vectorDyadicNodeMass_floor (μ : Paper.ParisiMeasure) (a : ℝ)
    (hμ : μ∈scalarFloor a) (q : Paper.Overlap) (j : ℕ) : a≤vectorDyadicNodeMass μ q j := by
  rw [vectorDyadicNodeMass_eq_CDF]
  exact parisiCDF_floor_at_overlap μ a hμ _

theorem measurable_vectorDyadicHessianEnergyExpectation (μ : Paper.ParisiMeasure)
    (a β t : ℝ) (ht : t≤1) (j : ℕ) :
    Measurable (fun q : Paper.Overlap=>∫sample : VectorDisorderBrownianSample n,
      vectorDyadicMovingHessianEnergy μ β t ht q j sample
        ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) := by
  letI:=vectorFiniteDisorderTilt_probability (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a
  exact (measurable_uncurry_vectorDyadicMovingHessianEnergy (n:=n) μ β t ht j).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

theorem vectorDyadicHessianEnergyExpectation_nonneg_le (μ : Paper.ParisiMeasure)
    (a β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (j : ℕ) :
    0≤(∫sample : VectorDisorderBrownianSample n,vectorDyadicMovingHessianEnergy μ β t ht q j sample
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) ∧
    (∫sample : VectorDisorderBrownianSample n,vectorDyadicMovingHessianEnergy μ β t ht q j sample
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)≤(n : ℝ)^3 := by
  letI:=vectorFiniteDisorderTilt_probability (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a
  have hi : Integrable (vectorDyadicMovingHessianEnergy (n:=n) μ β t ht q j)
      (vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) :=
    (integrable_const ((n : ℝ)^3)).mono'
      (measurable_vectorDyadicMovingHessianEnergy μ β t ht q j).aestronglyMeasurable
      (.of_forall fun sample=>by
        rw [Real.norm_of_nonneg (vectorDyadicMovingHessianEnergy_nonneg_le μ β t ht q j sample).1]
        exact (vectorDyadicMovingHessianEnergy_nonneg_le μ β t ht q j sample).2)
  refine ⟨integral_nonneg fun sample=>(vectorDyadicMovingHessianEnergy_nonneg_le μ β t ht q j sample).1,?_⟩
  have h:=integral_mono hi (integrable_const ((n : ℝ)^3)) fun sample=>
    (vectorDyadicMovingHessianEnergy_nonneg_le μ β t ht q j sample).2
  simpa only [integral_const,probReal_univ,one_smul] using h

def vectorMeasureScoreEnergyBudget (μ : Paper.ParisiMeasure) (a β t : ℝ) (ht : t≤1)
    (κ : Paper.Overlap→ℝ) : ℝ :=
  ∫q,κ q^2*((∫sample : VectorDisorderBrownianSample n,vectorMeasureHessianEnergy μ β t ht q sample
    ∂vectorMeasureDisorderTilt μ β t a)/Paper.parisiCDF μ q) ∂parisiFreeMeasure μ a

theorem tendsto_vectorDyadicScoreEnergyBudget (μ : Paper.ParisiMeasure) (a β t : ℝ)
    (ht : t≤1) (ha : 0<a) (hμ : μ∈scalarFloor a) (κ : Paper.Overlap→ℝ)
    (hκ : Continuous κ) (K : ℝ) (hK : 0≤K) (hB : ∀q,|κ q|≤K) :
    Tendsto (vectorDyadicScoreEnergyBudget (n:=n) μ a β t ht κ) atTop
      (𝓝 (vectorMeasureScoreEnergyBudget (n:=n) μ a β t ht κ)) := by
  unfold vectorDyadicScoreEnergyBudget vectorMeasureScoreEnergyBudget
  apply tendsto_integral_of_dominated_convergence (fun _=>K^2*((n : ℝ)^3/a))
  · intro j
    have hm : Measurable (vectorDyadicNodeMass μ · j) := by
      have he:=funext fun q=>vectorDyadicNodeMass_eq_CDF μ q j
      rw [he]
      exact (Paper.parisiCDF_monotone μ).measurable.comp
        (measurable_subtype_coe.comp (Paper.measurable_parisiGridRound _))
    exact (((hκ.measurable.comp (Paper.measurable_parisiGridRound _)).pow_const 2).mul
      ((measurable_vectorDyadicHessianEnergyExpectation μ a β t ht j).div hm)).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact .of_forall fun q=>by
      have hf:=(vectorDyadicHessianEnergyExpectation_nonneg_le (n:=n) μ a β t ht q j)
      have hm:=vectorDyadicNodeMass_floor μ a hμ q j
      have hm0:=ha.trans_le hm
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (div_nonneg hf.1 hm0.le))]
      have hsq : κ (Paper.parisiGridRound (vectorDyadicIndex j) q)^2≤K^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀
          (abs_nonneg (κ (Paper.parisiGridRound (vectorDyadicIndex j) q))) (hB _) 2
      exact mul_le_mul hsq (div_le_div₀ (by positivity) hf.2 ha hm)
        (div_nonneg hf.1 hm0.le) (sq_nonneg K)
  · exact .of_forall fun q=>
      (((hκ.tendsto q).comp ((Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex)).pow 2).mul
        ((tendsto_integral_vectorDyadicMovingHessianEnergy (n:=n) μ β t a ht q).div
          (tendsto_vectorDyadicNodeMass μ q)
          (ne_of_gt (ha.trans_le (parisiCDF_floor_at_overlap μ a hμ q))))

theorem vectorMeasureWeightedOverlapScore_variance_le_energy (hn : 0<n)
    (μ : Paper.ParisiMeasure) (a β t : ℝ) (hβ : β≠0) (ht : t<1)
    (ha : a∈Ioc (0 : ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hκ : Continuous κ) (K : ℝ) (hK : 0≤K) (hB : ∀q,|κ q|≤K) :
    variance (vectorMeasureWeightedOverlapScore (n:=n) μ a β t ht.le κ)
      (vectorMeasureSpinPathLaw μ β t a ht.le)≤
      vectorMeasureScoreEnergyBudget (n:=n) μ a β t ht.le κ/(n : ℝ)^2 := by
  apply le_of_tendsto_of_tendsto
    (tendsto_variance_vectorDyadicWeightedOverlapScore μ a β t ht.le ⟨ha.1.le,ha.2⟩ κ hκ K hK hB)
    ((tendsto_vectorDyadicScoreEnergyBudget μ a β t ht.le ha.1 hμ κ hκ K hK hB).div_const _)
  exact .of_forall fun j=>vectorDyadicWeightedOverlapScore_variance_le_budget hn μ a β t hβ ht ha hμ κ hκ.measurable j

end QuantitativePaper
