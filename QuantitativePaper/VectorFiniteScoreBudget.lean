module
public import QuantitativePaper.VectorPosteriorHessianSquare
public import QuantitativePaper.VectorFiniteScoreIntegral
public import QuantitativePaper.VectorFiniteStateExpectationTransport
public import QuantitativePaper.VectorDyadicMovingHessianEnergy

@[expose] public section

/-! The finite posterior estimate transported to the actual diffusion and
written as an integral on the original free overlap measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorFiniteStateHessianEnergy (s : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : ℝ :=
  vectorHessianHilbertSquare (vectorFiniteTailHessian s β t q sample.1
    (vectorFiniteState s β t ht (q : ℝ).toNNReal sample))

theorem measurable_uncurry_vectorFiniteStateHessianEnergy (s : RSBScheme k)
    (β t : ℝ) (ht : t≤1) :
    Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      vectorFiniteStateHessianEnergy s β t ht z.1 z.2) := by
  have hc : Measurable (fun q : Paper.Overlap=>(q : ℝ).toNNReal) :=
    continuous_real_toNNReal.measurable.comp measurable_subtype_coe
  have hX := (measurable_uncurry_vectorFiniteState (n:=n) s β t ht).comp
    ((hc.comp measurable_fst).prodMk measurable_snd)
  have hz : Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      (z.1,(z.2.1,vectorFiniteState s β t ht (z.1 : ℝ).toNNReal z.2))) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hX)
  unfold vectorFiniteStateHessianEnergy vectorHessianHilbertSquare
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.measurable_sum _ fun j _=>Finset.measurable_sum _ fun l _=>
    ((measurable_vectorFiniteTailHessian_entry s β t j l).comp hz).pow_const 2

theorem vectorFiniteStateHessianEnergy_nonneg_le (s : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    0≤vectorFiniteStateHessianEnergy s β t ht q sample ∧
      vectorFiniteStateHessianEnergy s β t ht q sample≤(n : ℝ)^3 :=
  ⟨vectorHessianHilbertSquare_nonneg _,vectorHessianHilbertSquare_le
    (norm_vectorFiniteTailHessian_le s β t q sample.1 _)⟩

theorem vectorFiniteStateHessianEnergy_at_node (s : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (i : ℕ) (hi : i≤k+2) (sample : VectorDisorderBrownianSample n) :
    vectorFiniteStateHessianEnergy s β t ht ⟨s.q i,s.q_nonneg hi,s.q_le_one hi⟩ sample=
      vectorHessianHilbertSquare (vectorFieldHessian s β t sample.1 (k+2-i)
        (vectorFiniteState s β t ht (s.q i).toNNReal sample)) := by
  unfold vectorFiniteStateHessianEnergy vectorFiniteTailHessian
  rw [vectorTailRecursion_at_node s β t i hi]
  rfl

theorem integral_vectorEuclideanHessianSquare_eq_finite (s : RSBScheme k)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+2) :
    (∫p : VectorGaussianSpace n k×Configuration n,
      vectorHessianHilbertSquare (vectorFieldHessian s β t
        (vectorEuclideanStateLinear s β t i p.1).1 (k+2-i)
        (vectorEuclideanStateLinear s β t i p.1).2)
      ∂vectorEuclideanJointLaw s β t a)=
      ∫sample : VectorDisorderBrownianSample n,vectorFiniteStateHessianEnergy s β t ht.le
        ⟨s.q i,s.q_nonneg hi,s.q_le_one hi⟩ sample ∂vectorFiniteDisorderTilt s β t a := by
  rw [integral_vectorEuclidean_state_eq_finite s β t a hβ ht i hi _
    (continuous_vectorFieldHessianHilbertSquare s β t i).measurable ((n : ℝ)^3)
    (fun x : VectorState n=>by
      rw [Real.norm_of_nonneg (vectorHessianHilbertSquare_nonneg _)]
      exact vectorHessianHilbertSquare_le (norm_vectorFieldHessian_le s β t _ _ _))]
  apply integral_congr_ae
  exact .of_forall fun sample : VectorDisorderBrownianSample n=>(vectorFiniteStateHessianEnergy_at_node s β t ht.le i hi sample).symm

theorem measurable_vectorFiniteHessianEnergyExpectation (s : RSBScheme k)
    (β t a : ℝ) (ht : t≤1) :
    Measurable (fun q : Paper.Overlap=>∫sample,vectorFiniteStateHessianEnergy (n:=n) s β t ht q sample
      ∂vectorFiniteDisorderTilt s β t a) := by
  letI:=vectorFiniteDisorderTilt_probability (n:=n) s β t a
  exact (measurable_uncurry_vectorFiniteStateHessianEnergy (n:=n) s β t ht).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

theorem vectorGridFeatureMass_eq_cdf (μ : Paper.ParisiMeasure) (j : ℕ)
    (i : vectorPosteriorFeatureIndex (vectorDyadicIndex j+1)) :
    observableDepthMass (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (vectorDyadicIndex j+3-vectorPosteriorFeatureTime i)=
      Paper.parisiCDF (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (vectorProfileAtom (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) i) := by
  have hi : vectorPosteriorFeatureTime i≤vectorDyadicIndex j+2 := by
    cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega
  have hi0 : 1≤vectorPosteriorFeatureTime i := by
    cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega
  have he : vectorDyadicIndex j+3-(vectorDyadicIndex j+3-vectorPosteriorFeatureTime i)=
      vectorPosteriorFeatureTime i := by omega
  unfold observableDepthMass
  rw [ite_eq_right (by omega)]
  change (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).m
    (vectorDyadicIndex j+3-(vectorDyadicIndex j+3-vectorPosteriorFeatureTime i))=_
  rw [he]
  change Paper.parisiGridSchemeMass μ (vectorDyadicIndex j) (vectorPosteriorFeatureTime i)=_
  rw [Paper.parisiGridSchemeMass,ite_eq_right (by omega)]
  rfl

def vectorDyadicScoreEnergyBudget (μ : Paper.ParisiMeasure) (a β t : ℝ) (ht : t≤1)
    (κ : Paper.Overlap→ℝ) (j : ℕ) : ℝ :=
  ∫q,κ (Paper.parisiGridRound (vectorDyadicIndex j) q)^2*
    ((∫sample : VectorDisorderBrownianSample n,vectorDyadicMovingHessianEnergy μ β t ht q j sample
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)/
        vectorDyadicNodeMass μ q j) ∂parisiFreeMeasure μ a

theorem vectorDyadicScoreEnergyBudget_eq_feature_sum (μ : Paper.ParisiMeasure)
    (a β t : ℝ) (hβ : β≠0) (ht : t<1) (ha : a∈Icc (0 : ℝ) 1)
    (hμ : μ∈scalarFloor a) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (j : ℕ) :
    vectorDyadicScoreEnergyBudget (n:=n) μ a β t ht.le κ j=
      ∑i,vectorPosteriorFeatureWeight (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a i*
        κ (vectorProfileAtom (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) i)^2*
        ((∫p : VectorGaussianSpace n (vectorDyadicIndex j+1)×Configuration n,
          vectorHessianHilbertSquare (vectorFieldHessian (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
            β t (vectorEuclideanStateLinear (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
              β t (vectorPosteriorFeatureTime i) p.1).1
            (vectorDyadicIndex j+3-vectorPosteriorFeatureTime i)
            (vectorEuclideanStateLinear (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
              β t (vectorPosteriorFeatureTime i) p.1).2)
          ∂vectorEuclideanJointLaw (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)/
            observableDepthMass (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
              (vectorDyadicIndex j+3-vectorPosteriorFeatureTime i)) := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let F : Paper.Overlap→ℝ:=fun q=>κ q^2*((∫sample,vectorFiniteStateHessianEnergy (n:=n) s β t ht.le q sample
    ∂vectorFiniteDisorderTilt s β t a)/Paper.parisiCDF (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) q)
  have hF : Measurable F:=(hκ.pow_const 2).mul
    ((measurable_vectorFiniteHessianEnergyExpectation s β t a ht.le).div
      ((Paper.parisiCDF_monotone _).measurable.comp measurable_subtype_coe))
  have he : vectorDyadicScoreEnergyBudget (n:=n) μ a β t ht.le κ j=
      ∫q,F q ∂parisiFreeMeasure (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) a := by
    rw [integral_parisiFreeMeasure_grid μ a ha hμ _ F hF]
    unfold vectorDyadicScoreEnergyBudget
    apply integral_congr_ae
    exact .of_forall fun q=>by
      dsimp only [F]
      rw [vectorDyadicNodeMass_eq_CDF,parisiCDF_grid_at_round]
      rfl
  rw [he,←FRSB.parisiSchemeMeasure_grid_eq,
    ←vectorProfileFreeMeasure_eq_actual_free s a ha.1 (parisiGridRSBScheme_floor μ a hμ _)
      (Paper.parisiGridSchemeOverlap_one _),
    integral_vectorProfileFreeMeasure s a (parisiGridRSBScheme_floor μ a hμ _)]
  apply Finset.sum_congr rfl
  intro i _
  have hi : vectorPosteriorFeatureTime i≤(vectorDyadicIndex j+1)+2 := by
    cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega
  dsimp only [F]
  rw [←vectorGridFeatureMass_eq_cdf μ j i]
  have hE:=integral_vectorEuclideanHessianSquare_eq_finite (n:=n) s β t a hβ ht _ hi
  dsimp only [vectorProfileAtom] at *
  rw [←hE]
  exact (mul_assoc _ _ _).symm

theorem vectorDyadicWeightedOverlapScore_variance_le_budget (hn : 0<n)
    (μ : Paper.ParisiMeasure) (a β t : ℝ) (hβ : β≠0) (ht : t<1)
    (ha : a∈Ioc (0 : ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (j : ℕ) :
    variance (vectorDyadicWeightedOverlapScore (n:=n) μ a β t ht.le κ j)
      (vectorFiniteSpinPathLaw (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ht.le)≤
      vectorDyadicScoreEnergyBudget (n:=n) μ a β t ht.le κ j/(n : ℝ)^2 := by
  rw [variance_vectorDyadicWeightedOverlapScore_eq_posterior μ a β t hβ ht ⟨ha.1.le,ha.2⟩ hμ κ hκ j,
    vectorDyadicScoreEnergyBudget_eq_feature_sum μ a β t hβ ht ⟨ha.1.le,ha.2⟩ hμ κ hκ j]
  have h:=vectorJoint_weightedOverlap_variance_le_hessian_square hn
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a hβ ht
    (Paper.parisiGridSchemeOverlap_one _) ha.1 (parisiGridRSBScheme_floor μ a hμ _)
      (fun q=>κ (projIcc (0 : ℝ) 1 zero_le_one q))
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  unfold vectorPosteriorFeatureKernel
  change κ (vectorProfileAtom _ i)^2=κ (projIcc (0 : ℝ) 1 zero_le_one
    (vectorProfileAtom (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) i : ℝ))^2
  rw [projIcc_of_mem zero_le_one (vectorProfileAtom _ i).property]

end QuantitativePaper
