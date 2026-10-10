module
public import QuantitativePaper.VectorDyadicHessianPassage
public import QuantitativePaper.VectorDyadicFixedEnergyMeasurable
public import QuantitativePaper.VectorDyadicTiltConvergence

@[expose] public section

/-! Literal Hessian Hilbert-square convergence at upward profile nodes along
the actual finite diffusions, with their actual fractional tilts. Atoms are
retained by the upward-node convention. -/
noncomputable section
open MeasureTheory Set Filter FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def vectorDyadicMovingHessian (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) : Field n→L[ℝ]Field n :=
  vectorFiniteTailHessian (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
    (Paper.parisiGridRound (vectorDyadicIndex j) q) sample.1
    (vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample)

theorem vectorDyadicMovingHessian_eq_node (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) :
    vectorDyadicMovingHessian μ β t ht q j sample=
      vectorFieldHessian (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t sample.1
        (vectorDyadicIndex j+3-vectorDyadicTimeIndex q j)
        (vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample) := by
  change hessianOperator
    (vectorDyadicTailPotential μ β t (Paper.parisiGridRound (vectorDyadicIndex j) q) j sample.1) _=_
  rw [vectorDyadicTailPotential_at_upward_node]
  rfl

theorem tendsto_vectorDyadicMovingHessian (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorDyadicMovingHessian μ β t ht q j sample) atTop
      (𝓝 (vectorMeasureHessian μ β t q sample.1
        (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))) := by
  let z : ℕ→Paper.Overlap×VectorParameter n := fun j=>
    (Paper.parisiGridRound (vectorDyadicIndex j) q,
      (sample.1,vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample))
  let z0 : Paper.Overlap×VectorParameter n :=
    (q,(sample.1,vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))
  have hX:=tendsto_vectorDyadicState_at_moving_time μ β t ht (q : ℝ).toNNReal
    (vectorDyadicTime q) (vectorDyadicTime_le_one q) (tendsto_vectorDyadicTime q) sample
  have hq:=(Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex
  have hz : Tendsto z atTop (𝓝 z0):=hq.prodMk_nhds (tendsto_const_nhds.prodMk_nhds hX)
  have hHm:=((continuous_vectorMeasureHessian (n:=n) μ β t ht).tendsto z0).comp hz
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hhalf : 0<ε/2:=by positivity
  have hu:=(Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_vectorDyadicTailPotential_jets (n:=n) μ β t ht 2)) (ε/2) hhalf
  have hm:=(Metric.tendsto_atTop.mp hHm) (ε/2) hhalf
  obtain ⟨N,hN⟩:=eventually_atTop.mp hu
  obtain ⟨M,hM⟩:=hm
  refine ⟨max N M,?_⟩
  intro j hj
  have hclose:=hN j ((le_max_left N M).trans hj) (z j)
  have hd : dist (vectorDyadicMovingHessian μ β t ht q j sample)
      (vectorMeasureHessian μ β t (z j).1 (z j).2.1 (z j).2.2)<ε/2 := by
    rw [dist_eq_norm]
    change ‖hessianOperator (vectorDyadicTailPotential μ β t (z j).1 j (z j).2.1) (z j).2.2-
      hessianOperator (vectorMeasureTailPotential μ β t (z j).1 (z j).2.1) (z j).2.2‖<ε/2
    rw [norm_hessianOperator_sub_eq_secondJet _ _
      (contDiff_vectorDyadicTailPotential μ β t (z j).1 j (z j).2.1)
      (contDiff_vectorMeasureTailPotential μ β t ht (z j).1 (z j).2.1) (z j).2.2]
    simpa only [dist_eq_norm,norm_sub_rev] using hclose
  have hmj:=hM j ((le_max_right N M).trans hj)
  dsimp only [Function.comp_apply,z0] at hmj
  exact (dist_triangle _ (vectorMeasureHessian μ β t (z j).1 (z j).2.1 (z j).2.2) _).trans_lt
    (by linarith only [hd,hmj])

def vectorDyadicMovingHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) : ℝ :=
  vectorHessianHilbertSquare (vectorDyadicMovingHessian μ β t ht q j sample)

theorem vectorDyadicMovingHessianEnergy_nonneg_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (sample : VectorDisorderBrownianSample n) :
    0≤vectorDyadicMovingHessianEnergy μ β t ht q j sample ∧
      vectorDyadicMovingHessianEnergy μ β t ht q j sample≤(n : ℝ)^3 :=
  ⟨vectorHessianHilbertSquare_nonneg _,vectorHessianHilbertSquare_le
    (norm_vectorFiniteTailHessian_le _ β t _ sample.1 _)⟩

theorem tendsto_vectorDyadicMovingHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorDyadicMovingHessianEnergy μ β t ht q j sample) atTop
      (𝓝 (vectorMeasureHessianEnergy μ β t ht q sample)) :=
  (continuous_vectorHessianHilbertSquare.tendsto _).comp
    (tendsto_vectorDyadicMovingHessian μ β t ht q sample)

theorem measurable_uncurry_vectorDyadicMovingHessianEnergy (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (j : ℕ) :
    Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      vectorDyadicMovingHessianEnergy μ β t ht z.1 j z.2) := by
  have hc : Measurable (fun q : Paper.Overlap=>vectorDyadicTime q j) := by
    unfold vectorDyadicTime
    exact continuous_real_toNNReal.measurable.comp
      (measurable_subtype_coe.comp (Paper.measurable_parisiGridRound _))
  have hX := (measurable_uncurry_vectorFiniteState (n:=n)
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht).comp
      ((hc.comp measurable_fst).prodMk measurable_snd)
  let insert : Paper.Overlap×VectorDisorderBrownianSample n→Paper.Overlap×VectorParameter n:=fun z=>
    (Paper.parisiGridRound (vectorDyadicIndex j) z.1,
      (z.2.1,vectorDyadicState μ β t ht j (vectorDyadicTime z.1 j) z.2))
  have hIns : Measurable insert:=((Paper.measurable_parisiGridRound _).comp measurable_fst).prodMk
    ((measurable_fst.comp measurable_snd).prodMk hX)
  unfold vectorDyadicMovingHessianEnergy vectorHessianHilbertSquare
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.measurable_sum
  intro r _
  apply Finset.measurable_sum
  intro l _
  exact ((measurable_vectorFiniteTailHessian_entry
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t r l).comp hIns).pow_const 2

theorem measurable_vectorDyadicMovingHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) :
    Measurable (vectorDyadicMovingHessianEnergy (n:=n) μ β t ht q j) := by
  exact Measurable.of_uncurry_left
    (f := fun q sample=>vectorDyadicMovingHessianEnergy (n:=n) μ β t ht q j sample) (x:=q)
    (measurable_uncurry_vectorDyadicMovingHessianEnergy μ β t ht j)

theorem tendsto_integral_vectorDyadicMovingHessianEnergy (μ : Paper.ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    Tendsto (fun j=>∫sample : VectorDisorderBrownianSample n,vectorDyadicMovingHessianEnergy μ β t ht q j sample
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t outer) atTop
      (𝓝 (∫sample : VectorDisorderBrownianSample n,vectorMeasureHessianEnergy μ β t ht q sample
        ∂vectorMeasureDisorderTilt μ β t outer)) := by
  apply tendsto_integral_vectorDyadicTilt_bounded μ β t outer ht _ _ ((n : ℝ)^3) (by positivity)
    (fun j=>measurable_vectorDyadicMovingHessianEnergy μ β t ht q j) _
    (.of_forall fun sample=>tendsto_vectorDyadicMovingHessianEnergy μ β t ht q sample)
  intro j sample
  rw [Real.norm_of_nonneg (vectorDyadicMovingHessianEnergy_nonneg_le μ β t ht q j sample).1]
  exact (vectorDyadicMovingHessianEnergy_nonneg_le μ β t ht q j sample).2

end QuantitativePaper
