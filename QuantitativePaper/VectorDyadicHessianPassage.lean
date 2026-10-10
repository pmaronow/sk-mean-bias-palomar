module
public import QuantitativePaper.VectorDyadicJetConvergence
public import QuantitativePaper.VectorMeasureSpatialContinuity
public import QuantitativePaper.VectorNodeGradient
public import FourPapersCommon.ParisiCDFRight

@[expose] public section

/-! The actual finite Hessian quadratic forms at upward nodes converge
along the genuine finite diffusions. Their masses converge to the right
CDF, including every atom. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def vectorDyadicNodeMass (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (j : ℕ) : ℝ :=
  observableDepthMass (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    (vectorDyadicIndex j+3-vectorDyadicTimeIndex q j)

theorem vectorDyadicNodeMass_eq_CDF (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (j : ℕ) :
    vectorDyadicNodeMass μ q j=Paper.parisiCDF μ (Paper.parisiGridRound (vectorDyadicIndex j) q) := by
  have hi0 : 0<vectorDyadicTimeIndex q j := by unfold vectorDyadicTimeIndex;omega
  have hi : vectorDyadicTimeIndex q j≤vectorDyadicIndex j+2 := vectorDyadicTimeIndex_le q j
  have hj : vectorDyadicIndex j+3-vectorDyadicTimeIndex q j≠0 := by omega
  have he : vectorDyadicIndex j+3-(vectorDyadicIndex j+3-vectorDyadicTimeIndex q j)=
      vectorDyadicTimeIndex q j := by omega
  unfold vectorDyadicNodeMass observableDepthMass
  rw [ite_eq_right hj]
  change (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).m
      (vectorDyadicIndex j+3-(vectorDyadicIndex j+3-vectorDyadicTimeIndex q j))=_
  rw [he]
  change Paper.parisiGridSchemeMass μ (vectorDyadicIndex j) (vectorDyadicTimeIndex q j)=_
  rw [Paper.parisiGridSchemeMass,ite_eq_right hi0.ne']
  change Paper.parisiCDF (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (vectorDyadicTimeIndex q j))=_
  rw [vectorDyadicTimeIndex_node,parisiCDF_grid_at_round]

theorem tendsto_vectorDyadicNodeMass (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Tendsto (vectorDyadicNodeMass μ q) atTop (𝓝 (Paper.parisiCDF μ q)) := by
  have he:=(tendsto_parisiCDF_grid_at_round μ q).comp tendsto_vectorDyadicIndex
  convert he using 1
  funext j
  exact (vectorDyadicNodeMass_eq_CDF μ q j).trans
    (parisiCDF_grid_at_round μ (vectorDyadicIndex j) q).symm

theorem vectorDyadicTailPotential_at_upward_node (μ : Paper.ParisiMeasure) (β t : ℝ)
    (q : Paper.Overlap) (j : ℕ) (p : Couplings n×ℝ) :
    vectorDyadicTailPotential μ β t (Paper.parisiGridRound (vectorDyadicIndex j) q) j p=
      vectorRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t p
        (vectorDyadicIndex j+3-vectorDyadicTimeIndex q j) := by
  unfold vectorDyadicTailPotential
  rw [←vectorDyadicTimeIndex_node μ q j]
  exact vectorTailRecursion_at_node _ β t _ ((vectorDyadicTimeIndex_le q j).trans (by omega)) p

def vectorDyadicHessianQuadratic (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (w : Field n) (sample : VectorDisorderBrownianSample n) : ℝ :=
  inner ℝ w (vectorFieldHessian (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t sample.1
    (vectorDyadicIndex j+3-vectorDyadicTimeIndex q j)
    (vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample) w)

def vectorMeasureHessianQuadratic (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (w : Field n) (sample : VectorDisorderBrownianSample n) : ℝ :=
  inner ℝ w (vectorMeasureHessian μ β t q sample.1
    (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample) w)

theorem continuous_vectorFieldHessian_quadratic {k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (j : ℕ) (w : Field n) :
    Continuous (fun p : VectorParameter n=>inner ℝ w (vectorFieldHessian s β t p.1 j p.2 w)) := by
  let F:=fun p : VectorParameter n=>vectorRecursion s β t p.1 j p.2
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) :=
    (contDiff_vectorRecursion_joint s β t j).fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ F)) := h1.fderiv_right (by simp)
  have he:=funext (fun p=>vectorFieldHessian_quadratic_eq_joint s β t p j w)
  rw [he]
  exact (h2.continuous.clm_apply continuous_const).clm_apply continuous_const

theorem measurable_vectorDyadicHessianQuadratic (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n) :
    Measurable (vectorDyadicHessianQuadratic μ β t ht q j w) := by
  have hm:= (continuous_vectorFieldHessian_quadratic
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
      (vectorDyadicIndex j+3-vectorDyadicTimeIndex q j) w).measurable.comp
      (measurable_vectorFiniteJointState
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht (vectorDyadicTime q j))
  exact hm

theorem vectorDyadicHessianQuadratic_bound (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n) (sample : VectorDisorderBrownianSample n) :
    |vectorDyadicHessianQuadratic μ β t ht q j w sample|≤(n : ℝ)*‖w‖^2 := by
  unfold vectorDyadicHessianQuadratic
  rw [real_inner_comm]
  exact vectorFieldHessian_quadratic_bound _ β t _ _ _ w

theorem tendsto_vectorDyadicHessianQuadratic (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (w : Field n) (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorDyadicHessianQuadratic μ β t ht q j w sample) atTop
      (𝓝 (vectorMeasureHessianQuadratic μ β t ht q w sample)) := by
  have hX:=tendsto_vectorDyadicState_at_moving_time μ β t ht (q : ℝ).toNNReal
    (vectorDyadicTime q) (vectorDyadicTime_le_one q) (tendsto_vectorDyadicTime q) sample
  have hq:=(Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex
  have hp : Tendsto (fun _ : ℕ=>sample.1) atTop (𝓝 sample.1) := tendsto_const_nhds
  have hz:=hq.prodMk_nhds (hp.prodMk_nhds hX)
  have hj:=(tendstoUniformly_vectorDyadicTailPotential_jets (n:=n) μ β t ht 2).tendsto_comp
    (continuous_vectorMeasureTailPotential_jet μ β t ht 2).continuousAt hz
  have hEval : Continuous (fun H : ContinuousMultilinearMap ℝ (fun _ : Fin 2=>Field n) ℝ=>
      H (fun _=>w)) := continuous_eval_const _
  have he:=(hEval.tendsto _).comp hj
  have hD (j : ℕ) : vectorDyadicHessianQuadratic μ β t ht q j w sample=
      iteratedFDeriv ℝ 2
        (vectorDyadicTailPotential μ β t (Paper.parisiGridRound (vectorDyadicIndex j) q) j sample.1)
        (vectorDyadicState μ β t ht j (vectorDyadicTime q j) sample) (fun _=>w) := by
    rw [vectorDyadicTailPotential_at_upward_node,iteratedFDeriv_two_apply]
    unfold vectorDyadicHessianQuadratic
    rw [real_inner_comm,vectorFieldHessian,inner_hessianOperator]
  have hM : vectorMeasureHessianQuadratic μ β t ht q w sample=
      iteratedFDeriv ℝ 2 (vectorMeasureTailPotential μ β t q sample.1)
        (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample) (fun _=>w) := by
    rw [iteratedFDeriv_two_apply]
    unfold vectorMeasureHessianQuadratic vectorMeasureHessian
    rw [real_inner_comm,inner_hessianOperator]
  simp_rw [hD]
  rw [hM]
  exact he

end QuantitativePaper
