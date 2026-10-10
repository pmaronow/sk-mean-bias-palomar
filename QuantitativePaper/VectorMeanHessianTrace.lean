module
public import QuantitativePaper.ResponseModel
public import QuantitativePaper.VectorMeasureHessianProcess
public import QuantitativePaper.VectorDyadicFixedEnergyMeasurable

@[expose] public section

/-! The actual normalized Hessian trace and its genuine dyadic approximation.
Every expectation is under the constructed fractional-tilt Wiener law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup Paper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def vectorMeanHessianTrace (μ : ParisiMeasure) (β t outer : ℝ) (ht : t≤1) (q : Overlap) : ℝ :=
  (∑l : Fin n,∫sample,(vectorMeasureHessianProcess μ β t ht q sample (EuclideanSpace.single l 1)) l
    ∂vectorMeasureDisorderTilt μ β t outer)/(n : ℝ)

theorem norm_operator_diagonal_le (H : Field n→L[ℝ]Field n) (l : Fin n) :
    ‖(H (EuclideanSpace.single l 1)) l‖≤‖H‖ := by
  exact (PiLp.norm_apply_le _ l).trans (by
    simpa only [PiLp.norm_single,norm_one,mul_one] using H.le_opNorm (EuclideanSpace.single l 1))

theorem integrable_vectorMeasureHessian_diagonal (μ : ParisiMeasure) (β t outer : ℝ)
    (ht : t≤1) (q : Overlap) (l : Fin n) :
    Integrable (fun sample=>(vectorMeasureHessianProcess μ β t ht q sample (EuclideanSpace.single l 1)) l)
      (vectorMeasureDisorderTilt μ β t outer) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  have hm:=((show Measurable (fun H : Field n→L[ℝ]Field n=>(H (EuclideanSpace.single l 1)) l) from by fun_prop).comp
    ((adapted_vectorMeasureHessianProcess μ β t ht q).mono ((vectorBrownianFiltration n).le _) le_rfl))
  exact Integrable.of_bound hm.aestronglyMeasurable (n : ℝ) (.of_forall fun sample=>
    (norm_operator_diagonal_le _ l).trans (norm_vectorMeasureHessianProcess_le μ β t ht q sample))

theorem continuous_vectorMeanHessianTrace (μ : ParisiMeasure) (β t outer : ℝ) (ht : t≤1) :
    Continuous (vectorMeanHessianTrace (n:=n) μ β t outer ht) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  unfold vectorMeanHessianTrace
  apply Continuous.div_const
  apply continuous_finsetSum
  intro l _
  apply continuous_of_dominated (bound:=fun _=>(n : ℝ))
  · intro q
    exact (integrable_vectorMeasureHessian_diagonal μ β t outer ht q l).aestronglyMeasurable
  · intro q
    exact .of_forall fun sample=>(norm_operator_diagonal_le _ l).trans
      (norm_vectorMeasureHessianProcess_le μ β t ht q sample)
  · exact integrable_const _
  · exact .of_forall fun sample=>(EuclideanSpace.proj l).continuous.comp
      ((continuous_vectorMeasureHessianProcess_path μ β t ht sample).clm_apply
        (continuous_const : Continuous (fun _ : Overlap=>EuclideanSpace.single l (1:ℝ))))

theorem responseMeanHessian_eq_meanTrace (μ : ParisiMeasure) (β t lam : ℝ) (ht : t≤1) (q : Overlap) :
    responseMeanHessian (n:=n) μ β t lam ht q=
      β*vectorMeanHessianTrace (n:=n) μ β t (lam/β) ht q := by
  have hs:=integral_finsetSum (Finset.univ : Finset (Fin n))
    (fun l _=>integrable_vectorMeasureHessian_diagonal (n:=n) μ β t (lam/β) ht q l)
  unfold vectorMeasureHessianProcess at hs
  unfold responseMeanHessian responseHessianTrace Matrix.trace Matrix.diag vectorMeasureHessianMatrix
    vectorMeanHessianTrace vectorMeasureHessianProcess
  rw [integral_const_mul,hs]
  ring

theorem tendsto_vectorFiniteTailHessian_dyadic (μ : ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Overlap) (p : Couplings n×ℝ) (x : Field n) :
    Tendsto (fun j=>vectorFiniteTailHessian (parisiGridRSBScheme μ (vectorDyadicIndex j)) β t q p x)
      atTop (𝓝 (vectorMeasureHessian μ β t q p x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (j : ℕ) : ‖vectorFiniteTailHessian (parisiGridRSBScheme μ (vectorDyadicIndex j)) β t q p x-
      vectorMeasureHessian μ β t q p x‖=
      ‖iteratedFDeriv ℝ 2 (vectorDyadicTailPotential μ β t q j p) x-
        iteratedFDeriv ℝ 2 (vectorMeasureTailPotential μ β t q p) x‖:=
    norm_hessianOperator_sub_eq_secondJet _ _ (contDiff_vectorDyadicTailPotential μ β t q j p)
      (contDiff_vectorMeasureTailPotential μ β t ht q p) x
  simp_rw [he]
  have h:=((tendstoUniformly_vectorDyadicTailPotential_jets (n:=n) μ β t ht 2).tendsto_at (q,(p,x))).sub_const
    (iteratedFDeriv ℝ 2 (vectorMeasureTailPotential μ β t q p) x) |>.norm
  simpa only [sub_self,norm_zero] using h

theorem tendsto_expected_vectorFiniteTailHessian_diagonal (μ : ParisiMeasure) (β t outer : ℝ)
    (ht : t≤1) (q : Overlap) (l : Fin n) :
    Tendsto (fun j=>∫sample,(vectorFiniteTailHessian (parisiGridRSBScheme μ (vectorDyadicIndex j))
        β t q sample.1 (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample) (EuclideanSpace.single l 1)) l
      ∂vectorMeasureDisorderTilt μ β t outer) atTop
      (𝓝 (∫sample,(vectorMeasureHessianProcess μ β t ht q sample (EuclideanSpace.single l 1)) l
        ∂vectorMeasureDisorderTilt μ β t outer)) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  have hX : Measurable (vectorMeasureState (n:=n) μ β t ht (q : ℝ).toNNReal):=
    ((stronglyAdapted_vectorMeasureState μ β t ht (q : ℝ).toNNReal).measurable).mono
      ((vectorBrownianFiltration n).le _) le_rfl
  have hmap : Measurable (fun sample : VectorDisorderBrownianSample n=>(q,(sample.1,
      vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))):=measurable_const.prodMk (measurable_fst.prodMk hX)
  apply tendsto_integral_of_dominated_convergence (bound:=fun _=>(n : ℝ))
  · intro j
    exact ((measurable_vectorFiniteTailHessian_entry _ β t l l).comp hmap).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact .of_forall fun sample=>(norm_operator_diagonal_le _ l).trans
      (norm_vectorFiniteTailHessian_le _ β t q sample.1 _)
  · exact .of_forall fun sample=>
      (show Continuous (fun H : Field n→L[ℝ]Field n=>(H (EuclideanSpace.single l 1)) l) from by fun_prop).tendsto
        (vectorMeasureHessianProcess μ β t ht q sample) |>.comp
          (tendsto_vectorFiniteTailHessian_dyadic μ β t ht q sample.1 _)

end QuantitativePaper
