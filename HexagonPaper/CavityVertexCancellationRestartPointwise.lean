module
public import HexagonPaper.CavityVertexCancellationRestartHessian
public import HexagonPaper.CavityVertexCancellation

@[expose] public section

/-! Literal node curvature and variance cancellation for every initial
field of the actual arbitrary-profile restarted diffusion. The current
atom is retained through clamped finite laws before taking genuine limits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Topology
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass SpinGlass.Targets
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

 theorem anisotropicRestartSpinSquare_current (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (i : Fin n) :
    anisotropicRestartSpinSquare D μ g q x i q=
      (anisotropicMeasureTailMagnetization D μ q
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i)^2 := by
  simp only [anisotropicRestartSpinSquare,anisotropicRestartSpinResponse,
    sub_self,Real.toNNReal_zero,anisotropicRestartPhysicalParameter,
    anisotropicRestartState_zero,anisotropicUnitInput,ContinuousLinearMap.comp_apply,
    anisotropicNoiseMap_inverseNoise,integral_const,probReal_univ,one_smul]

 theorem tendsto_cavityFinite_clamped_coordinate_square (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (x : Field n) (i : Fin n) :
    Tendsto (fun j=>cavityFiniteConditionalCoordinateSquare D
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
      (vectorDyadicIndex j+3) (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i
      (anisotropicClampOverlap q (Paper.parisiGridRound (vectorDyadicIndex j) r))) atTop
      (𝓝 (if q<r then anisotropicRestartSpinSquare D μ g q x i r else
        (anisotropicMeasureTailMagnetization D μ q
          (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i)^2)) := by
  let P:=anisotropicDisorderInjection n g+anisotropicFieldInjection n x
  have hM := (((EuclideanSpace.proj i).continuous.tendsto _).comp
    ((tendstoUniformly_anisotropicFiniteDyadicTailMagnetization D μ).tendsto_at (q,P))).pow 2
  by_cases hqr : q≤r
  · have ht:=tendsto_anisotropicVarianceRestart_node_square_le D μ i (D.variance_pos i)
      (tendsto_const_nhds (x:=D.variance i)) g q r hqr x
    have hcl j : anisotropicClampOverlap q (Paper.parisiGridRound (vectorDyadicIndex j) r)=
        Paper.parisiGridRound (vectorDyadicIndex j) r :=
      Subtype.ext (max_eq_right (hqr.trans (Paper.le_parisiGridRound _ r)))
    simp only [anisotropicReplaceVariance_self] at ht
    simp only [hcl]
    by_cases hlt : q<r
    · simpa only [ite_eq_left hlt] using ht
    · have he : r=q:=le_antisymm (le_of_not_gt hlt) hqr
      simpa only [he,ite_self,anisotropicRestartSpinSquare_current] using ht
  · have hrq : r<q:=lt_of_not_ge hqr
    have ht:=(Paper.tendsto_parisiGridRound r).comp tendsto_vectorDyadicIndex
    have he : ∀ᶠj in atTop,Paper.parisiGridRound (vectorDyadicIndex j) r≤q :=
      (ht.eventually (eventually_lt_nhds hrq)).mono fun _ h=>h.le
    have hc : (fun j=>cavityFiniteConditionalCoordinateSquare D
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        (vectorDyadicIndex j+3) P i
        (anisotropicClampOverlap q (Paper.parisiGridRound (vectorDyadicIndex j) r)))=ᶠ[atTop]
        fun j=>(anisotropicFiniteTailMagnetization D
          (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q P i)^2 := by
      filter_upwards [he] with j hj
      have hcl : anisotropicClampOverlap q (Paper.parisiGridRound (vectorDyadicIndex j) r)=q :=
        Subtype.ext (max_eq_left hj)
      rw [hcl]
      exact cavityFinite_clamped_coordinate_square_current D _ q P i
    have hnlt : ¬q<r:=not_lt_of_ge hrq.le
    simpa only [ite_eq_right hnlt,P,EuclideanSpace.coe_proj,ContinuousLinearMap.id_apply]
      using hM.congr' hc.symm

 theorem anisotropic_restart_spin_second_node_response (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (i : Fin n) :
    fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x)
      (anisotropicCoordinateDirection n i) (anisotropicCoordinateDirection n i)=
      1-Paper.parisiCDF μ q*(anisotropicMeasureTailMagnetization D μ q
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i)^2-
      ∫r : Paper.Overlap,if q<r then anisotropicRestartSpinSquare D μ g q x i r else 0
        ∂(μ:Measure Paper.Overlap) := by
  classical
  let P:=anisotropicDisorderInjection n g+anisotropicFieldInjection n x
  let K:=anisotropicCoordinateDirection n i
  let sj:=fun j=>Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let Qj:=fun j r=>cavityFiniteConditionalCoordinateSquare D (vectorClampedScheme (sj j) q q.property)
    (vectorDyadicIndex j+3) P i (anisotropicClampOverlap q (Paper.parisiGridRound (vectorDyadicIndex j) r))
  let m:=anisotropicMeasureTailMagnetization D μ q P i
  let f:=fun r : Paper.Overlap=>if q<r then anisotropicRestartSpinSquare D μ g q x i r else m^2
  have hmj j : Measurable (Qj j) :=
    (measurable_cavityFiniteConditionalCoordinateSquare D _ _ P i).comp
      ((continuous_anisotropicClampOverlap q).measurable.comp (Paper.measurable_parisiGridRound _))
  have hbj j r : ‖Qj j r‖≤(1:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (cavityFiniteConditionalCoordinateSquare_mem_Icc D _ _ P i _).1]
    exact (cavityFiniteConditionalCoordinateSquare_mem_Icc D _ _ P i _).2
  have htI:=tendsto_integral_filter_of_dominated_convergence (μ:=(μ:Measure Paper.Overlap))
    (fun _=>(1:ℝ)) (.of_forall fun j=>(hmj j).aestronglyMeasurable)
    (.of_forall fun j=>.of_forall (hbj j)) (integrable_const _)
    (.of_forall fun r=>tendsto_cavityFinite_clamped_coordinate_square D μ g q r x i)
  have he j : fderiv ℝ (fderiv ℝ (anisotropicDyadicTailPotential D μ q j)) P K K=
      1-∫r,Qj j r∂(μ:Measure Paper.Overlap) := by
    rw [show anisotropicDyadicTailPotential D μ q j=anisotropicFiniteTailPotential D (sj j) q by rfl,
      cavityFinite_tail_spin_second_total_integral,FRSB.parisiSchemeMeasure_grid_eq,
      Paper.parisiGridMeasure,ProbabilityMeasure.toMeasure_map,
      integral_map_of_stronglyMeasurable (Paper.measurable_parisiGridRound _)]
    exact ((measurable_cavityFiniteConditionalCoordinateSquare D _ _ P i).comp
      (continuous_anisotropicClampOverlap q).measurable).stronglyMeasurable
  let H:=fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P
  have htH := (ContinuousLinearMap.lipschitzWith_apply K).continuous.tendsto (H K) |>.comp
    ((ContinuousLinearMap.lipschitzWith_apply K).continuous.tendsto H |>.comp
      ((anisotropicMeasureTailPotential_hessian_limit D μ q).1.tendsto_at P))
  have hformula : fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P K K=
      1-∫r,f r∂(μ:Measure Paper.Overlap) := by
    exact tendsto_nhds_unique htH
      (((tendsto_const_nhds (x:=(1:ℝ))).sub htI).congr fun j=>(he j).symm)
  have hset : MeasurableSet {r : Paper.Overlap | q<r}:=measurableSet_lt measurable_const measurable_id
  have hf : Measurable (fun r : Paper.Overlap=>if q<r then anisotropicRestartSpinSquare D μ g q x i r else 0):=
    Measurable.ite hset (measurable_anisotropicRestartSpinSquare D μ g q x i) measurable_const
  have hfi : Integrable (fun r : Paper.Overlap=>if q<r then anisotropicRestartSpinSquare D μ g q x i r else 0)
      (μ:Measure Paper.Overlap) := (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
    (.of_forall fun r=>by
      split_ifs
      · rw [Real.norm_eq_abs,abs_of_nonneg (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).1]
        exact (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).2
      · simp)
  have hcur : Integrable (fun r : Paper.Overlap=>(if r≤q then (1:ℝ) else 0)*m^2)
      (μ:Measure Paper.Overlap) :=
    ((integrable_const (1:ℝ)).indicator (measurableSet_Iic)).mul_const _
  have hfdecomp : f=(fun r=>(if r≤q then (1:ℝ) else 0)*m^2)+
      (fun r=>if q<r then anisotropicRestartSpinSquare D μ g q x i r else 0) := by
    funext r
    by_cases hr:q<r
    · simp [f,hr,not_le_of_gt hr]
    · simp [f,hr,le_of_not_gt hr]
  rw [hformula,hfdecomp]
  simp only [Pi.add_apply]
  rw [integral_add hcur hfi,integral_mul_const]
  have hCDF : (∫r : Paper.Overlap,if r≤q then (1:ℝ) else 0 ∂(μ:Measure Paper.Overlap))=
      Paper.parisiCDF μ q := by
    change (∫r : Paper.Overlap,if (r:ℝ)≤(q:ℝ) then (1:ℝ) else 0 ∂(μ:Measure Paper.Overlap))=_
    exact (Paper.parisiCDF_eq_integral_upperIndicator μ q).symm
  rw [hCDF]
  dsimp only [m,P]
  ring

end HexagonPaper
