module
public import HexagonPaper.CavityVertexCancellationRestartPointwise

@[expose] public section

/-! Every-field variance response and the printed local vertex cancellation
for the actual restarted continuation. Free/root atoms are removed only
where the strict-future integrand is exactly zero at the root. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Topology
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

 theorem integral_zero_root_eq_parisiFreeMeasure (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (f : Paper.Overlap→ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀r,‖f r‖≤B) (hzero : f zeroOverlap=0) :
    (∫r,f r∂(μ:Measure Paper.Overlap))=∫r,f r∂parisiFreeMeasure μ a := by
  have hfi : Integrable f (parisiFreeMeasure μ a) :=
    (integrable_const B).mono' hf.aestronglyMeasurable (.of_forall hB)
  have hdi : Integrable f (ENNReal.ofReal a • Measure.dirac zeroOverlap) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [←root_add_parisiFreeMeasure μ a ha hμ,integral_add_measure hdi hfi,
    integral_smul_measure,integral_dirac,hzero,smul_zero,zero_add]

 theorem anisotropic_restart_spin_second_node_response_free (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (i : Fin n) :
    fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x)
      (anisotropicCoordinateDirection n i) (anisotropicCoordinateDirection n i)=
      1-Paper.parisiCDF μ q*(anisotropicMeasureTailMagnetization D μ q
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i)^2-
      ∫r : Paper.Overlap,if q<r then anisotropicRestartSpinSquare D μ g q x i r else 0
        ∂parisiFreeMeasure μ a := by
  rw [anisotropic_restart_spin_second_node_response]
  congr 1
  apply integral_zero_root_eq_parisiFreeMeasure μ a ha hμ _
    (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (measurable_anisotropicRestartSpinSquare D μ g q x i) measurable_const) 1
  · intro r
    split_ifs
    · rw [Real.norm_eq_abs,abs_of_nonneg (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).1]
      exact (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).2
    · simp
  · have hq0 : ¬q<zeroOverlap := not_lt_of_ge q.property.1
    exact ite_eq_right hq0

 theorem hasDerivAt_anisotropic_restart_variance_node_response_free (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (i : Fin n) :
    HasDerivAt (fun b=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ q
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x))
      ((1/2:ℝ)*(1-(q:ℝ)-∫r : Paper.Overlap,if q<r then ((r:ℝ)-(q:ℝ))*
        anisotropicRestartSpinSquare D μ g q x i r else 0 ∂parisiFreeMeasure μ a)) (D.variance i) := by
  have hd:=hasDerivAt_anisotropicMeasureTailPotential_variance_restart D μ i g q x
    (D.variance i) (D.variance_pos i)
  rw [anisotropicReplaceVariance_self] at hd
  let f:=fun r : Paper.Overlap=>max 0 ((r:ℝ)-(q:ℝ))*anisotropicRestartSpinSquare D μ g q x i r
  have hf : Measurable f := (measurable_const.max (measurable_subtype_coe.sub_const _)).mul
    (measurable_anisotropicRestartSpinSquare D μ g q x i)
  have hb r : ‖f r‖≤(1:ℝ) := by
    rw [norm_mul,Real.norm_of_nonneg (le_max_left _ _)]
    exact (mul_le_of_le_one_right (le_max_left _ _)
      (by simpa only [Real.norm_eq_abs,abs_of_nonneg (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).1]
        using (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).2)).trans
      (max_le (by norm_num) (by linarith [q.property.1,r.property.2]))
  have hz : f zeroOverlap=0 := by
    simp only [f,zeroOverlap,Set.Icc.coe_zero,zero_sub,
      max_eq_left (neg_nonpos.mpr q.property.1),zero_mul]
  have he:=integral_zero_root_eq_parisiFreeMeasure μ a ha hμ f hf 1 hb hz
  unfold anisotropicRestartVarianceResponse at hd
  change HasDerivAt _ ((1/2:ℝ)*(1-(q:ℝ)-∫r,f r∂(μ:Measure Paper.Overlap))) _ at hd
  rw [he] at hd
  have hfe : f=(fun r : Paper.Overlap=>if q<r then ((r:ℝ)-(q:ℝ))*
      anisotropicRestartSpinSquare D μ g q x i r else 0) := by
    funext r
    by_cases hqr:q<r
    · simp only [f,ite_eq_left hqr,max_eq_right (sub_nonneg.mpr (show (q:ℝ)≤(r:ℝ) from hqr.le))]
    · simp only [f,ite_eq_right hqr,max_eq_left (sub_nonpos.mpr (show (r:ℝ)≤(q:ℝ) from le_of_not_gt hqr)),zero_mul]
  simpa only [hfe] using hd

 theorem anisotropic_restart_vertex_variance_cancellation (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (i : Fin n) :
    (q:ℝ)*fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n x)
        (anisotropicCoordinateDirection n i) (anisotropicCoordinateDirection n i)+
      2*deriv (fun b=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ q
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n x)) (D.variance i)=
      1-(q:ℝ)*Paper.parisiCDF μ q*(anisotropicMeasureTailMagnetization D μ q
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i)^2-
      ∫r : Paper.Overlap,if q<r then (r:ℝ)*anisotropicRestartSpinSquare D μ g q x i r else 0
        ∂parisiFreeMeasure μ a := by
  let K:=anisotropicRestartSpinSquare D μ g q x i
  let f:=fun r : Paper.Overlap=>if q<r then K r else 0
  let g₁:=fun r : Paper.Overlap=>if q<r then ((r:ℝ)-(q:ℝ))*K r else 0
  have hKm:=measurable_anisotropicRestartSpinSquare D μ g q x i
  have hset : MeasurableSet {r : Paper.Overlap | q<r}:=measurableSet_lt measurable_const measurable_id
  have hfi : Integrable f (parisiFreeMeasure μ a) := (integrable_const (1:ℝ)).mono'
    (Measurable.ite hset hKm measurable_const).aestronglyMeasurable (.of_forall fun r=>by
      dsimp only [f,K]
      split_ifs
      · rw [Real.norm_eq_abs,abs_of_nonneg (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).1]
        exact (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).2
      · simp)
  have hgi : Integrable g₁ (parisiFreeMeasure μ a) := (integrable_const (1:ℝ)).mono'
    (Measurable.ite hset ((measurable_subtype_coe.sub_const _).mul hKm) measurable_const).aestronglyMeasurable
    (.of_forall fun r=>by
      dsimp only [g₁,K]
      split_ifs
      · rw [norm_mul]
        have hnorm : ‖(r:ℝ)-(q:ℝ)‖≤1 := by
          rw [Real.norm_eq_abs,abs_le]
          constructor <;> linarith [r.property.1,r.property.2,q.property.1,q.property.2]
        have hk : ‖anisotropicRestartSpinSquare D μ g q x i r‖≤1 := by
          rw [Real.norm_eq_abs,abs_of_nonneg (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).1]
          exact (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).2
        exact (mul_le_mul hnorm hk (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
      · simp)
  have hc : (q:ℝ)*(∫r,f r∂parisiFreeMeasure μ a)+(∫r,g₁ r∂parisiFreeMeasure μ a)=
      ∫r : Paper.Overlap,if q<r then (r:ℝ)*K r else 0 ∂parisiFreeMeasure μ a := by
    rw [←integral_const_mul,←integral_add (hfi.const_mul _) hgi]
    apply integral_congr_ae
    exact .of_forall fun r=>by
      dsimp only [f,g₁]
      split_ifs <;> ring
  rw [anisotropic_restart_spin_second_node_response_free D μ a ha hμ g q x i,
    (hasDerivAt_anisotropic_restart_variance_node_response_free D μ a ha hμ g q x i).deriv]
  dsimp only [f,g₁,K] at hc
  linarith

end HexagonPaper
