module
public import QuantitativePaper.VectorJointResponseEndpointPast
public import QuantitativePaper.VectorJointObservableRecursion
public import QuantitativePaper.VectorFiniteIto

@[expose] public section

/-! The actual finite-profile vector diffusion obeys the genuine backward
branching identity on each full cell, conditional on its whole earlier past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

theorem vectorFinite_actual_cell_drift (s : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (i : ℕ) (hi : i≤k+1) (r : ℝ≥0)
    (hr : (r : ℝ)∈Ioo (s.q i) (s.q (i+1))) (sample : VectorDisorderBrownianSample n) :
    vectorAdditiveDrift (vectorFiniteDriftData s β t ht) (Real.sqrt ((1-t)*β^2)) 0 1 r sample=
      ((1-t)*β^2) • ((s.m i) • gradient
        (vectorColeHopfStep (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
          (vectorRecursion s β t sample.1 (k+1-i))) (vectorFiniteState s β t ht r sample)) := by
  have hr0 : 0≤(r : ℝ) := r.coe_nonneg
  have hr1 : (r : ℝ)≤1 := hr.2.le.trans (s.q_le_one (by omega))
  have hrnn : r≤1 := by exact_mod_cast hr1
  rw [vectorAdditiveDrift,if_pos hrnn]
  change vectorFiniteDrift s β t r sample.1 (vectorFiniteState s β t ht r sample)=_
  unfold vectorFiniteDrift
  rw [Paper.parisiCDF_scheme_cell s hi ⟨hr.1.le,hr.2⟩]
  unfold vectorFiniteTailGradient
  rw [projIcc_of_mem _ ⟨hr0,hr1⟩,
    vectorTailRecursion_eq_finiteCell s β t r sample.1 i hi ⟨hr.1.le,hr.2.le⟩]
  simp only [smul_smul]
  rfl

theorem vectorFinite_cell_backward_identity (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(G (sample.1,vectorFiniteState s β t ht.le
        (s.q (i+1)).toNNReal sample)-
      vectorJointResponse (fun p=>vectorRecursion s β t p.1 (k+1-i) p.2) G
        (((1-t)*β^2)*(s.q (i+1)-s.q i)) (s.m i)
        (sample.1,vectorFiniteState s β t ht.le (s.q i).toNNReal sample)))
      (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(G (sample.1,vectorFiniteState s β t ht.le
        (s.q (i+1)).toNNReal sample)-
      vectorJointResponse (fun p=>vectorRecursion s β t p.1 (k+1-i) p.2) G
        (((1-t)*β^2)*(s.q (i+1)-s.q i)) (s.m i)
        (sample.1,vectorFiniteState s β t ht.le (s.q i).toNNReal sample))
      ∂vectorDisorderBrownianMeasure n)=0 := by
  let a := (s.q i).toNNReal
  let Q := (s.q (i+1)).toNNReal
  have ha : (a : ℝ)=s.q i := Real.coe_toNNReal _ (s.q_nonneg (by omega))
  have hQ : (Q : ℝ)=s.q (i+1) := Real.coe_toNNReal _ (s.q_nonneg (by omega))
  have haQ : a≤Q := by
    apply NNReal.coe_le_coe.mp
    rw [ha,hQ]
    exact s.q_mono i (by omega)
  have hcpos : 0<(1-t)*β^2 := mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  have hh := vector_jointResponse_endpoint_martingale_past
    (vectorRecursionJointResponseData s β t (k+1-i) hG)
    (vectorItoCharacteristics_vectorFiniteState s β t ht.le)
    (Real.sq_sqrt hcpos.le) hcpos a Q haQ
    (fun r hr sample=>by
      have hr' : (r : ℝ)∈Ioo (s.q i) (s.q (i+1)) := by
        rw [←ha,←hQ]
        exact ⟨hr.1,hr.2⟩
      rw [hQ]
      exact vectorFinite_actual_cell_drift s β t ht.le i hi r hr' sample)
    Z hZ C hC
  simpa only [ha,hQ] using hh

end QuantitativePaper
