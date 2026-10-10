module
public import QuantitativePaper.VectorJointResponseIntervalPast
public import QuantitativePaper.VectorResponseBoundary

@[expose] public section

/-! Genuine endpoint backward-response identity, obtained by bounded
convergence as the actual remaining Gaussian variance tends to zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem vector_jointResponse_endpoint_martingale_past
    {F G : VectorParameter n→ℝ} (data : VectorJointResponseTestData F G)
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ m c : ℝ}
    (hc : VectorItoCharacteristics X d σ) (hσ : σ^2=c) (hcpos : 0<c)
    (a Q : ℝ≥0) (haQ : a≤Q)
    (hd : ∀ r∈Ioo a Q,∀ sample,d r sample=
      c • (m • gradient (vectorColeHopfStep (c*(Q-r)) m (fun x=>F (sample.1,x))) (X r sample)))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n a] Z) (C : ℝ≥0)
    (hC : ∀ sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(G (sample.1,X Q sample)-
      vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))) (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,Z sample*(G (sample.1,X Q sample)-
      vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample)) ∂vectorDisorderBrownianMeasure n)=0 := by
  let P := vectorDisorderBrownianMeasure n
  let M := data.observableBounds 0
  have hM : 0≤M := data.observableBounds_nonneg 0
  have hR (v : ℝ) (sample : VectorDisorderBrownianSample n) (x : Field n) :
      ‖vectorJointResponse F G v m (sample.1,x)‖≤M := by
    simpa only [vectorJointResponse,Real.norm_eq_abs,VectorJointResponseTestData.fieldData,M] using
      (data.fieldData sample.1).response_bound m v x
  have hG (p : VectorParameter n) : ‖G p‖≤M := by
    simpa only [norm_iteratedFDeriv_zero] using data.observableJets 0 (by omega) p
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le a) le_rfl
  have hXm (q : ℝ≥0) : Measurable (fun sample=>(sample.1,X q sample)) :=
    measurable_fst.prodMk ((hc.adapted_state q).measurable.mono ((vectorBrownianFiltration n).le q) le_rfl)
  have htargetm : Measurable (fun sample=>Z sample*(G (sample.1,X Q sample)-
      vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))) :=
    hZg.mul ((data.observableRegularity.continuous.measurable.comp (hXm Q)).sub
      (((data.jointBounds m).responseRegularity _).continuous.measurable.comp (hXm a)))
  have htargetb (sample : VectorDisorderBrownianSample n) :
      ‖Z sample*(G (sample.1,X Q sample)-vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))‖
        ≤ (C : ℝ)*(2*M) := by
    rw [norm_mul]
    apply mul_le_mul (hC sample) ((norm_sub_le _ _).trans ?_) (norm_nonneg _) C.coe_nonneg
    linarith [hG (sample.1,X Q sample),hR (c*(Q-a)) sample (X a sample)]
  have hi : Integrable (fun sample=>Z sample*(G (sample.1,X Q sample)-
      vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))) P :=
    (integrable_const ((C : ℝ)*(2*M))).mono' htargetm.aestronglyMeasurable (Eventually.of_forall htargetb)
  refine ⟨hi,?_⟩
  rcases eq_or_lt_of_le haQ with heq|hlt
  · subst Q
    simp [vectorJointResponse,vectorStepResponse_zero]
  have hpow (j : ℕ) : (1/2 : ℝ)^j≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpowpos (j : ℕ) : 0<(1/2 : ℝ)^j := pow_pos (by norm_num) _
  have hspan : 0<(Q : ℝ)-a := sub_pos.mpr hlt
  let b (j : ℕ) : ℝ≥0 := ⟨(Q : ℝ)-((Q : ℝ)-a)*(1/2 : ℝ)^j,by
    have hh := mul_le_mul_of_nonneg_left (hpow j) hspan.le
    nlinarith [a.coe_nonneg]⟩
  have hab (j : ℕ) : a≤b j := by
    change (a : ℝ)≤(Q : ℝ)-((Q : ℝ)-a)*(1/2 : ℝ)^j
    have hh := mul_le_mul_of_nonneg_left (hpow j) hspan.le
    nlinarith
  have hbQ (j : ℕ) : (b j : ℝ)<Q := by
    change (Q : ℝ)-((Q : ℝ)-a)*(1/2 : ℝ)^j<Q
    linarith [mul_pos hspan (hpowpos j)]
  have hblimR : Tendsto (fun j=>(b j : ℝ)) atTop (𝓝 (Q : ℝ)) := by
    change Tendsto (fun j=>(Q : ℝ)-((Q : ℝ)-a)*(1/2 : ℝ)^j) atTop (𝓝 (Q : ℝ))
    have hh := (tendsto_const_nhds (x:=(Q : ℝ))).sub
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2 : ℝ))
        (by norm_num : (1/2 : ℝ)<1)).const_mul ((Q : ℝ)-a))
    simpa only [mul_zero,sub_zero] using hh
  have hblim : Tendsto b atTop (𝓝 Q) := NNReal.tendsto_coe.mp hblimR
  have hcell (j : ℕ) := vector_jointResponse_interval_martingale_past data hc hσ hcpos a (b j)
    (hab j) (hbQ j) (fun r hr sample=>hd r ⟨hr.1,hr.2.trans_lt (hbQ j)⟩ sample) Z hZ C hC
  have hlim : ∀ᵐ sample ∂P,Tendsto
      (fun j=>Z sample*(vectorJointResponse F G (c*(Q-b j)) m (sample.1,X (b j) sample)-
        vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample))) atTop
      (𝓝 (Z sample*(G (sample.1,X Q sample)-
        vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample)))) := by
    apply Eventually.of_forall
    intro sample
    have hv : Tendsto (fun j=>c*((Q : ℝ)-b j)) atTop (𝓝 0) := by
      simpa only [sub_self,mul_zero] using ((tendsto_const_nhds (x:=(Q : ℝ))).sub hblimR).const_mul c
    have hx := (hc.continuous_state sample).continuousAt.tendsto.comp hblim
    exact tendsto_const_nhds.mul
      (((data.fieldData sample.1).tendsto_response_zero m hv hx).sub tendsto_const_nhds)
  have hh := tendsto_integral_of_dominated_convergence (fun _=>(C : ℝ)*(2*M))
    (fun j=>(hcell j).1.aestronglyMeasurable) (integrable_const _) (fun j=>Eventually.of_forall
      (fun sample=>by
        rw [norm_mul]
        apply mul_le_mul (hC sample) ((norm_sub_le _ _).trans ?_) (norm_nonneg _) C.coe_nonneg
        linarith [hR (c*(Q-b j)) sample (X (b j) sample),hR (c*(Q-a)) sample (X a sample)])) hlim
  have hz : (fun j=>∫ sample,Z sample*(vectorJointResponse F G (c*(Q-b j)) m (sample.1,X (b j) sample)-
      vectorJointResponse F G (c*(Q-a)) m (sample.1,X a sample)) ∂P)=fun _ : ℕ=>(0 : ℝ) :=
    funext (fun j=>(hcell j).2)
  rw [hz] at hh
  exact (tendsto_nhds_unique tendsto_const_nhds hh).symm

end QuantitativePaper
