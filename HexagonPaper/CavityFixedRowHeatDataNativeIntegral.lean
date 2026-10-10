module
public import HexagonPaper.CavityTreeNativeAllJets
public import QuantitativePaper.SmoothIntegral
public import QuantitativePaper.BoundedPositiveJets
public import FourPapersCommon.ExponentialLinearChange

@[expose] public section

/-! Actual native potential jets survive affine incident-row changes and
integration against a finite compact tree charge. Bounds depend on the
charge mass and the fixed linear chart, never on the retained path record. -/
noncomputable section
open Set Filter MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ContDiff BigOperators
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n m : ℕ}

 theorem cavityNativeAffineTail_jet (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (L : Field m→L[ℝ]AnisotropicParameter n) (r : ℕ) (θ : Field m) :
    iteratedFDeriv ℝ r (fun y=>anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q (P+L y)) θ=
      (iteratedFDeriv ℝ r (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q)
        (P+L θ)).compContinuousLinearMap (fun _=>L) := by
  let f:=fun x:AnisotropicParameter n=>anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q (P+x)
  have hf : ContDiff ℝ ∞ f:=
    (cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1.comp
      (contDiff_const.add contDiff_id)
  have he:=L.iteratedFDeriv_comp_right hf θ (by simp : (r:WithTop ℕ∞)≤∞)
  simpa only [f,Function.comp_def,iteratedFDeriv_comp_add_left] using he

 theorem cavityNativeAffineTail_positive_jet_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (L : Field m→L[ℝ]AnisotropicParameter n) (r : ℕ) (hr : 1≤r) (θ : Field m) :
    ‖iteratedFDeriv ℝ r (fun y=>anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q (P+L y)) θ‖≤
      cavityTreeUniformParameterJetBound n r*‖L‖^r := by
  rw [cavityNativeAffineTail_jet]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right
    (cavityTree_native_unit_tail_positive_jet_bound D μ q r hr _) (pow_nonneg (norm_nonneg _) _)

 theorem cavityNativeAffineTail_jet_joint_continuous (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (L : Field m→L[ℝ]AnisotropicParameter n) (r : ℕ) :
    Continuous (fun z:(Paper.Overlap×AnisotropicParameter n)×Field m=>
      iteratedFDeriv ℝ r (fun y=>anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ z.1.1
        (z.1.2+L y)) z.2) := by
  simp_rw [cavityNativeAffineTail_jet]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin r=>L)).continuous.comp
    ((cavityTree_native_tail_jet_joint_continuous (anisotropicUnitCouplings D) μ r).comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.add (L.continuous.comp continuous_snd))))

section CompactCharge
variable {X : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

def cavityNativeChargePotential (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ν : Measure X) (A : C(X,Paper.Overlap×AnisotropicParameter n))
    (L : Field m→L[ℝ]AnisotropicParameter n) (θ : Field m) : ℝ :=
  ∫v,anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ (A v).1 ((A v).2+L θ) ∂ν

private theorem cavityNativeCharge_local_envelope
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ν : Measure X) [IsFiniteMeasure ν] (A : C(X,Paper.Overlap×AnisotropicParameter n))
    (L : Field m→L[ℝ]AnisotropicParameter n) (N : ℕ) (θ : Field m) :
    ∃s∈𝓝 θ,∃C : ℕ→X→ℝ,(∀r,r≤N→Integrable (C r) ν) ∧
      ∀r,r≤N→∀y∈s,∀v,‖iteratedFDeriv ℝ r
        (fun u=>anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ (A v).1 ((A v).2+L u)) y‖≤C r v := by
  have hc (r : ℕ) : Continuous (fun z:Field m×X=>iteratedFDeriv ℝ r
      (fun u=>anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ (A z.2).1 ((A z.2).2+L u)) z.1) := by
    let b : Field m×X→(Paper.Overlap×AnisotropicParameter n)×Field m:=fun z=>(A z.2,z.1)
    have hbc : Continuous b := (A.continuous.comp continuous_snd).prodMk continuous_fst
    have hh:=(cavityNativeAffineTail_jet_joint_continuous D μ L r).comp hbc
    apply hh.congr
    intro z
    rfl
  have hb (r : ℕ) : ∃C : ℝ,∀y∈Metric.closedBall θ 1,∀v,‖iteratedFDeriv ℝ r
      (fun u=>anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ (A v).1 ((A v).2+L u)) y‖≤C := by
    obtain ⟨C,hC⟩:=(isCompact_closedBall θ 1 |>.prod (isCompact_univ : IsCompact (univ : Set X))).exists_bound_of_continuousOn
      (hc r).continuousOn
    exact ⟨C,fun y hy v=>hC (y,v) ⟨hy,mem_univ v⟩⟩
  choose C hC using hb
  exact ⟨Metric.ball θ 1,Metric.ball_mem_nhds θ (by norm_num),fun r _=>C r,
    fun _ _=>integrable_const _,fun r _ y hy v=>hC r y (Metric.ball_subset_closedBall hy) v⟩

 theorem cavityNativeChargePotential_smooth (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ν : Measure X) [IsFiniteMeasure ν] (A : C(X,Paper.Overlap×AnisotropicParameter n))
    (L : Field m→L[ℝ]AnisotropicParameter n) :
    ContDiff ℝ ∞ (cavityNativeChargePotential D μ ν A L) := by
  apply contDiff_infty.mpr
  intro N
  exact contDiff_integral_of_dominated_derivatives N ν _
    (fun v=>((cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ (A v).1).1.comp
      (contDiff_const.add L.contDiff)).of_le (by simp))
    (fun r _ θ=>by
      have hh:=((cavityNativeAffineTail_jet_joint_continuous D μ L r).comp
        (A.continuous.prodMk (continuous_const : Continuous (fun _ : X=>θ)))).aestronglyMeasurable (μ:=ν)
      apply hh.congr
      exact .of_forall fun v=>rfl)
    (cavityNativeCharge_local_envelope D μ ν A L N)

 theorem cavityNativeChargePotential_iterated_derivative (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ν : Measure X) [IsFiniteMeasure ν] (A : C(X,Paper.Overlap×AnisotropicParameter n))
    (L : Field m→L[ℝ]AnisotropicParameter n) (r : ℕ) (θ : Field m) :
    iteratedFDeriv ℝ r (cavityNativeChargePotential D μ ν A L) θ=
      ∫v,iteratedFDeriv ℝ r (fun u=>anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ (A v).1
        ((A v).2+L u)) θ∂ν := by
  exact iteratedFDeriv_integral_of_dominated_derivatives r ν _
    (fun v=>((cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ (A v).1).1.comp
      (contDiff_const.add L.contDiff)).of_le (by simp))
    (fun k _ θ=>by
      have hh:=((cavityNativeAffineTail_jet_joint_continuous D μ L k).comp
        (A.continuous.prodMk (continuous_const : Continuous (fun _ : X=>θ)))).aestronglyMeasurable (μ:=ν)
      apply hh.congr
      exact .of_forall fun v=>rfl)
    (cavityNativeCharge_local_envelope D μ ν A L r) r le_rfl θ

 theorem cavityNativeChargePotential_positive_jet_bound (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (ν : Measure X) [IsFiniteMeasure ν] (A : C(X,Paper.Overlap×AnisotropicParameter n))
    (L : Field m→L[ℝ]AnisotropicParameter n) (r : ℕ) (hr : 1≤r) (θ : Field m) :
    ‖iteratedFDeriv ℝ r (cavityNativeChargePotential D μ ν A L) θ‖≤
      ν.real univ*(cavityTreeUniformParameterJetBound n r*‖L‖^r) := by
  rw [cavityNativeChargePotential_iterated_derivative]
  simpa only [mul_comm] using norm_integral_le_of_norm_le_const (μ:=ν) (.of_forall fun v=>
    cavityNativeAffineTail_positive_jet_bound D μ (A v).1 (A v).2 L r hr θ)

end CompactCharge
end HexagonPaper
