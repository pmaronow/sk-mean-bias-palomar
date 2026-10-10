module
public import QuantitativeFollowup.AnisotropicTerminalFeatures
public import QuantitativeFollowup.AnisotropicGridNodes

@[expose] public section

/-! Honest passage of terminal-spin pairings from the genuine finite
transition laws to every profile. The upper grid nodes retain all events
in the fixed observation-time past; no filtration right-continuity is assumed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem anisotropicFinitePhysicalParameter_eq_native (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (sample : VectorDisorderBrownianSample n) :
    anisotropicFinitePhysicalParameter D s g (q:ℝ).toNNReal sample=
      anisotropicFiniteProcessParameter D s q (g,sample.2) := by rfl

def anisotropicProcessPairResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  anisotropicTailPairResponse D μ q (anisotropicProcessParameter D μ q sample) e

theorem measurable_anisotropicProcessPairResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    Measurable (anisotropicProcessPairResponse D μ q e) := by
  have hP := (measurable_uncurry_anisotropicProcessParameter D μ).comp
    ((measurable_const (a:=q)).prodMk measurable_id)
  have h := (continuous_anisotropicTailPairResponse_joint D μ e).measurable.comp
    ((measurable_const (a:=q)).prodMk hP)
  change Measurable (fun sample=>anisotropicTailPairResponse D μ q
    (anisotropicProcessParameter D μ q sample) e)
  simpa only [Function.comp_def,anisotropicProcessPairResponse,id_eq] using h

theorem anisotropicProcessPairResponse_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) : ‖anisotropicProcessPairResponse D μ q e sample‖≤1 :=
  anisotropicTailPairResponse_bound D μ q _ e

theorem anisotropic_terminalPair_weighted_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (e : AnisotropicCouplingIndex n) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] Z)
    (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    (∫p,Z p*anisotropicProcessPairResponse D μ 1 e (g,p.2) ∂vectorDisorderBrownianMeasure n)=
      ∫p,Z p*anisotropicProcessPairResponse D μ q e (g,p.2) ∂vectorDisorderBrownianMeasure n := by
  let sj := fun j=>Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let qj := fun j=>Paper.parisiGridRound (vectorDyadicIndex j) q
  let ij := fun j=>anisotropicGridNodeIndex (vectorDyadicIndex j) q
  let fj := fun j=>fun p : VectorDisorderBrownianSample n=>
    anisotropicFiniteTailPairResponse D (sj j) 1 (anisotropicFiniteProcessParameter D (sj j) 1 (g,p.2)) e
  let rj := fun j=>fun p : VectorDisorderBrownianSample n=>
    anisotropicFiniteTailPairResponse D (sj j) (qj j) (anisotropicFiniteProcessParameter D (sj j) (qj j) (g,p.2)) e
  have heq (j : ℕ) : (∫p,Z p*fj j p ∂vectorDisorderBrownianMeasure n)=
      ∫p,Z p*rj j p ∂vectorDisorderBrownianMeasure n := by
    have hi : ij j≤(vectorDyadicIndex j+1)+2 := by
      have h:=anisotropicGridNodeIndex_le (vectorDyadicIndex j) q
      dsimp only [ij]
      omega
    have hZ' : Measurable[vectorBrownianFiltration n ((sj j).q (ij j)).toNNReal] Z :=
      hZ.mono ((vectorBrownianFiltration n).mono (Real.toNNReal_mono
        (anisotropicGridNode_after μ (vectorDyadicIndex j) q))) le_rfl
    have hb (σ : Configuration n) : ‖Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)‖≤1 := by
      simp only [norm_mul,Real.norm_eq_abs,Paper.abs_spinSign,mul_one,le_refl]
    have h := anisotropicFinite_terminalFeature_weighted_pairing D (sj j) g (ij j) hi
      (fun σ=>Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)) 1 hb Z hZ' hZi
    have hnode := anisotropicGridNode_eq_round μ (vectorDyadicIndex j) q
    have hpair := anisotropicFiniteTailPairResponse_node D (sj j) (ij j) hi
    simp_rw [anisotropicFiniteFeatureMean_zero] at h
    have hz : (sj j).q (ij j)=(qj j:ℝ) := anisotropicGridNode_overlap μ (vectorDyadicIndex j) q
    simp only [fj,anisotropicFiniteTailPairResponse_one,←anisotropicFinitePhysicalParameter_eq_native,
      Set.Icc.coe_one,Real.toNNReal_one,rj,anisotropicGridNode_overlap] at h ⊢
    apply h.trans
    apply integral_congr_ae
    exact .of_forall fun p=>by
      dsimp only
      rw [hz]
      congr 1
      have hn : qj j=anisotropicSchemeNode (sj j) (ij j) hi := hnode.symm
      rw [hn,anisotropicFiniteTailPairResponse_node]
      rfl
  have hq : Tendsto qj atTop (𝓝 q) := (Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex
  have hf (p : VectorDisorderBrownianSample n) : Tendsto (fun j=>fj j p) atTop
      (𝓝 (anisotropicProcessPairResponse D μ 1 e (g,p.2))) :=
    tendsto_anisotropicProcessPairResponse_moving D μ (g,p.2) e tendsto_const_nhds
  have hr (p : VectorDisorderBrownianSample n) : Tendsto (fun j=>rj j p) atTop
      (𝓝 (anisotropicProcessPairResponse D μ q e (g,p.2))) :=
    tendsto_anisotropicProcessPairResponse_moving D μ (g,p.2) e hq
  have hZg := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hm (j : ℕ) (v : Paper.Overlap) : Measurable (fun p : VectorDisorderBrownianSample n=>
      anisotropicFiniteTailPairResponse D (sj j) v (anisotropicFiniteProcessParameter D (sj j) v (g,p.2)) e) := by
    have hP := (measurable_uncurry_anisotropicFiniteProcessParameter D (sj j)).comp
      ((measurable_const (a:=v)).prodMk ((measurable_const (a:=g)).prodMk
        (measurable_snd : Measurable (Prod.snd : VectorDisorderBrownianSample n→VectorBrownianSample n))))
    have hd := (contDiff_anisotropicFiniteTailPotential (anisotropicUnitCouplings D) (sj j) v).continuous_fderiv
      (by simp)
    have htail := ((hd.comp (anisotropicCouplingRescaling D).continuous).clm_apply
      (continuous_const (y:=anisotropicCouplingDirection e)))
    have h := htail.measurable.comp hP
    simpa only [Function.comp_def,anisotropicFiniteTailPairResponse] using h
  have hleft := tendsto_integral_of_dominated_convergence (fun p=>‖Z p‖)
    (fun j=>(hZg.mul (hm j 1)).aestronglyMeasurable) hZi.norm
    (fun j=>.of_forall fun p=>by
      simp only [Pi.mul_apply,norm_mul]
      exact (mul_le_mul_of_nonneg_left (anisotropicFiniteTailPairResponse_bound D (sj j) 1 _ e)
        (norm_nonneg (Z p))).trans_eq (mul_one _))
    (.of_forall fun p=>(tendsto_const_nhds (x:=Z p)).mul (hf p))
  have hright := tendsto_integral_of_dominated_convergence (fun p=>‖Z p‖)
    (fun j=>(hZg.mul (hm j (qj j))).aestronglyMeasurable) hZi.norm
    (fun j=>.of_forall fun p=>by
      simp only [Pi.mul_apply,norm_mul]
      exact (mul_le_mul_of_nonneg_left (anisotropicFiniteTailPairResponse_bound D (sj j) (qj j) _ e)
        (norm_nonneg (Z p))).trans_eq (mul_one _))
    (.of_forall fun p=>(tendsto_const_nhds (x:=Z p)).mul (hr p))
  exact tendsto_nhds_unique hleft (hright.congr (fun j=>(heq j).symm))

end QuantitativeFollowup
