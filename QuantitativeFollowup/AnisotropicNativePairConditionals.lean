module
public import QuantitativeFollowup.AnisotropicAdapted
public import QuantitativeFollowup.AnisotropicPairConditionalLimit

@[expose] public section

/-! The response pair is the actual conditional terminal-spin moment under
 the native anisotropic disorder/Wiener law. Every event in the entire earlier
 past is retained and the initial exponential disorder tilt is mixed exactly. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

def anisotropicWienerInsertion (g : AnisotropicDisorder n)
    (sample : VectorDisorderBrownianSample n) : AnisotropicDisorderBrownianSample n := (g,sample.2)

theorem measurable_anisotropicWienerInsertion_past (g : AnisotropicDisorder n) (q : ℝ≥0) :
    @Measurable (VectorDisorderBrownianSample n) (AnisotropicDisorderBrownianSample n)
      (vectorBrownianFiltration n q) (anisotropicBrownianFiltration n q)
      (anisotropicWienerInsertion g) := by
  rw [anisotropicBrownianFiltration,Filtration.natural_eq_comap,measurable_comap_iff]
  letI : MeasurableSpace (VectorDisorderBrownianSample n):=vectorBrownianFiltration n q
  apply Measurable.of_eval
  intro r
  have hW := ((stronglyAdapted_disorderVectorBrownian n r).mono
    ((vectorBrownianFiltration n).mono r.property)).measurable
  have hG : Measurable (fun _ : VectorDisorderBrownianSample n=>g) := measurable_const
  have h := hG.prodMk hW
  simpa only [Function.comp_def,anisotropicBrownianRecord,anisotropicWienerInsertion,
    disorderVectorBrownian] using h

theorem adapted_anisotropicProcessParameter (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) :
    Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] (anisotropicProcessParameter D μ q) := by
  have hq : (q:ℝ).toNNReal≤1 := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ q.property.1]
    exact q.property.2
  have hX := adapted_anisotropicMeasureState D μ (q:ℝ).toNNReal hq
  have hx : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal]
      (fun sample=>anisotropicMeasureState D μ (q:ℝ) sample) := by
    simpa only [Real.coe_toNNReal _ q.property.1] using hX
  have h := ((anisotropicDisorderInjection n).continuous.measurable.comp
    (measurable_anisotropicInitialDisorder (q:ℝ).toNNReal)).add
      ((anisotropicFieldInjection n).continuous.measurable.comp hx)
  change Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] (fun sample=>anisotropicDisorderInjection n sample.1+
    anisotropicFieldInjection n (anisotropicMeasureState D μ (q:ℝ) sample))
  simpa only [Function.comp_def,Pi.add_def] using h

theorem adapted_anisotropicProcessPairResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] (anisotropicProcessPairResponse D μ q e) := by
  have h := (continuous_anisotropicTailPairResponse_joint D μ e).measurable.comp
    ((measurable_const (a:=q)).prodMk (adapted_anisotropicProcessParameter D μ q))
  change Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] (fun sample=>anisotropicTailPairResponse D μ q (anisotropicProcessParameter D μ q sample) e)
  simpa only [Function.comp_def] using h

theorem anisotropic_native_terminalPair_bounded_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (Z : AnisotropicDisorderBrownianSample n→ℝ)
    (hZ : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] Z)
    (B : ℝ) (hB : ∀sample,‖Z sample‖≤B) :
    (∫sample,Z sample*anisotropicProcessPairResponse D μ 1 e sample ∂anisotropicMeasureSampleLaw D μ a)=
      ∫sample,Z sample*anisotropicProcessPairResponse D μ q e sample ∂anisotropicMeasureSampleLaw D μ a := by
  have hZg := hZ.mono ((anisotropicBrownianFiltration n).le _) le_rfl
  have hi (r : Paper.Overlap) : Integrable (fun sample=>Z sample*anisotropicProcessPairResponse D μ r e sample)
      (anisotropicMeasureSampleLaw D μ a) := by
    apply (integrable_const B).mono'
      (hZg.mul (measurable_anisotropicProcessPairResponse D μ r e)).aestronglyMeasurable
    exact .of_forall fun sample=>by
      simp only [Pi.mul_apply,norm_mul]
      exact (mul_le_mul_of_nonneg_left (anisotropicProcessPairResponse_bound D μ r e sample)
        (norm_nonneg (Z sample))).trans (by simpa only [mul_one] using hB sample)
  rw [anisotropicMeasureSampleLaw,integral_prod _ (hi 1),integral_prod _ (hi q)]
  apply integral_congr_ae
  exact .of_forall fun g=>by
    have hZp := hZ.comp (measurable_anisotropicWienerInsertion_past g (q:ℝ).toNNReal)
    have hZpg := hZp.mono ((vectorBrownianFiltration n).le _) le_rfl
    have hZi : Integrable (fun p : VectorDisorderBrownianSample n=>Z (g,p.2))
        (vectorDisorderBrownianMeasure n) :=
      (integrable_const B).mono' hZpg.aestronglyMeasurable (.of_forall fun p=>hB (g,p.2))
    have h := anisotropic_terminalPair_weighted_pairing D μ g q e (fun p=>Z (g,p.2)) hZp hZi
    change (∫p : VectorDisorderBrownianSample n,
      (fun w : VectorBrownianSample n=>Z (g,w)*anisotropicProcessPairResponse D μ 1 e (g,w)) p.2
        ∂(completionLaw n).prod (vectorBrownianMeasure n))=
      ∫p : VectorDisorderBrownianSample n,
        (fun w : VectorBrownianSample n=>Z (g,w)*anisotropicProcessPairResponse D μ q e (g,w)) p.2
          ∂(completionLaw n).prod (vectorBrownianMeasure n) at h
    have h1 := integral_fun_snd (μ:=completionLaw n) (ν:=vectorBrownianMeasure n)
      (fun w : VectorBrownianSample n=>Z (g,w)*anisotropicProcessPairResponse D μ 1 e (g,w))
    have h2 := integral_fun_snd (μ:=completionLaw n) (ν:=vectorBrownianMeasure n)
      (fun w : VectorBrownianSample n=>Z (g,w)*anisotropicProcessPairResponse D μ q e (g,w))
    have hout := h1.symm.trans (h.trans h2)
    simpa only [probReal_univ,one_smul] using hout

theorem anisotropicProcessPairResponse_eq_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    (anisotropicMeasureSampleLaw D μ a)[anisotropicProcessPairResponse D μ 1 e |
      anisotropicBrownianFiltration n (q:ℝ).toNNReal]=ᵐ[anisotropicMeasureSampleLaw D μ a]
      anisotropicProcessPairResponse D μ q e := by
  have hi (r : Paper.Overlap) : Integrable (anisotropicProcessPairResponse D μ r e)
      (anisotropicMeasureSampleLaw D μ a) :=
    (integrable_const (1 : ℝ)).mono' (measurable_anisotropicProcessPairResponse D μ r e).aestronglyMeasurable
      (.of_forall (anisotropicProcessPairResponse_bound D μ r e))
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq ((anisotropicBrownianFiltration n).le _) (hi 1)
  · intro A hA hfin
    exact (hi q).integrableOn
  · intro A hA hfin
    have hm : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal]
        (A.indicator (fun _ : AnisotropicDisorderBrownianSample n=>(1 : ℝ))) :=
      measurable_const.indicator hA
    have hb (sample : AnisotropicDisorderBrownianSample n) :
        ‖A.indicator (fun _=>(1 : ℝ)) sample‖≤1 := by
      by_cases hs : sample∈A <;> simp [Set.indicator_of_mem,Set.indicator_of_notMem,hs]
    have h := anisotropic_native_terminalPair_bounded_pairing D μ a q e _ hm 1 hb
    have hAg : MeasurableSet A := ((anisotropicBrownianFiltration n).le _) A hA
    have hiA (r : Paper.Overlap) : (fun sample=>A.indicator (fun _=>(1 : ℝ)) sample*
        anisotropicProcessPairResponse D μ r e sample)=A.indicator (anisotropicProcessPairResponse D μ r e) := by
      funext sample
      by_cases hs : sample∈A <;> simp [hs]
    simp_rw [hiA,integral_indicator hAg] at h
    exact h.symm
  · exact (adapted_anisotropicProcessPairResponse D μ q e).stronglyMeasurable.aestronglyMeasurable

end QuantitativeFollowup
