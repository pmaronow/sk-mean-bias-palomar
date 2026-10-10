module
public import QuantitativeFollowup.AnisotropicTerminalPathLaw

@[expose] public section

/-! Genuine terminal-spin conditional laws for the full anisotropic profile. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

def anisotropicTerminalObservable (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (f : Configuration n→ℝ) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  anisotropicTerminalFeatureMean D f (anisotropicProcessParameter D μ 1 sample)

theorem measurable_anisotropicTerminalObservable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (f : Configuration n→ℝ) : Measurable (anisotropicTerminalObservable D μ f) :=
  (measurable_anisotropicTerminalFeatureMean D f).comp
    ((adapted_anisotropicProcessParameter D μ 1).mono ((anisotropicBrownianFiltration n).le _) le_rfl)

theorem integrable_anisotropicTerminalObservable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (f : Configuration n→ℝ) :
    Integrable (anisotropicTerminalObservable D μ f) (anisotropicMeasureSampleLaw D μ a) := by
  let B : ℝ:=∑σ : Configuration n,‖f σ‖
  have hb (σ : Configuration n) : ‖f σ‖≤B :=
    Finset.single_le_sum (fun τ _=>norm_nonneg (f τ)) (Finset.mem_univ σ)
  exact (integrable_const B).mono' (measurable_anisotropicTerminalObservable D μ f).aestronglyMeasurable
    (.of_forall fun sample=>anisotropicTerminalFeatureMean_bound D f B hb _)

theorem anisotropicMeasureSpinPathLaw_terminal_observable_condExp (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) (d : Configuration n→ℝ) :
    (anisotropicMeasureSpinPathLaw D μ a)[
      (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>d p.2)|anisotropicSpinPast n (q:ℝ).toNNReal]
      =ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      (fun p=>(anisotropicMeasureSampleLaw D μ a)[anisotropicTerminalObservable D μ d|
        anisotropicBrownianFiltration n (q:ℝ).toNNReal] p.1) := by
  let P:=anisotropicMeasureSampleLaw D μ a
  let J:=anisotropicMeasureSpinPathLaw D μ a
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n) := inferInstance
  let V:=anisotropicBrownianFiltration n (q:ℝ).toNNReal
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n) := ambient
  let F:=anisotropicTerminalObservable D μ d
  let G:=P[F|V]
  letI:=anisotropicMeasureSpinPathLaw_probability D μ a
  have hGi : Integrable G P:=integrable_condExp
  have hGm : StronglyMeasurable[V] G:=stronglyMeasurable_condExp
  have hGmg:Measurable G:=(hGm.mono ((anisotropicBrownianFiltration n).le _)).measurable
  have hci : Integrable (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>G p.1) J :=
    (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).integrable_comp_of_integrable hGi
  have hspinm:Measurable (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>d p.2):=
    (measurable_of_finite d).comp measurable_snd
  let C:=∑σ : Configuration n,|d σ|
  have hspin : Integrable (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>d p.2) J :=
    (integrable_const C).mono' hspinm.aestronglyMeasurable (.of_forall fun p=>by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ p.2))
  have had : StronglyMeasurable[anisotropicSpinPast n (q:ℝ).toNNReal]
      (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>G p.1) :=
    hGm.comp_measurable (comap_measurable Prod.fst)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (anisotropicSpinPast_le n _) hspin
  · intro A _ _
    exact hci.integrableOn
  · intro A hA _
    obtain ⟨B,hB,rfl⟩:=MeasurableSpace.measurableSet_comap.mp hA
    have hBg:MeasurableSet B:=((anisotropicBrownianFiltration n).le _) B hB
    have he:=integral_anisotropicMeasureSpinPathLaw_terminal_weight D μ a
      (B.indicator (fun _=>1)) (measurable_const.indicator hBg) 1
      (fun sample=>by by_cases hs:sample∈B <;> simp [hs]) d
    rw [integral_pullback_indicator_one_mul J Prod.fst measurable_fst B hBg,
      integral_indicator_one_mul_eq_setIntegral P B hBg] at he
    have hmB:Measurable (B.indicator G):=hGmg.indicator hBg
    have heG:=integral_anisotropicMeasureSpinPathLaw_sample D μ a (B.indicator G) hmB
    have hleft : (∫p in Prod.fst⁻¹' B,G p.1∂J)=∫sample in B,G sample∂P := by
      rw [←integral_indicator (measurable_fst hBg),←integral_indicator hBg]
      convert heG using 1
      apply integral_congr_ae
      exact .of_forall fun p=>by by_cases hs:p.1∈B <;> simp [hs]
    rw [hleft,he]
    exact setIntegral_condExp ((anisotropicBrownianFiltration n).le _)
      (integrable_anisotropicTerminalObservable D μ a d) hB
  · exact had.aestronglyMeasurable

theorem anisotropicMeasureSpinPathLaw_spin_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i : Fin n) :
    (anisotropicMeasureSpinPathLaw D μ a)[
      (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>Paper.spinSign (p.2 i))|
        anisotropicSpinPast n (q:ℝ).toNNReal]=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>anisotropicProcessSpinResponse D μ q i p.1 := by
  have h := anisotropicMeasureSpinPathLaw_terminal_observable_condExp D μ a q
    (fun σ=>Paper.spinSign (σ i))
  have he : anisotropicTerminalObservable D μ (fun σ=>Paper.spinSign (σ i))=
      anisotropicProcessSpinResponse D μ 1 i := by
    funext sample
    exact (anisotropicProcessSpinResponse_one D μ _ i).symm
  rw [he] at h
  exact h.trans ((measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).quasiMeasurePreserving.ae
    (anisotropicProcessSpinResponse_eq_condExp D μ a q i))

theorem anisotropicMeasureSpinPathLaw_pair_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    (anisotropicMeasureSpinPathLaw D μ a)[
      (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
        Paper.spinSign (p.2 e.1.1)*Paper.spinSign (p.2 e.1.2))|
          anisotropicSpinPast n (q:ℝ).toNNReal]=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>anisotropicProcessPairResponse D μ q e p.1 := by
  have h := anisotropicMeasureSpinPathLaw_terminal_observable_condExp D μ a q
    (fun σ=>Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2))
  have he : anisotropicTerminalObservable D μ (fun σ=>Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2))=
      anisotropicProcessPairResponse D μ 1 e := by
    funext sample
    exact (anisotropicTailPairResponse_one D μ _ e).symm
  rw [he] at h
  exact h.trans ((measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).quasiMeasurePreserving.ae
    (anisotropicProcessPairResponse_eq_condExp D μ a q e))

end QuantitativeFollowup
