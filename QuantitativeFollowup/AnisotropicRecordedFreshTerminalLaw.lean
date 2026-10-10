module
public import QuantitativeFollowup.AnisotropicRecordedConditionalMean
public import QuantitativeFollowup.FollowupCavityRootNormalizerFreshMarks

@[expose] public section

/-! The actual full-past conditional terminal law is the normalized native
continuation kernel. Thus independent fresh marks agree with two genuinely
independent restarted continuations, rather than a repeated terminal mark. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem anisotropicFreshTerminalSpinKernel_eq_native_continuation (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    anisotropicFreshTerminalSpinKernel D μ a q=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>anisotropicObservationTerminalSpinKernel D μ q (anisotropicNativeObservation D μ q p.1) := by
  have hmeans (d : Configuration n→ℝ) :
      (fun p=>∫σ,d σ∂anisotropicFreshTerminalSpinKernel D μ a q p)=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
        fun p=>∫σ,d σ∂anisotropicObservationTerminalSpinKernel D μ q (anisotropicNativeObservation D μ q p.1) :=
    (anisotropicFreshTerminalSpinKernel_conditional_mean D μ a q d).symm.trans
      ((anisotropicMeasureSpinPathLaw_terminal_observable_condExp D μ a q d).trans
        ((measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).quasiMeasurePreserving.ae
          (anisotropic_terminal_continuation_conditional_mean D μ a q d)))
  have hsingle : ∀ᵐ p∂anisotropicMeasureSpinPathLaw D μ a,∀σ : Configuration n,
      (anisotropicFreshTerminalSpinKernel D μ a q p).real {σ}=
      (anisotropicObservationTerminalSpinKernel D μ q (anisotropicNativeObservation D μ q p.1)).real {σ} := by
    apply ae_all_iff.mpr
    intro σ
    have hh:=hmeans (({σ} : Set (Configuration n)).indicator (fun _=>1))
    filter_upwards [hh] with p hp
    have hl : (∫τ,({σ} : Set (Configuration n)).indicator (fun _=>(1:ℝ)) τ
        ∂anisotropicFreshTerminalSpinKernel D μ a q p)=
        (anisotropicFreshTerminalSpinKernel D μ a q p).real {σ} := by
      simpa using integral_indicator_const (μ:=anisotropicFreshTerminalSpinKernel D μ a q p)
        (1:ℝ) (measurableSet_singleton σ)
    have hr : (∫τ,({σ} : Set (Configuration n)).indicator (fun _=>(1:ℝ)) τ
        ∂anisotropicObservationTerminalSpinKernel D μ q (anisotropicNativeObservation D μ q p.1))=
        (anisotropicObservationTerminalSpinKernel D μ q (anisotropicNativeObservation D μ q p.1)).real {σ} := by
      simpa using integral_indicator_const
        (μ:=anisotropicObservationTerminalSpinKernel D μ q (anisotropicNativeObservation D μ q p.1))
        (1:ℝ) (measurableSet_singleton σ)
    exact hl.symm.trans (hp.trans hr)
  filter_upwards [hsingle] with p hp
  apply Measure.ext_of_singleton
  intro σ
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (hp σ)

theorem anisotropicFreshTerminalPairLaw_eq_native_continuations (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    anisotropicFreshTerminalPairLaw D μ a q=
      (anisotropicMeasureSpinPathLaw D μ a) ⊗ₘ
        ((anisotropicObservationTerminalSpinKernel D μ q).comap
          (fun p=>anisotropicNativeObservation D μ q p.1)
          ((measurable_anisotropicNativeObservation D μ q).comp measurable_fst) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q).comap
          (fun p=>anisotropicNativeObservation D μ q p.1)
          ((measurable_anisotropicNativeObservation D μ q).comp measurable_fst)) := by
  apply Measure.compProd_congr
  filter_upwards [anisotropicFreshTerminalSpinKernel_eq_native_continuation D μ a q] with p hp
  simp only [Kernel.prod_apply,Kernel.comap_apply]
  rw [hp]

theorem anisotropicFreshTerminalPairLaw_pair_marginal (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    (anisotropicFreshTerminalPairLaw D μ a q).snd=
      ((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) ∘ₘ
        ((anisotropicMeasureSampleLaw D μ a).map (anisotropicNativeObservation D μ q)) := by
  rw [anisotropicFreshTerminalPairLaw_eq_native_continuations,Measure.snd_compProd]
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map ((Kernel.prod _ _).measurable_coe hA)
      (measurable_anisotropicNativeObservation D μ q)]
  have hh:=congrArg (fun P : Measure (AnisotropicDisorderBrownianSample n)=>
      ∫⁻p,((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) (anisotropicNativeObservation D μ q p) A∂P)
    (anisotropicMeasureSpinPathLaw_fst D μ a)
  rw [Measure.fst] at hh
  have hm : Measurable (fun p : AnisotropicDisorderBrownianSample n=>
      ((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) (anisotropicNativeObservation D μ q p) A) :=
    ((Kernel.prod _ _).measurable_coe hA).comp (measurable_anisotropicNativeObservation D μ q)
  rw [lintegral_map hm measurable_fst] at hh
  convert hh using 1
  simp only [Kernel.prod_apply,Kernel.comap_apply]

end QuantitativeFollowup
