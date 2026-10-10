module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterLaw
public import FourPapersCommon.FiniteHistoryKernel
public import FourPapersCommon.TiltedPushforward

@[expose] public section

/-! The full outer Gaussian posterior realizes the genuine chronological
normalized Markov history, with every field and the terminal spin retained.
The initial distribution is the actual Gaussian fractional tilt. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityOuterHistoryMap (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (N : ℕ) (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
    (p : FiniteStateGaussianInput J×((Fin N→Field n)×S)) :
    FiniteHistory (FiniteStateField S) N×S :=
  (cascadePosteriorHistory L N (H+R p.1) p.2.1,p.2.2)

theorem measurable_cavityOuterHistoryMap (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (N : ℕ) (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    Measurable (cavityOuterHistoryMap L N R H) :=by
  have hm : Measurable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
      (H+R p.1,p.2.1)) :=by fun_prop
  exact ((measurable_independentHistory _ (measurable_cascadePosteriorUpdate L N) N).comp hm).prodMk
    measurable_snd.snd

def cavityOuterHistoryInitial (V : S→ℝ) (a : ℕ→ℝ) (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (s : ℝ) (N : ℕ) (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    Measure (FiniteStateField S) :=
  ((stdGaussian (FiniteStateGaussianInput J)).tilted
    (fun g=>s*finiteStateGaussianTerminalCascade V a L N (H+R g))).map (fun g=>H+R g)

theorem cavityOuterHistoryInitial_eq_tilted_field (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    cavityOuterHistoryInitial V a L s N R H=
      (finiteStateGaussianRawKernel R H).tilted
        (fun Q=>s*finiteStateGaussianTerminalCascade V a L N Q) :=by
  have he:=map_tilted_pullback (stdGaussian (FiniteStateGaussianInput J))
    (fun g=>H+R g) (by fun_prop)
    (fun Q=>s*finiteStateGaussianTerminalCascade V a L N Q)
    (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L N).continuous.measurable).const_mul s)
  simpa only [cavityOuterHistoryInitial,Function.comp_def,finiteStateGaussianRawKernel_apply] using he

private theorem posterior_history_kernel_apply (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) (H : FiniteStateField S) :
    (((Kernel.id : Kernel (FiniteHistory (FiniteStateField S) N) (FiniteHistory (FiniteStateField S) N))×ₖ
      cascadePosteriorTerminalKernel V N) ∘ₖ finiteHistoryKernel (cascadePosteriorKernel V a L N) N) H=
      cascadePosteriorLaw V a L N H :=by
  haveI:=isProbabilityMeasure_finiteHistoryLaw (Measure.dirac H) _
    (cascadePosteriorKernel_markov V a ha L N) N
  rw [Kernel.comp_apply,finiteHistoryKernel_apply _ (cascadePosteriorKernel_markov V a ha L N)]
  change (_ ∘ₘ _)=_
  rw [←Measure.compProd_eq_comp_prod]
  rfl

theorem cavityOuterHistoryMap_law (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    (cavityOuterPosteriorLaw V a L s N R H).map (cavityOuterHistoryMap L N R H)=
      finiteHistoryLaw (cavityOuterHistoryInitial V a L s N R H)
        (cascadePosteriorKernel V a L N) N ⊗ₘ cascadePosteriorTerminalKernel V N :=by
  let P:=(stdGaussian (FiniteStateGaussianInput J)).tilted
    (fun g=>s*finiteStateGaussianTerminalCascade V a L N (H+R g))
  haveI := isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz
    (finiteStateGaussianTerminalCascade V a L N) (finiteStateGaussianTerminalCascade_lipschitz V a ha L N)
      R H s)
  haveI := cavityPosteriorGaussianKernel_markov V a ha L N
  haveI := finiteHistoryKernel_markov (cascadePosteriorKernel V a L N)
    (cascadePosteriorKernel_markov V a ha L N) N
  haveI : IsProbabilityMeasure (cavityOuterHistoryInitial V a L s N R H):=by
    unfold cavityOuterHistoryInitial
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  haveI:=isProbabilityMeasure_finiteHistoryLaw (cavityOuterHistoryInitial V a L s N R H) _
    (cascadePosteriorKernel_markov V a ha L N) N
  let K:=((Kernel.id : Kernel (FiniteHistory (FiniteStateField S) N) (FiniteHistory (FiniteStateField S) N))×ₖ
      cascadePosteriorTerminalKernel V N) ∘ₖ finiteHistoryKernel (cascadePosteriorKernel V a L N) N
  have hk : K ∘ₘ cavityOuterHistoryInitial V a L s N R H=
      finiteHistoryLaw (cavityOuterHistoryInitial V a L s N R H)
        (cascadePosteriorKernel V a L N) N ⊗ₘ cascadePosteriorTerminalKernel V N :=by
    rw [←Measure.comp_assoc,finiteHistoryKernel_comp _ _ (cascadePosteriorKernel_markov V a ha L N),
      ←Measure.compProd_eq_comp_prod]
  have hK (Q : FiniteStateField S) : K Q=cascadePosteriorLaw V a L N Q :=
    posterior_history_kernel_apply V a ha L N Q
  rw [←hk]
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_cavityOuterHistoryMap L N R H)]
  rw [cavityOuterPosteriorLaw]
  change (∫⁻p,(F ∘ cavityOuterHistoryMap L N R H) p ∂(_ ⊗ₘ _))=_
  rw [Measure.lintegral_compProd
    (hF.comp (measurable_cavityOuterHistoryMap L N R H)),
    Measure.lintegral_bind K.aemeasurable hF.aemeasurable,
    cavityOuterHistoryInitial,lintegral_map (hF.lintegral_kernel) (by fun_prop)]
  apply lintegral_congr
  intro g
  rw [Kernel.comap_apply,cavityPosteriorGaussianKernel_apply V a ha L N,
    hK,
    ←cascadePosteriorGaussianLaw_map V a ha L N (H+R g),
    lintegral_map hF (measurable_cascadePosteriorCoordinateMap L N (H+R g))]
  rfl

end QuantitativeFollowup
