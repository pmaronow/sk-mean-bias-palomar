module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTwoBlockSelection

@[expose] public section

/-! The diagonal and reverse-order cases of the genuine two-ancestor
block law. Equal observations retain the same ancestral field. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {E S : Type} {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem nativeStreamingTwoBlockSelection_swap {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p k : ℕ) :
    nativeStreamingTwoBlockSelection (E:=E) (S:=S) T d p k=
      (fun z=> (z.2.1,(z.1,z.2.2))) ∘ nativeStreamingTwoBlockSelection T d k p := by
  funext z
  rfl

 theorem nativeStreamingTwoBlockSelection_kernel_eq (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (Q : ℕ → Paper.Overlap) (hQ : Antitone Q)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d p : ℕ) (hp : p<d) :
    (anisotropicRecordedProfileTreeKernel D μ Q (.advance (observationTreePad T d))).map
      (nativeStreamingTwoBlockSelection T d p p)=
      ((Kernel.id ×ₖ ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ Q T) ∘ₖ
        anisotropicObservationTransition D μ (Q (j+p+1)) (Q j))) ∘ₖ
          anisotropicObservationTransition D μ (Q (j+d+1)) (Q (j+p+1))).map
            (fun z=> (z.1,(z.1,z.2))) := by
  rw [nativeStreamingTwoBlockSelection_equal,
    Kernel.map_comp_right _ (measurable_nativeStreamingBlockSelectionAt T d p)
      (measurable_fst.prodMk (measurable_fst.prodMk measurable_snd)),
    nativeStreamingBlockSelectionAt_kernel D μ Q hQ T d p hp]

 theorem nativeStreamingTwoBlockSelection_kernel_gt (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (Q : ℕ → Paper.Overlap) (hQ : Antitone Q)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d p k : ℕ) (hkp : k<p) (hp : p<d) :
    (anisotropicRecordedProfileTreeKernel D μ Q (.advance (observationTreePad T d))).map
      (nativeStreamingTwoBlockSelection T d p k)=
      (Kernel.id ×ₖ ((Kernel.id ×ₖ ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ Q T) ∘ₖ
        anisotropicObservationTransition D μ (Q (j+k+1)) (Q j))) ∘ₖ
          anisotropicObservationTransition D μ (Q (j+p+1)) (Q (j+k+1)))) ∘ₖ
            anisotropicObservationTransition D μ (Q (j+d+1)) (Q (j+p+1)) := by
  have hs : Measurable (fun z : AnisotropicObservationState n ×
      (AnisotropicObservationState n × (AnisotropicObservationState n ×
        Records (AnisotropicObservationState n) (Configuration n) T)) =>
          (z.2.1,(z.1,z.2.2))) :=
    measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)
  rw [nativeStreamingTwoBlockSelection_swap T d p k,
    Kernel.map_comp_right _ (measurable_nativeStreamingTwoBlockSelection T d k p) hs,
    nativeStreamingTwoBlockSelection_kernel_lt D μ Q hQ T d k p hkp hp,
    ←Kernel.map_comp_right _ hs hs]
  change Kernel.map _ id=_
  exact Kernel.map_id _

end QuantitativeFollowup
