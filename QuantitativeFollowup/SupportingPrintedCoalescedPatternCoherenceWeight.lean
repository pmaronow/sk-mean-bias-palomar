module
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceStates
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginFubini

@[expose] public section

/-! Stieltjes weights only inspect physical origins. This keeps fixed edge
parameters in their genuine cells while passing coherence through an
outer attachment integral. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128

theorem nativeStreamingOriginWeightIntegral_congr_valid
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (s : ℝ)
    (Φ Ψ : NativeStreamingOrigin T → ℝ)
    (heq : ∀ o, nativeCoalescedOriginValid q o → Φ o=Ψ o) :
    nativeStreamingOriginWeightIntegral μ a q T s Φ =
      nativeStreamingOriginWeightIntegral μ a q T s Ψ := by
  induction T generalizing s with
  | leaf =>
      change (1-s)*Φ (.vertex (.root .leaf))=(1-s)*Ψ (.vertex (.root .leaf))
      rw [heq _ trivial]
  | @advance j T ih =>
      have hchild := ih (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginChild o))
        (fun o => Ψ (nativeStreamingOriginChild o))
        (fun o ho => heq (nativeStreamingOriginChild o) (by cases o <;> exact ho))
      have hedge : (∫ r in Ioc (q (j+1)) (q j), Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a) =
          ∫ r in Ioc (q (j+1)) (q j), Ψ (.edge (.here T) r) ∂parisiFreeMeasure μ a := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact heq _ ⟨hr.1.le,hr.2⟩
      change _+_+_=_+_+_
      rw [hchild,hedge,heq (.vertex (.root T.advance)) trivial]
  | @fork j T U ihT ihU =>
      have ht := ihT (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginLeft o))
        (fun o => Ψ (nativeStreamingOriginLeft o))
        (fun o ho => heq (nativeStreamingOriginLeft o) (by cases o <;> exact ho))
      have hu := ihU (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginRight o))
        (fun o => Ψ (nativeStreamingOriginRight o))
        (fun o ho => heq (nativeStreamingOriginRight o) (by cases o <;> exact ho))
      change _+_+_=_+_+_
      rw [ht,hu,heq (.vertex (.root (.fork T U))) trivial]

theorem nativeStreamingRootCoherent_originWeightIntegral
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j k : ℕ}
    (T : FiniteTerminalGenealogy j) (U : FiniteTerminalGenealogy k) (s : ℝ)
    (Φ : FiniteCascadeRecordVertex T → NativeStreamingOrigin U → ℝ)
    (hΦ : ∀ o, nativeCoalescedOriginValid q o → nativeStreamingRootCoherent T (fun v => Φ v o)) :
    nativeStreamingRootCoherent T (fun v => nativeStreamingOriginWeightIntegral μ a q U s (Φ v)) := by
  induction T with
  | leaf => trivial
  | advance T ih => exact ih (fun v o => Φ (.child v) o) (fun o ho => hΦ o ho)
  | fork T V ihT ihV =>
      refine ⟨?_,?_,?_,?_⟩
      · exact nativeStreamingOriginWeightIntegral_congr_valid μ a q U s _ _ (fun o ho => (hΦ o ho).1)
      · exact nativeStreamingOriginWeightIntegral_congr_valid μ a q U s _ _ (fun o ho => (hΦ o ho).2.1)
      · exact ihT (fun v o => Φ (.left v) o) (fun o ho => (hΦ o ho).2.2.1)
      · exact ihV (fun v o => Φ (.right v) o) (fun o ho => (hΦ o ho).2.2.2)

end QuantitativeFollowup
